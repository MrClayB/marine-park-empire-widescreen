/* Widescreen interposer for Marine Park Empire (d3d9.dll proxy).
 *
 * The game only knows two display profiles (800x600 and 1024x768) and lays every screen out for them.
 * This DLL, loaded in place of d3d9.dll, makes the 1024x768 profile follow the desktop resolution:
 *   - the 3D world and mouse range cover the whole screen (more map at the sides, nothing stretched);
 *   - screens that do not click into the 3D world (main menu, setup/load/tutorial screens) have their
 *     1024x768 interface block centred on the screen;
 *   - in a running zoo the original (unshifted) interface layout is kept, because the engine uses a single
 *     mouse position for both UI and world and cannot represent a shifted UI without breaking world clicks.
 * Everything is done in memory; mpe.exe on disk is not modified.
 */
#define COBJMACROS
#include <windows.h>
#include <d3d9.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdarg.h>

#include "sites.h"
#define UI_W 1024
#define UI_H 768

static int SW = UI_W, SH = UI_H;   /* desktop size */
static int ox, oy;                 /* where the 1024x768 UI block sits on screen while centred */
static FILE *lg;

/* Game state flags inside mpe.exe's data (found by diffing memory between menus and a running zoo):
   both are 0 in the front end and become 1 when a zoo starts. */
/* 0x10760a5 drops to 0 while some modal dialogs (Tips) are open although the zoo is still running; 0xfd984a stays 1
   for the whole zoo session, so once the zoo has started it decides. */
static int inGame(void) {
  static int seen;
  if (!*(volatile unsigned char *)0xfd984a) { seen = 0; return 0; }
  if (*(volatile unsigned char *)0x10760a5) seen = 1;
  return seen;
}
#define COX() (inGame() ? 0 : ox)
#define COY() (inGame() ? 0 : oy)

/* Menus are scaled uniformly (FS) about the screen centre so they fill the screen; engine cursor coordinates
   (the 1024x768 layout, shifted by ox,oy) map to screen pixels as  C + FS*(e + o - C). */
static float FS = 1.0f;
static float GG = 1.0f;            /* in-game HUD scale, applied about each piece's anchor */
static int dbgCx, dbgCy;
static int feToScreenX(int e) { return (int)(SW * 0.5f + FS * (e + ox - SW * 0.5f) + 0.5f); }
static int feToScreenY(int e) { return (int)(SH * 0.5f + FS * (e + oy - SH * 0.5f) + 0.5f); }
static int screenToFeX(int p) { return (int)floorf((p - SW * 0.5f) / FS + SW * 0.5f - ox + 0.5f); }
static int screenToFeY(int p) { return (int)floorf((p - SH * 0.5f) / FS + SH * 0.5f - oy + 0.5f); }
/* cursor range in engine coordinates that exactly covers the screen */
static void feRect(int *L, int *T, int *R, int *B) {
  *L = screenToFeX(0) + 1; *T = screenToFeY(0) + 1; *R = screenToFeX(SW - 1) - 1; *B = screenToFeY(SH - 1) - 1;
}

static void note(const char *fmt, ...) {
  if (!lg) return;
  va_list a; va_start(a, fmt); vfprintf(lg, fmt, a); va_end(a); fflush(lg);
}

/* ---------- display profile (entry 1 of the table in mpe.exe's .data) ---------- */
#define PROFILE1_ADDR 0x924328u
/* dwords: [1],[2] size; [4..7] cursor clamp rect; [10..13] 3D camera rect; [22..25] second screen rect.
   The cursor clamp and second rect are expressed in the shifted (front end) space; the camera rect must
   stay at 0,0 because the engine rejects a camera with a negative origin. */
static void patchProfile(void) {
  if ((DWORD)GetModuleHandleA(NULL) != 0x400000) { note("unexpected image base\n"); return; }
  DWORD *p = (DWORD *)PROFILE1_ADDR;
  if (p[0] != 1 || p[1] != 1024 || p[2] != 768) { note("profile mismatch %u %u %u\n", p[0], p[1], p[2]); return; }
  DWORD old; VirtualProtect(p, 0x70, PAGE_READWRITE, &old);
  int L, T, R, B; feRect(&L, &T, &R, &B);
  p[1] = SW; p[2] = SH;
  p[4] = L; p[5] = T; p[6] = R; p[7] = B;
  p[10] = 0; p[11] = 0; p[12] = SW - 1; p[13] = SH - 1;
  p[14] = SW; p[15] = SH;
  p[22] = L; p[23] = T; p[24] = R; p[25] = B;
  p[26] = SW; p[27] = SH;
  VirtualProtect(p, 0x70, old, &old);
  note("profile patched %dx%d, front-end UI offset %d,%d\n", SW, SH, ox, oy);
}

/* make VIDEO.DAT agree with the desktop size so the game accepts the mode */
static void patchVideoDat(void) {
  char path[MAX_PATH]; GetModuleFileNameA(NULL, path, MAX_PATH);
  char *s = strrchr(path, '\\'); if (!s) return; strcpy(s + 1, "VIDEO.DAT");
  FILE *f = fopen(path, "rb"); if (!f) return;
  unsigned char b[17]; size_t n = fread(b, 1, 17, f); fclose(f);
  if (n != 17) return;
  DWORD w = *(DWORD *)b, h = *(DWORD *)(b + 4);
  if (w == 800 && h == 600) return;          /* user chose the 800x600 profile: leave it */
  if (w == (DWORD)SW && h == (DWORD)SH) return;
  *(DWORD *)b = SW; *(DWORD *)(b + 4) = SH;
  f = fopen(path, "wb"); if (!f) return; fwrite(b, 1, 17, f); fclose(f);
  note("VIDEO.DAT -> %dx%d\n", SW, SH);
}

/* ---------- Win32 cursor calls (imported by address from mpe.exe) ---------- */
#define IAT_GETCURSORPOS 0x87d2e8u
#define IAT_SETCURSORPOS 0x87d2f8u
typedef BOOL (WINAPI *PFN_GCP)(LPPOINT);
typedef BOOL (WINAPI *PFN_SCP)(int, int);
static PFN_GCP oGCP; static PFN_SCP oSCP;
/* the game seeds its virtual cursor from the OS cursor at start-up (front end): give it front-end coordinates */
static BOOL WINAPI hGCP(LPPOINT p) { BOOL r = oGCP(p); if (r && p) { p->x = screenToFeX(p->x); p->y = screenToFeY(p->y); } return r; }
static BOOL WINAPI hSCP(int x, int y) { return inGame() ? oSCP(x, y) : oSCP(feToScreenX(x), feToScreenY(y)); }
static void patchIAT(void) {
  static int done; if (done) return; done = 1;
  void **g = (void **)IAT_GETCURSORPOS, **s2 = (void **)IAT_SETCURSORPOS;
  HMODULE u = GetModuleHandleA("user32.dll");
  if (*g != (void *)GetProcAddress(u, "GetCursorPos") || *s2 != (void *)GetProcAddress(u, "SetCursorPos")) { note("IAT mismatch\n"); return; }
  DWORD old; VirtualProtect(g, 4, PAGE_READWRITE, &old); oGCP = (PFN_GCP)*g; *g = hGCP; VirtualProtect(g, 4, old, &old);
  VirtualProtect(s2, 4, PAGE_READWRITE, &old); oSCP = (PFN_SCP)*s2; *s2 = hSCP; VirtualProtect(s2, 4, old, &old);
}

/* ---------- Direct3D 9 hooks ---------- */
typedef HRESULT (WINAPI *PFN_TR)(IDirect3DDevice9 *, D3DTRANSFORMSTATETYPE, const D3DMATRIX *);
typedef HRESULT (WINAPI *PFN_CD)(IDirect3D9 *, UINT, D3DDEVTYPE, HWND, DWORD, D3DPRESENT_PARAMETERS *, IDirect3DDevice9 **);
typedef IDirect3D9 *(WINAPI *PFN_D3DC)(UINT);
typedef HRESULT (WINAPI *PFN_VP)(IDirect3DDevice9 *, const D3DVIEWPORT9 *);
typedef void (WINAPI *PFN_SCPOS)(IDirect3DDevice9 *, int, int, DWORD);
static PFN_SCPOS oSCPOS;
static PFN_TR oTR; static PFN_CD oCD; static PFN_VP oVP;
static int bbW, bbH;

/* ---------- UI mouse mirror ----------
   The engine keeps ONE mouse position (screen pixels in a zoo). The interface code reads it directly (274
   places) or through the cursor object's InRect-style methods (561 call sites). Those reads are redirected to
   this mirror, which holds the mouse position in the interface's own 1024x768 layout space: the real position
   minus the shift of whichever interface piece is under the pointer (or "nowhere" over the 3D world).
   The 3D camera / picking code keeps reading the real position. */
#define CURSOR_OBJ 0x10638c0u
#define CURSOR_SIZE 0x700
/* a shadow of the engine's cursor object: its current position (+0x1c,+0x20) and the stored button press /
   release positions are in layout space; everything else is a copy */
static union { unsigned char raw[CURSOR_SIZE]; struct { unsigned char pad[0x1c]; volatile int x, y; }; } mirror;
#define REAL_X (*(volatile int *)0x10638dc)
#define REAL_Y (*(volatile int *)0x10638e0)

typedef struct { int l, t, r, b; int sx, sy; int ol, ot, or_, ob; int afx, afy; } Grp;   /* shifted rect, shift, original rect */
#define MAXG 512
static Grp gNow[MAXG], gShown[MAXG];
static int nNow, nShown;
static int capKind;                   /* 0 none, 1 captured by a piece, 2 captured by the world */
static int capSx, capSy, capAfx, capAfy, wasDown;
static int ptrOn, ptrSx, ptrSy, ptrAfx, ptrAfy;      /* the piece under the pointer (if any) and its shift */

/* The engine's cursor range comes from the display profile, i.e. the centred front-end space. In a zoo the
   cursor must cover the whole screen in screen coordinates, so re-base it whenever the mode flips. */
#define CUR_CLAMP ((volatile int *)(0x10638c0 + 0x524))
static void rebaseCursor(int in) {
  static int last = -1;
  if (in == last) return;
  int first = last < 0; last = in;
  if (first && !in) return;
  int d = in ? 1 : -1;
  note("old clamp %d %d %d %d pos %d %d\n", CUR_CLAMP[0], CUR_CLAMP[1], CUR_CLAMP[2], CUR_CLAMP[3], (int)REAL_X, (int)REAL_Y);
  int x = in ? feToScreenX(REAL_X) : screenToFeX(REAL_X), y = in ? feToScreenY(REAL_Y) : screenToFeY(REAL_Y);
  int L, T, R, B; feRect(&L, &T, &R, &B);
  if (in) { L = 0; T = 0; R = SW - 1; B = SH - 1; }
  /* the cursor rect is re-read from the active profile (0xfe75b0..) on every screen change: switch that too */
  volatile int *ap = (volatile int *)0xfe75b0, *tp = (volatile int *)(PROFILE1_ADDR + 0x10);
  ap[0] = tp[0] = L; ap[1] = tp[1] = T; ap[2] = tp[2] = R; ap[3] = tp[3] = B;
  CUR_CLAMP[0] = L; CUR_CLAMP[1] = T; CUR_CLAMP[2] = R; CUR_CLAMP[3] = B;
  if (x < CUR_CLAMP[0]) x = CUR_CLAMP[0]; if (x > CUR_CLAMP[2]) x = CUR_CLAMP[2];
  if (y < CUR_CLAMP[1]) y = CUR_CLAMP[1]; if (y > CUR_CLAMP[3]) y = CUR_CLAMP[3];
  REAL_X = x; REAL_Y = y;
  note("cursor space -> %s\n", in ? "screen" : "front end");
}

/* screen position -> the piece's own layout space: undo the scale about the anchor, then the shift */
static int unmapC(int g, int af, int sh) { float G = inGame() ? GG : 1.0f; return (int)floorf(af + (g - af) / G + 0.5f) - sh; }

/* layout-space position of a screen position: minus the shift of the piece it is over; -9999 over the world */
static void toLayout(int gx, int gy, int *ux, int *uy) {
  int fallback = !inGame();
  for (int i = nShown - 1; i >= 0; i--) {
    Grp *g = &gShown[i];
    if (gx >= g->l && gx <= g->r && gy >= g->t && gy <= g->b) { *ux = unmapC(gx, g->afx, g->sx); *uy = unmapC(gy, g->afy, g->sy); return; }
  }
  if (fallback) { *ux = gx; *uy = gy; } else { *ux = -9999; *uy = -9999; }
}

static int curU_x, curU_y;            /* current pointer in layout space */
static int dbgOff, dbgPhase;                    /* debug: widescreen.off exists -> interface reads see the real pointer */

static void computeCurrent(void) {
  int gx = REAL_X, gy = REAL_Y;
  int down = (GetAsyncKeyState(VK_LBUTTON) | GetAsyncKeyState(VK_RBUTTON)) & 0x8000;
  int found = 0, sx = 0, sy = 0, afx = 0, afy = 0;
  if (down && wasDown && capKind) {
    found = capKind == 1; sx = capSx; sy = capSy; afx = capAfx; afy = capAfy;
  } else {
    for (int i = nShown - 1; i >= 0; i--) {
      Grp *g = &gShown[i];
      if (gx >= g->l && gx <= g->r && gy >= g->t && gy <= g->b) { found = 1; sx = g->sx; sy = g->sy; afx = g->afx; afy = g->afy; break; }
    }
    if (down) { capKind = found ? 1 : 2; capSx = sx; capSy = sy; capAfx = afx; capAfy = afy; } else capKind = 0;
  }
  wasDown = down != 0;
  ptrOn = found; ptrSx = sx; ptrSy = sy; ptrAfx = afx; ptrAfy = afy;
  if (found) { curU_x = unmapC(gx, afx, sx); curU_y = unmapC(gy, afy, sy); } else if (inGame()) { curU_x = -9999; curU_y = -9999; } else { curU_x = gx; curU_y = gy; }
  /* dragging something out of the interface (an animal from the list, a build item) and over the 3D world:
     the world code that draws the drop preview needs the real pointer position */
  if (inGame() && down && capKind == 1 && found) {
    int over = 0;
    for (int i = nShown - 1; i >= 0; i--) { Grp *g = &gShown[i]; if (gx >= g->l && gx <= g->r && gy >= g->t && gy <= g->b) { over = 1; break; } }
    if (!over) { curU_x = gx; curU_y = gy; }
  }
  /* pointer on the bottom-left button cluster while a build / animal panel is open: the world's drop preview would
     read the cluster's layout position (half way up the screen), so hand out the real position instead (button
     presses still use the layout position, see the capture above) */
  if (inGame() && found && !down) {
    int onCluster = 0, panelOpen = 0;
    for (int i = 0; i < nShown; i++) { Grp *g = &gShown[i]; if (g->or_ - g->ol > 400 && g->ot > 450 && g->ot < 700) panelOpen = 1; }
    for (int i = nShown - 1; i >= 0; i--) { Grp *g = &gShown[i];
      if (gx >= g->l && gx <= g->r && gy >= g->t && gy <= g->b) { onCluster = g->ot >= 480 && g->ob <= 780; break; } }
    if (onCluster && panelOpen) { curU_x = gx; curU_y = gy; }
  }
  /* over the 3D world the interface reads the real position (the drop preview of an animal / building follows it),
     unless that position happens to fall inside a visible piece's layout rectangle (would be a false hover) */
  if (inGame() && !found) {
    int clash = 0;
    for (int i = 0; i < nShown; i++) { Grp *g = &gShown[i]; if (gx >= g->ol - 4 && gx <= g->or_ + 4 && gy >= g->ot - 4 && gy <= g->ob + 4) { clash = 1; break; } }
    if (!clash) { curU_x = gx; curU_y = gy; }
  }
  if (dbgOff) { curU_x = gx; curU_y = gy; }
}

static void updateMirror(void) {
  { static int n; if ((n++ & 31) == 0) dbgOff = GetFileAttributesA("widescreen.off") != INVALID_FILE_ATTRIBUTES; dbgPhase = GetFileAttributesA("widescreen.p1") != INVALID_FILE_ATTRIBUTES; }
  rebaseCursor(inGame());
  computeCurrent();
  mirror.x = curU_x; mirror.y = curU_y;
  { static int lx, ly, ln; int gx = REAL_X, gy = REAL_Y;
    if ((gx != lx || gy != ly) && ln < 400) { ln++; lx = gx; ly = gy; note("mouse real(%d,%d) ui(%d,%d) grp=%d\n", gx, gy, curU_x, curU_y, ptrOn); } }
}

/* Called at the entry of every cursor method that compares positions with interface rectangles: builds the
   shadow object they will look at. */
static const unsigned posOff[] = { 0x57c, 0x580, 0x584, 0x588, 0x598, 0x59c, 0x5a0, 0x5a4, 0x5b4, 0x5b8, 0x5bc, 0x5c0 };
static void *__attribute__((cdecl)) prepShadow(void) {
  memcpy(mirror.raw, (void *)CURSOR_OBJ, CURSOR_SIZE);
  {
    computeCurrent();
    mirror.x = curU_x; mirror.y = curU_y;
    for (unsigned i = 0; i < sizeof posOff / sizeof *posOff; i += 2) {
      int *px = (int *)(mirror.raw + posOff[i]), *py = (int *)(mirror.raw + posOff[i + 1]);
      int ux, uy; if (dbgOff) continue; toLayout(*px, *py, &ux, &uy); *px = ux; *py = uy;
    }
  }
  return mirror.raw;
}

static int dbgN; static int cfgMask;
static void *__attribute__((cdecl)) prepShadowIR(int r2, int l, int t, int r, int b) {
  static int cnt; (void)cnt;
  void *p = prepShadow();
  /* a test against (nearly) the whole screen is the root/3D-view window asking where the pointer is: real position */
  if (inGame() && (r - l) >= SW * 7 / 10 && (b - t) >= SH * 7 / 10) return (void *)CURSOR_OBJ;
  int gx = REAL_X, gy = REAL_Y, ux = mirror.x, uy = mirror.y;
  if (dbgN < 400 && ((r2 >= 0x69b000 && r2 < 0x69d000) || (r2 >= 0x5ed800 && r2 < 0x5ef000) || (r2 >= 0x5f2000 && r2 < 0x5f3400))) { dbgN++; note("InRect caller %x rect(%d,%d,%d,%d) real(%d,%d) ui(%d,%d)\n", r2, l, t, r, b, gx, gy, ux, uy); }
  return p;
}

typedef unsigned char (__attribute__((thiscall)) *PFN_HT)(void *, int, int);
static PFN_HT oHT;
static unsigned char __attribute__((thiscall)) hHT(void *self, int x, int y) {
  unsigned char r = oHT(self, x, y);
  short *w = (short *)((char *)self + 5);
  static int n;
  if (n < 40) {
    n++; note("hit5f3310 win(%d,%d,%d,%d) pt(%d,%d) -> %d\n", w[0], w[1], w[2], w[3], x, y, r);
  }
  return r;
}
static void hookHT(void) {
  unsigned char *src = (unsigned char *)0x5f3310;
  unsigned char *t = VirtualAlloc(NULL, 32, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
  memcpy(t, src, 5); t[5] = 0xE9; *(int *)(t + 6) = (int)(0x5f3315 - (unsigned)(t + 10));
  oHT = (PFN_HT)t;
  DWORD old; VirtualProtect(src, 5, PAGE_EXECUTE_READWRITE, &old);
  src[0] = 0xE9; *(int *)(src + 1) = (int)((unsigned)hHT - (unsigned)(src + 5));
  VirtualProtect(src, 5, old, &old);
}

typedef int (__attribute__((thiscall)) *PFN_WH)(void *, int, int, int, int, int, int);
static PFN_WH oWH;
static int __attribute__((thiscall)) hWH(void *self, int a1, int a2, int a3, int a4, int a5, int a6) {
  int r = oWH(self, a1, a2, a3, a4, a5, a6);
  unsigned char *p = (unsigned char *)self; short *w = (short *)(p + 0x1e);
  static int n;
  if (n < 80 && p[9] && (r || (REAL_X > -2000 && w[0] > 900))) {
    n++; note("wh5ed8a0 self=%p vis=%d rect(%d,%d,%d,%d) flags %d %d %d %d args %x %x %x %x %x %x -> %d\n", self, p[9], w[0], w[1], w[2], w[3], p[2], p[3], p[4], p[0x30], a1, a2, a3, a4, a5, a6, r);
  }
  return r;
}
static void hookWH(void) {
  unsigned char *src = (unsigned char *)0x5ed8a0;
  unsigned char *t = VirtualAlloc(NULL, 32, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
  memcpy(t, src, 5); t[5] = 0xE9; *(int *)(t + 6) = (int)(0x5ed8a5 - (unsigned)(t + 10));
  oWH = (PFN_WH)t;
  DWORD old; VirtualProtect(src, 5, PAGE_EXECUTE_READWRITE, &old);
  src[0] = 0xE9; *(int *)(src + 1) = (int)((unsigned)hWH - (unsigned)(src + 5));
  VirtualProtect(src, 5, old, &old);
}

/* mouse reads inside the code that picks things out of the 3D world keep the real pointer position */
static int worldSite(unsigned a) { return a >= 0x573280 && a <= 0x5734b8; }
static void patchDword(unsigned addr, unsigned expect, unsigned val) {
  unsigned *p = (unsigned *)addr; DWORD old;
  if (*p != expect) return;
  VirtualProtect(p, 4, PAGE_EXECUTE_READWRITE, &old); *p = val; VirtualProtect(p, 4, old, &old);
}

/* redirect each position-comparing cursor method: its first bytes become a jump to a stub that swaps `this`
   for the shadow, runs the displaced bytes and continues. Call sites that test the 3D viewport rectangle are
   pointed at an untouched copy so they keep the real position. */
static void patchMouse(void) {
  if ((DWORD)GetModuleHandleA(NULL) != 0x400000) return;
  if (cfgMask & 4) return;
  for (unsigned i = 0; i < sizeof rdX / sizeof *rdX && !(cfgMask & 16); i++) if (!worldSite(rdX[i])) patchDword(rdX[i], 0x10638dc, (unsigned)&mirror.x);
  for (unsigned i = 0; i < sizeof rdY / sizeof *rdY && !(cfgMask & 16); i++) if (!worldSite(rdY[i])) patchDword(rdY[i], 0x10638e0, (unsigned)&mirror.y);
  for (unsigned i = 0; i < sizeof rdX2 / sizeof *rdX2; i++) patchDword(rdX2[i], 0x10638dc, (unsigned)&mirror.x);
  for (unsigned i = 0; i < sizeof rdY2 / sizeof *rdY2; i++) patchDword(rdY2[i], 0x10638e0, (unsigned)&mirror.y);
  if (cfgMask & 2) return;
  unsigned nm = sizeof methEntry / sizeof *methEntry;
  unsigned char *buf = VirtualAlloc(NULL, nm * 64, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
  if (!buf) return;
  unsigned char *w = buf; unsigned plain[64], patched = 0;
  for (unsigned i = 0; i < nm; i++) {
    unsigned char *src = (unsigned char *)methEntry[i]; unsigned n = methLen[i];
    /* untouched copy */
    plain[i] = (unsigned)w;
    memcpy(w, src, n); w += n; *w++ = 0xE9; *(int *)w = (int)(methEntry[i] + n - (unsigned)(w + 4)); w += 4;
    /* shadowing stub */
    unsigned char *stub = w;
    *w++ = 0x81; *w++ = 0xF9; *(unsigned *)w = CURSOR_OBJ; w += 4;      /* cmp ecx, cursor */
    *w++ = 0x75; *w++ = 0x07;                                           /* jne +7 */
    *w++ = 0xE8; *(int *)w = (int)((unsigned)(void *)prepShadowIR - (unsigned)(w + 4)); w += 4;   /* call prepShadow */
    *w++ = 0x89; *w++ = 0xC1;                                           /* mov ecx, eax */
    memcpy(w, src, n); w += n; *w++ = 0xE9; *(int *)w = (int)(methEntry[i] + n - (unsigned)(w + 4)); w += 4;
    DWORD old; VirtualProtect(src, n, PAGE_EXECUTE_READWRITE, &old);
    src[0] = 0xE9; *(int *)(src + 1) = (int)((unsigned)stub - (unsigned)(src + 5));
    for (unsigned k = 5; k < n; k++) src[k] = 0x90;
    VirtualProtect(src, n, old, &old);
    patched++;
  }
  for (unsigned i = 0; i < sizeof exclCall / sizeof *exclCall; i++) {
    unsigned char *c = (unsigned char *)exclCall[i];
    if (c[0] != 0xE8) continue;
    unsigned target = exclCall[i] + 5 + *(int *)(c + 1);
    for (unsigned k = 0; k < nm; k++) if (methEntry[k] == target) {
      DWORD old; VirtualProtect(c, 5, PAGE_EXECUTE_READWRITE, &old);
      *(int *)(c + 1) = (int)(plain[k] - (exclCall[i] + 5));
      VirtualProtect(c, 5, old, &old);
    }
  }
  note("mouse: %u direct reads, %u cursor methods redirected\n", (unsigned)(sizeof rdX / sizeof *rdX + sizeof rdY / sizeof *rdY), patched);
}

/* ---------- interface anchoring in a running zoo ----------
   In a zoo the interface is drawn with an orthographic projection as indexed triangle lists whose vertices are
   in the 1024x768 layout, centred on the screen centre. Each draw is split into pieces (connected groups of
   triangles) and every piece is anchored to the screen edge/corner/centre it was laid out near. */
static int orthoNow;
static D3DMATRIX curWorld; static int haveWorld;
static int fillTol = 10;

static HRESULT WINAPI hTR(IDirect3DDevice9 *d, D3DTRANSFORMSTATETYPE s, const D3DMATRIX *m) {
  if (s == D3DTS_PROJECTION) orthoNow = (m->_34 == 0.0f && m->_44 == 1.0f);
  if (s == D3DTS_WORLD) { curWorld = *m; haveWorld = 1; }
  if (s == D3DTS_PROJECTION && m->_34 == 0.0f && m->_44 == 1.0f && bbW > 0 && (COX() || COY())) {
    D3DMATRIX n = *m;
    n._41 += 2.0f * COX() / bbW;
    n._42 -= 2.0f * COY() / bbH;
    n._11 *= FS; n._21 *= FS; n._31 *= FS; n._41 *= FS;
    n._12 *= FS; n._22 *= FS; n._32 *= FS; n._42 *= FS;
    return oTR(d, s, &n);
  }
  return oTR(d, s, m);
}

/* front-end frames drawn in real screen coordinates (loading screens) / with the 4:3 menu backdrop (sub menus) */
static int rawNow, rawPrev, subNow, vidNow, vidPrev;   /* vid*: photo / video camera overlay (a full 4:3 layout piece) */
static int callIdx, prevCalls;      /* UI draw calls so far this frame / in the previous frame (tooltips are drawn last) */
static int nearCorner(int px, int py, int l, int t, int r, int b, int d) {
  return ((abs(px - l) < d || abs(px - r) < d) && (abs(py - t) < d || abs(py - b) < d));
}

static void anchorFor(int l, int t, int r, int b, int *sx, int *sy, int *afx, int *afy) {
  int dx = SW - UI_W, dy = SH - UI_H;
  if (inGame() && (vidNow || vidPrev)) {      /* camera overlay: every piece hangs on the screen edge / centre it was laid out near */
    int cx2 = (l + r) / 2, cy2 = (t + b) / 2, w2 = r - l, h2 = b - t;
    *sx = (w2 >= UI_W * 8 / 10) ? dx / 2 : cx2 < UI_W / 4 ? 0 : cx2 > UI_W * 3 / 4 ? dx : dx / 2;
    *sy = (h2 >= UI_H * 8 / 10) ? dy / 2 : cy2 < UI_H / 3 ? 0 : cy2 > UI_H * 2 / 3 ? dy : dy / 2;
    *afx = *sx == 0 ? 0 : *sx == dx ? SW : SW / 2;
    *afy = *sy == 0 ? 0 : *sy == dy ? SH : SH / 2;
    return;
  }
  int cx = (l + r) / 2, cy = (t + b) / 2, w = r - l, h = b - t;
  long area = (long)w * h;
  if (ptrOn && w < 520 && h < 140 && callIdx >= prevCalls - 8 && mirror.x + 110 >= l && mirror.x - 110 <= r && mirror.y + 90 >= t && mirror.y - 90 <= b) {
    *sx = ptrSx; *sy = ptrSy; *afx = ptrAfx; *afy = ptrAfy; return;                     /* tooltip / drag image next to the pointer */
  }
  /* sits on top of a bigger piece (drawn earlier this frame, or seen last frame): move with it */
  for (int pass = 0; pass < 2; pass++) {
    Grp *list = pass ? gShown : gNow; int n = pass ? nShown : nNow;
    for (int i = n - 1; i >= 0; i--) {
      Grp *g = &list[i];
      long ga = (long)(g->or_ - g->ol) * (g->ob - g->ot);
      if (ga > area && cx >= g->ol && cx <= g->or_ && cy >= g->ot && cy <= g->ob) { *sx = g->sx; *sy = g->sy; *afx = g->afx; *afy = g->afy; return; }
    }
  }
  { long da = (long)(cx - SW / 2) * (cx - SW / 2) + (long)(cy - SH / 2) * (cy - SH / 2);
    long db = (long)(cx - UI_W / 2) * (cx - UI_W / 2) + (long)(cy - UI_H / 2) * (cy - UI_H / 2);
    if (da < db) { *sx = inGame() ? 0 : -ox; *sy = inGame() ? 0 : -oy; *afx = SW / 2; *afy = SH / 2; return; }   /* centred on the real screen by the engine */
  }
  *afx = 0; *afy = 0;
  if (!inGame()) { *sx = 0; *sy = 0; return; }                /* menus: the whole layout is centred by the projection */
  *sx = 0; *sy = dy; *afy = SH;                               /* in a zoo the HUD keeps its original layout, scaled, sitting on the bottom-left corner */
  (void)dx; (void)dy; (void)cx; (void)cy;
}

typedef HRESULT (WINAPI *PFN_DIP)(IDirect3DDevice9 *, D3DPRIMITIVETYPE, INT, UINT, UINT, UINT, UINT);
static PFN_DIP oDIP;
typedef HRESULT (WINAPI *PFN_PRES)(IDirect3DDevice9 *, const RECT *, const RECT *, HWND, const RGNDATA *);
static PFN_PRES oPRES;
static int logFrames;

#define MAXT 3000
static float tl[MAXT], tt[MAXT], tr_[MAXT], tb[MAXT];
static short par[MAXT]; static short cid[MAXT];
static int fnd(int i) { while (par[i] != i) { par[i] = par[par[i]]; i = par[i]; } return i; }

static HRESULT WINAPI hDIP(IDirect3DDevice9 *d, D3DPRIMITIVETYPE pt, INT base, UINT mi, UINT nv, UINT si, UINT pc) {
  if ((cfgMask & 1) && !inGame()) return oDIP(d, pt, base, mi, nv, si, pc);
  if (!(orthoNow && haveWorld && pt == D3DPT_TRIANGLELIST && pc > 0 && pc <= MAXT && (SW > UI_W || SH > UI_H)))
    return oDIP(d, pt, base, mi, nv, si, pc);
  callIdx++;
  IDirect3DVertexBuffer9 *vb = 0; IDirect3DIndexBuffer9 *ib = 0; UINT off = 0, str = 0;
  HRESULT r = 0; int done = 0;
  if (SUCCEEDED(IDirect3DDevice9_GetStreamSource(d, 0, &vb, &off, &str)) && vb && str >= 12 &&
      SUCCEEDED(IDirect3DDevice9_GetIndices(d, &ib)) && ib) {
    D3DINDEXBUFFER_DESC id; IDirect3DIndexBuffer9_GetDesc(ib, &id);
    UINT isz = id.Format == D3DFMT_INDEX32 ? 4 : 2;
    void *ip = 0, *vp = 0;
    if (SUCCEEDED(IDirect3DIndexBuffer9_Lock(ib, si * isz, pc * 3 * isz, &ip, D3DLOCK_READONLY))) {
      if (SUCCEEDED(IDirect3DVertexBuffer9_Lock(vb, 0, 0, &vp, D3DLOCK_READONLY))) {
        int ok = 1; float cx0 = SW * 0.5f, cy0 = SH * 0.5f;
        for (UINT k = 0; k < pc && ok; k++) {
          float x0 = 1e9f, y0 = 1e9f, x1 = -1e9f, y1 = -1e9f;
          for (int c = 0; c < 3; c++) {
            UINT ix = isz == 4 ? ((UINT *)ip)[k * 3 + c] : ((WORD *)ip)[k * 3 + c];
            const float *f = (const float *)((char *)vp + off + (UINT)(base + (INT)ix) * str);
            float x = f[0] * curWorld._11 + curWorld._41 + cx0, y = f[1] * curWorld._22 + curWorld._42 + cy0;
            if (!(x > -1e5f && x < 1e5f && y > -1e5f && y < 1e5f)) ok = 0;
            if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y;
          }
          tl[k] = x0; tt[k] = y0; tr_[k] = x1; tb[k] = y1; par[k] = k;
        }
        if (ok) {
          for (UINT i = 0; i < pc; i++) for (UINT j = i + 1; j < pc; j++) {
            if (tl[i] - fillTol <= tr_[j] && tl[j] - fillTol <= tr_[i] && tt[i] - fillTol <= tb[j] && tt[j] - fillTol <= tb[i]) {
              int a = fnd(i), b = fnd(j); if (a != b) par[a] = b;
            }
          }
          /* per piece: bounding box and anchor */
          static float cl[MAXT], ct[MAXT], cr[MAXT], cb[MAXT]; static int csx[MAXT], csy[MAXT], cax[MAXT], cay[MAXT], cdone[MAXT];
          for (UINT i = 0; i < pc; i++) { cl[i] = ct[i] = 1e9f; cr[i] = cb[i] = -1e9f; cdone[i] = 0; }
          for (UINT i = 0; i < pc; i++) {
            int c = fnd(i); cid[i] = c;
            if (tl[i] < cl[c]) cl[c] = tl[i]; if (tt[i] < ct[c]) ct[c] = tt[i];
            if (tr_[i] > cr[c]) cr[c] = tr_[i]; if (tb[i] > cb[c]) cb[c] = tb[i];
          }
          if (!inGame() && callIdx <= 2) for (UINT i = 0; i < pc; i++) {
            int c = cid[i]; float bw = cr[c] - cl[c], bh = cb[c] - ct[c];
            if (bw >= SW - 8 && bh >= SH - 8) rawNow = 1;
            else if (bw >= UI_W - 30 && bh >= UI_H - 30) subNow = 1;
          }
          if (inGame()) for (UINT i = 0; i < pc; i++) { int c = cid[i]; if (cr[c] - cl[c] >= UI_W * 3 / 4 && cb[c] - ct[c] >= UI_H * 3 / 4) vidNow = 1; }
          D3DMATRIX w = curWorld; r = 0;
          UINT i = 0;
          while (i < pc) {
            int c = cid[i];
            if (!cdone[c]) {
              cdone[c] = 1;
              anchorFor((int)cl[c], (int)ct[c], (int)cr[c], (int)cb[c], &csx[c], &csy[c], &cax[c], &cay[c]);
              if (nNow < MAXG) {
                Grp *g = &gNow[nNow++];
                g->ol = (int)cl[c]; g->ot = (int)ct[c]; g->or_ = (int)cr[c]; g->ob = (int)cb[c];
                g->sx = csx[c]; g->sy = csy[c]; g->afx = cax[c]; g->afy = cay[c];
                { float G = inGame() ? GG : 1.0f;
                  g->l = (int)(g->afx + G * (g->ol + g->sx - g->afx)) - 1; g->t = (int)(g->afy + G * (g->ot + g->sy - g->afy)) - 1;
                  g->r = (int)(g->afx + G * (g->or_ + g->sx - g->afx)) + 1; g->b = (int)(g->afy + G * (g->ob + g->sy - g->afy)) + 1; }
              }
            }
            UINT j = i; while (j < pc && cid[j] == c) j++;
            D3DMATRIX n = w;
            int bgQuad = 0; float uM = 1, vM = 1;
            if (!inGame() && (rawNow || rawPrev)) {   /* the engine laid this frame out in real screen pixels: undo the menu scaling */
              n._11 = w._11 / FS; n._22 = w._22 / FS;
              n._41 = w._41 / FS - ox; n._42 = w._42 / FS - oy;
              if (cr[c] - cl[c] >= SW - 8 && cb[c] - ct[c] >= SH - 8 && str >= 24) {
                /* the loading picture: a screen-sized quad whose UVs run past 1 (texture is 4:3, clamped): show it whole, 4:3, centred */
                for (UINT t = i * 3; t < j * 3; t++) {
                  UINT ix = isz == 4 ? ((UINT *)ip)[t] : ((WORD *)ip)[t];
                  const float *f = (const float *)((char *)vp + off + (UINT)(base + (INT)ix) * str);
                  if (f[4] > uM) uM = f[4]; if (f[5] > vM) vM = f[5];
                }
                bgQuad = 1;
                { D3DRECT all = { 0, 0, SW, SH }; IDirect3DDevice9_Clear(d, 1, &all, D3DCLEAR_TARGET, 0xff000000, 1.0f, 0); }
                float a = (SH * 4.0f / 3.0f) / SW; n._11 *= a;
                { D3DMATRIX tm = { { { 1 / uM, 0, 0, 0, 0, 0.75f / vM, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1 } } };
                  oTR(d, (D3DTRANSFORMSTATETYPE)16, &tm);
                  IDirect3DDevice9_SetTextureStageState(d, 0, D3DTSS_TEXTURETRANSFORMFLAGS, D3DTTFF_COUNT2); }
              }
            } else if (inGame() && (vidNow || vidPrev) && cr[c] - cl[c] >= UI_W * 3 / 4 && cb[c] - ct[c] >= UI_H * 3 / 4) {
              n._11 = w._11 * SW / UI_W; n._22 = w._22 * SH / UI_H;    /* the lens shading fills the whole screen */
              n._41 = (w._41 + cx0) * SW / UI_W - cx0; n._42 = (w._42 + cy0) * SH / UI_H - cy0;
            } else if (inGame() && GG != 1.0f) {
              n._11 = GG * w._11; n._22 = GG * w._22;
              n._41 = cax[c] + GG * (w._41 + cx0 + csx[c] - cax[c]) - cx0;
              n._42 = cay[c] + GG * (w._42 + cy0 + csy[c] - cay[c]) - cy0;
            } else { n._41 += csx[c]; n._42 += csy[c]; }
            oTR(d, D3DTS_WORLD, &n);
            r = oDIP(d, pt, base, mi, nv, si + i * 3, j - i);
            if (bgQuad) IDirect3DDevice9_SetTextureStageState(d, 0, D3DTSS_TEXTURETRANSFORMFLAGS, D3DTTFF_DISABLE);
            i = j;
          }
          oTR(d, D3DTS_WORLD, &w);
          done = 1;
        }
        IDirect3DVertexBuffer9_Unlock(vb);
      }
      IDirect3DIndexBuffer9_Unlock(ib);
    }
  }
  if (ib) IDirect3DIndexBuffer9_Release(ib);
  if (vb) IDirect3DVertexBuffer9_Release(vb);
  if (!done) return oDIP(d, pt, base, mi, nv, si, pc);
  return r;
}

static HRESULT WINAPI hPRES(IDirect3DDevice9 *d, const RECT *a, const RECT *b, HWND h, const RGNDATA *rg) {
  if (!inGame() && subNow && !rawNow) {      /* menu pages are a centred 4:3 block: black bars at the sides */
    int L = (int)(SW * 0.5f - FS * UI_W * 0.5f + 0.5f);
    if (L > 0) { D3DRECT rc[2] = { { 0, 0, L, SH }, { SW - L, 0, SW, SH } }; IDirect3DDevice9_Clear(d, 2, rc, D3DCLEAR_TARGET, 0xff000000, 1.0f, 0); }
  }
  rawPrev = rawNow; rawNow = 0; subNow = 0; vidPrev = vidNow; vidNow = 0;
  memcpy(gShown, gNow, nNow * sizeof(Grp)); nShown = nNow; nNow = 0;
  prevCalls = callIdx; callIdx = 0;
  { static int lastN = -1, logs; if (inGame() && nShown != lastN && logs < 14) { logs++; lastN = nShown;
      for (int i = 0; i < nShown; i++) note("grp %d: orig(%d,%d,%d,%d) shift(%d,%d)\n", i, gShown[i].ol, gShown[i].ot, gShown[i].or_, gShown[i].ob, gShown[i].sx, gShown[i].sy);
      note("--\n"); } }
  updateMirror();
  return oPRES(d, a, b, h, rg);
}

/* Viewports issued by the engine that do not cover the whole screen are UI sub-views (previews, panels)
   positioned in UI-block coordinates: move them with the UI. Full-screen ones are the 3D world. */
static HRESULT WINAPI hVP(IDirect3DDevice9 *d, const D3DVIEWPORT9 *v) {
  DWORD ra = (DWORD)__builtin_return_address(0);
  D3DVIEWPORT9 n = *v;
  int fromEngine = ra >= 0x401000 && ra < 0xc9a000;
  if (fromEngine && bbW > 0 && (n.Width < (DWORD)bbW || n.Height < (DWORD)bbH) && (int)n.X >= 0 && (int)n.Y >= 0) {
    if (!inGame()) {
      n.X = (DWORD)feToScreenX(n.X); n.Y = (DWORD)feToScreenY(n.Y);
      n.Width = (DWORD)(n.Width * FS + 0.5f); n.Height = (DWORD)(n.Height * FS + 0.5f);
    }
  }
  if ((int)n.X < 0) n.X = 0;
  if ((int)n.Y < 0) n.Y = 0;
  if (bbW > 0 && n.X + n.Width > (DWORD)bbW) n.Width = bbW - n.X;
  if (bbH > 0 && n.Y + n.Height > (DWORD)bbH) n.Height = bbH - n.Y;
  return oVP(d, &n);
}

/* the game draws its cursor with D3D using its own (UI-space) position */
static void WINAPI hSCPOS(IDirect3DDevice9 *d, int x, int y, DWORD f) {
  updateMirror();
  { int px = inGame() ? x : feToScreenX(x), py = inGame() ? y : feToScreenY(y); dbgCx = px; dbgCy = py; oSCPOS(d, px, py, f); }
}

static void patchVT(void **vt, int idx, void *nw, void **orig) {
  DWORD old; VirtualProtect(&vt[idx], 4, PAGE_READWRITE, &old);
  *orig = vt[idx]; vt[idx] = nw; VirtualProtect(&vt[idx], 4, old, &old);
}
typedef HRESULT (WINAPI *PFN_CRT)(IDirect3DDevice9 *, UINT, UINT, D3DFORMAT, D3DMULTISAMPLE_TYPE, DWORD, BOOL, IDirect3DSurface9 **, HANDLE *);
static PFN_CRT oCRT;
static HRESULT WINAPI hCRT(IDirect3DDevice9 *d, UINT w, UINT h, D3DFORMAT f, D3DMULTISAMPLE_TYPE ms, DWORD q, BOOL lk, IDirect3DSurface9 **out, HANDLE *sh) {
  HRESULT hr = oCRT(d, w, h, f, ms, q, lk, out, sh);
  note("CreateRenderTarget %ux%u fmt=%d ms=%d q=%lu lockable=%d -> hr=%lx surf=%p ret=%p\n", w, h, (int)f, (int)ms, q, lk, (unsigned long)hr, out ? (void *)*out : 0, __builtin_return_address(0));
  return hr;
}
typedef HRESULT (WINAPI *PFN_COPS)(IDirect3DDevice9 *, UINT, UINT, D3DFORMAT, D3DPOOL, IDirect3DSurface9 **, HANDLE *);
static PFN_COPS oCOPS;
static HRESULT WINAPI hCOPS(IDirect3DDevice9 *d, UINT w, UINT h, D3DFORMAT f, D3DPOOL p, IDirect3DSurface9 **out, HANDLE *sh) {
  if (f == D3DFMT_UNKNOWN) f = D3DFMT_X8R8G8B8;
  HRESULT hr = oCOPS(d, w, h, f, p, out, sh);
  return hr;
}

static HRESULT WINAPI hCD(IDirect3D9 *d3d, UINT a, D3DDEVTYPE t, HWND w, DWORD f, D3DPRESENT_PARAMETERS *pp, IDirect3DDevice9 **out) {
  note("CreateDevice %ux%u windowed=%d\n", pp->BackBufferWidth, pp->BackBufferHeight, pp->Windowed);
  HRESULT hr = oCD(d3d, a, t, w, f, pp, out);
  if (SUCCEEDED(hr)) {
    bbW = pp->BackBufferWidth; bbH = pp->BackBufferHeight;
    static int hooked;
    if (!hooked) {
      hooked = 1;
      void **vt = *(void ***)*out;
      patchVT(vt, 44, hTR, (void **)&oTR);
      patchVT(vt, 47, hVP, (void **)&oVP);
      patchVT(vt, 11, hSCPOS, (void **)&oSCPOS);
      patchVT(vt, 82, hDIP, (void **)&oDIP);
      patchVT(vt, 17, hPRES, (void **)&oPRES);
      patchVT(vt, 28, hCRT, (void **)&oCRT); patchVT(vt, 36, hCOPS, (void **)&oCOPS);
    }
  }
  return hr;
}

IDirect3D9 *WINAPI Direct3DCreate9(UINT v) {
  static PFN_D3DC real; static int done;
  if (!real) {
    char p[MAX_PATH]; GetSystemDirectoryA(p, MAX_PATH); strcat(p, "\\d3d9.dll");
    real = (PFN_D3DC)GetProcAddress(LoadLibraryA(p), "Direct3DCreate9");
  }
  patchIAT();
  IDirect3D9 *d = real(v);
  if (d && !done) { done = 1; patchVT(*(void ***)d, 16, hCD, (void **)&oCD); }
  return d;
}

/* The video-capture code asks IWMProfile::GetName for a name length in characters and mallocs that many BYTES: the
   UTF-16 name then overruns the heap block and corrupts memory (crash when recording). Give those two mallocs room. */
typedef void *(__cdecl *PFN_MALLOC)(unsigned);
static PFN_MALLOC oMalloc;
static void *__cdecl hMalloc2(unsigned n) { return oMalloc(n * 2 + 32); }
static void patchWmvMalloc(void) {
  static const unsigned sites[] = { 0x644c93, 0x644d29 };
  if ((DWORD)GetModuleHandleA(NULL) != 0x400000) return;
  { /* starting a WMV capture crashes inside the Windows Media setup on current Windows (the code overruns its own stack):
       make the capture-start routine a no-op that just returns, so the click does nothing instead of crashing the game */
    unsigned char *f = (unsigned char *)0x644960; DWORD o;
    if (f[0] == 0x81 && f[1] == 0xEC) { VirtualProtect(f, 3, PAGE_EXECUTE_READWRITE, &o); f[0] = 0xC2; f[1] = 0x14; f[2] = 0x00; VirtualProtect(f, 3, o, &o); }
  }
  for (unsigned i = 0; i < sizeof sites / sizeof *sites; i++) {
    unsigned char *c = (unsigned char *)sites[i];
    if (c[0] != 0xE8) continue;
    unsigned target = sites[i] + 5 + *(int *)(c + 1);
    if (target != 0x8491b7) continue;
    oMalloc = (PFN_MALLOC)target;
    DWORD old; VirtualProtect(c, 5, PAGE_EXECUTE_READWRITE, &old);
    *(int *)(c + 1) = (int)((unsigned)hMalloc2 - (sites[i] + 5));
    VirtualProtect(c, 5, old, &old);
  }
}
BOOL WINAPI DllMain(HINSTANCE h, DWORD reason, LPVOID r) {
  if (reason == DLL_PROCESS_ATTACH) {
    DisableThreadLibraryCalls(h);
    SetProcessDPIAware();
    SW = GetSystemMetrics(SM_CXSCREEN); SH = GetSystemMetrics(SM_CYSCREEN);
    if (SW < UI_W) SW = UI_W;
    if (SH < UI_H) SH = UI_H;
    ox = (SW - UI_W) / 2; oy = (SH - UI_H) / 2;
    { float fx = (float)SW / UI_W, fy = (float)SH / UI_H; FS = fx < fy ? fx : fy; if (FS < 1.0f) FS = 1.0f; GG = 1.0f + 0.6f * (FS - 1.0f); }
    char path[MAX_PATH]; GetModuleFileNameA(NULL, path, MAX_PATH);
    char *s = strrchr(path, '\\'); if (s) { strcpy(s + 1, "widescreen.log"); lg = fopen(path, "w"); }
    note("desktop %dx%d\n", SW, SH);
    patchVideoDat();
    patchProfile();
    { FILE *cf = fopen("widescreen.cfg", "r"); if (cf) { fscanf(cf, "%d", &cfgMask); fclose(cf); } }
    patchMouse();
    patchWmvMalloc();
    if ((DWORD)GetModuleHandleA(NULL) == 0x400000 && cfgMask & 8) hookWH();
  }
  return TRUE;
}
