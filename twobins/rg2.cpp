// rg2.cpp: rounded game (fill levels, as in Lieskovsky) for a lottery over K deterministic
// policies on two bins; exact integer minimax DP over (H, N, K policy states).
// usage: rg k w1,w2,...,wK [mode=grid] [r=R] [x2=1] [cert=FILE] [maxgb=G]
//   r=R (rounded mode): loads, volume and item classes are measured in FINE units 1/(k*R) (fine capacity kf=k*R);
//            only the packability test is coarse: H = multiset of coarse classes floor(c/R) >= 1, lower sizes fit k-1.
//   x2=1: joint constraint X2 (no free policy with pattern (0,0) together with one with pattern (1,1)).
//   rounded: classes c in 0..k-1 (real size in (c,c+1], capacity k), H = multiset of classes >= 1 whose LOWER
//            sizes fit two bins of capacity k-1; N = ceil(total volume); policy state (U_small,U_big), U = ceil(load),
//            U_small+U_big = N+e, e in {0,1}.  Adversary move (c,nu) plus overflow bits (paper, App. E).
//   grid:    exact integer sizes 1..k, capacity k (sanity anchor: reproduces the grid K-lottery values).
// value printed: T(root) = max over adversary of sum_j w_j * max(U^j_1,U^j_2); bound u = T/(W*k).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <string>
#include <unordered_map>
#include <algorithm>
#include <omp.h>
using namespace std;
typedef unsigned long long u64;
typedef uint16_t val_t;
static int k, kf, R = 1, x2 = 0, K, w[8], Wsum, gridmode = 0, capL, cmaxH; // H classes 1..cmaxH, capacity capL per offline bin
static int NMAX;
#define SMAX 132
struct Tab { int valid; int npat[SMAX]; int ns[SMAX][4]; int nb[SMAX][4]; unsigned char stay[SMAX][4]; };
static Tab *tab; // [N][c][nu]
static inline Tab &TB(int N, int c, int nu) { return tab[((size_t)N * kf + c) * 2 + nu]; }
static inline int enc(int N, int e, int a) { return e == 0 ? a : N / 2 + a; }
static inline void dec(int N, int s, int &e, int &a) { if (s <= N / 2) { e = 0; a = s; } else { e = 1; a = s - N / 2; } }
// multisets
static vector<vector<unsigned char> > Hcnt; static vector<int> Hsum; static vector<int> child; // child[h*(cmaxH+1)+c]
static unordered_map<u64, int> Hid; static vector<u64> radix;
static u64 keyof(const vector<unsigned char> &cnt) { u64 key = 0; for (int c = cmaxH; c >= 1; c--) key = key * radix[c] + cnt[c]; return key; }
static bool packable(u64 mask, int sum) { for (int s = 0; s <= capL; s++) if (((mask >> s) & 1) && sum - s <= capL) return true; return false; }
static void dfs(vector<unsigned char> &cnt, int last, int sum, u64 mask) {
  int id = (int)Hcnt.size(); Hcnt.push_back(cnt); Hsum.push_back(sum); Hid[keyof(cnt)] = id;
  for (int c = last; c <= cmaxH; c++) {
    int ns = sum + c; if (ns > 2 * capL) break;
    u64 nm = mask | (mask << c);
    if (!packable(nm, ns)) continue;
    cnt[c]++; dfs(cnt, c, ns, nm); cnt[c]--;
  }
}
static vector<long long> off; // off[h*(NMAX+1)+N] or -1
static val_t *T; static long long pw[SMAX][9];
static inline int lowN(int h) { if (gridmode) return Hsum[h]; return Hsum[h] == 0 ? 0 : R * Hsum[h] + 1; }
static inline int highN(int h) { if (gridmode) return Hsum[h]; return NMAX; }
struct Move { int c, nu, Np; val_t *Tn; int same; };
static void process(int h, int N) {
  val_t *base = T + off[(size_t)h * (NMAX + 1) + N];
  int n1 = N + 1; long long total = pw[N][K];
  vector<Move> mv;
  for (int c = 0; c < kf; c++) for (int nu = 0; nu < 2; nu++) {
    if (gridmode && nu == 0) continue;
    Tab &t = TB(N, c, nu); if (!t.valid) continue;
    int Np = N + c + nu; int hp = h;
    if (gridmode) { hp = child[(size_t)h * (cmaxH + 1) + (c + 1)]; if (hp < 0) continue; }
    else if (c / R >= 1) { hp = child[(size_t)h * (cmaxH + 1) + c / R]; if (hp < 0) continue; }
    long long o = off[(size_t)hp * (NMAX + 1) + Np]; if (o < 0) { fprintf(stderr, "missing array\n"); exit(3); }
    Move m; m.c = c; m.nu = nu; m.Np = Np; m.Tn = T + o; m.same = (c == 0 && nu == 0); mv.push_back(m);
  }
  int es[SMAX], as_[SMAX]; for (int s = 0; s <= N; s++) dec(N, s, es[s], as_[s]);
  for (int pc = K; pc >= 0; pc--) {
    int s[8]; for (int j = 0; j < K; j++) s[j] = 0;
    for (long long idx = 0; idx < total; idx++) {
      int ec = 0; for (int j = 0; j < K; j++) ec += es[s[j]];
      if (ec == pc) {
        int best = 0; for (int j = 0; j < K; j++) best += w[j] * (N + es[s[j]] - as_[s[j]]);
        for (size_t mi = 0; mi < mv.size(); mi++) {
          const Move &m = mv[mi]; Tab &t = TB(N, m.c, m.nu); const long long *pwp = pw[m.Np];
          int np[8], p[8]; for (int j = 0; j < K; j++) { np[j] = t.npat[s[j]]; p[j] = 0; }
          while (true) {
            bool skip = false;
            if (m.same) { skip = true; for (int j = 0; j < K; j++) if (!t.stay[s[j]][p[j]]) { skip = false; break; } }
            if (x2 && !skip) { int h00 = 0, h11 = 0; for (int j = 0; j < K; j++) if (np[j] == 4) { if (p[j] == 0) h00 = 1; if (p[j] == 3) h11 = 1; } if (h00 && h11) skip = true; }
            if (!skip) {
              int mn = 1 << 30;
              for (int r = 0; r < (1 << K); r++) {
                long long ix = 0;
                for (int j = 0; j < K; j++) ix += (long long)(((r >> j) & 1) ? t.nb[s[j]][p[j]] : t.ns[s[j]][p[j]]) * pwp[j];
                int v = m.Tn[ix]; if (v < mn) { mn = v; if (mn <= best) break; }
              }
              if (mn > best) best = mn;
            }
            int j = 0; while (j < K) { if (++p[j] < np[j]) break; p[j] = 0; j++; }
            if (j == K) break;
          }
        }
        base[idx] = (val_t)best;
      }
      int j = 0; while (j < K) { if (++s[j] < n1) break; s[j] = 0; j++; }
    }
  }
}
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: rg k w1,..,wK [mode=grid] [cert=FILE] [maxgb=G]\n"); return 1; }
  k = atoi(argv[1]); K = 0; Wsum = 0;
  { char *q = strdup(argv[2]); for (char *tok = strtok(q, ","); tok; tok = strtok(NULL, ",")) { w[K++] = atoi(tok); Wsum += w[K - 1]; } }
  const char *certfile = NULL; double maxgb = 64;
  for (int i = 3; i < argc; i++) {
    if (!strcmp(argv[i], "mode=grid")) gridmode = 1;
    else if (!strncmp(argv[i], "r=", 2)) R = atoi(argv[i] + 2);
    else if (!strncmp(argv[i], "x2=", 3)) x2 = atoi(argv[i] + 3);
    else if (!strncmp(argv[i], "cert=", 5)) certfile = argv[i] + 5;
    else if (!strncmp(argv[i], "maxgb=", 6)) maxgb = atof(argv[i] + 6);
  }
  if (gridmode) R = 1;
  kf = k * R; NMAX = 2 * kf; capL = gridmode ? k : k - 1; cmaxH = gridmode ? k : k - 1;
  if (NMAX > SMAX - 2 || 2 * capL > 62 || K > 6) { fprintf(stderr, "too large\n"); return 1; }
  double t0 = omp_get_wtime();
  for (int N = 0; N <= NMAX; N++) { pw[N][0] = 1; for (int j = 1; j <= 8; j++) pw[N][j] = pw[N][j - 1] * (N + 1); }
  // transition tables
  tab = (Tab *)calloc((size_t)(NMAX + 1) * kf * 2, sizeof(Tab));
  for (int N = 0; N <= NMAX; N++) for (int c = 0; c < kf; c++) for (int nu = 0; nu < 2; nu++) {
    Tab &t = TB(N, c, nu); int Np = N + c + nu; t.valid = 0;
    if (Np > NMAX) continue; if (N == 0 && nu == 0) continue;
    t.valid = 1;
    for (int s = 0; s <= N; s++) {
      int e, a; dec(N, s, e, a); int big = N + e - a; int pats[4][2]; int np = 0;
      if (a == 0) { pats[0][0] = 1; pats[0][1] = (N == 0) ? 1 : (nu == 1 ? 1 : 0); np = 1; if (e != 0) { fprintf(stderr, "bad state\n"); exit(2); } }
      else if (e == 0 && nu == 1) { pats[0][0] = 1; pats[0][1] = 1; np = 1; }
      else if (e == 1 && nu == 0) { pats[0][0] = 0; pats[0][1] = 0; np = 1; }
      else { np = 4; for (int q = 0; q < 4; q++) { pats[q][0] = q & 1; pats[q][1] = (q >> 1) & 1; } }
      t.npat[s] = np;
      for (int q = 0; q < np; q++) {
        int os = pats[q][0], ob = pats[q][1];
        int e1 = e + os - nu, e2 = e + ob - nu;
        if (e1 < 0 || e1 > 1 || e2 < 0 || e2 > 1) { fprintf(stderr, "bad e\n"); exit(2); }
        int na = a + c + os, nb_ = big; int a1 = na < nb_ ? na : nb_;
        if (na + nb_ != Np + e1) { fprintf(stderr, "bad sum\n"); exit(2); }
        if (e1 == 1 && a1 < 1) { fprintf(stderr, "bad a1\n"); exit(2); }
        t.ns[s][q] = enc(Np, e1, a1);
        if (a + big + c + ob != Np + e2) { fprintf(stderr, "bad sum2\n"); exit(2); }
        if (e2 == 1 && a < 1) { fprintf(stderr, "bad a2\n"); exit(2); }
        t.nb[s][q] = enc(Np, e2, a);
        t.stay[s][q] = (c == 0 && nu == 0 && (os == 0 || ob == 0)) ? 1 : 0;
      }
    }
  }
  // multisets
  radix.assign(cmaxH + 2, 1); for (int c = 1; c <= cmaxH; c++) radix[c] = (u64)(2 * capL / c) + 1;
  { vector<unsigned char> cnt(cmaxH + 2, 0); dfs(cnt, 1, 0, 1ULL); }
  int nH = (int)Hcnt.size();
  child.assign((size_t)nH * (cmaxH + 1), -1);
  for (int h = 0; h < nH; h++) for (int c = 1; c <= cmaxH; c++) {
    if (Hsum[h] + c > 2 * capL) continue;
    vector<unsigned char> cnt = Hcnt[h]; cnt[c]++; if ((u64)cnt[c] >= radix[c]) continue;
    unordered_map<u64, int>::iterator it = Hid.find(keyof(cnt)); if (it != Hid.end()) child[(size_t)h * (cmaxH + 1) + c] = it->second;
  }
  off.assign((size_t)nH * (NMAX + 1), -1); long long total = 0; long long narr = 0;
  for (int h = 0; h < nH; h++) for (int N = lowN(h); N <= highN(h); N++) { off[(size_t)h * (NMAX + 1) + N] = total; total += pw[N][K]; narr++; }
  printf("k %d r %d x2 %d K %d weights", k, R, x2, K); for (int j = 0; j < K; j++) printf(" %d", w[j]);
  printf(" mode %s: %d multisets, %lld arrays, %lld entries (%.2f GB), threads %d\n", gridmode ? "grid" : "rounded", nH, narr, total, total * sizeof(val_t) / 1e9, omp_get_max_threads()); fflush(stdout);
  if (total * sizeof(val_t) / 1e9 > maxgb) { printf("too big, abort\n"); return 4; }
  T = (val_t *)malloc(total * sizeof(val_t)); if (!T) { printf("malloc failed\n"); return 5; }
  vector<vector<int> > byN(NMAX + 1);
  for (int h = 0; h < nH; h++) for (int N = lowN(h); N <= highN(h); N++) byN[N].push_back(h);
  for (int N = NMAX; N >= 0; N--) {
    int nh = (int)byN[N].size();
    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < nh; i++) process(byN[N][i], N);
    printf("  level N=%d done (%d arrays, %.0fs)\n", N, nh, omp_get_wtime() - t0); fflush(stdout);
  }
  int root = T[off[0 * (NMAX + 1) + 0]];
  printf("RESULT k %d r %d x2 %d weights %s mode %s: T(root) = %d, W = %d, value = %d/%d = %.10f  (%.0fs)\n", k, R, x2, argv[2], gridmode ? "grid" : "rounded", root, Wsum, root, Wsum * kf, (double)root / (Wsum * kf), omp_get_wtime() - t0); fflush(stdout);
  if (certfile) {
    // closed set reachable from the root under an optimal joint response; written as a potential table
    vector<unsigned char> vis((size_t)total, 0);
    struct Q { int h, N; long long idx; }; vector<Q> queue; Q q0; q0.h = 0; q0.N = 0; q0.idx = 0; queue.push_back(q0); vis[off[0]] = 1;
    size_t head = 0;
    while (head < queue.size()) {
      Q cur = queue[head++]; int h = cur.h, N = cur.N; int n1 = N + 1; int s[8]; { long long x = cur.idx; for (int j = 0; j < K; j++) { s[j] = (int)(x % n1); x /= n1; } }
      for (int c = 0; c < kf; c++) for (int nu = 0; nu < 2; nu++) {
        if (gridmode && nu == 0) continue;
        Tab &t = TB(N, c, nu); if (!t.valid) continue; int Np = N + c + nu; int hp = h;
        if (gridmode) { hp = child[(size_t)h * (cmaxH + 1) + (c + 1)]; if (hp < 0) continue; }
        else if (c / R >= 1) { hp = child[(size_t)h * (cmaxH + 1) + c / R]; if (hp < 0) continue; }
        long long o = off[(size_t)hp * (NMAX + 1) + Np]; const long long *pwp = pw[Np]; bool same = (c == 0 && nu == 0);
        int np[8], p[8]; for (int j = 0; j < K; j++) { np[j] = t.npat[s[j]]; p[j] = 0; }
        while (true) {
          bool skip = false;
          if (same) { skip = true; for (int j = 0; j < K; j++) if (!t.stay[s[j]][p[j]]) { skip = false; break; } }
          if (x2 && !skip) { int h00 = 0, h11 = 0; for (int j = 0; j < K; j++) if (np[j] == 4) { if (p[j] == 0) h00 = 1; if (p[j] == 3) h11 = 1; } if (h00 && h11) skip = true; }
          if (!skip) {
            int mn = 1 << 30; long long bi = -1; bool bv = false;
            for (int r = 0; r < (1 << K); r++) {
              long long ix = 0;
              for (int j = 0; j < K; j++) ix += (long long)(((r >> j) & 1) ? t.nb[s[j]][p[j]] : t.ns[s[j]][p[j]]) * pwp[j];
              int v = T[o + ix]; bool vv = vis[o + ix];
              if (v < mn || (v == mn && vv && !bv)) { mn = v; bi = ix; bv = vv; }
            }
            if (!vis[o + bi]) { vis[o + bi] = 1; Q nq; nq.h = hp; nq.N = Np; nq.idx = bi; queue.push_back(nq); }
          }
          int j = 0; while (j < K) { if (++p[j] < np[j]) break; p[j] = 0; j++; }
          if (j == K) break;
        }
      }
    }
    printf("certificate: %zu reachable states (%.0fs)\n", queue.size(), omp_get_wtime() - t0); fflush(stdout);
    FILE *f = fopen(certfile, "w");
    fprintf(f, "# rounded-game potential certificate: k %d r %d x2 %d weights %s mode %s root %d\n# line: N T | coarse classes of H (or -) | U_small,U_big per policy (fine units)\n", k, R, x2, argv[2], gridmode ? "grid" : "rounded", root);
    for (size_t i = 0; i < queue.size(); i++) {
      Q cur = queue[i]; int N = cur.N, n1 = N + 1; long long x = cur.idx;
      fprintf(f, "%d %d |", N, (int)T[off[(size_t)cur.h * (NMAX + 1) + N] + cur.idx]);
      bool any = false; for (int c = 1; c <= cmaxH; c++) for (int r = 0; r < Hcnt[cur.h][c]; r++) { fprintf(f, " %d", c); any = true; }
      if (!any) fprintf(f, " -");
      fprintf(f, " |");
      for (int j = 0; j < K; j++) { int sj = (int)(x % n1); x /= n1; int e, a; dec(N, sj, e, a); fprintf(f, " %d,%d", a, N + e - a); }
      fprintf(f, "\n");
    }
    fclose(f);
    printf("certificate written to %s\n", certfile);
  }
  return 0;
}
