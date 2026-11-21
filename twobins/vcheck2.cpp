// vcheck2.cpp -- the checks of vcheck.cpp with compact storage, for certificates of billions of states.
// Each state is stored as a 128-bit code in one open-addressing table (20 bytes per slot).
// usage: vcheck2 CERT   (OpenMP threads from OMP_NUM_THREADS)
// Accepts iff (a) the root state is listed with the header's root value, (b) every listed state is well formed and
// its payoff sum_j w_j v_j is at most its potential, (c) for every listed state and every legal adversary move
// (fine class c, volume bit nu, overflow pattern of every copy) some joint response leads to a listed state whose
// potential is at most the current one.  Then E[cost] <= T(root) / (W k r) for every real packable input.
// Code: A = class counts of H in mixed radix; B = N (8 bits), then u_j (8 bits) and e_j = u_j + v_j - N (1 bit).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <algorithm>
#include <omp.h>
using namespace std;
typedef unsigned long long u64;

static int k = -1, r = -1, x2 = -1, K = 0, F, NMAX, CM;
static vector<int> w;
static long long rootT = -1;
static u64 rad[64], rpw[64];
static u64 *KA, *KB, msk; static int32_t *TT;

// can the classes H[0..n) be split into two groups, each of sum <= cap?  (1 <= H[i] <= cap <= 62)
static bool splits(const int *H, int n, int cap) {
  int tot = 0; for (int i = 0; i < n; i++) tot += H[i];
  if (tot > 2 * cap) return false;
  u64 can = 1, lim = (1ULL << (cap + 1)) - 1;
  for (int i = 0; i < n; i++) can = (can | (can << H[i])) & lim;
  for (int s = 0; s <= cap; s++) if (((can >> s) & 1) && tot - s <= cap) return true;
  return false;
}
static inline u64 mix(u64 x) {
  x += 0x9e3779b97f4a7c15ULL; x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL; return x ^ (x >> 31);
}
static inline u64 slot0(u64 a, u64 b) { return mix(a ^ mix(b)) & msk; }
// potential of the state with code (a, b), or -1 if it is not listed
static inline long long look(u64 a, u64 b) {
  for (u64 i = slot0(a, b);; i = (i + 1) & msk) {
    if (TT[i] < 0) return -1;
    if (KA[i] == a && KB[i] == b) return TT[i];
  }
}
// B code of (N, pairs); false if the pairs are not well formed for N (such a state is never listed)
static inline bool codeB(int N, const int *u, const int *v, u64 &b) {
  b = (u64)N;
  for (int j = 0; j < K; j++) {
    int e = u[j] + v[j] - N;
    if (u[j] < 0 || u[j] > v[j] || (e != 0 && e != 1) || (e == 1 && u[j] == 0) || u[j] > 255) return false;
    b |= ((u64)u[j] << (8 + 9 * j)) | ((u64)e << (16 + 9 * j));
  }
  return true;
}
static bool num(const char *&p, long long &x) {
  while (*p == ' ' || *p == '\t') p++;
  bool neg = false; if (*p == '-' && p[1] >= '0' && p[1] <= '9') { neg = true; p++; }
  if (*p < '0' || *p > '9') return false;
  x = 0; while (*p >= '0' && *p <= '9') { x = x * 10 + (*p - '0'); if (x > 4000000000000LL) return false; p++; }
  if (neg) x = -x; return true;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: vcheck2 CERT\n"); return 2; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror("open"); return 2; }
  static char line[1 << 16];
  if (!fgets(line, sizeof line, f)) { fprintf(stderr, "empty file\n"); return 2; }
  {  // header: "# rounded-game potential certificate: k K r R x2 X weights W mode M root T"
    string h = string(" ") + line; auto grab = [&](const char *name) -> string {
      string pat = string(" ") + name + " "; size_t p = h.find(pat); if (p == string::npos) return "";
      p += pat.size(); size_t q = h.find_first_of(" \n", p); return h.substr(p, q - p); };
    k = atoi(grab("k").c_str()); r = atoi(grab("r").c_str()); x2 = atoi(grab("x2").c_str());
    rootT = atoll(grab("root").c_str());
    if (grab("mode") != "rounded") { fprintf(stderr, "FAIL: only the rounded game is handled\n"); return 1; }
    string ws = grab("weights"); size_t p = 0;
    while (p < ws.size()) { size_t q = ws.find(',', p); if (q == string::npos) q = ws.size(); w.push_back(atoi(ws.substr(p, q - p).c_str())); p = q + 1; }
  }
  K = (int)w.size(); F = k * r; NMAX = 2 * F; CM = k - 1;
  long long W = 0; for (int x : w) { if (x <= 0) { fprintf(stderr, "FAIL: weight\n"); return 1; } W += x; }
  if (k < 2 || r < 1 || (x2 != 0 && x2 != 1) || K < 1 || K > 6) { fprintf(stderr, "FAIL: header\n"); return 1; }
  if (NMAX > 255 || CM > 62) { fprintf(stderr, "FAIL: too large for vcheck2\n"); return 1; }
  rpw[1] = 1;
  for (int c = 1; c <= CM; c++) {
    rad[c] = (u64)(2 * CM / c) + 1;
    if ((long double)rpw[c] * rad[c] > 4.0e18L) { fprintf(stderr, "FAIL: too large for vcheck2\n"); return 1; }
    rpw[c + 1] = rpw[c] * rad[c];
  }
  // pass 1: count lines, size the table
  long long nl = 0;
  { static char buf[1 << 22]; size_t m; while ((m = fread(buf, 1, sizeof buf, f)) > 0) for (size_t i = 0; i < m; i++) nl += (buf[i] == '\n'); }
  u64 cap = 1024; while ((long double)cap * 0.7L < (long double)nl) cap <<= 1;
  msk = cap - 1;
  KA = (u64 *)malloc(cap * sizeof(u64)); KB = (u64 *)malloc(cap * sizeof(u64)); TT = (int32_t *)malloc(cap * sizeof(int32_t));
  if (!KA || !KB || !TT) { fprintf(stderr, "FAIL: out of memory\n"); return 1; }
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)cap; i++) TT[i] = -1;
  // pass 2: parse, check (b), store
  rewind(f); if (!fgets(line, sizeof line, f)) return 2;
  long long ns = 0;
  vector<int> H, u(K), v(K);
  while (fgets(line, sizeof line, f)) {
    if (line[0] == '#' || line[0] == '\n') continue;
    const char *p = line; long long N, T, x;
    if (!num(p, N) || !num(p, T)) { fprintf(stderr, "FAIL: bad N T\n"); return 1; }
    while (*p == ' ' || *p == '\t') p++;
    if (*p++ != '|') { fprintf(stderr, "FAIL: bad line\n"); return 1; }
    while (*p == ' ' || *p == '\t') p++;
    H.clear();
    if (*p == '-') p++;
    else while (*p >= '0' && *p <= '9') { num(p, x); H.push_back((int)x); while (*p == ' ' || *p == '\t') p++; }
    while (*p == ' ' || *p == '\t') p++;
    if (*p++ != '|') { fprintf(stderr, "FAIL: bad line\n"); return 1; }
    for (int j = 0; j < K; j++) {
      long long a, b;
      if (!num(p, a) || *p++ != ',' || !num(p, b)) { fprintf(stderr, "FAIL: pair\n"); return 1; }
      u[j] = (int)a; v[j] = (int)b;
      if (a < -1000000 || a > 1000000 || b < -1000000 || b > 1000000) { printf("FAIL (b) at state %lld\n", ns); return 1; }
    }
    while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') p++;
    if (*p) { fprintf(stderr, "FAIL: wrong number of copies\n"); return 1; }
    // (b) well formed, payoff
    bool ok = (N >= 0 && N <= NMAX && T >= 0 && T <= 2000000000LL);
    for (int c : H) if (c < 1 || c > CM) ok = false;
    if (ok && !H.empty() && !splits(H.data(), (int)H.size(), CM)) ok = false;
    long long pay = 0; u64 b = 0, a = 0;
    if (ok) { for (int j = 0; j < K; j++) pay += (long long)w[j] * v[j]; if (!codeB((int)N, u.data(), v.data(), b)) ok = false; }
    if (!ok || pay > T) { printf("FAIL (b) at state %lld (N %lld)\n", ns, N); return 1; }
    for (int c : H) a += rpw[c];
    u64 i = slot0(a, b);
    while (TT[i] >= 0) { if (KA[i] == a && KB[i] == b) { fprintf(stderr, "FAIL: duplicate state\n"); return 1; } i = (i + 1) & msk; }
    KA[i] = a; KB[i] = b; TT[i] = (int32_t)T; ns++;
  }
  fclose(f);
  {  // (a) root
    int z[8] = {0}; u64 b0; codeB(0, z, z, b0);
    if (look(0, b0) != rootT) { printf("FAIL: root missing or root value differs\n"); return 1; }
  }
  printf("vcheck2: k %d r %d x2 %d K %d W %lld, %lld states, root %lld, table %llu slots\n", k, r, x2, K, W, ns, rootT, cap); fflush(stdout);
  long long fails = 0, moves = 0;
  #pragma omp parallel for schedule(dynamic, 4096) reduction(+:fails, moves)
  for (long long i = 0; i < (long long)cap; i++) {
    if (fails || TT[i] < 0) continue;
    const u64 a = KA[i], b = KB[i]; const long long T = TT[i];
    const int N = (int)(b & 255);
    int u[8], v[8], e[8];
    for (int j = 0; j < K; j++) { u[j] = (int)((b >> (8 + 9 * j)) & 255); e[j] = (int)((b >> (16 + 9 * j)) & 1); v[j] = N + e[j] - u[j]; }
    int Hs[130], nh = 0; bool okC[64];
    for (int c = 1; c <= CM; c++) { int n = (int)((a / rpw[c]) % rad[c]); for (int t = 0; t < n; t++) Hs[nh++] = c; }
    for (int C = 1; C <= CM; C++) { Hs[nh] = C; okC[C] = splits(Hs, nh + 1, CM); }
    // (c) every legal move
    for (int c = 0; c < F && !fails; c++) for (int nu = 0; nu <= 1; nu++) {
      if (N == 0 && nu == 0) continue;
      int N2 = N + c + nu; if (N2 > NMAX) continue;
      int C = c / r; u64 a2 = a;
      if (C >= 1) { if (!okC[C]) continue; a2 = a + rpw[C]; }
      int np[8], pt[8][4], idx[8]; bool fr[8];
      for (int j = 0; j < K; j++) {
        idx[j] = 0; fr[j] = false;
        if (u[j] == 0) { np[j] = 1; pt[j][0] = 2 + nu; }
        else if (e[j] == 0 && nu == 1) { np[j] = 1; pt[j][0] = 3; }
        else if (e[j] == 1 && nu == 0) { np[j] = 1; pt[j][0] = 0; }
        else { np[j] = 4; for (int q = 0; q < 4; q++) pt[j][q] = q; fr[j] = true; }
      }
      while (true) {
        bool skip = false;
        if (x2) { bool h00 = false, h11 = false;
          for (int j = 0; j < K; j++) if (fr[j]) { int q = pt[j][idx[j]]; if (q == 0) h00 = true; if (q == 3) h11 = true; }
          if (h00 && h11) skip = true; }
        if (!skip) {
          moves++;
          bool answered = false;
          for (int resp = 0; resp < (1 << K) && !answered; resp++) {
            int u2[8], v2[8];
            for (int j = 0; j < K; j++) {
              int q = pt[j][idx[j]], os = q >> 1, ob = q & 1;
              if ((resp >> j) & 1) { u2[j] = u[j]; v2[j] = v[j] + c + ob; }
              else { int x = u[j] + c + os; if (x <= v[j]) { u2[j] = x; v2[j] = v[j]; } else { u2[j] = v[j]; v2[j] = x; } }
            }
            u64 b2;
            if (!codeB(N2, u2, v2, b2)) continue;
            long long t2 = look(a2, b2);
            if (t2 >= 0 && t2 <= T) answered = true;
          }
          if (!answered) {
            #pragma omp critical
            printf("FAIL (c) at slot %lld (N %d T %lld): move c %d nu %d unanswered\n", i, N, T, c, nu);
            fails++; break;
          }
        }
        int j = 0; while (j < K && ++idx[j] == np[j]) { idx[j] = 0; j++; }
        if (j == K) break;
      }
    }
  }
  if (fails) { printf("vcheck2: FAIL (%lld failures)\n", fails); return 1; }
  long long den = W * (long long)F, g; { long long x = rootT, y = den; while (y) { long long t = x % y; x = y; y = t; } g = x; }
  printf("vcheck2: PASS. %lld states, %lld answered move patterns. E[cost] <= %lld/%lld = %lld/%lld = %.10f\n",
         ns, moves, rootT, den, rootT / g, den / g, (double)rootT / den);
  return 0;
}
