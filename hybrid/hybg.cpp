// hybg.cpp: writes a hybrid certificate of the rounded game, for m <= 4 bins and K <= 3 copies.
// g++ -O2 -std=c++17 -o hybg hybg.cpp && ./hybg m K k r w_1 .. w_K T0 [relax=1] [out=FILE] [maxnodes=N]
// relax=1 asks (J3) for relaxed moves, else for moves with one common point. Exit 0 proved, 3 out of nodes, 4 refuted.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <map>
#include <unordered_map>
#include <algorithm>
#include <string>
#include <chrono>
using namespace std;
typedef unsigned long long u64;
static int m, K, k, r, F, NMAX, w[3], T0, RELAX = 0, SIZES = 0;
static long long MAXNODES = 50000000LL;

static double now() { return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count(); }

typedef vector<int> Prof;
static vector<Prof> P; static vector<int> Psum; static vector<vector<int> > Pchild; static map<Prof, int> Pid;
static vector<vector<int> > Prep;
static inline int fld(int v, int i) { return (v >> (5 * i)) & 31; }
static int packV(const int *q0) { int q[4]; for (int i = 0; i < m; i++) q[i] = q0[i]; sort(q, q + m); int v = 0; for (int i = 0; i < m; i++) v |= q[i] << (5 * i); return v; }
static Prof minimize(Prof v) {
  sort(v.begin(), v.end()); v.erase(unique(v.begin(), v.end()), v.end());
  Prof out;
  for (size_t i = 0; i < v.size(); i++) {
    bool dom = false;
    for (size_t j = 0; j < v.size() && !dom; j++) if (j != i) {
      bool le = true; for (int a = 0; a < m && le; a++) if (fld(v[j], a) > fld(v[i], a)) le = false;
      if (le) dom = true;
    }
    if (!dom) out.push_back(v[i]);
  }
  return out;
}
static void buildProfiles() {
  Prof z(1, 0); Pid[z] = 0; P.push_back(z); Psum.push_back(0); Pchild.push_back(vector<int>(k, -1)); Prep.push_back(vector<int>());
  for (size_t p = 0; p < P.size(); p++) for (int C = 1; C <= k - 1; C++) {
    Prof nt;
    for (size_t z2 = 0; z2 < P[p].size(); z2++) {
      int q[4]; for (int i = 0; i < m; i++) q[i] = fld(P[p][z2], i);
      for (int i = 0; i < m; i++) if (q[i] + C <= k - 1) { int u[4]; for (int a = 0; a < m; a++) u[a] = q[a]; u[i] += C; nt.push_back(packV(u)); }
    }
    if (nt.empty()) continue;
    nt = minimize(nt);
    map<Prof, int>::iterator it = Pid.find(nt); int id;
    if (it == Pid.end()) {
      id = (int)P.size(); Pid[nt] = id; P.push_back(nt); Psum.push_back(Psum[p] + C); Pchild.push_back(vector<int>(k, -1));
      vector<int> h = Prep[p]; h.push_back(C); sort(h.begin(), h.end()); Prep.push_back(h);
    } else { id = it->second; if (Psum[id] != Psum[p] + C) { fprintf(stderr, "profile sum mismatch\n"); exit(2); } }
    Pchild[p][C] = id;
  }
}
static inline int lowN(int p) { return Psum[p] == 0 ? 0 : r * Psum[p] + 1; }

struct CS { int q[4]; int e, n; };
static vector<vector<CS> > cs;
static vector<unordered_map<uint32_t, int> > cidx;
static vector<vector<int> > succT;
static inline uint32_t qkey(const int *q) { uint32_t x = 0; for (int i = 0; i < m; i++) x |= (uint32_t)q[i] << (8 * i); return x; }
static void enumVec(int N, int e, int S, int pos, int minv, int *q) {
  if (pos == m - 1) {
    if (S < minv) return;
    q[pos] = S;
    int n = 0; for (int i = 0; i < m; i++) n += q[i] > 0;
    if (n < 1 || e > n - 1) return;
    if (q[pos] > 255) { fprintf(stderr, "q too large\n"); exit(2); }
    CS z; for (int i = 0; i < 4; i++) z.q[i] = i < m ? q[i] : 0; z.e = e; z.n = n;
    cidx[N][qkey(z.q)] = (int)cs[N].size(); cs[N].push_back(z);
    return;
  }
  for (int v = minv; v * (m - pos) <= S; v++) { q[pos] = v; enumVec(N, e, S - v, pos + 1, v, q); }
}
static void buildCopyStates() {
  cs.assign(NMAX + 1, vector<CS>()); cidx.assign(NMAX + 1, unordered_map<uint32_t, int>());
  { CS z; for (int i = 0; i < 4; i++) z.q[i] = 0; z.e = 0; z.n = 0; cs[0].push_back(z); cidx[0][0] = 0; }
  for (int N = 1; N <= NMAX; N++)
    for (int e = m - 1; e >= 0; e--) { int q[4]; enumVec(N, e, N + e, 0, 0, q); }
  succT.assign(NMAX + 1, vector<int>());
  if (SIZES) return;
  for (int N = 0; N <= NMAX; N++) {
    succT[N].assign(cs[N].size() * m * (F + 1) * 3, -1);
    for (size_t s = 0; s < cs[N].size(); s++) for (int i = 0; i < m; i++) for (int add = 0; add <= F; add++) for (int dd = -1; dd <= 1; dd++) {
      int N2 = N + add + dd; if (N2 > NMAX || N2 < N) continue;
      int q[4]; for (int a = 0; a < 4; a++) q[a] = cs[N][s].q[a]; q[i] += add; sort(q, q + m);
      unordered_map<uint32_t, int>::iterator it = cidx[N2].find(qkey(q));
      if (it != cidx[N2].end()) succT[N][((s * m + i) * (F + 1) + add) * 3 + (dd + 1)] = it->second;
    }
  }
}
static inline int succ(int N, int s, int i, int c, int bit, int nu) { return succT[N][((s * m + i) * (F + 1) + (c + bit)) * 3 + (nu - bit + 1)]; }

static bool bp(int nu, int cnt, const int *n, const int *e, const int *b) {
  for (int d = 1; d <= m; d++) for (int a = 0; a <= d; a++) {
    int U = d; if (nu == 1) U = min(U, a);
    int L = 0; if (nu == 0) L = max(L, a);
    for (int j = 0; j < cnt; j++) { U = min(U, (n[j] - b[j]) * a + (b[j] - e[j]) * d); L = max(L, b[j] * a - e[j] * d); }
    if (U > L) return true;
  }
  return false;
}
static inline int tid(int n, int e, int b) { return (n * 4 + e) * 5 + b; }
static bool feas1[2][5][4][5];
static vector<char> feasJ;
static void buildFeas() {
  memset(feas1, 0, sizeof(feas1));
  for (int nu = 0; nu < 2; nu++) for (int n = 1; n <= m; n++) for (int e = 0; e < n; e++) for (int b = 0; b <= n; b++) feas1[nu][n][e][b] = bp(nu, 1, &n, &e, &b);
  size_t sz = 2; for (int j = 0; j < K; j++) sz *= 100; feasJ.assign(sz, 0);
  vector<int> trip; for (int n = 1; n <= m; n++) for (int e = 0; e < n; e++) for (int b = 0; b <= n; b++) trip.push_back(tid(n, e, b));
  int T = (int)trip.size(); int idx[3] = {0, 0, 0};
  for (int nu = 0; nu < 2; nu++) {
    long long tot = 1; for (int j = 0; j < K; j++) tot *= T;
    for (long long z = 0; z < tot; z++) {
      long long y = z; int nn[3], ee[3], bb[3]; size_t off = nu;
      for (int j = K - 1; j >= 0; j--) { idx[j] = (int)(y % T); y /= T; }
      bool f1 = true;
      for (int j = 0; j < K; j++) { int t = trip[idx[j]]; bb[j] = t % 5; ee[j] = (t / 5) % 4; nn[j] = t / 20; off = off * 100 + t; f1 = f1 && feas1[nu][nn[j]][ee[j]][bb[j]]; }
      bool f = RELAX ? f1 : bp(nu, K, nn, ee, bb);
      feasJ[off] = f;
    }
  }
}
static vector<int> masks[5][5];
static void buildMasks() {
  for (int n = 0; n <= m; n++) for (int b = 0; b <= n; b++) for (int mk = 0; mk < (1 << m); mk++) {
    bool ok = true; int zeros = 0;
    for (int i = 0; i < m; i++) { bool empty = (i < m - n); int bit = (mk >> i) & 1; if (empty && !bit) ok = false; if (!empty && !bit) zeros++; }
    if (ok && zeros == b) masks[n][b].push_back(mk);
  }
}

static vector<vector<long long> > off;
static vector<unsigned char> phi; static long long nSingle = 0;
static inline int PHI(int p, int N, int s) { return phi[off[p][N] + s]; }
static void solveSingle() {
  off.assign(P.size(), vector<long long>(NMAX + 1, -1));
  for (size_t p = 0; p < P.size(); p++) for (int N = lowN(p); N <= NMAX; N++) { if (N == 0 && p != 0) continue; off[p][N] = nSingle; nSingle += cs[N].size(); }
  phi.assign(nSingle, 0);
  for (int N = NMAX; N >= 0; N--) for (size_t s = 0; s < cs[N].size(); s++) {
    const CS &z = cs[N][s];
    for (size_t p = 0; p < P.size(); p++) {
      if (off[p][N] < 0) continue;
      int val = z.q[m - 1];
      for (int c = 0; c < F; c++) {
        int C = c / r; int pc = C ? Pchild[p][C] : (int)p; if (pc < 0) continue;
        for (int nu = 0; nu < 2; nu++) {
          int N2 = N + c + nu; if (N2 > NMAX) continue;
          if (N == 0 && nu == 0) continue;
          if (off[pc][N2] < 0) { fprintf(stderr, "successor profile below lowN\n"); exit(2); }
          if (N == 0) {
            int t = succ(N, (int)s, m - 1, c, 1, 1); if (t < 0) { fprintf(stderr, "bad succ N=0\n"); exit(2); }
            val = max(val, PHI(pc, N2, t)); continue;
          }
          for (int b = 0; b <= z.n; b++) {
            if (!feas1[nu][z.n][z.e][b]) continue;
            if (c == 0 && nu == 0 && b >= 1) continue;
            for (size_t mi = 0; mi < masks[z.n][b].size(); mi++) {
              int mk = masks[z.n][b][mi]; int best = 1 << 20;
              for (int i = 0; i < m; i++) {
                int t = succ(N, (int)s, i, c, (mk >> i) & 1, nu);
                if (t < 0) { fprintf(stderr, "bad succ N=%d c=%d nu=%d mk=%d i=%d\n", N, c, nu, mk, i); exit(2); }
                best = min(best, PHI(pc, N2, t));
              }
              val = max(val, best);
            }
          }
        }
      }
      if (val > 255) { fprintf(stderr, "one-copy value above 255\n"); exit(2); }
      phi[off[p][N] + s] = (unsigned char)val;
    }
  }
}

static u64 SMAX;
static inline u64 jkey(int p, int N, const int *s) { u64 x = (u64)p * (NMAX + 1) + N; for (int j = 0; j < K; j++) x = x * SMAX + s[j]; return x; }
static vector<u64> mk_; static vector<unsigned char> mv_; static u64 mmask = 0, mcount = 0;
static inline u64 mix(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static void memoInit(u64 cap) { vector<u64>(cap, 0).swap(mk_); vector<unsigned char>(cap, 0).swap(mv_); mmask = cap - 1; mcount = 0; }
static inline int memoGet(u64 key) { u64 h = mix(key) & mmask; while (mk_[h]) { if (mk_[h] == key + 1) return mv_[h]; h = (h + 1) & mmask; } return 0; }
static void memoPut(u64 key, int v);
static void memoGrow() {
  vector<u64> ok; vector<unsigned char> ov; ok.swap(mk_); ov.swap(mv_); memoInit(ok.size() * 2);
  for (size_t i = 0; i < ok.size(); i++) if (ok[i]) memoPut(ok[i] - 1, ov[i]);
}
static void memoPut(u64 key, int v) {
  if (mcount * 10 >= (mmask + 1) * 6) memoGrow();
  u64 h = mix(key) & mmask; while (mk_[h]) { if (mk_[h] == key + 1) { mv_[h] = (unsigned char)v; return; } h = (h + 1) & mmask; }
  mk_[h] = key + 1; mv_[h] = (unsigned char)v; mcount++;
}
static long long nodes = 0, nTrue = 0, nFalse = 0; static bool aborted = false;
static inline int UBv(int p, int N, const int *s) { int u = 0; for (int j = 0; j < K; j++) u += w[j] * PHI(p, N, s[j]); return u; }
static inline int LBv(int p, int N, const int *s) {
  int pay = 0; for (int j = 0; j < K; j++) pay += w[j] * cs[N][s[j]].q[m - 1];
  int best = 0;
  for (int j = 0; j < K; j++) best = max(best, pay - w[j] * cs[N][s[j]].q[m - 1] + w[j] * PHI(p, N, s[j]));
  return best;
}
static inline int quick(int p, int N, const int *s) {
  if (UBv(p, N, s) <= T0) return 1;
  if (LBv(p, N, s) > T0) return 2;
  return memoGet(jkey(p, N, s));
}
static int NRESP;
static int RK[64][3];
static inline void respState(const int t[3][4], int x, int *s) { for (int j = 0; j < K; j++) s[j] = t[j][RK[x][j]]; }
static bool prove(int p, int N, const int *s);
template <class Fn> static bool forMoves(int p, int N, const int *s, Fn f) {
  const CS *z[3]; for (int j = 0; j < K; j++) z[j] = &cs[N][s[j]];
  for (int c = 0; c < F; c++) {
    int C = c / r; int pc = C ? Pchild[p][C] : p; if (pc < 0) continue;
    for (int nu = 0; nu < 2; nu++) {
      int N2 = N + c + nu; if (N2 > NMAX) continue;
      if (N == 0) {
        if (nu == 0) continue;
        int t[3][4]; for (int j = 0; j < K; j++) for (int i = 0; i < m; i++) t[j][i] = succ(N, s[j], i, c, 1, 1);
        if (!f(pc, N2, t)) return false; continue;
      }
      int bb[3] = {0, 0, 0};
      while (true) {
        size_t off2 = nu; bool allz = true;
        for (int j = 0; j < K; j++) { off2 = off2 * 100 + tid(z[j]->n, z[j]->e, bb[j]); if (bb[j] < 1) allz = false; }
        if (feasJ[off2] && !(c == 0 && nu == 0 && allz)) {
          size_t mi[3] = {0, 0, 0};
          while (true) {
            int t[3][4];
            for (int j = 0; j < K; j++) { int mkv = masks[z[j]->n][bb[j]][mi[j]]; for (int i = 0; i < m; i++) t[j][i] = succ(N, s[j], i, c, (mkv >> i) & 1, nu); }
            if (!f(pc, N2, t)) return false;
            int j = K - 1; while (j >= 0) { if (++mi[j] < masks[z[j]->n][bb[j]].size()) break; mi[j] = 0; j--; }
            if (j < 0) break;
          }
        }
        int j = K - 1; while (j >= 0) { if (++bb[j] <= z[j]->n) break; bb[j] = 0; j--; }
        if (j < 0) break;
      }
    }
  }
  return true;
}
struct OpenMove { int pc, N2, unk; int t[3][4]; };
static bool prove(int p, int N, const int *s0) {
  int s[3]; for (int j = 0; j < K; j++) s[j] = s0[j];
  int qs = quick(p, N, s); if (qs) return qs == 1;
  if (++nodes > MAXNODES) { aborted = true; return false; }
  vector<OpenMove> open; bool refuted = false;
  forMoves(p, N, s, [&](int pc, int N2, int t[3][4]) -> bool {
    int unk = 0;
    for (int x = 0; x < NRESP; x++) {
      int u[3]; respState(t, x, u);
      for (int j = 0; j < K; j++) if (u[j] < 0) { fprintf(stderr, "bad joint succ\n"); exit(2); }
      int st = quick(pc, N2, u);
      if (st == 1) return true;
      if (st == 0) unk++;
    }
    if (unk == 0) { refuted = true; return false; }
    OpenMove om; om.pc = pc; om.N2 = N2; om.unk = unk; memcpy(om.t, t, sizeof(om.t));
    open.push_back(om); return true;
  });
  bool ok = !refuted;
  if (ok) {
    stable_sort(open.begin(), open.end(), [](const OpenMove &x, const OpenMove &y) { return x.unk < y.unk; });
    for (size_t o = 0; o < open.size() && ok; o++) {
      OpenMove &om = open[o]; int cand[64], ub[64], nc = 0; bool done = false;
      for (int x = 0; x < NRESP && !done; x++) {
        int u[3]; respState(om.t, x, u);
        int st = quick(om.pc, om.N2, u);
        if (st == 1) done = true;
        else if (st == 0) { cand[nc] = x; ub[nc] = UBv(om.pc, om.N2, u) * 4096 + LBv(om.pc, om.N2, u); nc++; }
      }
      if (done) continue;
      for (int x = 0; x < nc; x++) for (int y = x + 1; y < nc; y++) if (ub[y] < ub[x]) { swap(ub[x], ub[y]); swap(cand[x], cand[y]); }
      bool found = false;
      for (int x = 0; x < nc && !found; x++) {
        int u[3]; respState(om.t, cand[x], u);
        if (prove(om.pc, om.N2, u)) found = true;
        if (aborted) return false;
      }
      if (!found) ok = false;
    }
  }
  memoPut(jkey(p, N, s), ok ? 1 : 2); if (ok) nTrue++; else nFalse++;
  return ok;
}

struct JS { int p, N, s[3]; };
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: hybg m K k r w_1 .. w_K T0 [maxnodes=N] [out=FILE] [relax=1] [scan=HI]\n"); return 1; }
  m = atoi(argv[1]); K = atoi(argv[2]);
  if (m < 2 || m > 4 || K < 1 || K > 3 || argc < 6 + K) { fprintf(stderr, "need 2 <= m <= 4, 1 <= K <= 3 and all arguments\n"); return 1; }
  k = atoi(argv[3]); r = atoi(argv[4]); for (int j = 0; j < K; j++) w[j] = atoi(argv[5 + j]); T0 = atoi(argv[5 + K]);
  string out, alsoList; int scanHi = -1;
  for (int i = 6 + K; i < argc; i++) {
    if (!strncmp(argv[i], "maxnodes=", 9)) MAXNODES = atoll(argv[i] + 9);
    else if (!strncmp(argv[i], "out=", 4)) out = argv[i] + 4;
    else if (!strncmp(argv[i], "relax=", 6)) RELAX = atoi(argv[i] + 6);
    else if (!strncmp(argv[i], "scan=", 5)) scanHi = atoi(argv[i] + 5);
    else if (!strncmp(argv[i], "sizes=", 6)) SIZES = atoi(argv[i] + 6);
    else if (!strncmp(argv[i], "also=", 5)) alsoList = argv[i] + 5;
    else { fprintf(stderr, "unknown option %s\n", argv[i]); return 1; }
  }
  for (int j = 0; j < K; j++) if (w[j] < 1) { fprintf(stderr, "weights must be >= 1\n"); return 1; }
  F = k * r; NMAX = m * F; if (k > 31 || m * F + m > 255) { fprintf(stderr, "grid too large\n"); return 1; }
  int W = 0; for (int j = 0; j < K; j++) W += w[j];
  NRESP = 1; for (int j = 0; j < K; j++) NRESP *= m;
  for (int x = 0; x < NRESP; x++) { int y = x; for (int j = K - 1; j >= 0; j--) { RK[x][j] = y % m; y /= m; } }
  double t0 = now();
  buildProfiles(); buildCopyStates(); buildMasks(); buildFeas();
  SMAX = 0; for (int N = 0; N <= NMAX; N++) SMAX = max<u64>(SMAX, cs[N].size());
  if (SIZES) {
    long long tot = 0, ns = 0; for (int N = 0; N <= NMAX; N++) tot += cs[N].size();
    for (size_t p = 0; p < P.size(); p++) for (int N = lowN(p); N <= NMAX; N++) { if (N == 0 && p != 0) continue; ns += cs[N].size(); }
    printf("SIZES m %d k %d r %d F %d profiles %zu copy-vectors %lld SMAX %llu one-copy states %lld succT-bytes %lld\n",
           m, k, r, F, P.size(), tot, (unsigned long long)SMAX, ns, tot * m * (F + 1) * 3 * 4LL);
    return 0;
  }
  { long double lim = (long double)P.size() * (NMAX + 1); for (int j = 0; j < K; j++) lim *= SMAX; if (lim > 9.0e18L) { fprintf(stderr, "joint key overflow\n"); return 1; } }
  solveSingle();
  int root1 = PHI(0, 0, 0);
  long long cnt1 = 0, nfe = 0; for (int nu = 0; nu < 2; nu++) for (int n = 1; n <= m; n++) for (int e = 0; e < n; e++) for (int b = 0; b <= n; b++) { cnt1++; nfe += feas1[nu][n][e][b]; }
  string ws; for (int j = 0; j < K; j++) { if (j) ws += ","; ws += to_string(w[j]); }
  printf("m %d K %d grid k %d r %d F %d weights %s W %d (one-copy table: %lld rows, %lld allowed)\n", m, K, k, r, F, ws.c_str(), W, cnt1, nfe);
  printf("profiles %zu, one-copy states %lld, one-copy value at root %d/%d = %.6f (%.1fs)\n", P.size(), nSingle, root1, F, (double)root1 / F, now() - t0);
  fflush(stdout);
  auto solveCase = [&](int scanHi, const string &out) -> int {
  int W = 0; for (int j = 0; j < K; j++) W += w[j];
  if (scanHi < T0) scanHi = T0;
  bool ok = false;
  for (; T0 <= scanHi; T0++) {
    memoInit(1ULL << 22); nodes = nTrue = nFalse = 0; aborted = false;
    int root[3] = {0, 0, 0};
    ok = prove(0, 0, root);
    printf("T0 %d (target %d/%d = %.6f) relax %d search: %s, expanded %lld, proved %lld, refuted %lld (%.1fs)\n", T0, T0, W * F, (double)T0 / (W * F), RELAX,
           aborted ? "ABORTED (node budget)" : ok ? "ROOT PROVED" : "ROOT REFUTED", nodes, nTrue, nFalse, now() - t0);
    fflush(stdout);
    if (aborted) return 3;
    if (ok) break;
  }
  if (!ok) return 4;
  unordered_map<u64, int> inJ; vector<JS> J;
  { int root[3] = {0, 0, 0}; if (UBv(0, 0, root) > T0) { JS s = {0, 0, {0, 0, 0}}; inJ[jkey(0, 0, root)] = 0; J.push_back(s); } }
  long long movesChecked = 0, leafAnswers = 0;
  for (size_t h = 0; h < J.size(); h++) {
    JS s = J[h];
    bool good = forMoves(s.p, s.N, s.s, [&](int pc, int N2, int t[3][4]) -> bool {
      movesChecked++; int u[3];
      for (int x = 0; x < NRESP; x++) { respState(t, x, u); if (UBv(pc, N2, u) <= T0) { leafAnswers++; return true; } }
      for (int x = 0; x < NRESP; x++) { respState(t, x, u); if (inJ.count(jkey(pc, N2, u))) return true; }
      int bx = -1, bu = 1 << 30;
      for (int x = 0; x < NRESP; x++) {
        respState(t, x, u);
        if (memoGet(jkey(pc, N2, u)) == 1) { int v = UBv(pc, N2, u); if (v < bu) { bu = v; bx = x; } }
      }
      if (bx < 0) return false;
      respState(t, bx, u);
      JS tt; tt.p = pc; tt.N = N2; for (int j = 0; j < 3; j++) tt.s[j] = j < K ? u[j] : 0;
      inJ[jkey(pc, N2, u)] = (int)J.size(); J.push_back(tt);
      return true;
    });
    if (!good) { fprintf(stderr, "extraction failed\n"); return 5; }
  }
  int maxN = 0; vector<long long> byN(NMAX + 1, 0);
  for (size_t h = 0; h < J.size(); h++) { maxN = max(maxN, J[h].N); byN[J[h].N]++; }
  printf("J: %zu joint states, %lld non-idle moves at them, %lld answered by a leaf; largest N in J = %d (%.1fs)\n", J.size(), movesChecked, leafAnswers, maxN, now() - t0);
  printf("J by N:"); for (int N = 0; N <= maxN; N++) if (byN[N]) printf(" %d:%lld", N, byN[N]); printf("\n");
  if (!out.empty()) {
    FILE *f = fopen(out.c_str(), "w"); if (!f) { perror("out"); return 1; }
    if (m == 3 && K == 2) {
      fprintf(f, "# hybrid certificate: joint states with one-copy leaves.  line: N | H (coarse classes, or -) | q1 | q2\n");
      fprintf(f, "HYB3 %d %d %d %d %d %zu\n", k, r, w[0], w[1], T0, J.size());
    } else {
      fprintf(f, "# hybrid certificate: joint states with one-copy leaves.  line: N | H (coarse classes, or -) | q_1 | ... | q_K\n");
      fprintf(f, "HYBG %d %d %d %d", m, K, k, r); for (int j = 0; j < K; j++) fprintf(f, " %d", w[j]); fprintf(f, " %d %zu\n", T0, J.size());
    }
    for (size_t h = 0; h < J.size(); h++) {
      const JS &s = J[h]; fprintf(f, "%d |", s.N);
      if (Prep[s.p].empty()) fprintf(f, " -"); else for (size_t i = 0; i < Prep[s.p].size(); i++) fprintf(f, " %d", Prep[s.p][i]);
      for (int j = 0; j < K; j++) { const CS &x = cs[s.N][s.s[j]]; fprintf(f, " |"); for (int i = 0; i < m; i++) fprintf(f, " %d", x.q[i]); }
      fprintf(f, "\n");
    }
    fclose(f);
  }
  return 0;
  };
  int rc = solveCase(scanHi, out);
  for (size_t ai = 0, cnum = 1; ai < alsoList.size(); cnum++) {
    size_t bj = alsoList.find('/', ai); string item = alsoList.substr(ai, bj == string::npos ? string::npos : bj - ai);
    ai = bj == string::npos ? alsoList.size() : bj + 1;
    vector<int> v; size_t a = 0; while (a <= item.size()) { size_t c2 = item.find(',', a); v.push_back(atoi(item.substr(a, c2 == string::npos ? string::npos : c2 - a).c_str())); if (c2 == string::npos) break; a = c2 + 1; }
    if ((int)v.size() != K + 1) { fprintf(stderr, "bad also= item %s\n", item.c_str()); return 1; }
    for (int j = 0; j < K; j++) { w[j] = v[j]; if (w[j] < 1) { fprintf(stderr, "weights must be >= 1\n"); return 1; } }
    T0 = v[K];
    string ws2; for (int j = 0; j < K; j++) { if (j) ws2 += ","; ws2 += to_string(w[j]); }
    printf("also case %zu: weights %s\n", cnum, ws2.c_str()); fflush(stdout);
    int rc2 = solveCase(T0, out.empty() ? out : out + ".also" + to_string(cnum));
    printf("also case %zu: exit %d\n", cnum, rc2); fflush(stdout);
  }
  return rc;
}
