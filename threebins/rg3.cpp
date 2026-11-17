// rg3.cpp: solves the rounded lottery game for three bins (paper, App. F).
// g++ -O2 -fopenmp -o rg3 rg3.cpp && ./rg3 k r w_1,...,w_K [cert=FILE]
// Prints the root value T0. The lottery of the weights has expected cost at most T0/(W k r).
// cert=FILE writes the certificate (format in c3a.cpp). ./rg3 reread FILE is a self-test, not a checker.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <climits>
#include <vector>
#include <map>
#include <algorithm>
#include <sys/types.h>
#include <omp.h>
using namespace std;
typedef uint16_t val_t;
typedef unsigned long long u64;

static int k, r, F, NMAX, cap, K, w[3], Wsum;
static int LOt[2][4][3][4], HIt[2][4][3][4];
static void set_(int nu, int n, int e, int b, int lo, int hi) { LOt[nu][n][e][b] = lo; HIt[nu][n][e][b] = hi; }
static void table() {
  memset(LOt, 0, sizeof LOt); memset(HIt, 0, sizeof HIt);
  for (int nu = 0; nu < 2; nu++) for (int n = 1; n <= 3; n++) for (int e = 0; e < n; e++) {
    int eps = e - nu;
    if (eps == -1) set_(nu, n, e, 0, 1, 4);
    else if (eps == n - 1) set_(nu, n, e, n, 1, 4);
    else if (n == 2 && eps == 0) { set_(nu, n, e, 0, 3, 4); set_(nu, n, e, 1, 1, 4); set_(nu, n, e, 2, 1, 2); }
    else if (n == 3 && eps == 0) { set_(nu, n, e, 0, 2, 4); set_(nu, n, e, 1, 1, 4); set_(nu, n, e, 2, 1, 2); set_(nu, n, e, 3, 1, 1); }
    else if (n == 3 && eps == 1) { set_(nu, n, e, 0, 4, 4); set_(nu, n, e, 1, 3, 4); set_(nu, n, e, 2, 1, 4); set_(nu, n, e, 3, 1, 3); }
    else { fprintf(stderr, "table gap\n"); exit(1); }
  }
}

static inline int pk3(int a, int b, int c) { return (a << 12) | (b << 6) | c; }
static vector<vector<int> > Ptri; static vector<int> Psum; static vector<vector<int> > Pchild; static map<vector<int>, int> Pid;
static vector<int> minimize(vector<int> v) {
  sort(v.begin(), v.end()); v.erase(unique(v.begin(), v.end()), v.end());
  vector<int> out;
  for (size_t i = 0; i < v.size(); i++) {
    int a0 = v[i] >> 12, a1 = (v[i] >> 6) & 63, a2 = v[i] & 63; bool dom = false;
    for (size_t j = 0; j < v.size() && !dom; j++) if (j != i) { int b0 = v[j] >> 12, b1 = (v[j] >> 6) & 63, b2 = v[j] & 63; if (b0 <= a0 && b1 <= a1 && b2 <= a2) dom = true; }
    if (!dom) out.push_back(v[i]);
  }
  return out;
}
static int getProf(const vector<int> &tri, int sum) {
  map<vector<int>, int>::iterator it = Pid.find(tri);
  if (it != Pid.end()) { if (Psum[it->second] != sum) { fprintf(stderr, "profile sum\n"); exit(2); } return it->second; }
  int id = (int)Ptri.size(); Pid[tri] = id; Ptri.push_back(tri); Psum.push_back(sum); Pchild.push_back(vector<int>(k, -1));
  return id;
}
static void buildProfiles() {
  getProf(vector<int>(1, pk3(0, 0, 0)), 0);
  for (size_t p = 0; p < Ptri.size(); p++) for (int C = 1; C <= k - 1; C++) {
    vector<int> nt;
    for (size_t z = 0; z < Ptri[p].size(); z++) {
      int s[3] = {Ptri[p][z] >> 12, (Ptri[p][z] >> 6) & 63, Ptri[p][z] & 63};
      for (int i = 0; i < 3; i++) if (s[i] + C <= cap) { int t[3] = {s[0], s[1], s[2]}; t[i] += C; sort(t, t + 3); nt.push_back(pk3(t[0], t[1], t[2])); }
    }
    if (nt.empty()) continue;
    nt = minimize(nt); int sum = Psum[p] + C;
    int c = getProf(nt, sum); Pchild[p][C] = c;
  }
}
static inline int lowN(int p) { return Psum[p] == 0 ? 0 : r * Psum[p] + 1; }

struct CS { int q[3]; int e, n; };
static vector<vector<CS> > cs; static vector<int> cidx; static int CD;
static inline int &CI(int N, int e, int u, int v) { return cidx[((size_t)(N * 3 + e) * CD + u) * CD + v]; }
struct Vec { int bits, lo, hi, b; };
static vector<Vec> vecs[2][4][3];
static long long pw[512][4];
static int succ(int N, const CS &x, int c, int nu, int i, int o) {
  int q[3] = {x.q[0], x.q[1], x.q[2]}; q[i] += c + o; sort(q, q + 3);
  int Np = N + c + nu, e2 = x.e + o - nu, n2 = (q[0] > 0) + (q[1] > 0) + (q[2] > 0);
  if (Np > NMAX || e2 < 0 || e2 > 2 || e2 > n2 - 1 || q[0] + q[1] + q[2] != Np + e2) return -1;
  return CI(Np, e2, q[0], q[1]);
}
static vector<long long> off; static val_t *T;
struct Mv { int c, nu, Np, pp; val_t *Tn; long long o; };
static void moves(int p, int N, vector<Mv> &mv) {
  mv.clear();
  for (int c = 0; c < F; c++) for (int nu = 0; nu < 2; nu++) {
    if (N == 0 && nu == 0) continue;
    int Np = N + c + nu; if (Np > NMAX) continue;
    int C = c / r, pp = p; if (C >= 1) { pp = Pchild[p][C]; if (pp < 0) continue; }
    long long o = off[(size_t)pp * (NMAX + 1) + Np]; if (o < 0) { fprintf(stderr, "missing array p=%d N=%d -> %d %d\n", p, N, pp, Np); exit(3); }
    Mv m; m.c = c; m.nu = nu; m.Np = Np; m.pp = pp; m.Tn = T ? T + o : NULL; m.o = o; mv.push_back(m);
  }
}
static long long bad = 0;

static int evalMove(int N, const int *s, const Mv &m, int best, bool earlyExit) {
  int sc[3][3][2]; const vector<Vec> *V[3]; int na[3] = {1, 1, 1};
  for (int j = 0; j < K; j++) {
    const CS &x = cs[N][s[j]];
    for (int i = 0; i < 3; i++) for (int o = 0; o < 2; o++) sc[j][i][o] = succ(N, x, m.c, m.nu, i, o);
    V[j] = &vecs[m.nu][x.n][x.e]; na[j] = (int)V[j]->size();
    if (na[j] == 0) { fprintf(stderr, "no pattern\n"); exit(4); }
  }
  int a[3] = {0, 0, 0};
  while (true) {
    int lo = 1, hi = 4; bool idle = (m.c == 0 && m.nu == 0);
    for (int j = 0; j < K; j++) { const Vec &vv = (*V[j])[a[j]]; lo = max(lo, vv.lo); hi = min(hi, vv.hi); if (vv.b == 0) idle = false; }
    if (lo <= hi && !idle) {
      int mn = INT_MAX; int rr[3] = {0, 0, 0};
      while (true) {
        long long ix = 0;
        for (int j = 0; j < K; j++) { int bit = ((*V[j])[a[j]].bits >> rr[j]) & 1; int t = sc[j][rr[j]][bit]; if (t < 0) { fprintf(stderr, "invalid successor\n"); exit(5); } ix += (long long)t * pw[m.Np][j]; }
        int v = m.Tn[ix]; if (v < mn) { mn = v; if (earlyExit && mn <= best) break; }
        int j = 0; while (j < K) { if (++rr[j] < 3) break; rr[j] = 0; j++; }
        if (j == K) break;
      }
      if (mn > best) best = mn;
    }
    int j = 0; while (j < K) { if (++a[j] < na[j]) break; a[j] = 0; j++; }
    if (j == K) break;
  }
  return best;
}
static void process(int p, int N) {
  val_t *base = T + off[(size_t)p * (NMAX + 1) + N];
  int S = (int)cs[N].size(); long long total = pw[N][K];
  vector<Mv> mv; moves(p, N, mv);
  for (int E = 2 * K; E >= 0; E--) {
    int s[3] = {0, 0, 0};
    for (long long idx = 0; idx < total; idx++) {
      int Es = 0; for (int j = 0; j < K; j++) Es += cs[N][s[j]].e;
      if (Es == E) {
        int best = 0; for (int j = 0; j < K; j++) best += w[j] * cs[N][s[j]].q[2];
        for (size_t mi = 0; mi < mv.size(); mi++) best = evalMove(N, s, mv[mi], best, true);
        if (best > 65535) { fprintf(stderr, "overflow\n"); exit(6); }
        base[idx] = (val_t)best;
      }
      int j = 0; while (j < K) { if (++s[j] < S) break; s[j] = 0; j++; }
    }
  }
}

static long long simSteps = 0, simFail = 0, simPrefixes = 0; static double simWorst = 0; static int rootT = 0;
static char simWorstDesc[512];
static inline long long cdivll(long long a, long long q) { return (a + q - 1) / q; }
struct Sim { long long D, V; long long L[3][3]; int p; };
static bool sfail(const char *m) { if (simFail < 20) printf("SIM FAIL: %s\n", m); simFail++; return false; }
static bool simStep(Sim &S, long long a) {
  long long D = S.D; int N = (int)cdivll(S.V, D);
  long long c = cdivll(a, D) - 1, t = a - c * D, x = (long long)N * D - S.V;
  int nu = (t > x) ? 1 : 0;
  if (c < 0 || c > F - 1) return sfail("fine class out of range");
  if (N + c + nu > NMAX) return sfail("(M2) violated by a feasible input");
  int C = (int)(c / r), pp = S.p; if (C >= 1) { pp = Pchild[S.p][C]; if (pp < 0) return sfail("(M3) violated by a feasible input"); }
  int rank[3][3], sidx[3], bits[3], lo = 1, hi = 4; bool idle = (c == 0 && nu == 0);
  long long idx = 0;
  for (int j = 0; j < K; j++) {
    long long q[3]; int ord[3] = {0, 1, 2};
    for (int i = 0; i < 3; i++) q[i] = cdivll(S.L[j][i], D);
    sort(ord, ord + 3, [&](int a1, int b1) { return q[a1] < q[b1] || (q[a1] == q[b1] && a1 < b1); });
    for (int i = 0; i < 3; i++) rank[j][i] = ord[i];
    int e = (int)(q[0] + q[1] + q[2] - N), n = (q[0] > 0) + (q[1] > 0) + (q[2] > 0);
    if (N >= 1 && (e < 0 || e > n - 1)) return sfail("invariant (ii)");
    if (N == 0 && (n != 0 || e != 0)) return sfail("root state");
    sidx[j] = CI(N, e, (int)q[ord[0]], (int)q[ord[1]]); if (sidx[j] < 0) return sfail("state index");
    idx += (long long)sidx[j] * pw[N][j];
    bits[j] = 0;
    for (int i = 0; i < 3; i++) { long long Lr = S.L[j][rank[j][i]]; long long f = cdivll(Lr, D) * D - Lr; int o = (t > f) ? 1 : 0; bits[j] |= o << i; }
    const vector<Vec> &vv = vecs[nu][n][e]; int found = -1;
    for (size_t z = 0; z < vv.size(); z++) if (vv[z].bits == bits[j]) found = (int)z;
    if (found < 0) return sfail("real bit vector not allowed");
    lo = max(lo, vv[found].lo); hi = min(hi, vv[found].hi); if (vv[found].b == 0) idle = false;
  }
  if (lo > hi) return sfail("real joint pattern not allowed");
  long long o0 = off[(size_t)S.p * (NMAX + 1) + N]; if (o0 < 0) return sfail("no array");
  int Tv = T[o0 + idx]; int Np = N + (int)c + nu;
  long long o1 = off[(size_t)pp * (NMAX + 1) + Np]; if (o1 < 0) return sfail("no target array");
  int choice[3] = {0, 0, 0}, pred[3] = {0, 0, 0};
  if (idle) {
    for (int j = 0; j < K; j++) { choice[j] = -1; for (int i = 0; i < 3 && choice[j] < 0; i++) if (S.L[j][rank[j][i]] > 0 && !((bits[j] >> i) & 1)) choice[j] = i; pred[j] = sidx[j]; }
  } else {
    int rr[3] = {0, 0, 0}; bool found = false;
    while (true) {
      long long ix = 0; int tt[3];
      for (int j = 0; j < K; j++) { tt[j] = succ(N, cs[N][sidx[j]], (int)c, nu, rr[j], (bits[j] >> rr[j]) & 1); if (tt[j] < 0) return sfail("successor"); ix += (long long)tt[j] * pw[Np][j]; }
      if (T[o1 + ix] <= Tv) { found = true; for (int j = 0; j < K; j++) { choice[j] = rr[j]; pred[j] = tt[j]; } break; }
      int j = 0; while (j < K) { if (++rr[j] < 3) break; rr[j] = 0; j++; }
      if (j == K) break;
    }
    if (!found) return sfail("no response satisfies (c)");
  }
  for (int j = 0; j < K; j++) S.L[j][rank[j][choice[j]]] += a;
  S.V += a; S.p = (idle ? S.p : pp); simSteps++;
  int N2 = (int)cdivll(S.V, D); if (N2 != (idle ? N : Np)) return sfail("N prediction");
  for (int j = 0; j < K; j++) {
    long long q[3]; for (int i = 0; i < 3; i++) q[i] = cdivll(S.L[j][i], D);
    sort(q, q + 3); int e = (int)(q[0] + q[1] + q[2] - N2);
    if (e < 0 || e > 2 || CI(N2, e, (int)q[0], (int)q[1]) != pred[j]) return sfail("successor prediction");
  }

  long long cost = 0; for (int j = 0; j < K; j++) { long long m = max(S.L[j][0], max(S.L[j][1], S.L[j][2])); cost += (long long)w[j] * m; }
  if (cost > (long long)rootT * D) return sfail("prefix cost exceeds T(root)/(WF)");
  double ratio = (double)cost / ((double)D * Wsum * F); simPrefixes++;
  if (ratio > simWorst) { simWorst = ratio; snprintf(simWorstDesc, sizeof simWorstDesc, "D=%lld V=%lld", D, S.V); }
  return true;
}
static unsigned long long srng = 0x9E3779B97F4A7C15ULL;
static unsigned long long sx() { srng ^= srng << 13; srng ^= srng >> 7; srng ^= srng << 17; return srng; }
static void simRandom(long long n) {
  const long long Ds[] = {1, 2, 3, 4, 5, 6, 7, 8, 12, 60};
  for (long long it = 0; it < n; it++) {
    long long D = Ds[sx() % 10], cap = (long long)F * D; vector<long long> jobs;
    int mode = (int)(sx() % 4);
    for (int b = 0; b < 3; b++) {
      long long rem = cap;
      while (rem > 0) {
        long long s;
        if (mode == 0) s = 1 + (long long)(sx() % rem);
        else if (mode == 1) s = 1 + (long long)(sx() % min(rem, D * (1 + (long long)(sx() % 3))));
        else if (mode == 2) { long long u = D * (1 + (long long)(sx() % F)); s = min(rem, u - (long long)(sx() % 2)); if (s <= 0) s = 1; }
        else s = 1 + (long long)(sx() % min(rem, cap / 2 + 1));
        jobs.push_back(s); rem -= s;
        if (sx() % 5 == 0) break;
      }
    }
    for (size_t i = jobs.size(); i > 1; i--) swap(jobs[i - 1], jobs[sx() % i]);
    Sim S; S.D = D; S.V = 0; S.p = 0; memset(S.L, 0, sizeof S.L);
    for (size_t i = 0; i < jobs.size(); i++) if (!simStep(S, jobs[i])) break;
  }
}

static bool fits3(vector<long long> &v, long long cap) {
  long long b[3] = {0, 0, 0}; vector<long long> s = v; sort(s.rbegin(), s.rend());

  struct R { static bool go(vector<long long> &s, size_t i, long long *b, long long cap) {
    if (i == s.size()) return true;
    for (int k2 = 0; k2 < 3; k2++) { if (b[k2] + s[i] > cap) continue; bool dup = false; for (int k3 = 0; k3 < k2; k3++) if (b[k3] == b[k2]) dup = true; if (dup) continue;
      b[k2] += s[i]; if (go(s, i + 1, b, cap)) { b[k2] -= s[i]; return true; } b[k2] -= s[i]; }
    return false; } };
  return R::go(s, 0, b, cap);
}
static void simExhaust(Sim S, vector<long long> &jobs, int m, long long d) {
  if ((int)jobs.size() == m) return;
  for (long long a = 1; a <= (long long)F * d; a++) {
    jobs.push_back(a);
    if (fits3(jobs, (long long)F * d)) { Sim S2 = S; if (simStep(S2, a)) simExhaust(S2, jobs, m, d); }
    jobs.pop_back();
  }
}

static int selfCheck(const char *wname, long long total, double t0) {
  vector<u64> vis((total + 63) / 64, 0);
  vector<long long> qp; vector<int> qN; vector<long long> qi;
  qp.push_back(0); qN.push_back(0); qi.push_back(0); vis[0] |= 1;
  long long movesChecked = 0, idleMoves = 0;
  for (size_t h = 0; h < qp.size(); h++) {
    int p = (int)qp[h], N = qN[h]; long long idx = qi[h]; int S = (int)cs[N].size();
    int s[3] = {0, 0, 0}; { long long x = idx; for (int j = 0; j < K; j++) { s[j] = (int)(x % S); x /= S; } }
    int Tv = T[off[(size_t)p * (NMAX + 1) + N] + idx];
    int pay = 0, Es = 0; for (int j = 0; j < K; j++) { pay += w[j] * cs[N][s[j]].q[2]; Es += cs[N][s[j]].e;
      const CS &x = cs[N][s[j]]; if (N >= 1 && (x.n < 1 || x.e > x.n - 1)) bad++; }
    if (pay > Tv) { bad++; if (bad < 10) printf("FAIL (b)\n"); }
    if (Psum[p] > 0 && N < r * Psum[p] + 1) bad++;
    vector<Mv> mv; moves(p, N, mv);
    for (size_t mi = 0; mi < mv.size(); mi++) {
      const Mv &m = mv[mi]; int sc[3][3][2]; const vector<Vec> *V[3]; int na[3] = {1, 1, 1};
      for (int j = 0; j < K; j++) { for (int i = 0; i < 3; i++) for (int o = 0; o < 2; o++) sc[j][i][o] = succ(N, cs[N][s[j]], m.c, m.nu, i, o); V[j] = &vecs[m.nu][cs[N][s[j]].n][cs[N][s[j]].e]; na[j] = (int)V[j]->size(); }
      int a[3] = {0, 0, 0};
      while (true) {
        int lo = 1, hi = 4; bool idle = (m.c == 0 && m.nu == 0);
        for (int j = 0; j < K; j++) { const Vec &vv = (*V[j])[a[j]]; lo = max(lo, vv.lo); hi = min(hi, vv.hi); if (vv.b == 0) idle = false; }
        if (lo <= hi) {
          movesChecked++;
          if (idle) idleMoves++;
          else {
            int mn = INT_MAX; long long bi = -1; bool bv = false; int rr[3] = {0, 0, 0};
            while (true) {
              long long ix = 0; int E2 = 0;
              for (int j = 0; j < K; j++) { int bit = ((*V[j])[a[j]].bits >> rr[j]) & 1; int t = sc[j][rr[j]][bit]; if (t < 0) { bad++; t = 0; } ix += (long long)t * pw[m.Np][j]; E2 += cs[m.Np][t].e; }
              if (m.c == 0 && m.nu == 0 && E2 <= Es) { bad++; if (bad < 10) printf("FAIL order\n"); }
              int v = m.Tn[ix]; bool vv = (vis[(m.o + ix) >> 6] >> ((m.o + ix) & 63)) & 1;
              if (v < mn || (v == mn && vv && !bv)) { mn = v; bi = ix; bv = vv; }
              int j = 0; while (j < K) { if (++rr[j] < 3) break; rr[j] = 0; j++; }
              if (j == K) break;
            }
            if (mn > Tv) { bad++; if (bad < 10) printf("FAIL (c) at N=%d\n", N); }
            long long g = m.o + bi;
            if (!((vis[g >> 6] >> (g & 63)) & 1)) { vis[g >> 6] |= 1ULL << (g & 63); qp.push_back(m.pp); qN.push_back(m.Np); qi.push_back(bi); }
          }
        }
        int j = 0; while (j < K) { if (++a[j] < na[j]) break; a[j] = 0; j++; }
        if (j == K) break;
      }
    }
  }
  printf("CHECK k %d r %d weights %s: %zu reachable states, %lld moves (%lld idle), %s (%.0fs)\n", k, r, wname, qp.size(), movesChecked, idleMoves, bad ? "FAIL" : "PASS", omp_get_wtime() - t0);
  fflush(stdout);
  return bad ? 9 : 0;
}

static vector<vector<int> > Hc;
static vector<int> HP, HS;
static vector<vector<int> > HC;
static map<vector<int>, int> HId;

static void buildH() {
  vector<int> z(k - 1, 0); HId[z] = 0; Hc.push_back(z); HP.push_back(0); HS.push_back(0); HC.push_back(vector<int>(k, -1));
  for (size_t h = 0; h < Hc.size(); h++) for (int C = 1; C <= k - 1; C++) {
    int pc = Pchild[HP[h]][C]; if (pc < 0) continue;
    vector<int> v = Hc[h]; v[C - 1]++;
    map<vector<int>, int>::iterator it = HId.find(v); int id;
    if (it == HId.end()) { id = (int)Hc.size(); HId[v] = id; Hc.push_back(v); HP.push_back(pc); HS.push_back(HS[h] + C); HC.push_back(vector<int>(k, -1)); }
    else { id = it->second; if (HP[id] != pc) { fprintf(stderr, "profile check: the profile of H depends on the order of its jobs\n"); exit(20); } }
    HC[h][C] = id;
  }
}

static vector<int> directProf(const vector<int> &cnt) {
  int D = cap + 1; vector<char> cur((size_t)D * D * D, 0), nx; cur[0] = 1;
  for (int C = 1; C <= k - 1; C++) for (int t = 0; t < cnt[C - 1]; t++) {
    nx.assign((size_t)D * D * D, 0);
    for (int a = 0; a < D; a++) for (int b = 0; b < D; b++) for (int c = 0; c < D; c++) if (cur[((size_t)a * D + b) * D + c]) {
      if (a + C < D) nx[((size_t)(a + C) * D + b) * D + c] = 1;
      if (b + C < D) nx[((size_t)a * D + (b + C)) * D + c] = 1;
      if (c + C < D) nx[((size_t)a * D + b) * D + (c + C)] = 1;
    }
    cur.swap(nx);
  }
  vector<int> v;
  for (int a = 0; a < D; a++) for (int b = 0; b < D; b++) for (int c = 0; c < D; c++) if (cur[((size_t)a * D + b) * D + c]) {
    int t[3] = {a, b, c}; sort(t, t + 3); v.push_back(pk3(t[0], t[1], t[2]));
  }
  if (v.empty()) return v;
  return minimize(v);
}

static void checkH() {
  for (size_t h = 0; h < Hc.size(); h++) {
    vector<int> dp = directProf(Hc[h]); int s = 0;
    for (int C = 1; C <= k - 1; C++) s += C * Hc[h][C - 1];
    if (dp.empty() || dp != Ptri[HP[h]] || s != HS[h] || HS[h] != Psum[HP[h]]) { fprintf(stderr, "profile check fails at multiset %zu\n", h); exit(21); }
    for (int C = 1; C <= k - 1; C++) {
      vector<int> v = Hc[h]; v[C - 1]++;
      bool splits = !directProf(v).empty();
      if (splits != (HC[h][C] >= 0)) { fprintf(stderr, "profile check (a) fails at multiset %zu, class %d\n", h, C); exit(22); }
    }
  }
}

static vector<long long> baseP, sizeP, offX; static long long TX = 0;
static void layoutX(long long total) {
  int nP = (int)Ptri.size(); baseP.assign(nP, 0); sizeP.assign(nP, 0);
  for (int p = 0; p < nP; p++) baseP[p] = off[(size_t)p * (NMAX + 1) + lowN(p)];
  for (int p = 0; p < nP; p++) sizeP[p] = (p + 1 < nP ? baseP[p + 1] : total) - baseP[p];
  offX.assign(Hc.size(), 0); TX = 0;
  for (size_t h = 0; h < Hc.size(); h++) { offX[h] = TX; TX += sizeP[HP[h]]; }
}
static inline long long GX(int h, int N, long long idx) { int p = HP[h]; return offX[h] + (off[(size_t)p * (NMAX + 1) + N] - baseP[p]) + idx; }

static const int IB = 36;
static inline u64 ePack(int h, int N, long long idx) { return ((u64)h << (IB + 10)) | ((u64)N << IB) | (u64)idx; }
static inline int eH(u64 e) { return (int)(e >> (IB + 10)); }
static inline int eN(u64 e) { return (int)((e >> IB) & 1023); }
static inline long long eI(u64 e) { return (long long)(e & ((1ULL << IB) - 1)); }
static inline long long GXe(u64 e) { return GX(eH(e), eN(e), eI(e)); }

static void expandX(u64 e, const u64 *vis, vector<u64> &out, vector<Mv> &mv, long long &nonIdle, long long &idleN, long long &badN) {
  int h = eH(e), N = eN(e); long long idx = eI(e); int p = HP[h], S = (int)cs[N].size();
  int s[3] = {0, 0, 0}; { long long x = idx; for (int j = 0; j < K; j++) { s[j] = (int)(x % S); x /= S; } }
  int Tv = T[off[(size_t)p * (NMAX + 1) + N] + idx];
  int pay = 0, Es = 0;
  for (int j = 0; j < K; j++) {
    const CS &x = cs[N][s[j]]; pay += w[j] * x.q[2]; Es += x.e;
    if (N >= 1 && (x.n < 1 || x.e > x.n - 1)) badN++;
    if (N == 0 && (x.n != 0 || x.e != 0)) badN++;
  }
  if (pay > Tv) badN++;
  if (HS[h] > 0 && N < r * HS[h] + 1) badN++;
  moves(p, N, mv);
  for (size_t mi = 0; mi < mv.size(); mi++) {
    const Mv &m = mv[mi]; int C = m.c / r, h2 = (C >= 1) ? HC[h][C] : h;
    if (h2 < 0 || HP[h2] != m.pp) { badN++; continue; }
    long long bx = offX[h2] + (m.o - baseP[m.pp]);
    int sc[3][3][2]; const vector<Vec> *V[3]; int na[3] = {1, 1, 1}; bool okm = true;
    for (int j = 0; j < K; j++) {
      const CS &x = cs[N][s[j]];
      for (int i = 0; i < 3; i++) for (int o = 0; o < 2; o++) sc[j][i][o] = succ(N, x, m.c, m.nu, i, o);
      V[j] = &vecs[m.nu][x.n][x.e]; na[j] = (int)V[j]->size(); if (na[j] == 0) okm = false;
    }
    if (!okm) { badN++; continue; }
    int a[3] = {0, 0, 0};
    while (true) {
      int lo = 1, hi = 4; bool idle = (m.c == 0 && m.nu == 0);
      for (int j = 0; j < K; j++) { const Vec &vv = (*V[j])[a[j]]; lo = max(lo, vv.lo); hi = min(hi, vv.hi); if (vv.b == 0) idle = false; }
      if (lo <= hi) {
        if (idle) idleN++;
        else {
          nonIdle++;
          int mn = INT_MAX, nc = 0; long long cand[27]; int rr[3] = {0, 0, 0};
          while (true) {
            long long ix = 0; int E2 = 0; bool okr = true;
            for (int j = 0; j < K; j++) { int bit = ((*V[j])[a[j]].bits >> rr[j]) & 1; int t = sc[j][rr[j]][bit]; if (t < 0) { okr = false; break; } ix += (long long)t * pw[m.Np][j]; E2 += cs[m.Np][t].e; }
            if (!okr) badN++;
            else {
              if (m.c == 0 && m.nu == 0 && E2 <= Es) badN++;
              int v = m.Tn[ix];
              if (v < mn) { mn = v; nc = 0; }
              if (v == mn) cand[nc++] = ix;
            }
            int j = 0; while (j < K) { if (++rr[j] < 3) break; rr[j] = 0; j++; }
            if (j == K) break;
          }
          if (nc == 0 || mn > Tv) badN++;
          else {
            bool listed = false;
            for (int y = 0; y < nc && !listed; y++) { long long g = bx + cand[y]; if ((vis[g >> 6] >> (g & 63)) & 1) listed = true; }
            if (!listed) { out.push_back((u64)nc); for (int y = 0; y < nc; y++) out.push_back(ePack(h2, m.Np, cand[y])); }
          }
        }
      }
      int j = 0; while (j < K) { if (++a[j] < na[j]) break; a[j] = 0; j++; }
      if (j == K) break;
    }
  }
}
static inline void putu(char *&p, u64 v) { char t[24]; int l = 0; do { t[l++] = (char)('0' + v % 10); v /= 10; } while (v); while (l) *p++ = t[--l]; }
static long long writeCertFile(const char *fn, const vector<u64> &Q, int root, const char *wname, bool &ok) {
  ok = true; FILE *f = fopen(fn, "wb"); if (!f) { ok = false; return 0; }
  vector<char> buf((size_t)1 << 24); char *b0 = buf.data(), *p = b0, *lim = b0 + buf.size() - 8192; long long bytes = 0;
  p += sprintf(p, "# CERT3 certificate written by rg3.cpp, k %d r %d weights %s, bound T0/(W F) = %d/%d\n", k, r, wname, root, Wsum * F);
  p += sprintf(p, "RG3CERT %d %d %d", k, r, K);
  for (int j = 0; j < K; j++) p += sprintf(p, " %d", w[j]);
  p += sprintf(p, " %d %zu\n", root, Q.size());
  for (size_t i = 0; i < Q.size(); i++) {
    u64 e = Q[i]; int h = eH(e), N = eN(e); long long idx = eI(e); int S = (int)cs[N].size();
    putu(p, (u64)N);
    for (int C = 1; C <= k - 1; C++) { *p++ = ' '; putu(p, (u64)Hc[h][C - 1]); }
    long long x = idx;
    for (int j = 0; j < K; j++) { const CS &c = cs[N][(int)(x % S)]; x /= S; for (int z = 0; z < 3; z++) { *p++ = ' '; putu(p, (u64)c.q[z]); } }
    *p++ = ' '; putu(p, (u64)T[off[(size_t)HP[h] * (NMAX + 1) + N] + idx]); *p++ = '\n';
    if (p > lim) { size_t L = (size_t)(p - b0); if (fwrite(b0, 1, L, f) != L) ok = false; bytes += (long long)L; p = b0; }
  }
  { size_t L = (size_t)(p - b0); if (fwrite(b0, 1, L, f) != L) ok = false; bytes += (long long)L; }
  if (fclose(f) != 0) ok = false;
  return bytes;
}

static int bfsCert(const char *fn, long long chunk, const char *wname, int root, double t0) {
  for (int j = 0; j < K; j++) if (w[j] < 1) { printf("CERT: CERT3 needs weights >= 1, no file written\n"); return 11; }
  if (chunk < 1) chunk = 1;
  double tb0 = omp_get_wtime();
  vector<u64> vis((size_t)((TX + 63) / 64), 0);
  vector<u64> Q; Q.reserve((size_t)1 << 16);
  { long long g = GX(0, 0, 0); vis[g >> 6] |= 1ULL << (g & 63); Q.push_back(ePack(0, 0, 0)); }
  vector<vector<u64> > rec((size_t)chunk);
  vector<vector<Mv> > mvT((size_t)omp_get_max_threads());
  long long nonIdle = 0, idleN = 0, badN = 0; size_t head = 0; double tp = tb0;
  while (head < Q.size()) {
    long long m = (long long)min((size_t)chunk, Q.size() - head);
    long long a1 = 0, a2 = 0, a3 = 0; const u64 *vp = vis.data(); const u64 *qp = Q.data() + head;
    #pragma omp parallel for schedule(dynamic, 8) reduction(+ : a1, a2, a3)
    for (long long i = 0; i < m; i++) { rec[i].clear(); expandX(qp[i], vp, rec[i], mvT[omp_get_thread_num()], a1, a2, a3); }
    nonIdle += a1; idleN += a2; badN += a3;
    if (badN) break;
    for (long long i = 0; i < m; i++) {
      const vector<u64> &R = rec[i];
      for (size_t z = 0; z < R.size(); z += (size_t)R[z] + 1) {
        size_t nc = (size_t)R[z]; bool listed = false;
        for (size_t y = 1; y <= nc && !listed; y++) { long long g = GXe(R[z + y]); if ((vis[g >> 6] >> (g & 63)) & 1) listed = true; }
        if (!listed) { long long g = GXe(R[z + 1]); vis[g >> 6] |= 1ULL << (g & 63); Q.push_back(R[z + 1]); }
      }
    }
    head += (size_t)m;
    if (omp_get_wtime() - tp > 60) { tp = omp_get_wtime(); printf("  search: %zu states done, %zu listed (%.0fs)\n", head, Q.size(), tp - t0); fflush(stdout); }
  }
  double tb1 = omp_get_wtime();
  if (badN) { printf("CERT FAIL k %d r %d weights %s: %lld violations of (b), (c) or of the invariants, no file written\n", k, r, wname, badN); fflush(stdout); return 12; }
  { long long cnt = 0; for (size_t i = 0; i < vis.size(); i++) cnt += __builtin_popcountll(vis[i]);
    if (cnt != (long long)Q.size()) { printf("CERT FAIL: %lld marked states but %zu listed, no file written\n", cnt, Q.size()); return 13; } }
  bool ok; long long bytes = writeCertFile(fn, Q, root, wname, ok);
  double tw = omp_get_wtime();
  if (!ok) { printf("CERT FAIL: could not write %s\n", fn); return 14; }
  printf("CERT k %d r %d weights %s: T0 %d, bound T0/(W F) = %d/%d = %.6f, %zu states, %lld non-idle moves checked (%lld idle), file %s, %lld bytes (search %.0fs, write %.0fs, total %.0fs)\n",
         k, r, wname, root, root, Wsum * F, (double)root / (Wsum * F), Q.size(), nonIdle, idleN, fn, bytes, tb1 - tb0, tw - tb1, tw - t0);
  fflush(stdout);
  return 0;
}

static char *lineBuf = NULL; static size_t lineCap = 0;

static bool nextLine(FILE *f, vector<char *> &tk) {
  while (true) {
    ssize_t L = getline(&lineBuf, &lineCap, f); if (L < 0) return false;
    if (L > 0 && lineBuf[L - 1] == '\n') lineBuf[--L] = 0;
    tk.clear(); char *p = lineBuf;
    while (*p) {
      while (*p == ' ' || *p == '\t') p++;
      if (!*p) break;
      tk.push_back(p);
      while (*p && *p != ' ' && *p != '\t') p++;
      if (*p) *p++ = 0;
    }
    if (tk.empty() || tk[0][0] == '#') continue;
    return true;
  }
}
static bool parseNum(const char *s, u64 &v) {
  size_t L = strlen(s); if (L == 0 || L > 18) return false;
  v = 0; for (size_t i = 0; i < L; i++) { if (s[i] < '0' || s[i] > '9') return false; v = v * 10 + (u64)(s[i] - '0'); }
  return true;
}
static int rfail(int chk, long long id, const char *why) { printf("REREAD FAIL check %d state %lld: %s\n", chk, id, why); fflush(stdout); return 1; }
static int readHeader(FILE *f, long long &T0, long long &n) {
  vector<char *> tk; u64 v;
  if (!nextLine(f, tk)) return rfail(1, -1, "no header");
  if (strcmp(tk[0], "RG3CERT") != 0 || tk.size() < 4) return rfail(1, -1, "header must start with RG3CERT k r K");
  u64 a[3]; for (int i = 0; i < 3; i++) if (!parseNum(tk[1 + i], a[i])) return rfail(1, -1, "bad number in the header");
  if (a[0] < 2 || a[0] > 64 || a[1] < 1 || a[1] > 500 || a[2] < 1 || a[2] > 3) return rfail(1, -1, "k, r or K out of the range of this program (K <= 3)");
  k = (int)a[0]; r = (int)a[1]; K = (int)a[2];
  if ((int)tk.size() != 4 + K + 2) return rfail(1, -1, "wrong number of tokens in the header");
  Wsum = 0;
  for (int j = 0; j < K; j++) { if (!parseNum(tk[4 + j], v) || v < 1 || v > 1000000) return rfail(1, -1, "bad weight"); w[j] = (int)v; Wsum += w[j]; }
  if (!parseNum(tk[4 + K], v)) return rfail(1, -1, "bad T0");
  T0 = (long long)v;
  if (!parseNum(tk[5 + K], v) || v < 1 || v > (u64)1 << 40) return rfail(1, -1, "bad n");
  n = (long long)v;
  return 0;
}
static vector<u64> hk; static vector<val_t> hv; static size_t hcap = 0; static int hbits = 0;
static inline size_t hslot(u64 g) { return (size_t)((g * 0x9E3779B97F4A7C15ULL) >> (64 - hbits)); }
static bool hins(u64 g, val_t v) { size_t i = hslot(g); while (hk[i]) { if (hk[i] == g + 1) return false; i = (i + 1) & (hcap - 1); } hk[i] = g + 1; hv[i] = v; return true; }
static inline int hget(u64 g) { size_t i = hslot(g); while (hk[i]) { if (hk[i] == g + 1) return hv[i]; i = (i + 1) & (hcap - 1); } return -1; }

static const char *verifyX(u64 e, int Tv, vector<Mv> &mv, long long &movesN, long long &idleN) {
  int h = eH(e), N = eN(e); long long idx = eI(e); int p = HP[h], S = (int)cs[N].size();
  int s[3] = {0, 0, 0}; { long long x = idx; for (int j = 0; j < K; j++) { s[j] = (int)(x % S); x /= S; } }
  moves(p, N, mv);
  for (size_t mi = 0; mi < mv.size(); mi++) {
    const Mv &m = mv[mi]; int C = m.c / r, h2 = (C >= 1) ? HC[h][C] : h;
    if (h2 < 0 || HP[h2] != m.pp) return "profile of H + {C}";
    long long bx = offX[h2] + (m.o - baseP[m.pp]);
    int sc[3][3][2]; const vector<Vec> *V[3]; int na[3] = {1, 1, 1};
    for (int j = 0; j < K; j++) {
      const CS &x = cs[N][s[j]];
      for (int i = 0; i < 3; i++) for (int o = 0; o < 2; o++) sc[j][i][o] = succ(N, x, m.c, m.nu, i, o);
      V[j] = &vecs[m.nu][x.n][x.e]; na[j] = (int)V[j]->size(); if (na[j] == 0) return "a copy has no allowed bit vector";
    }
    int a[3] = {0, 0, 0};
    while (true) {
      int lo = 1, hi = 4; bool idle = (m.c == 0 && m.nu == 0);
      for (int j = 0; j < K; j++) { const Vec &vv = (*V[j])[a[j]]; lo = max(lo, vv.lo); hi = min(hi, vv.hi); if (vv.b == 0) idle = false; }
      if (lo <= hi) {
        if (idle) idleN++;
        else {
          movesN++; bool found = false; int rr[3] = {0, 0, 0};
          while (true) {
            long long ix = 0; bool okr = true;
            for (int j = 0; j < K; j++) { int bit = ((*V[j])[a[j]].bits >> rr[j]) & 1; int t = sc[j][rr[j]][bit]; if (t < 0) { okr = false; break; } ix += (long long)t * pw[m.Np][j]; }
            if (okr) { int v = hget((u64)(bx + ix)); if (v >= 0 && v <= Tv) { found = true; break; } }
            int j = 0; while (j < K) { if (++rr[j] < 3) break; rr[j] = 0; j++; }
            if (j == K) break;
          }
          if (!found) return "a non-idle move has no response to a listed state with potential at most T";
        }
      }
      int j = 0; while (j < K) { if (++a[j] < na[j]) break; a[j] = 0; j++; }
      if (j == K) break;
    }
  }
  return NULL;
}
static int reread(FILE *f, const char *fn, long long T0, long long n, const char *wname, double t0) {
  int ntok = 1 + (k - 1) + 3 * K + 1;
  vector<u64> key((size_t)n); vector<val_t> pot((size_t)n);
  hcap = 1; hbits = 0; while (hcap < 2 * (size_t)n + 16) { hcap <<= 1; hbits++; }
  hk.assign(hcap, 0); hv.assign(hcap, 0);
  vector<char *> tk; vector<u64> v((size_t)ntok); vector<int> hcnt(k - 1);
  for (long long i = 0; i < n; i++) {
    if (!nextLine(f, tk)) return rfail(1, i, "fewer state lines than n");
    if ((int)tk.size() != ntok) return rfail(1, i, "wrong number of tokens");
    for (int z = 0; z < ntok; z++) if (!parseNum(tk[z], v[z])) return rfail(1, i, "a token is not a decimal number of at most 18 digits");
    if (v[0] > (u64)NMAX) return rfail(4, i, "N > 3F");
    int N = (int)v[0]; bool hsmall = true;
    for (int C = 1; C <= k - 1; C++) { if (v[C] > 1000) hsmall = false; else hcnt[C - 1] = (int)v[C]; }
    map<vector<int>, int>::iterator it = hsmall ? HId.find(hcnt) : HId.end();
    if (it == HId.end()) return rfail(4, i, "H does not split into three groups with sums at most k - 1");
    int h = it->second;
    if (HS[h] > 0 && N < r * HS[h] + 1) return rfail(4, i, "N < r sum(H) + 1");
    long long idx = 0, pay = 0;
    for (int j = 0; j < K; j++) {
      u64 a = v[k + 3 * j], b = v[k + 3 * j + 1], c = v[k + 3 * j + 2];
      if (!(a <= b && b <= c)) return rfail(1, i, "a triple is not sorted");
      if (c > (u64)NMAX + 2) return rfail(4, i, "a rounded load is too large (e_j > 2)");
      int e = (int)(a + b + c) - N, nn = (a > 0) + (b > 0) + (c > 0);
      if (N == 0) { if (c != 0) return rfail(4, i, "N = 0 but a rounded load is positive"); }
      else if (nn < 1 || e < 0 || e > nn - 1) return rfail(4, i, "e_j out of range");
      int sj = CI(N, e, (int)a, (int)b); if (sj < 0) return rfail(4, i, "no such copy state");
      idx += (long long)sj * pw[N][j]; pay += (long long)w[j] * (long long)c;
    }
    u64 Tv = v[ntok - 1];
    if ((u64)pay > Tv) return rfail(5, i, "payoff above the potential");
    if (Tv > 65535) return rfail(1, i, "potential above 65535 (not supported by this self-test)");
    if (i == 0) { if (N != 0 || h != 0) return rfail(2, 0, "state 0 is not the root"); if ((long long)Tv > T0) return rfail(2, 0, "root potential above T0"); }
    if (!hins((u64)GX(h, N, idx), (val_t)Tv)) return rfail(3, i, "two states with the same key");
    key[(size_t)i] = ePack(h, N, idx); pot[(size_t)i] = (val_t)Tv;
  }
  if (nextLine(f, tk)) return rfail(1, n, "more state lines than n");
  fclose(f);
  double tr = omp_get_wtime();
  long long movesN = 0, idleN = 0, firstBad = LLONG_MAX; const char *whyBad = "";
  vector<vector<Mv> > mvT((size_t)omp_get_max_threads());
  #pragma omp parallel for schedule(dynamic, 256) reduction(+ : movesN, idleN)
  for (long long i = 0; i < n; i++) {
    const char *why = verifyX(key[(size_t)i], pot[(size_t)i], mvT[omp_get_thread_num()], movesN, idleN);
    if (why) {
      #pragma omp critical
      { if (i < firstBad) { firstBad = i; whyBad = why; } }
    }
  }
  if (firstBad != LLONG_MAX) return rfail(6, firstBad, whyBad);
  printf("REREAD PASS k %d r %d weights %s T0 %lld states %lld moves %lld (idle %lld) bound %lld/%d, file %s (read %.0fs, moves %.0fs)\n",
         k, r, wname, T0, n, movesN, idleN, T0, Wsum * F, fn, tr - t0, omp_get_wtime() - tr);
  fflush(stdout);
  return 0;
}

int main(int argc, char **argv) {
  bool rereadMode = (argc >= 3 && !strcmp(argv[1], "reread"));
  double maxgb = 8; int docheck = 0; long long nsim = 0; int exd = 0, exm = 0; const char *certFile = NULL; long long chunk = 8192;
  FILE *rf = NULL; long long hT0 = 0, hn = 0; const char *wArg = NULL;
  if (rereadMode) {
    rf = fopen(argv[2], "r"); if (!rf) { printf("REREAD FAIL: cannot open %s\n", argv[2]); return 1; }
    if (readHeader(rf, hT0, hn)) return 1;
  } else {
    if (argc < 4) { fprintf(stderr, "usage: rg3 k r w1,..,wK [cert=FILE] [chunk=S] [check=0|1] [maxgb=G] [sim=n] [exh=d,m]\n       rg3 reread FILE\n"); return 1; }
    k = atoi(argv[1]); r = atoi(argv[2]); K = 0; Wsum = 0; wArg = argv[3];
    { char *q = strdup(argv[3]); for (char *tok = strtok(q, ","); tok; tok = strtok(NULL, ",")) { if (K == 3) { fprintf(stderr, "K<=3\n"); return 1; } w[K++] = atoi(tok); Wsum += w[K - 1]; } }
    for (int i = 4; i < argc; i++) {
      if (!strncmp(argv[i], "maxgb=", 6)) maxgb = atof(argv[i] + 6);
      else if (!strncmp(argv[i], "check=", 6)) docheck = atoi(argv[i] + 6);
      else if (!strncmp(argv[i], "sim=", 4)) nsim = atoll(argv[i] + 4);
      else if (!strncmp(argv[i], "exh=", 4)) sscanf(argv[i] + 4, "%d,%d", &exd, &exm);
      else if (!strncmp(argv[i], "cert=", 5)) certFile = argv[i] + 5;
      else if (!strncmp(argv[i], "chunk=", 6)) chunk = atoll(argv[i] + 6);
      else { fprintf(stderr, "unknown option %s\n", argv[i]); return 1; }
    }
    if (k < 2 || r < 1 || K < 1) { fprintf(stderr, "need k >= 2, r >= 1, K >= 1\n"); return 1; }
  }
  char wname[256]; { int L = 0; for (int j = 0; j < K; j++) L += snprintf(wname + L, sizeof wname - L, j ? ",%d" : "%d", w[j]); }
  if (!wArg) wArg = wname;
  F = k * r; NMAX = 3 * F; cap = k - 1; CD = NMAX + 3; table();
  if (cap > 63 || NMAX > 500) { fprintf(stderr, "too large\n"); return 1; }
  double t0 = omp_get_wtime();
  buildProfiles(); int nP = (int)Ptri.size();
  cs.assign(NMAX + 1, vector<CS>()); cidx.assign((size_t)(NMAX + 1) * 3 * CD * CD, -1);
  { CS z; z.q[0] = z.q[1] = z.q[2] = 0; z.e = 0; z.n = 0; CI(0, 0, 0, 0) = 0; cs[0].push_back(z); }
  for (int N = 1; N <= NMAX; N++) for (int e = 0; e <= 2; e++) { int m = N + e;
    for (int u = 0; 3 * u <= m; u++) for (int v = u; u + 2 * v <= m; v++) { int x = m - u - v; int n = (u > 0) + (v > 0) + (x > 0); if (e > n - 1) continue;
      CS c; c.q[0] = u; c.q[1] = v; c.q[2] = x; c.e = e; c.n = n; CI(N, e, u, v) = (int)cs[N].size(); cs[N].push_back(c); } }
  for (int N = 0; N <= NMAX; N++) { pw[N][0] = 1; for (int j = 1; j <= 3; j++) pw[N][j] = pw[N][j - 1] * (long long)cs[N].size(); }

  { Vec z; z.bits = 7; z.lo = 1; z.hi = 4; z.b = 0; vecs[1][0][0].push_back(z); }
  for (int nu = 0; nu < 2; nu++) for (int n = 1; n <= 3; n++) for (int e = 0; e < n; e++) for (int bits = 0; bits < 8; bits++) {
    bool ok = true; int b = 0;
    for (int i = 0; i < 3; i++) { int o = (bits >> i) & 1; bool empty = i < 3 - n; if (empty && !o) ok = false; if (!empty && !o) b++; }
    if (!ok || !LOt[nu][n][e][b]) continue;
    Vec z; z.bits = bits; z.lo = LOt[nu][n][e][b]; z.hi = HIt[nu][n][e][b]; z.b = b; vecs[nu][n][e].push_back(z);
  }
  off.assign((size_t)nP * (NMAX + 1), -1); long long total = 0;
  for (int p = 0; p < nP; p++) for (int N = lowN(p); N <= NMAX; N++) { off[(size_t)p * (NMAX + 1) + N] = total; total += pw[N][K]; }

  buildH(); checkH(); layoutX(total);
  if (Hc.size() >= ((size_t)1 << 18) || pw[NMAX][K] >= (1LL << IB)) { fprintf(stderr, "too large for the packed state\n"); return 1; }
  if (rereadMode) {
    printf("reread %s: k %d r %d K %d weights %s, T0 %lld, n %lld, %zu multisets H (profiles checked directly), threads %d\n", argv[2], k, r, K, wname, hT0, hn, Hc.size(), omp_get_max_threads());
    fflush(stdout);
    return reread(rf, argv[2], hT0, hn, wname, t0);
  }
  printf("k %d r %d K %d weights", k, r, K); for (int j = 0; j < K; j++) printf(" %d", w[j]);
  printf(": %d profiles, %lld states (%.3f GB), threads %d\n", nP, total, total * 2.0 / 1e9, omp_get_max_threads()); fflush(stdout);
  printf("explicit H: %zu multisets (profiles checked directly on each), explicit index %lld states (%.3f GB as a bitset)\n", Hc.size(), TX, TX / 8.0 / 1e9); fflush(stdout);
  if (total * 2.0 / 1e9 > maxgb) { printf("too big\n"); return 7; }
  T = (val_t *)calloc(total, sizeof(val_t)); if (!T) { printf("alloc failed\n"); return 8; }
  vector<vector<int> > byN(NMAX + 1);
  for (int p = 0; p < nP; p++) for (int N = lowN(p); N <= NMAX; N++) byN[N].push_back(p);
  for (int N = NMAX; N >= 0; N--) {
    int nh = (int)byN[N].size();
    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < nh; i++) process(byN[N][i], N);
  }
  int root = T[off[0]];
  printf("RESULT k %d r %d weights %s: T(root) = %d, W*F = %d, value = %.6f (%.0fs)\n", k, r, wArg, root, Wsum * F, (double)root / (Wsum * F), omp_get_wtime() - t0); fflush(stdout);
  rootT = root;
  if (nsim > 0 || exd > 0) {
    if (nsim > 0) simRandom(nsim);
    if (exd > 0) { Sim S; S.D = exd; S.V = 0; S.p = 0; memset(S.L, 0, sizeof S.L); vector<long long> jobs; simExhaust(S, jobs, exm, exd); }
    printf("SIM k %d r %d weights %s: %lld random inputs, exhaustive d=%d m=%d, %lld steps, %lld prefixes, worst prefix cost %.6f (%s), bound %.6f, %lld failures, %s (%.0fs)\n",
           k, r, wArg, nsim, exd, exm, simSteps, simPrefixes, simWorst, simWorstDesc, (double)root / (Wsum * F), simFail, simFail ? "FAIL" : "PASS", omp_get_wtime() - t0);
    fflush(stdout);
  }
  int rc = 0;
  if (docheck) rc = selfCheck(wArg, total, t0);
  if (certFile && rc == 0) rc = bfsCert(certFile, chunk, wname, root, t0);
  return rc;
}
