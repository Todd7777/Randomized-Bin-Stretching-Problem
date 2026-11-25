// rgmcert.cpp: value and CERTM certificate of the rounded lottery game, m = 2..6 bins, K <= 3 copies.
// g++ -O2 -std=c++17 -fopenmp -o rgmcert rgmcert.cpp && ./rgmcert m k r w_1,..,w_K [cap=p/q] [maxgb=G] [cert=FILE]
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <climits>
#include <vector>
#include <map>
#include <unordered_map>
#include <algorithm>
#include <string>
#include <sys/resource.h>
#include <fcntl.h>
#include <unistd.h>
#ifdef _OPENMP
#include <omp.h>
#else
#include <chrono>
static int omp_get_max_threads() { return 1; }
static int omp_get_thread_num() { return 0; }
static double omp_get_wtime() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
#endif
using namespace std;
typedef unsigned long long u64;
typedef uint16_t val_t;

static int m, k, r, F, NMAX, CAPH, K, w[3], Wsum, B, INF;
static const int BITS = 9;
static const u64 QM = (1ULL << BITS) - 1;
static inline int getq(u64 key, int i) { return (int)((key >> (BITS * i)) & QM); }
static u64 packSorted(int *q) { sort(q, q + m); u64 key = 0; for (int i = 0; i < m; i++) key |= (u64)q[i] << (BITS * i); return key; }

static vector<vector<u64> > Ptup; static vector<int> Psum; static vector<vector<int> > Pchild; static map<vector<u64>, int> Pid;
static vector<u64> minimizeT(vector<u64> v) {
  sort(v.begin(), v.end()); v.erase(unique(v.begin(), v.end()), v.end());
  vector<u64> out;
  for (size_t i = 0; i < v.size(); i++) {
    bool dom = false;
    for (size_t j = 0; j < v.size() && !dom; j++) if (j != i) {
      bool le = true; for (int a = 0; a < m && le; a++) if (getq(v[j], a) > getq(v[i], a)) le = false;
      if (le) dom = true;
    }
    if (!dom) out.push_back(v[i]);
  }
  return out;
}
static int getProf(const vector<u64> &t, int sum) {
  map<vector<u64>, int>::iterator it = Pid.find(t);
  if (it != Pid.end()) { if (Psum[it->second] != sum) { fprintf(stderr, "profile sum\n"); exit(2); } return it->second; }
  int id = (int)Ptup.size(); Pid[t] = id; Ptup.push_back(t); Psum.push_back(sum); Pchild.push_back(vector<int>(k, -1));
  return id;
}
static void buildProfiles() {
  getProf(vector<u64>(1, 0ULL), 0);
  for (size_t p = 0; p < Ptup.size(); p++) for (int C = 1; C <= k - 1; C++) {
    vector<u64> nt;
    for (size_t z = 0; z < Ptup[p].size(); z++) {
      int q[8]; for (int i = 0; i < m; i++) q[i] = getq(Ptup[p][z], i);
      for (int i = 0; i < m; i++) if (q[i] + C <= CAPH) { int u[8]; for (int a = 0; a < m; a++) u[a] = q[a]; u[i] += C; nt.push_back(packSorted(u)); }
    }
    if (nt.empty()) continue;
    nt = minimizeT(nt); int sum = Psum[p] + C;
    int c = getProf(nt, sum); Pchild[p][C] = c;
  }
}
static inline int lowN(int p) { return Psum[p] == 0 ? 0 : r * Psum[p] + 1; }

struct CS { u64 key; int e, n, x; };
static vector<vector<CS> > cs;
static vector<unordered_map<u64, int> > cidx;
static vector<vector<int> > cntLE;
static vector<vector<int> > succT;
static void genT(int pos, int minv, int rem, int *q, vector<u64> &out) {
  if (pos == m - 1) { if (rem >= minv) { q[pos] = rem; u64 key = 0; for (int i = 0; i < m; i++) key |= (u64)q[i] << (BITS * i); out.push_back(key); } return; }
  for (int v = minv; v * (m - pos) <= rem; v++) { q[pos] = v; genT(pos + 1, v, rem - v, q, out); }
}
static int XMAX;
static void buildStates() {
  cs.assign(NMAX + 1, vector<CS>()); cidx.assign(NMAX + 1, unordered_map<u64, int>()); cntLE.assign(NMAX + 1, vector<int>());
  XMAX = NMAX + m;
  for (int N = 0; N <= NMAX; N++) {
    vector<CS> v;
    if (N == 0) { CS z; z.key = 0; z.e = 0; z.n = 0; z.x = 0; v.push_back(z); }
    else for (int e = 0; e < m; e++) {
      vector<u64> tl; int q[8]; genT(0, 0, N + e, q, tl);
      for (size_t i = 0; i < tl.size(); i++) {
        int n = 0; for (int a = 0; a < m; a++) if (getq(tl[i], a) > 0) n++;
        if (n < 1 || e > n - 1) continue;
        CS c; c.key = tl[i]; c.e = e; c.n = n; c.x = getq(tl[i], m - 1); v.push_back(c);
      }
    }
    sort(v.begin(), v.end(), [](const CS &a, const CS &b) { return a.x < b.x || (a.x == b.x && a.key < b.key); });
    cs[N] = v;
    cidx[N].reserve(v.size() * 2);
    for (size_t i = 0; i < v.size(); i++) cidx[N][v[i].key] = (int)i;
    cntLE[N].assign(XMAX + 1, 0);
    for (size_t i = 0; i < v.size(); i++) cntLE[N][v[i].x]++;
    for (int x = 1; x <= XMAX; x++) cntLE[N][x] += cntLE[N][x - 1];
  }
  succT.assign(NMAX + 1, vector<int>());
  for (int N = 0; N <= NMAX; N++) {
    int S = (int)cs[N].size(); succT[N].assign((size_t)S * m * (F + 1) * 3, -1);
    for (int s = 0; s < S; s++) for (int i = 0; i < m; i++) for (int d = 0; d <= F; d++) {
      int q[8]; for (int a = 0; a < m; a++) q[a] = getq(cs[N][s].key, a);
      q[i] += d; u64 key = packSorted(q);
      for (int del = -1; del <= 1; del++) {
        int Np = N + d + del; if (Np < 0 || Np > NMAX) continue;
        unordered_map<u64, int>::iterator it = cidx[Np].find(key);
        if (it != cidx[Np].end()) succT[N][(((size_t)s * m + i) * (F + 1) + d) * 3 + (del + 1)] = it->second;
      }
    }
  }
}

struct Cn { long long at, ax, c; bool strict; };
static bool fracLess(long long n1, long long d1, long long n2, long long d2) { return (__int128)n1 * d2 < (__int128)n2 * d1; }
static bool feasible(const vector<Cn> &cons) {
  vector<Cn> P, Q, Z;
  for (size_t i = 0; i < cons.size(); i++) { if (cons[i].ax > 0) P.push_back(cons[i]); else if (cons[i].ax < 0) Q.push_back(cons[i]); else Z.push_back(cons[i]); }
  for (size_t i = 0; i < P.size(); i++) for (size_t j = 0; j < Q.size(); j++) {
    long long p = P[i].ax, q = -Q[j].ax; Cn c; c.at = q * P[i].at + p * Q[j].at; c.ax = 0; c.c = q * P[i].c + p * Q[j].c; c.strict = P[i].strict || Q[j].strict; Z.push_back(c);
  }
  bool hasLo = false, hasHi = false; long long loN = 0, loD = 1, hiN = 0, hiD = 1; bool loS = false, hiS = false;
  for (size_t i = 0; i < Z.size(); i++) {
    long long a = Z[i].at, c = Z[i].c; bool s = Z[i].strict;
    if (a == 0) { if (s ? !(c > 0) : !(c >= 0)) return false; continue; }
    if (a > 0) {
      long long n = -c, d = a;
      if (!hasLo || fracLess(loN, loD, n, d)) { loN = n; loD = d; loS = s; hasLo = true; }
      else if (!fracLess(n, d, loN, loD)) loS = loS || s;
    } else {
      long long n = c, d = -a;
      if (!hasHi || fracLess(n, d, hiN, hiD)) { hiN = n; hiD = d; hiS = s; hasHi = true; }
      else if (!fracLess(hiN, hiD, n, d)) hiS = hiS || s;
    }
  }
  if (!hasLo || !hasHi) return true;
  if (fracLess(loN, loD, hiN, hiD)) return true;
  if (!fracLess(hiN, hiD, loN, loD) && !loS && !hiS) return true;
  return false;
}
static void baseCons(int nu, vector<Cn> &v) {
  v.clear();
  v.push_back(Cn{1, 0, 0, true});
  v.push_back(Cn{-1, 0, 1, true});
  v.push_back(Cn{0, 1, 0, false});
  v.push_back(Cn{0, -1, 1, true});
  if (nu) v.push_back(Cn{1, -1, 0, true}); else v.push_back(Cn{-1, 1, 0, false});
}
static void copyCons(int n, int e, int b, vector<Cn> &v) {
  v.push_back(Cn{-(long long)b, 1, (long long)e, false});
  v.push_back(Cn{(long long)(n - b), -1, (long long)(b - e), true});
}
static int NT; static int tidOf[8][8][9]; static int tN[256], tE[256], tB[256];
static vector<char> okR[2], okP[2], okT[2];
struct Vec { int bits, b, tid; };
static vector<Vec> vecs[2][8][8];
static Vec rootVec;
static void buildM4() {
  NT = 0;
  for (int n = 1; n <= m; n++) for (int e = 0; e < n; e++) for (int b = 0; b <= n; b++) { tidOf[n][e][b] = NT; tN[NT] = n; tE[NT] = e; tB[NT] = b; NT++; }
  vector<Cn> v;
  for (int nu = 0; nu < 2; nu++) {
    okR[nu].assign(NT, 0);
    for (int t = 0; t < NT; t++) { baseCons(nu, v); copyCons(tN[t], tE[t], tB[t], v); okR[nu][t] = feasible(v); }
    if (K >= 2) {
      okP[nu].assign((size_t)NT * NT, 0);
      for (int a = 0; a < NT; a++) for (int b = 0; b < NT; b++) { baseCons(nu, v); copyCons(tN[a], tE[a], tB[a], v); copyCons(tN[b], tE[b], tB[b], v); okP[nu][(size_t)a * NT + b] = feasible(v); }
    }
    if (K >= 3) {
      okT[nu].assign((size_t)NT * NT * NT, 0);
      for (int a = 0; a < NT; a++) for (int b = 0; b < NT; b++) for (int c = 0; c < NT; c++) {
        baseCons(nu, v); copyCons(tN[a], tE[a], tB[a], v); copyCons(tN[b], tE[b], tB[b], v); copyCons(tN[c], tE[c], tB[c], v);
        okT[nu][((size_t)a * NT + b) * NT + c] = feasible(v);
      }
    }
    for (int n = 1; n <= m; n++) for (int e = 0; e < n; e++) {
      vecs[nu][n][e].clear();
      for (int bits = 0; bits < (1 << m); bits++) {
        bool ok = true; int b = 0;
        for (int i = 0; i < m; i++) { int o = (bits >> i) & 1; bool empty = i < m - n; if (empty && !o) ok = false; if (!empty && !o) b++; }
        if (!ok) continue;
        int t = tidOf[n][e][b]; if (!okR[nu][t]) continue;
        Vec z; z.bits = bits; z.b = b; z.tid = t; vecs[nu][n][e].push_back(z);
      }
    }
  }
  rootVec.bits = (1 << m) - 1; rootVec.b = 0; rootVec.tid = -1;
}
static int LOt[2][4][3][4], HIt[2][4][3][4];
static void set_(int nu, int n, int e, int b, int lo, int hi) { LOt[nu][n][e][b] = lo; HIt[nu][n][e][b] = hi; }
static void rg3table() {
  memset(LOt, 0, sizeof LOt); memset(HIt, 0, sizeof HIt);
  for (int nu = 0; nu < 2; nu++) for (int n = 1; n <= 3; n++) for (int e = 0; e < n; e++) {
    int eps = e - nu;
    if (eps == -1) set_(nu, n, e, 0, 1, 4);
    else if (eps == n - 1) set_(nu, n, e, n, 1, 4);
    else if (n == 2 && eps == 0) { set_(nu, n, e, 0, 3, 4); set_(nu, n, e, 1, 1, 4); set_(nu, n, e, 2, 1, 2); }
    else if (n == 3 && eps == 0) { set_(nu, n, e, 0, 2, 4); set_(nu, n, e, 1, 1, 4); set_(nu, n, e, 2, 1, 2); set_(nu, n, e, 3, 1, 1); }
    else if (n == 3 && eps == 1) { set_(nu, n, e, 0, 4, 4); set_(nu, n, e, 1, 3, 4); set_(nu, n, e, 2, 1, 4); set_(nu, n, e, 3, 1, 3); }
  }
}
static int selftestM4() {
  int bad = 0;
  if (m == 3) {
    rg3table();
    for (int nu = 0; nu < 2; nu++) for (int a = 0; a < NT; a++) {
      bool r3 = LOt[nu][tN[a]][tE[a]][tB[a]] != 0; if (r3 != (bool)okR[nu][a]) bad++;
      if (K >= 2) for (int b = 0; b < NT; b++) {
        bool both = LOt[nu][tN[a]][tE[a]][tB[a]] && LOt[nu][tN[b]][tE[b]][tB[b]];
        bool i3 = both && max(LOt[nu][tN[a]][tE[a]][tB[a]], LOt[nu][tN[b]][tE[b]][tB[b]]) <= min(HIt[nu][tN[a]][tE[a]][tB[a]], HIt[nu][tN[b]][tE[b]][tB[b]]);
        if (i3 != (bool)okP[nu][(size_t)a * NT + b]) bad++;
        if (K >= 3) for (int c = 0; c < NT; c++) {
          bool all = both && LOt[nu][tN[c]][tE[c]][tB[c]];
          int lo = max(max(LOt[nu][tN[a]][tE[a]][tB[a]], LOt[nu][tN[b]][tE[b]][tB[b]]), LOt[nu][tN[c]][tE[c]][tB[c]]);
          int hi = min(min(HIt[nu][tN[a]][tE[a]][tB[a]], HIt[nu][tN[b]][tE[b]][tB[b]]), HIt[nu][tN[c]][tE[c]][tB[c]]);
          bool t3 = all && lo <= hi;
          if (t3 != (bool)okT[nu][((size_t)a * NT + b) * NT + c]) bad++;
        }
      }
    }
    printf("selftest (M4) vs rg3 interval table: %d differences\n", bad);
  }
  if (m == 2) {
    for (int nu = 0; nu < 2; nu++) for (int a = 0; a < NT; a++) {
      int n = tN[a], e = tE[a], b = tB[a]; bool exp;
      if (n == 1) exp = (b == 1 - nu); else if (e == 0 && nu == 1) exp = (b == 0); else if (e == 1 && nu == 0) exp = (b == 2); else exp = true;
      if (exp != (bool)okR[nu][a]) bad++;
      if (K >= 2) for (int c = 0; c < NT; c++) {
        int n2 = tN[c], e2 = tE[c], b2 = tB[c]; bool exp2;
        if (n2 == 1) exp2 = (b2 == 1 - nu); else if (e2 == 0 && nu == 1) exp2 = (b2 == 0); else if (e2 == 1 && nu == 0) exp2 = (b2 == 2); else exp2 = true;
        bool pe = exp && exp2;
        if (n == 2 && n2 == 2 && e == nu && e2 == nu && ((b == 2 && b2 == 0) || (b == 0 && b2 == 2))) pe = false;
        if (pe != (bool)okP[nu][(size_t)a * NT + c]) bad++;
      }
    }
    printf("selftest (M4) vs Lemma E.1 (iii),(iv): %d differences\n", bad);
  }
  return bad;
}

static vector<vector<long long> > rowOff;
static vector<long long> blk;
static inline int lim(int N, int rem, int wj) { if (rem < 0) return 0; int xm = rem / wj; if (xm > XMAX) xm = XMAX; return cntLE[N][xm]; }
static void buildLayout() {
  rowOff.assign(NMAX + 1, vector<long long>()); blk.assign(NMAX + 1, 0);
  for (int N = 0; N <= NMAX; N++) {
    int S = (int)cs[N].size();
    if (K == 1) blk[N] = lim(N, B, w[0]);
    else if (K == 2) {
      rowOff[N].assign(S + 1, 0);
      for (int s = 0; s < S; s++) rowOff[N][s + 1] = rowOff[N][s] + lim(N, B - w[0] * cs[N][s].x, w[1]);
      blk[N] = rowOff[N][S];
    } else {
      rowOff[N].assign((size_t)S * S + 1, 0);
      for (int s = 0; s < S; s++) for (int t = 0; t < S; t++) {
        size_t i = (size_t)s * S + t; rowOff[N][i + 1] = rowOff[N][i] + lim(N, B - w[0] * cs[N][s].x - w[1] * cs[N][t].x, w[2]);
      }
      blk[N] = rowOff[N][(size_t)S * S];
    }
  }
}
static inline long long lin(int N, const int *t) {
  if (K == 1) return t[0] < blk[N] ? t[0] : -1;
  int S = (int)cs[N].size();
  if (K == 2) { long long a = rowOff[N][t[0]], b = rowOff[N][t[0] + 1]; return t[1] < b - a ? a + t[1] : -1; }
  size_t i = (size_t)t[0] * S + t[1]; long long a = rowOff[N][i], b = rowOff[N][i + 1]; return t[2] < b - a ? a + t[2] : -1;
}
static vector<long long> off; static val_t *T;

struct Mv { int c, nu, Np, pp; long long base; };
static void moves(int p, int N, vector<Mv> &mv) {
  mv.clear();
  for (int c = 0; c < F; c++) for (int nu = 0; nu < 2; nu++) {
    if (N == 0 && nu == 0) continue;
    int Np = N + c + nu; if (Np > NMAX) continue;
    int C = c / r, pp = p; if (C >= 1) { pp = Pchild[p][C]; if (pp < 0) continue; }
    long long o = off[(size_t)pp * (NMAX + 1) + Np]; if (o < 0) { fprintf(stderr, "missing array\n"); exit(3); }
    Mv x; x.c = c; x.nu = nu; x.Np = Np; x.pp = pp; x.base = o; mv.push_back(x);
  }
}
static long long badSucc = 0;
static int evalState(int N, const int *s, const vector<Mv> &mv) {
  int best = 0; for (int j = 0; j < K; j++) best += w[j] * cs[N][s[j]].x;
  if (best > B) return INF;
  for (size_t mi = 0; mi < mv.size(); mi++) {
    const Mv &M = mv[mi];
    const vector<Vec> *V[3]; int na[3] = {1, 1, 1}; int sc[3][8][2];
    for (int j = 0; j < K; j++) {
      const CS &x = cs[N][s[j]];
      for (int i = 0; i < m; i++) for (int o = 0; o < 2; o++) {
        int d = M.c + o, del = M.nu - o;
        sc[j][i][o] = succT[N][(((size_t)s[j] * m + i) * (F + 1) + d) * 3 + (del + 1)];
      }
      if (N == 0) { V[j] = NULL; na[j] = 1; } else { V[j] = &vecs[M.nu][x.n][x.e]; na[j] = (int)V[j]->size(); }
      if (na[j] == 0) { fprintf(stderr, "no pattern\n"); exit(4); }
    }
    int a[3] = {0, 0, 0};
    while (true) {
      const Vec *pv[3];
      for (int j = 0; j < K; j++) pv[j] = (N == 0) ? &rootVec : &(*V[j])[a[j]];
      bool feas = true, idle = (M.c == 0 && M.nu == 0);
      for (int j = 0; j < K; j++) if (pv[j]->b == 0) idle = false;
      if (N > 0) {
        if (K == 2) feas = okP[M.nu][(size_t)pv[0]->tid * NT + pv[1]->tid];
        else if (K == 3) feas = okT[M.nu][((size_t)pv[0]->tid * NT + pv[1]->tid) * NT + pv[2]->tid];
      }
      if (feas && !idle) {
        int mn = INF; int rr[3] = {0, 0, 0};
        while (true) {
          int t[3]; bool okr = true;
          for (int j = 0; j < K; j++) { int bit = (pv[j]->bits >> rr[j]) & 1; t[j] = sc[j][rr[j]][bit]; if (t[j] < 0) okr = false; }
          if (!okr) {
#pragma omp atomic
            badSucc++;
          } else {
            long long ix = lin(M.Np, t);
            int v = ix < 0 ? INF : (int)T[M.base + ix];
            if (v < mn) { mn = v; if (mn <= best) break; }
          }
          int j = 0; while (j < K) { if (++rr[j] < m) break; rr[j] = 0; j++; }
          if (j == K) break;
        }
        if (mn > best) { best = mn; if (best >= INF) return INF; }
      }
      int j = 0; while (j < K) { if (++a[j] < na[j]) break; a[j] = 0; j++; }
      if (j == K) break;
    }
  }
  return best > B ? INF : best;
}
static void processBlock(int p, int N) {
  vector<Mv> mv; moves(p, N, mv);
  val_t *base = T + off[(size_t)p * (NMAX + 1) + N];
  int S = (int)cs[N].size();
  for (int E = (m - 1) * K; E >= 0; E--) {
    if (K == 1) {
#pragma omp parallel for schedule(dynamic, 64)
      for (long long s0 = 0; s0 < blk[N]; s0++) { int s[3] = {(int)s0, 0, 0}; if (cs[N][s[0]].e == E) base[s0] = (val_t)evalState(N, s, mv); }
    } else if (K == 2) {
#pragma omp parallel for schedule(dynamic, 1)
      for (int s0 = 0; s0 < S; s0++) {
        long long a = rowOff[N][s0], b = rowOff[N][s0 + 1];
        for (long long s1 = 0; s1 < b - a; s1++) { int s[3] = {s0, (int)s1, 0}; if (cs[N][s0].e + cs[N][s[1]].e == E) base[a + s1] = (val_t)evalState(N, s, mv); }
      }
    } else {
#pragma omp parallel for schedule(dynamic, 1)
      for (int s0 = 0; s0 < S; s0++) for (int s1 = 0; s1 < S; s1++) {
        size_t i = (size_t)s0 * S + s1; long long a = rowOff[N][i], b = rowOff[N][i + 1];
        for (long long s2 = 0; s2 < b - a; s2++) { int s[3] = {s0, s1, (int)s2}; if (cs[N][s0].e + cs[N][s1].e + cs[N][s[2]].e == E) base[a + s2] = (val_t)evalState(N, s, mv); }
      }
    }
  }
}
static long long gcdll(long long a, long long b) { while (b) { long long t = a % b; a = b; b = t; } return a; }

static vector<vector<int> > Hc;
static vector<int> HP, HS;
static vector<vector<int> > HC;
static vector<u64> addAll(const vector<u64> &A, int C) {
  vector<u64> out;
  for (size_t z = 0; z < A.size(); z++) {
    int q[8]; for (int i = 0; i < m; i++) q[i] = getq(A[z], i);
    for (int i = 0; i < m; i++) if (q[i] + C <= CAPH) { int u[8]; for (int a = 0; a < m; a++) u[a] = q[a]; u[i] += C; out.push_back(packSorted(u)); }
  }
  sort(out.begin(), out.end()); out.erase(unique(out.begin(), out.end()), out.end());
  return out;
}
static int buildH() {
  map<vector<int>, int> HId; vector<vector<u64> > Hall;
  vector<int> z(k - 1, 0); HId[z] = 0; Hc.push_back(z); HP.push_back(0); HS.push_back(0); HC.push_back(vector<int>(k, -1));
  Hall.push_back(vector<u64>(1, 0ULL));
  for (size_t h = 0; h < Hc.size(); h++) {
    if (minimizeT(Hall[h]) != Ptup[HP[h]] || HS[h] != Psum[HP[h]]) { fprintf(stderr, "profile check fails at multiset %zu\n", h); return 1; }
    for (int C = 1; C <= k - 1; C++) {
      vector<u64> all = addAll(Hall[h], C); int pc = Pchild[HP[h]][C];
      if (all.empty() != (pc < 0)) { fprintf(stderr, "profile check (M3) fails at multiset %zu, class %d\n", h, C); return 1; }
      if (pc < 0) continue;
      vector<int> v = Hc[h]; v[C - 1]++;
      map<vector<int>, int>::iterator it = HId.find(v); int id;
      if (it == HId.end()) {
        id = (int)Hc.size(); HId[v] = id; Hc.push_back(v); HP.push_back(pc); HS.push_back(HS[h] + C); HC.push_back(vector<int>(k, -1));
        Hall.push_back(all);
      } else { id = it->second; if (HP[id] != pc) { fprintf(stderr, "profile check: the profile of H depends on the order of its elements\n"); return 1; } }
      HC[h][C] = id;
    }
    vector<u64>().swap(Hall[h]);
  }
  return 0;
}

static vector<long long> baseP;
static vector<u64> offX;
static u64 TX = 0;
static int layoutX(long long total) {
  int nP = (int)Ptup.size(); baseP.assign(nP + 1, total);
  for (int p = 0; p < nP; p++) baseP[p] = off[(size_t)p * (NMAX + 1) + lowN(p)];
  offX.assign(Hc.size(), 0); TX = 0;
  for (size_t h = 0; h < Hc.size(); h++) {
    offX[h] = TX; u64 sz = (u64)(baseP[HP[h] + 1] - baseP[HP[h]]);
    if (sz > (1ULL << 62) - TX) return 1;
    TX += sz;
  }
  return 0;
}
static inline u64 GX(int h, int N, long long ix) { int p = HP[h]; return offX[h] + (u64)(off[(size_t)p * (NMAX + 1) + N] - baseP[p] + ix); }
static inline void decodeX(u64 g, int &h, int &N, long long &ix, int *s) {
  h = (int)(upper_bound(offX.begin(), offX.end(), g) - offX.begin()) - 1;
  int p = HP[h]; long long loc = (long long)(g - offX[h]) + baseP[p];
  const long long *o = &off[(size_t)p * (NMAX + 1)];
  int lo = lowN(p), hi = NMAX;
  while (lo < hi) { int mid = (lo + hi + 1) / 2; if (o[mid] <= loc) lo = mid; else hi = mid - 1; }
  N = lo; ix = loc - o[N];
  if (K == 1) { s[0] = (int)ix; return; }
  const vector<long long> &R = rowOff[N];
  size_t i = (size_t)(upper_bound(R.begin(), R.end(), ix) - R.begin()) - 1;
  if (K == 2) { s[0] = (int)i; s[1] = (int)(ix - R[i]); }
  else { size_t S = cs[N].size(); s[0] = (int)(i / S); s[1] = (int)(i % S); s[2] = (int)(ix - R[i]); }
}

struct Queue {
  static const u64 QB = 1u << 20;
  vector<vector<u64> > qblk; vector<u64> wb; int fd = -1; u64 n = 0, fl = 0; string path;
  double memBytes() const { return (double)qblk.size() * QB * 8; }
  bool openFile(const char *pth) { path = pth; fd = ::open(pth, O_RDWR | O_CREAT | O_TRUNC, 0644); return fd >= 0; }
  bool flush() {
    const char *b = (const char *)wb.data(); size_t L = wb.size() * 8; off_t o = (off_t)(fl * 8);
    while (L) { ssize_t got = pwrite(fd, b, L, o); if (got <= 0) return false; b += got; L -= (size_t)got; o += got; }
    fl += wb.size(); wb.clear(); return true;
  }
  bool push(u64 x) {
    n++;
    if (fd < 0) { if (qblk.empty() || qblk.back().size() == QB) { qblk.push_back(vector<u64>()); qblk.back().reserve(QB); } qblk.back().push_back(x); return true; }
    wb.push_back(x); return wb.size() < (1u << 20) || flush();
  }
  bool read(u64 from, u64 cnt, u64 *dst) {
    if (fd < 0) {
      for (u64 i = 0; i < cnt;) { u64 b = (from + i) / QB, o = (from + i) % QB, L = min(cnt - i, QB - o); memcpy(dst + i, qblk[b].data() + o, (size_t)L * 8); i += L; }
      return true;
    }
    if (from + cnt > fl && !flush()) return false;
    char *b = (char *)dst; size_t L = (size_t)cnt * 8; off_t o = (off_t)(from * 8);
    while (L) { ssize_t got = pread(fd, b, L, o); if (got <= 0) return false; b += got; L -= (size_t)got; o += got; }
    return true;
  }
  void closeFile() { if (fd >= 0) { ::close(fd); unlink(path.c_str()); fd = -1; } }
};

struct XS { vector<int> val; vector<long long> ix; vector<unsigned> gen; vector<signed char> lst; unsigned cur = 0; };
static void expandX(u64 g, const u64 *vis, vector<u64> &out, vector<Mv> &mv, XS &xs, long long &nonIdle, long long &idleN, long long &badN) {
  int h, N, s[3] = {0, 0, 0}; long long ix; decodeX(g, h, N, ix, s);
  int p = HP[h];
  int Tv = T[off[(size_t)p * (NMAX + 1) + N] + ix];
  int pay = 0, Es = 0;
  for (int j = 0; j < K; j++) {
    const CS &x = cs[N][s[j]]; pay += w[j] * x.x; Es += x.e;
    if (N >= 1 && (x.n < 1 || x.e > x.n - 1)) badN++;
    if (N == 0 && (x.n != 0 || x.e != 0)) badN++;
  }
  if (pay > Tv || Tv > B) badN++;
  if (HS[h] > 0 && N < r * HS[h] + 1) badN++;
  const int D = 2 * m; size_t nU = 1; for (int j = 0; j < K; j++) nU *= (size_t)D;
  if (xs.gen.size() != nU) { xs.val.assign(nU, 0); xs.ix.assign(nU, 0); xs.gen.assign(nU, 0); xs.lst.assign(nU, 0); xs.cur = 0; }
  moves(p, N, mv);
  for (size_t mi = 0; mi < mv.size(); mi++) {
    const Mv &M = mv[mi]; int C = M.c / r, h2 = (C >= 1) ? HC[h][C] : h;
    if (h2 < 0 || HP[h2] != M.pp) { badN++; continue; }
    u64 bx = offX[h2] + (u64)(M.base - baseP[M.pp]);
    const vector<Vec> *V[3] = {NULL, NULL, NULL}; int na[3] = {1, 1, 1}; int sc[3][8][2]; bool okm = true;
    for (int j = 0; j < K; j++) {
      const CS &x = cs[N][s[j]];
      for (int i = 0; i < m; i++) for (int o = 0; o < 2; o++) {
        int d = M.c + o, del = M.nu - o;
        sc[j][i][o] = succT[N][(((size_t)s[j] * m + i) * (F + 1) + d) * 3 + (del + 1)];
      }
      if (N == 0) { V[j] = NULL; na[j] = 1; } else { V[j] = &vecs[M.nu][x.n][x.e]; na[j] = (int)V[j]->size(); }
      if (na[j] == 0) okm = false;
    }
    if (!okm) { badN++; continue; }
    if (++xs.cur == 0) { fill(xs.gen.begin(), xs.gen.end(), 0u); xs.cur = 1; }
    size_t mstart = out.size();
    int a[3] = {0, 0, 0};
    while (true) {
      const Vec *pv[3];
      for (int j = 0; j < K; j++) pv[j] = (N == 0) ? &rootVec : &(*V[j])[a[j]];
      bool feas = true, idle = (M.c == 0 && M.nu == 0);
      for (int j = 0; j < K; j++) if (pv[j]->b == 0) idle = false;
      if (N > 0) {
        if (K == 2) feas = okP[M.nu][(size_t)pv[0]->tid * NT + pv[1]->tid];
        else if (K == 3) feas = okT[M.nu][((size_t)pv[0]->tid * NT + pv[1]->tid) * NT + pv[2]->tid];
      }
      if (feas) {
        if (idle) idleN++;
        else {
          nonIdle++;
          int mn = INT_MAX, nc = 0; int cand[216]; int rr[3] = {0, 0, 0};
          while (true) {
            size_t u = 0, mul = 1; int bit[3] = {0, 0, 0};
            for (int j = 0; j < K; j++) { bit[j] = (pv[j]->bits >> rr[j]) & 1; u += (size_t)(2 * rr[j] + bit[j]) * mul; mul *= (size_t)D; }
            if (xs.gen[u] != xs.cur) {
              int t[3] = {0, 0, 0}; bool okr = true; int E2 = 0;
              for (int j = 0; j < K; j++) { t[j] = sc[j][rr[j]][bit[j]]; if (t[j] < 0) okr = false; else E2 += cs[M.Np][t[j]].e; }
              if (!okr) xs.val[u] = -1;
              else {
                if (M.c == 0 && M.nu == 0 && E2 <= Es) badN++;
                long long ix2 = lin(M.Np, t);
                xs.val[u] = ix2 < 0 ? INF : (int)T[M.base + ix2]; xs.ix[u] = ix2;
              }
              xs.lst[u] = -1; xs.gen[u] = xs.cur;
            }
            int v = xs.val[u];
            if (v < 0) badN++;
            else {
              if (v < mn) { mn = v; nc = 0; }
              if (v == mn) { bool dup = false; for (int y = 0; y < nc && !dup; y++) dup = xs.ix[cand[y]] == xs.ix[u]; if (!dup) cand[nc++] = (int)u; }
            }
            int j = 0; while (j < K) { if (++rr[j] < m) break; rr[j] = 0; j++; }
            if (j == K) break;
          }
          if (nc == 0 || mn > Tv) badN++;
          else {
            bool listed = false;
            for (int y = 0; y < nc && !listed; y++) {
              int u = cand[y];
              if (xs.lst[u] < 0) { u64 gg = bx + (u64)xs.ix[u]; xs.lst[u] = (signed char)((vis[gg >> 6] >> (gg & 63)) & 1); }
              listed = xs.lst[u] != 0;
            }
            for (size_t z = mstart; z < out.size() && !listed; z += (size_t)out[z] + 1) {
              bool all = true;
              for (size_t y = 1; y <= (size_t)out[z] && all; y++) {
                bool in = false; for (int q = 0; q < nc && !in; q++) in = (bx + (u64)xs.ix[cand[q]] == out[z + y]);
                all = in;
              }
              listed = all;
            }
            if (!listed) { out.push_back((u64)nc); for (int y = 0; y < nc; y++) out.push_back(bx + (u64)xs.ix[cand[y]]); }
          }
        }
      }
      int j = 0; while (j < K) { if (++a[j] < na[j]) break; a[j] = 0; j++; }
      if (j == K) break;
    }
  }
}

static inline void putu(char *&p, u64 v) { char t[24]; int L = 0; do { t[L++] = (char)('0' + v % 10); v /= 10; } while (v); while (L) *p++ = t[--L]; }
static inline void fmtState(u64 g, char *&p) {
  int h, N, s[3] = {0, 0, 0}; long long ix; decodeX(g, h, N, ix, s);
  putu(p, (u64)N);
  for (int C = 1; C <= k - 1; C++) { *p++ = ' '; putu(p, (u64)Hc[h][C - 1]); }
  for (int j = 0; j < K; j++) { u64 key = cs[N][s[j]].key; for (int i = 0; i < m; i++) { *p++ = ' '; putu(p, (u64)getq(key, i)); } }
  *p++ = ' '; putu(p, (u64)T[off[(size_t)HP[h] * (NMAX + 1) + N] + ix]); *p++ = '\n';
}
static long long writeCertFile(const char *fn, Queue &Q, int root, const char *wname, int hdrRg3, bool &ok) {
  ok = true; FILE *f = fopen(fn, "wb"); if (!f) { ok = false; return 0; }
  char hb[2048]; int L = 0;
  L += snprintf(hb + L, sizeof hb - L, "# CERTM certificate written by rgmcert.cpp, m %d k %d r %d weights %s, bound T0/(W F) = %d/%lld\n",
                m, k, r, wname, root, (long long)Wsum * F);
  if (hdrRg3) L += snprintf(hb + L, sizeof hb - L, "RG3CERT %d %d %d", k, r, K);
  else L += snprintf(hb + L, sizeof hb - L, "CERTM %d %d %d %d", m, k, r, K);
  for (int j = 0; j < K; j++) L += snprintf(hb + L, sizeof hb - L, " %d", w[j]);
  L += snprintf(hb + L, sizeof hb - L, " %d %llu\n", root, (unsigned long long)Q.n);
  long long bytes = L; if (fwrite(hb, 1, (size_t)L, f) != (size_t)L) ok = false;
  int nth = omp_get_max_threads(); const u64 PIECE = 1u << 15;
  const size_t LMAX = 8 * (size_t)(k + m * K + 1) + 8;
  vector<u64> qb((size_t)PIECE * nth); vector<vector<char> > tb((size_t)nth, vector<char>((size_t)PIECE * LMAX)); vector<size_t> tl((size_t)nth, 0);
  for (u64 i0 = 0; i0 < Q.n && ok; i0 += PIECE * (u64)nth) {
    u64 cnt = min(PIECE * (u64)nth, Q.n - i0);
    if (!Q.read(i0, cnt, qb.data())) { ok = false; break; }
#pragma omp parallel for schedule(static, 1)
    for (int t = 0; t < nth; t++) {
      char *p = tb[t].data(); u64 a = (u64)t * PIECE, b = min(cnt, a + PIECE);
      for (u64 i = a; i < b; i++) fmtState(qb[i], p);
      tl[t] = (size_t)(p - tb[t].data());
    }
    for (int t = 0; t < nth; t++) { if (tl[t] && fwrite(tb[t].data(), 1, tl[t], f) != tl[t]) ok = false; bytes += (long long)tl[t]; }
  }
  if (fclose(f) != 0) ok = false;
  return bytes;
}
static double peakRSS() {
  struct rusage ru; getrusage(RUSAGE_SELF, &ru);
#ifdef __APPLE__
  return (double)ru.ru_maxrss;
#else
  return (double)ru.ru_maxrss * 1024.0;
#endif
}

static int bfsCert(const char *fn, const char *qfn, long long chunk, const char *wname, int root, int hdrRg3, long long total, double t0) {
  if (chunk < 1) chunk = 1;
  double tb0 = omp_get_wtime();
  vector<u64> vis((size_t)((TX + 63) / 64), 0);
  Queue Q;
  if (qfn && !Q.openFile(qfn)) { printf("FAIL writer: cannot open the queue file %s\n", qfn); return 14; }
  bool qok = true;
  { u64 g = GX(0, 0, 0); vis[g >> 6] |= 1ULL << (g & 63); qok = Q.push(g) && qok; }
  vector<vector<u64> > rec((size_t)chunk);
  vector<vector<Mv> > mvT((size_t)omp_get_max_threads()); vector<XS> xsT((size_t)omp_get_max_threads());
  vector<u64> cb((size_t)chunk);
  long long nonIdle = 0, idleN = 0, badN = 0; u64 head = 0; double tp = tb0, recPeak = 0;
  while (head < Q.n && qok) {
    long long mc = (long long)min((u64)chunk, Q.n - head);
    if (!Q.read(head, (u64)mc, cb.data())) { qok = false; break; }
    long long a1 = 0, a2 = 0, a3 = 0; const u64 *vp = vis.data(); const u64 *qp = cb.data();
#pragma omp parallel for schedule(dynamic, 8) reduction(+ : a1, a2, a3)
    for (long long i = 0; i < mc; i++) { rec[i].clear(); expandX(qp[i], vp, rec[i], mvT[omp_get_thread_num()], xsT[omp_get_thread_num()], a1, a2, a3); }
    nonIdle += a1; idleN += a2; badN += a3;
    if (badN) break;
    { double rb = 0; for (long long i = 0; i < mc; i++) rb += (double)rec[i].capacity() * 8; if (rb > recPeak) recPeak = rb; }
    for (long long i = 0; i < mc; i++) {
      const vector<u64> &R = rec[i];
      for (size_t z = 0; z < R.size(); z += (size_t)R[z] + 1) {
        size_t nc = (size_t)R[z]; bool listed = false;
        for (size_t y = 1; y <= nc && !listed; y++) { u64 g = R[z + y]; if ((vis[g >> 6] >> (g & 63)) & 1) listed = true; }
        if (!listed) { u64 g = R[z + 1]; vis[g >> 6] |= 1ULL << (g & 63); qok = Q.push(g) && qok; }
      }
      if (rec[i].capacity() > 512) vector<u64>().swap(rec[i]);
    }
    head += (u64)mc;
    if (omp_get_wtime() - tp > 60) { tp = omp_get_wtime(); printf("  search: %llu states done, %llu listed (%.0fs)\n", (unsigned long long)head, (unsigned long long)Q.n, tp - t0); fflush(stdout); }
  }
  double tb1 = omp_get_wtime();
  if (!qok) { Q.closeFile(); printf("FAIL writer: queue file I/O error, no file written\n"); return 14; }
  if (badN) { Q.closeFile(); printf("FAIL writer m %d k %d r %d weights %s: %lld violations of (C4)-(C6) or of the table order, no file written\n", m, k, r, wname, badN); return 12; }
  { unsigned long long cnt = 0; for (size_t i = 0; i < vis.size(); i++) cnt += (unsigned long long)__builtin_popcountll(vis[i]);
    if (cnt != Q.n) { Q.closeFile(); printf("FAIL writer: %llu marked states but %llu listed, no file written\n", cnt, (unsigned long long)Q.n); return 13; } }
  bool ok; long long bytes = writeCertFile(fn, Q, root, wname, hdrRg3, ok);
  double tw = omp_get_wtime();
  Q.closeFile();
  if (!ok) { printf("FAIL writer: could not write %s\n", fn); return 14; }
  long long WF = (long long)Wsum * F; unsigned long long n = (unsigned long long)Q.n;
  printf("CERT m %d k %d r %d weights %s: T0 %d, bound T0/(W F) = %d/%lld = %.6f, %llu states, %lld non-idle moves checked (%lld idle), file %s, %lld bytes (search %.0fs, write %.0fs, total %.0fs)\n",
         m, k, r, wname, root, root, WF, (double)root / WF, n, nonIdle, idleN, fn, bytes, tb1 - tb0, tw - tb1, tw - t0);
  double bvis = (double)vis.size() * 8, bq = Q.memBytes();
  printf("MEM listed set: bitset of %llu bits = %.0f bytes = %.3f bytes per listed state (%.2f%% of the explicit index listed); queue %s %.0f bytes = %.1f per state; records peak %.0f bytes (chunk %lld); table %.0f bytes; peak RSS %.0f bytes; search %.3f us and write %.3f us per listed state, %.1f bytes per line\n",
         (unsigned long long)TX, bvis, bvis / (double)n, 100.0 * (double)n / (double)TX, qfn ? "on disk" : "in memory", qfn ? (double)n * 8 : bq, qfn ? 8.0 : bq / (double)n,
         recPeak, chunk, (double)total * 2, peakRSS(), 1e6 * (tb1 - tb0) / (double)n, 1e6 * (tw - tb1) / (double)n, (double)bytes / (double)n);
  printf("PASS writer m %d k %d r %d weights %s T0 %d states %llu moves %lld bound %d/%lld file %s\n", m, k, r, wname, root, n, nonIdle, root, WF, fn);
  fflush(stdout);
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: rgmcert m k r w1,..,wK [cap=p/q | below=p/q] [maxgb=G] [selftest=1] [cert=FILE] [hdr=certm|rg3] [chunk=S] [qfile=PATH] [dry=1]\n"); return 1; }
  m = atoi(argv[1]); k = atoi(argv[2]); r = atoi(argv[3]); K = 0; Wsum = 0;
  { char *q = strdup(argv[4]);
    for (char *tok = strtok(q, ","); tok; tok = strtok(NULL, ",")) {
      if (K == 3) { fprintf(stderr, "K<=3\n"); return 1; }
      long v = atol(tok); if (v < 1 || v > 1000000) { fprintf(stderr, "weights must be in 1..1000000\n"); return 1; }
      w[K++] = (int)v; Wsum += w[K - 1];
    } }
  long long capP = 0, capQ = 1; double maxgb = 64; int selftest = 0, strictCap = 0, dry = 0, hdrRg3 = 0;
  const char *certFile = NULL, *qFile = NULL; long long chunk = 8192;
  for (int i = 5; i < argc; i++) {
    if (!strncmp(argv[i], "cap=", 4)) { if (sscanf(argv[i] + 4, "%lld/%lld", &capP, &capQ) < 1) { fprintf(stderr, "bad cap\n"); return 1; } }
    else if (!strncmp(argv[i], "below=", 6)) { if (sscanf(argv[i] + 6, "%lld/%lld", &capP, &capQ) < 2) { fprintf(stderr, "bad below\n"); return 1; } strictCap = 1; }
    else if (!strncmp(argv[i], "maxgb=", 6)) maxgb = atof(argv[i] + 6);
    else if (!strncmp(argv[i], "selftest=", 9)) selftest = atoi(argv[i] + 9);
    else if (!strncmp(argv[i], "cert=", 5)) certFile = argv[i] + 5;
    else if (!strncmp(argv[i], "qfile=", 6)) qFile = argv[i] + 6;
    else if (!strncmp(argv[i], "chunk=", 6)) chunk = atoll(argv[i] + 6);
    else if (!strncmp(argv[i], "dry=", 4)) dry = atoi(argv[i] + 4);
    else if (!strcmp(argv[i], "hdr=rg3")) hdrRg3 = 1;
    else if (!strcmp(argv[i], "hdr=certm")) hdrRg3 = 0;
    else { fprintf(stderr, "unknown option %s\n", argv[i]); return 1; }
  }
  if (m < 2 || m > 6 || k < 2 || r < 1 || K < 1) { fprintf(stderr, "need 2<=m<=6, k>=2, r>=1\n"); return 1; }
  if (capP < 0 || capQ < 1) { fprintf(stderr, "cap needs p >= 0 and q >= 1\n"); return 1; }
  if (hdrRg3 && m != 3) { fprintf(stderr, "hdr=rg3 needs m = 3\n"); return 1; }
  F = k * r; NMAX = m * F; CAPH = k - 1;
  if (NMAX + m > (int)QM) { fprintf(stderr, "too large for 9-bit entries\n"); return 1; }
  long long maxPay = (long long)Wsum * (NMAX + m);
  if (capP > 0) {
    __int128 num = (__int128)capP * Wsum * F, b = strictCap ? (num + capQ - 1) / capQ - 1 : num / capQ;
    B = (int)(b > 65000 ? 65000 : b);
  } else B = (int)min(maxPay, 65000LL);
  if (B > 65000) B = 65000;
  INF = B + 1;
  char wname[64]; { int L = 0; for (int j = 0; j < K; j++) L += snprintf(wname + L, sizeof wname - L, j ? ",%d" : "%d", w[j]); }
  double t0 = omp_get_wtime();
  buildProfiles(); int nP = (int)Ptup.size();
  buildStates(); buildM4();
  if (selftest) { int bad = selftestM4(); if (bad) { printf("FAIL selftest: %d differences\n", bad); return 9; } }
  buildLayout();
  off.assign((size_t)nP * (NMAX + 1), -1); long long total = 0, full = 0;
  for (int p = 0; p < nP; p++) for (int N = lowN(p); N <= NMAX; N++) {
    off[(size_t)p * (NMAX + 1) + N] = total; total += blk[N];
    long long S = (long long)cs[N].size(), f = 1; for (int j = 0; j < K; j++) f *= S; full += f;
  }
  long long sumS = 0; for (int N = 0; N <= NMAX; N++) sumS += (long long)cs[N].size();
  printf("m %d k %d r %d F %d K %d weights", m, k, r, F, K); for (int j = 0; j < K; j++) printf(" %d", w[j]);
  printf(": %d profiles, %lld copy states, %d (n,e,b) types, B %d (%s), table %lld states (%.3f GB), uncapped %lld, threads %d\n",
         nP, sumS, NT, B, capP > 0 ? "capped" : "no cap", total, total * 2.0 / 1e9, full, omp_get_max_threads());
  fflush(stdout);
  if (certFile || dry) {
    if (buildH()) { printf("FAIL profile check\n"); return 20; }
    if (layoutX(total)) { printf("FAIL explicit index above 2^62\n"); return 21; }
    printf("explicit H: %zu multisets (profiles checked directly on each), explicit index %llu states (%.3f GB as a bitset)\n",
           Hc.size(), (unsigned long long)TX, (double)TX / 8.0 / 1e9);
    fflush(stdout);
  }
  if (dry) { printf("PASS dry m %d k %d r %d weights %s B %d table %lld explicit %llu\n", m, k, r, wname, B, total, (unsigned long long)TX); return 0; }
  double need = total * 2.0 / 1e9 + (certFile ? (double)TX / 8.0 / 1e9 : 0.0);
  if (need > maxgb) { printf("FAIL too big: %.3f GB needed, maxgb %.1f\n", need, maxgb); return 7; }
  T = (val_t *)calloc((size_t)total, sizeof(val_t)); if (!T) { printf("FAIL alloc failed\n"); return 8; }
  vector<vector<int> > byN(NMAX + 1);
  for (int p = 0; p < nP; p++) for (int N = lowN(p); N <= NMAX; N++) byN[N].push_back(p);
  for (int N = NMAX; N >= 0; N--) for (size_t i = 0; i < byN[N].size(); i++) processBlock(byN[N][i], N);
  int root = T[off[0]];
  long long WF = (long long)Wsum * F;
  if (root >= INF) printf("RESULT m %d k %d r %d weights %s: value > %d/%lld = %.6f (cap), badsucc %lld (%.0fs)\n", m, k, r, argv[4], B, WF, (double)B / WF, badSucc, omp_get_wtime() - t0);
  else { long long g = gcdll(root, WF); printf("RESULT m %d k %d r %d weights %s: T(root) = %d, W*F = %lld, value = %lld/%lld = %.6f, badsucc %lld (%.0fs)\n", m, k, r, argv[4], root, WF, root / g, WF / g, (double)root / WF, badSucc, omp_get_wtime() - t0); }
  fflush(stdout);
  if (badSucc) { printf("FAIL %lld invalid successors in the value computation\n", badSucc); return 10; }
  if (!certFile) {
    if (root >= INF) printf("PASS solver m %d k %d r %d weights %s: value above the cap B/(W F) = %d/%lld, no certificate requested\n", m, k, r, wname, B, WF);
    else printf("PASS solver m %d k %d r %d weights %s T0 %d bound %d/%lld, no certificate requested\n", m, k, r, wname, root, root, WF);
    return 0;
  }
  if (root >= INF) { printf("FAIL writer m %d k %d r %d weights %s: the value is above the cap B/(W F) = %d/%lld, no certificate\n", m, k, r, wname, B, WF); return 11; }
  return bfsCert(certFile, qFile, chunk, wname, root, hdrRg3, total, t0);
}
