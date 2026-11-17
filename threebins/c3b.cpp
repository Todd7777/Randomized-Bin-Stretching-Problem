// c3b.cpp: a second checker for rg3.cpp certificates (paper, App. F), with the format and checks of c3a.cpp.
// It decides each move from the definition of the bits, by Fourier-Motzkin elimination over t, x and the
// fractional parts of all loads, and checks a rational witness for every allowed pattern. 64-bit state numbers.
// g++ -O2 -std=c++17 -fopenmp -o c3b c3b.cpp && ./c3b FILE
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cstdarg>
#include <climits>
#include <string>
#include <vector>
#include <array>
#include <set>
#include <map>
#include <algorithm>
#include <functional>
#include <atomic>
#include <mutex>
#include <memory>
#include <chrono>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <omp.h>
#include <parallel/algorithm>

typedef long long ll;
typedef unsigned long long ull;
typedef __int128 i128;
typedef unsigned __int128 u128;

[[noreturn]] static void internal_error(const char* fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  fflush(stdout);
  fprintf(stdout, "INTERNAL ERROR: ");
  vfprintf(stdout, fmt, ap);
  fprintf(stdout, "\n");
  va_end(ap);
  fflush(stdout);
  fflush(stderr);
  _exit(3);
}
#define ASSERT(c) do { if (!(c)) internal_error("assertion failed at c3b.cpp:%d: %s", __LINE__, #c); } while (0)

static double now_s() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}
static std::string u128s(u128 v) {
  if (v == 0) return "0";
  std::string s;
  while (v) { s += char('0' + (int)(v % 10)); v /= 10; }
  std::reverse(s.begin(), s.end());
  return s;
}
static std::string i128s(i128 v) { return v < 0 ? "-" + u128s((u128)(-v)) : u128s((u128)v); }
static std::string ulls(ull v) { return std::to_string(v); }

static i128 gcd128(i128 a, i128 b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  while (b != 0) { i128 t = a % b; a = b; b = t; }
  return a;
}
struct Q { ll p, q; };
static const ll QLIM = (ll)1 << 50;
static Q mkq(i128 p, i128 q) {
  ASSERT(q != 0);
  if (q < 0) { p = -p; q = -q; }
  i128 g = gcd128(p, q);
  if (g > 1) { p /= g; q /= g; }
  ASSERT(p > -QLIM && p < QLIM && q < QLIM);
  return Q{(ll)p, (ll)q};
}
static Q qi(ll v) { return mkq(v, 1); }
static Q qadd(Q a, Q b) { return mkq((i128)a.p * b.q + (i128)b.p * a.q, (i128)a.q * b.q); }
static Q qsub(Q a, Q b) { return mkq((i128)a.p * b.q - (i128)b.p * a.q, (i128)a.q * b.q); }
static Q qmul(Q a, Q b) { return mkq((i128)a.p * b.p, (i128)a.q * b.q); }
static Q qdiv(Q a, Q b) { ASSERT(b.p != 0); return mkq((i128)a.p * b.q, (i128)a.q * b.p); }
static int qcmp(Q a, Q b) {
  i128 l = (i128)a.p * b.q, r = (i128)b.p * a.q;
  return l < r ? -1 : (l > r ? 1 : 0);
}
static std::string qs(Q a) {
  char buf[64];
  if (a.q == 1) snprintf(buf, sizeof buf, "%lld", a.p);
  else snprintf(buf, sizeof buf, "%lld/%lld", a.p, a.q);
  return buf;
}
static ll qceil(Q a) {
  ll fl = a.p / a.q;
  if (a.p % a.q != 0 && a.p < 0) fl -= 1;
  return (a.p % a.q == 0) ? fl : fl + 1;
}

namespace fm {
const int NV = 5;
const ll LIM = (ll)1 << 40;
struct Cn {
  ll a[NV];
  ll c;
  bool strict;
  Cn() : c(0), strict(false) { for (int i = 0; i < NV; i++) a[i] = 0; }
};
static bool lessc(const Cn& u, const Cn& v) {
  for (int i = 0; i < NV; i++) if (u.a[i] != v.a[i]) return u.a[i] < v.a[i];
  if (u.c != v.c) return u.c < v.c;
  return u.strict < v.strict;
}
static bool eqc(const Cn& u, const Cn& v) {
  for (int i = 0; i < NV; i++) if (u.a[i] != v.a[i]) return false;
  return u.c == v.c && u.strict == v.strict;
}
static ll gcdll(ll a, ll b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  while (b) { ll t = a % b; a = b; b = t; }
  return a;
}

static void normalize(Cn& z) {
  ll g = 0;
  for (int i = 0; i < NV; i++) g = gcdll(g, z.a[i]);
  g = gcdll(g, z.c);
  if (g > 1) {
    for (int i = 0; i < NV; i++) z.a[i] /= g;
    z.c /= g;
  }
}

static bool add(std::vector<Cn>& v, Cn z) {
  for (int i = 0; i < NV; i++) ASSERT(z.a[i] > -LIM && z.a[i] < LIM);
  ASSERT(z.c > -LIM && z.c < LIM);
  normalize(z);
  bool cst = true;
  for (int i = 0; i < NV; i++) if (z.a[i] != 0) cst = false;
  if (cst) return z.strict ? (z.c > 0) : (z.c >= 0);
  v.push_back(z);
  return true;
}
static void dedupe(std::vector<Cn>& v) {
  std::sort(v.begin(), v.end(), lessc);
  v.erase(std::unique(v.begin(), v.end(), eqc), v.end());
}

static bool elim(std::vector<Cn>& v, int k) {
  std::vector<Cn> P, M, out;
  for (const Cn& z : v) {
    if (z.a[k] > 0) P.push_back(z);
    else if (z.a[k] < 0) M.push_back(z);
    else out.push_back(z);
  }
  for (const Cn& p : P)
    for (const Cn& m : M) {
      i128 mp = -(i128)m.a[k], mm = (i128)p.a[k];
      Cn r;
      for (int i = 0; i < NV; i++) {
        i128 s = mp * p.a[i] + mm * m.a[i];
        ASSERT(s > -LIM && s < LIM);
        r.a[i] = (ll)s;
      }
      i128 s = mp * p.c + mm * m.c;
      ASSERT(s > -LIM && s < LIM);
      r.c = (ll)s;
      r.strict = p.strict || m.strict;
      ASSERT(r.a[k] == 0);
      if (!add(out, r)) return false;
    }
  dedupe(out);
  v.swap(out);
  return true;
}
static Cn mk2(ll at, ll ax, ll c, bool strict) {
  Cn z;
  z.a[0] = at;
  z.a[1] = ax;
  z.c = c;
  z.strict = strict;
  return z;
}
}

static inline int nzmask(int n) { return (7 << (3 - n)) & 7; }
static inline int nbit0(int n, int o) { return __builtin_popcount((~o) & nzmask(n) & 7); }
static inline bool empty_ok(int n, int o) { return (o | nzmask(n)) == 7; }

struct CopyProj {
  bool ok = false;
  std::vector<fm::Cn> cons;
};
static CopyProj CPJ[4][3][8];

static void build_copy_proj() {
  for (int n = 1; n <= 3; n++)
    for (int e = 0; e < n; e++)
      for (int o = 0; o < 8; o++) {
        CopyProj& P = CPJ[n][e][o];
        P.cons.clear();
        P.ok = empty_ok(n, o);
        if (!P.ok) continue;
        std::vector<fm::Cn> v;
        for (int s = 0; s < n; s++) {
          int rank = 3 - n + s, var = 2 + s, bit = (o >> rank) & 1;
          fm::Cn z;
          z = fm::Cn(); z.a[var] = 1; z.c = 0; z.strict = false; ASSERT(fm::add(v, z));
          z = fm::Cn(); z.a[var] = -1; z.c = 1; z.strict = true; ASSERT(fm::add(v, z));
          if (bit == 0) { z = fm::Cn(); z.a[var] = 1; z.a[0] = -1; z.strict = false; }
          else { z = fm::Cn(); z.a[0] = 1; z.a[var] = -1; z.strict = true; }
          ASSERT(fm::add(v, z));
        }
        fm::Cn lo, hi;
        for (int s = 0; s < n; s++) { lo.a[2 + s] = 1; hi.a[2 + s] = -1; }
        lo.a[1] = -1; lo.c = -e; lo.strict = false;
        hi.a[1] = 1; hi.c = e; hi.strict = false;
        ASSERT(fm::add(v, lo));
        ASSERT(fm::add(v, hi));
        fm::dedupe(v);
        bool ok = true;
        for (int s = n - 1; s >= 0 && ok; s--) ok = fm::elim(v, 2 + s);
        P.ok = ok;
        if (ok) {
          for (const fm::Cn& z : v) ASSERT(z.a[2] == 0 && z.a[3] == 0 && z.a[4] == 0);
          P.cons = v;
        }
      }
}

static bool m4_fm(int nu, int K, const int* n, const int* e, const int* o) {
  std::vector<fm::Cn> v;
  for (int j = 0; j < K; j++) {
    const CopyProj& P = CPJ[n[j]][e[j]][o[j]];
    if (!P.ok) return false;
    v.insert(v.end(), P.cons.begin(), P.cons.end());
  }
  ASSERT(fm::add(v, fm::mk2(1, 0, 0, true)));
  ASSERT(fm::add(v, fm::mk2(-1, 0, 1, false)));
  ASSERT(fm::add(v, fm::mk2(0, 1, 0, false)));
  ASSERT(fm::add(v, fm::mk2(0, -1, 1, true)));
  if (nu) ASSERT(fm::add(v, fm::mk2(1, -1, 0, true)));
  else ASSERT(fm::add(v, fm::mk2(-1, 1, 0, false)));
  fm::dedupe(v);
  if (!fm::elim(v, 1)) return false;
  if (!fm::elim(v, 0)) return false;
  ASSERT(v.empty());
  return true;
}

struct Witness { Q t, x; Q f[8][3]; };

static bool verify_witness(int nu, int K, const int* n, const int* e, const int* o, const Witness& w) {
  if (!(qcmp(w.t, qi(0)) > 0 && qcmp(w.t, qi(1)) <= 0)) return false;
  if (!(qcmp(w.x, qi(0)) >= 0 && qcmp(w.x, qi(1)) < 0)) return false;
  if ((nu == 1) != (qcmp(w.x, w.t) < 0)) return false;
  for (int j = 0; j < K; j++) {
    Q sum = qi(0);
    for (int r = 0; r < 3; r++) {
      int bit = (o[j] >> r) & 1;
      if (r < 3 - n[j]) { if (bit != 1) return false; continue; }
      Q f = w.f[j][r];
      if (!(qcmp(f, qi(0)) >= 0 && qcmp(f, qi(1)) < 0)) return false;
      if (bit == 0 && !(qcmp(f, w.t) >= 0)) return false;
      if (bit == 1 && !(qcmp(f, w.t) < 0)) return false;
      sum = qadd(sum, f);
    }
    if (qcmp(sum, qadd(qi(e[j]), w.x)) != 0) return false;
  }
  return true;
}

static bool m4_m2(int nu, int K, const int* n, const int* e, const int* o, Witness* wit) {
  int b[8];
  for (int j = 0; j < K; j++) {
    if (!empty_ok(n[j], o[j])) return false;
    b[j] = nbit0(n[j], o[j]);
  }
  struct Ln { ll m, d; };
  std::vector<Ln> L, U;
  L.push_back({0, 0});
  U.push_back({0, 1});
  for (int j = 0; j < K; j++) {
    L.push_back({b[j], -(ll)e[j]});
    U.push_back({(ll)(n[j] - b[j]), (ll)(b[j] - e[j])});
  }
  if (nu == 0) L.push_back({1, 0});
  else U.push_back({1, 0});
  std::vector<Ln> A = L;
  A.insert(A.end(), U.begin(), U.end());
  std::vector<Q> cand = {qi(0), qi(1)};
  for (size_t i = 0; i < A.size(); i++)
    for (size_t j = i + 1; j < A.size(); j++) {
      if (A[i].m == A[j].m) continue;
      Q t = mkq((i128)A[j].d - A[i].d, (i128)A[i].m - A[j].m);
      if (qcmp(t, qi(0)) >= 0 && qcmp(t, qi(1)) <= 0) cand.push_back(t);
    }
  std::sort(cand.begin(), cand.end(), [](Q a, Q b2) { return qcmp(a, b2) < 0; });
  cand.erase(std::unique(cand.begin(), cand.end(), [](Q a, Q b2) { return qcmp(a, b2) == 0; }), cand.end());
  auto at = [](const Ln& l, Q t) { return qadd(qmul(qi(l.m), t), qi(l.d)); };
  auto maxL = [&](Q t) { Q v = at(L[0], t); for (const Ln& l : L) { Q u = at(l, t); if (qcmp(u, v) > 0) v = u; } return v; };
  auto minU = [&](Q t) { Q v = at(U[0], t); for (const Ln& l : U) { Q u = at(l, t); if (qcmp(u, v) < 0) v = u; } return v; };
  auto g = [&](Q t) { return qsub(minU(t), maxL(t)); };
  size_t bi = 0;
  Q bg = g(cand[0]);
  for (size_t i = 1; i < cand.size(); i++) { Q v = g(cand[i]); if (qcmp(v, bg) > 0) { bg = v; bi = i; } }
  if (qcmp(bg, qi(0)) <= 0) return false;
  if (!wit) return true;

  Q tw;
  Q ts = cand[bi];
  if (qcmp(ts, qi(0)) > 0 && qcmp(ts, qi(1)) < 0) tw = ts;
  else {
    ASSERT(cand.size() >= 2);
    Q tn = (bi == 0) ? cand[1] : cand[cand.size() - 2];
    Q g1 = bg, g2 = g(tn);
    if (qcmp(g2, qi(0)) > 0) tw = qdiv(qadd(ts, tn), qi(2));
    else {
      Q lam = qdiv(g1, qmul(qi(2), qsub(g1, g2)));
      tw = qadd(ts, qmul(lam, qsub(tn, ts)));
    }
  }
  ASSERT(qcmp(tw, qi(0)) > 0 && qcmp(tw, qi(1)) < 0);
  ASSERT(qcmp(g(tw), qi(0)) > 0);
  Q xw = maxL(tw);
  wit->t = tw;
  wit->x = xw;
  for (int j = 0; j < K; j++) {
    Q D = qsub(qadd(qi(e[j]), xw), qmul(qi(b[j]), tw));
    Q cap = qadd(qmul(qi(b[j]), qsub(qi(1), tw)), qmul(qi(n[j] - b[j]), tw));
    ASSERT(qcmp(cap, qi(0)) > 0);
    Q lam = qdiv(D, cap);
    ASSERT(qcmp(lam, qi(0)) >= 0 && qcmp(lam, qi(1)) < 0);
    for (int r = 0; r < 3; r++) {
      if (r < 3 - n[j]) { wit->f[j][r] = qi(0); continue; }
      int bit = (o[j] >> r) & 1;
      if (bit == 0) wit->f[j][r] = qadd(tw, qmul(lam, qsub(qi(1), tw)));
      else wit->f[j][r] = qmul(lam, tw);
    }
  }
  if (!verify_witness(nu, K, n, e, o, *wit)) internal_error("witness does not verify");
  return true;
}

struct Iv { int lo, hi; };
static Iv tab32(int n, int eps, int b) {
  static const Iv D = {0, 0};
  if (n == 1) {
    if (eps == -1) return b == 0 ? Iv{1, 4} : D;
    if (eps == 0) return b == 1 ? Iv{1, 4} : D;
  }
  if (n == 2) {
    if (eps == -1) return b == 0 ? Iv{1, 4} : D;
    if (eps == 0) { static const Iv r[3] = {{3, 4}, {1, 4}, {1, 2}}; return r[b]; }
    if (eps == 1) return b == 2 ? Iv{1, 4} : D;
  }
  if (n == 3) {
    if (eps == -1) return b == 0 ? Iv{1, 4} : D;
    if (eps == 0) { static const Iv r[4] = {{2, 4}, {1, 4}, {1, 2}, {1, 1}}; return r[b]; }
    if (eps == 1) { static const Iv r[4] = {{4, 4}, {3, 4}, {1, 4}, {1, 3}}; return r[b]; }
    if (eps == 2) return b == 3 ? Iv{1, 4} : D;
  }
  internal_error("tab32 out of range n=%d eps=%d b=%d", n, eps, b);
}
static bool m4_table(int nu, int K, const int* n, const int* e, const int* o) {
  int lo = 1, hi = 4;
  for (int j = 0; j < K; j++) {
    if (!empty_ok(n[j], o[j])) return false;
    Iv I = tab32(n[j], e[j] - nu, nbit0(n[j], o[j]));
    if (I.lo == 0) return false;
    lo = std::max(lo, I.lo);
    hi = std::min(hi, I.hi);
  }
  return lo <= hi;
}

static std::string config_string(int nu, int K, const int* n, const int* e, const int* o, const Witness& w, bool* realok) {
  const int N = 6;
  std::string s = "N=6 t=" + qs(w.t) + " x=<V>=" + qs(w.x) + " V=" + qs(qsub(qi(N), w.x)) + " job s=c+t (c=0)";
  bool ok = true;
  Q V = qsub(qi(N), w.x);
  Q fracV = qsub(qi(qceil(V)), V);
  if (qceil(V) != N) ok = false;
  if ((qcmp(w.t, fracV) > 0) != (nu == 1)) ok = false;
  for (int j = 0; j < K; j++) {
    int q[3];
    if (n[j] == 1) { q[0] = 0; q[1] = 0; q[2] = N + e[j]; }
    else if (n[j] == 2) { q[0] = 0; q[1] = 3; q[2] = 3 + e[j]; }
    else { q[0] = 2; q[1] = 2; q[2] = 2 + e[j]; }
    s += " | copy" + std::to_string(j + 1) + " q=(" + std::to_string(q[0]) + "," + std::to_string(q[1]) + "," + std::to_string(q[2]) + ")";
    Q sumL = qi(0);
    for (int r = 0; r < 3; r++) {
      Q L = (q[r] == 0) ? qi(0) : qsub(qi(q[r]), w.f[j][r]);
      sumL = qadd(sumL, L);
      if (qceil(L) != q[r]) ok = false;
      Q fr = qsub(qi(qceil(L)), L);
      int realbit = qcmp(w.t, fr) > 0 ? 1 : 0;
      if (realbit != ((o[j] >> r) & 1)) ok = false;
      s += " L" + std::to_string(r + 1) + "=" + qs(L) + "(bit " + std::to_string(realbit) + ")";
    }
    if (qcmp(sumL, V) != 0) ok = false;
  }
  if (realok) *realok = ok;
  return s;
}

static std::string bits3(int o) {
  std::string s;
  for (int r = 0; r < 3; r++) s += char('0' + ((o >> r) & 1));
  return s;
}

static int m4_compare(int Kmax) {
  build_copy_proj();
  struct Ty { int n, e, o; };
  std::vector<Ty> ty;
  for (int n = 1; n <= 3; n++)
    for (int e = 0; e < n; e++)
      for (int o = 0; o < 8; o++) ty.push_back({n, e, o});
  const int NT = (int)ty.size();
  bool all_agree = true;

  const Q smp[2][4][2] = {
      {{mkq(1, 8), mkq(1, 2)}, {mkq(1, 5), mkq(1, 2)}, {mkq(1, 3), mkq(1, 2)}, {mkq(3, 4), mkq(7, 8)}},
      {{mkq(1, 4), mkq(1, 8)}, {mkq(1, 2), mkq(1, 4)}, {mkq(3, 4), mkq(3, 8)}, {mkq(9, 10), mkq(1, 2)}}};
  int rows = 0, rowbad = 0;
  printf("M4COMPARE part 1: (n,e,nu,b) -> cells allowed by the definition (sample points) vs the interval table\n");
  for (int n = 1; n <= 3; n++)
    for (int e = 0; e < n; e++)
      for (int nu = 0; nu < 2; nu++)
        for (int b = 0; b <= n; b++) {
          int cellmask = -1;
          bool inv = true;
          for (int o = 0; o < 8; o++) {
            if (!empty_ok(n, o) || nbit0(n, o) != b) continue;
            int m = 0;
            for (int c = 0; c < 4; c++) {
              Q t = smp[nu][c][0], x = smp[nu][c][1];
              const CopyProj& P = CPJ[n][e][o];
              bool hold = P.ok;
              if (hold)
                for (const fm::Cn& z : P.cons) {
                  i128 v = (i128)z.a[0] * t.p * x.q + (i128)z.a[1] * x.p * t.q + (i128)z.c * t.q * x.q;
                  if (z.strict ? !(v > 0) : !(v >= 0)) { hold = false; break; }
                }
              if (hold) m |= 1 << c;
            }
            if (cellmask == -1) cellmask = m;
            else if (cellmask != m) inv = false;
          }
          ASSERT(cellmask != -1);
          Iv I = tab32(n, e - nu, b);
          int tm = 0;
          if (I.lo) for (int c = I.lo; c <= I.hi; c++) tm |= 1 << (c - 1);
          bool ok = (tm == cellmask) && inv;
          rows++;
          if (!ok) rowbad++;
          std::string dc, tc;
          for (int c = 0; c < 4; c++) if (cellmask >> c & 1) dc += std::to_string(c + 1);
          if (dc.empty()) dc = "-";
          tc = I.lo ? ("[" + std::to_string(I.lo) + "," + std::to_string(I.hi) + "]") : "-";
          printf("  n=%d e=%d nu=%d b=%d eps=%2d  definition cells {%s}  table %s  %s%s\n", n, e, nu, b, e - nu,
                 dc.c_str(), tc.c_str(), ok ? "agree" : "DIFFER", inv ? "" : " (depends on more than b)");
        }
  printf("M4COMPARE part 1: %d rows, %d differences\n", rows, rowbad);
  if (rowbad) all_agree = false;

  std::string example;
  for (int K = 1; K <= Kmax; K++) {
    ll total = 1;
    for (int j = 0; j < K; j++) total *= NT;
    total *= 2;
    std::atomic<ll> nallow(0), ntab(0), d12(0), defonly(0), tabonly(0), realbad(0);
    std::mutex mu;
    std::vector<std::string> msgs;
#pragma omp parallel for schedule(dynamic, 256)
    for (ll idx = 0; idx < total; idx++) {
      ll r = idx;
      int nu = (int)(r % 2);
      r /= 2;
      int n[8], e[8], o[8];
      for (int j = 0; j < K; j++) {
        const Ty& T = ty[r % NT];
        r /= NT;
        n[j] = T.n; e[j] = T.e; o[j] = T.o;
      }
      bool a = m4_fm(nu, K, n, e, o);
      Witness w;
      bool b = m4_m2(nu, K, n, e, o, &w);
      bool c = m4_table(nu, K, n, e, o);
      if (a) nallow++;
      if (c) ntab++;
      bool rok = true;
      std::string cfg;
      if (b) cfg = config_string(nu, K, n, e, o, w, &rok);
      if (b && !rok) realbad++;
      if (a != b) d12++;
      if (a && !c) defonly++;
      if (!a && c) tabonly++;
      if (a != b || a != c || (b && !rok) || (K == 3 && a && c && nu == 0 && e[0] == 0 && n[0] == 3 && o[0] == 0)) {
        std::string s = "nu=" + std::to_string(nu);
        for (int j = 0; j < K; j++)
          s += " copy" + std::to_string(j + 1) + "(n=" + std::to_string(n[j]) + ",e=" + std::to_string(e[j]) + ",o=" + bits3(o[j]) +
               ",b=" + std::to_string(nbit0(n[j], o[j])) + ")";
        s += std::string(" FM=") + (a ? "allowed" : "forbidden") + " M2=" + (b ? "allowed" : "forbidden") + " table=" + (c ? "allowed" : "forbidden");
        if (b) s += "\n      witness: " + cfg + (rok ? "  [real bits match]" : "  [REAL BITS DO NOT MATCH]");
        std::lock_guard<std::mutex> g(mu);
        if (a != b || a != c || !rok) { if (msgs.size() < 40) msgs.push_back(s); }
        else if (example.empty()) example = s;
      }
    }
    printf("M4COMPARE K=%d: %lld patterns (all %d^%d copy types, both nu); allowed by definition (FM) %lld, by the interval table %lld; "
           "FM vs second method: %lld differences; allowed by definition but forbidden by table: %lld; "
           "allowed by table but forbidden by definition: %lld; witnesses with wrong real bits: %lld\n",
           K, total, NT, K, nallow.load(), ntab.load(), d12.load(), defonly.load(), tabonly.load(), realbad.load());
    for (const std::string& s : msgs) printf("  DIFFERENCE %s\n", s.c_str());
    if (d12 || defonly || tabonly || realbad) all_agree = false;
  }
  if (!example.empty()) printf("M4COMPARE example of an allowed pattern with its explicit configuration:\n  %s\n", example.c_str());

  for (int K = 1; K <= std::min(Kmax, 3); K++) {
    const int D = (K <= 2) ? 120 : 24;
    ll total = 2;
    for (int j = 0; j < K; j++) total *= NT;
    std::atomic<ll> gridhit(0), fmonly(0), griderr(0);
    std::mutex mu;
    std::vector<std::string> msgs;
#pragma omp parallel for schedule(dynamic, 16)
    for (ll idx = 0; idx < total; idx++) {
      ll r = idx;
      int nu = (int)(r % 2);
      r /= 2;
      int n[8], e[8], o[8];
      for (int j = 0; j < K; j++) {
        const Ty& T = ty[r % NT];
        r /= NT;
        n[j] = T.n; e[j] = T.e; o[j] = T.o;
      }
      bool a = m4_fm(nu, K, n, e, o);
      bool found = false, possible = true;
      for (int j = 0; j < K; j++) if (!empty_ok(n[j], o[j])) possible = false;
      Witness w;
      for (int ta = 1; ta <= D && possible && !found; ta++)
        for (int xb = 0; xb < D && !found; xb++) {
          w.t = mkq(ta, D);
          w.x = mkq(xb, D);
          bool ok = true;
          for (int j = 0; j < K && ok; j++) {
            int b = nbit0(n[j], o[j]);
            Q Dd = qsub(qadd(qi(e[j]), w.x), qmul(qi(b), w.t));
            Q cap = qadd(qmul(qi(b), qsub(qi(1), w.t)), qmul(qi(n[j] - b), w.t));
            if (qcmp(cap, qi(0)) <= 0) { ok = false; break; }
            Q lam = qdiv(Dd, cap);
            if (qcmp(lam, qi(0)) < 0 || qcmp(lam, qi(1)) >= 0) { ok = false; break; }
            for (int rr = 0; rr < 3; rr++) {
              if (rr < 3 - n[j]) { w.f[j][rr] = qi(0); continue; }
              if (((o[j] >> rr) & 1) == 0) w.f[j][rr] = qadd(w.t, qmul(lam, qsub(qi(1), w.t)));
              else w.f[j][rr] = qmul(lam, w.t);
            }
          }
          if (ok && verify_witness(nu, K, n, e, o, w)) found = true;
        }
      if (found) gridhit++;
      if (found && !a) {
        griderr++;
        std::string s = "nu=" + std::to_string(nu);
        for (int j = 0; j < K; j++) s += " (n=" + std::to_string(n[j]) + ",e=" + std::to_string(e[j]) + ",o=" + bits3(o[j]) + ")";
        s += " t=" + qs(w.t) + " x=" + qs(w.x);
        std::lock_guard<std::mutex> g(mu);
        if (msgs.size() < 20) msgs.push_back(s);
      }
      if (a && !found) fmonly++;
    }
    printf("M4COMPARE brute force K=%d (grid 1/%d): %lld patterns, grid witness found for %lld; "
           "grid witness for an FM-forbidden pattern: %lld; FM-allowed without a grid witness: %lld\n",
           K, D, total, gridhit.load(), griderr.load(), fmonly.load());
    for (const std::string& s : msgs) printf("  FM ERROR (grid witness for a forbidden pattern) %s\n", s.c_str());
    if (griderr) all_agree = false;
  }
  printf("M4COMPARE RESULT: %s\n", all_agree ? "AGREE (definition = interval table everywhere checked)" : "DIFFERENCES FOUND");
  return all_agree ? 0 : 1;
}

struct Hdr {
  ull k = 0, r = 0, K = 0, T0 = 0, n = 0, F = 0, Wsum = 0;
  std::vector<ull> w;
};

static int bitlen(ull v) {
  int b = 0;
  while (v) { b++; v >>= 1; }
  return b < 1 ? 1 : b;
}

struct Layout {
  int k = 0, K = 0, nf = 0, words = 0, totbits = 0, qbits = 0;
  std::vector<int> pos, wid;
  void build(const Hdr& h) {
    k = (int)h.k;
    K = (int)h.K;
    nf = 1 + (k - 1) + 3 * K;
    pos.assign(nf, 0);
    wid.assign(nf, 0);
    std::vector<ull> mx(nf);
    mx[0] = 3 * h.F;
    for (int C = 1; C <= k - 1; C++) mx[C] = (3ULL * (h.k - 1)) / C;
    for (int f = k; f < nf; f++) mx[f] = 3 * h.F + 2;
    for (int f = 0; f < nf; f++) wid[f] = bitlen(mx[f]);
    int p = 0;
    for (int f = nf - 1; f >= 0; f--) { pos[f] = p; p += wid[f]; }
    totbits = p;
    words = (p + 63) / 64;
    qbits = 0;
    for (int f = k; f < nf; f++) qbits += wid[f];
  }
};

template <int W> struct Key { ull w[W]; };
template <int W> static inline bool kless(const Key<W>& a, const Key<W>& b) {
  for (int i = W - 1; i >= 0; i--) if (a.w[i] != b.w[i]) return a.w[i] < b.w[i];
  return false;
}
template <int W> static inline bool keq(const Key<W>& a, const Key<W>& b) {
  for (int i = 0; i < W; i++) if (a.w[i] != b.w[i]) return false;
  return true;
}
template <int W> static inline void kzero(Key<W>& a) { for (int i = 0; i < W; i++) a.w[i] = 0; }
template <int W> static inline void kput(Key<W>& K, int pos, int wid, ull v) {
  int wd = pos >> 6, off = pos & 63;
  K.w[wd] |= v << off;
  if (off + wid > 64) K.w[wd + 1] |= v >> (64 - off);
}
template <int W> static inline ull kget(const Key<W>& K, int pos, int wid) {
  int wd = pos >> 6, off = pos & 63;
  ull v = K.w[wd] >> off;
  if (off + wid > 64) v |= K.w[wd + 1] << (64 - off);
  return v & ((1ULL << wid) - 1);
}
template <int W> static inline Key<W> kgroup(const Key<W>& a, int qbits) {
  Key<W> g = a;
  int full = qbits >> 6, rem = qbits & 63;
  for (int i = 0; i < full && i < W; i++) g.w[i] = 0;
  if (rem && full < W) g.w[full] &= ~((1ULL << rem) - 1);
  return g;
}
template <int W> struct Rec { Key<W> key; ull T; ull id; };

struct Text {
  const char* d = nullptr;
  size_t sz = 0, p = 0;
  ull lineno = 0;

  bool next(const char*& b, const char*& e, bool& nl) {
    while (p < sz) {
      const char* s = d + p;
      const char* q = (const char*)memchr(s, '\n', sz - p);
      size_t len = q ? (size_t)(q - s) : sz - p;
      p += len + (q ? 1 : 0);
      lineno++;
      size_t i = 0;
      while (i < len && (s[i] == ' ' || s[i] == '\t')) i++;
      if (i == len) continue;
      if (s[i] == '#') continue;
      b = s;
      e = s + len;
      nl = (q != nullptr);
      return true;
    }
    return false;
  }
};

static std::string clip(const char* b, const char* e, size_t mx = 24) {
  std::string s(b, e), o;
  if (s.size() > mx) s = s.substr(0, mx) + "...";
  for (unsigned char ch : s) {
    if (ch < 32 || ch > 126) { char buf[8]; snprintf(buf, sizeof buf, "\\x%02x", ch); o += buf; }
    else o += (char)ch;
  }
  return o;
}

static bool parse_nums(const char* b, const char* e, ull* out, int want, std::string& err) {
  int cnt = 0;
  const char* p = b;
  while (true) {
    while (p < e && (*p == ' ' || *p == '\t')) p++;
    if (p >= e) break;
    const char* s = p;
    ull v = 0;
    int nd = 0;
    bool bad = false;
    while (p < e && *p != ' ' && *p != '\t') {
      unsigned ch = (unsigned)(unsigned char)*p - '0';
      if (ch > 9) bad = true;
      else if (nd < 18) v = v * 10 + ch;
      nd++;
      p++;
    }
    if (bad) { err = "token " + std::to_string(cnt + 1) + " '" + clip(s, p) + "' is not a decimal number"; return false; }
    if (nd > 18) { err = "token " + std::to_string(cnt + 1) + " '" + clip(s, p) + "' has more than 18 digits"; return false; }
    if (cnt < want) out[cnt] = v;
    cnt++;
  }
  if (cnt != want) { err = "line has " + std::to_string(cnt) + " tokens, expected " + std::to_string(want); return false; }
  return true;
}

[[noreturn]] static void verdict_fail(int check, long long state, const std::string& why) {
  fflush(stderr);
  printf("FAIL check %d state %lld: %s\n", check, state, why.c_str());
  fflush(stdout);
  _exit(1);
}
[[noreturn]] static void unsupported(const std::string& why) {
  fflush(stderr);
  printf("UNSUPPORTED: %s\n", why.c_str());
  fflush(stdout);
  _exit(2);
}

static bool split3(const std::vector<int>& h, int cap) {
  std::vector<int> items;
  long long tot = 0;
  for (int C = (int)h.size() - 1; C >= 1; C--)
    for (int i = 0; i < h[C]; i++) { items.push_back(C); tot += C; }
  if (tot > 3LL * cap) return false;
  for (int s : items) if (s > cap) return false;
  std::set<std::array<int, 4>> bad;
  std::function<bool(size_t, int, int, int)> go = [&](size_t i, int a, int b, int c) -> bool {
    if (i == items.size()) return true;
    std::array<int, 4> st = {(int)i, a, b, c};
    if (bad.count(st)) return false;
    int s = items[i];
    int ld[3] = {a, b, c};
    for (int t = 0; t < 3; t++) {
      if (t > 0 && ld[t] == ld[t - 1]) continue;
      if (ld[t] + s > cap) continue;
      int nl[3] = {a, b, c};
      nl[t] += s;
      std::sort(nl, nl + 3, std::greater<int>());
      if (go(i + 1, nl[0], nl[1], nl[2])) return true;
    }
    bad.insert(st);
    return false;
  };
  return go(0, 0, 0, 0);
}

static int TYPEIDX[4][3];
static int TN[6], TE[6];

struct JointTable {
  int K = 0;
  ll B6 = 1, P8 = 1;
  std::vector<uint8_t> full;
  std::unique_ptr<std::atomic<uint8_t*>[]> lazy;
  std::mutex mu;
  std::atomic<ll> nallow{0}, ndef_only{0}, ntab_only{0}, ncomputed{0};
  void block(int nu, ll base, uint8_t* out) {
    int n[8], e[8], o[8];
    ll r = base;
    for (int j = 0; j < K; j++) { int t = (int)(r % 6); r /= 6; n[j] = TN[t]; e[j] = TE[t]; }
    for (ll P = 0; P < P8; P++) {
      ll s = P;
      for (int j = 0; j < K; j++) { o[j] = (int)(s & 7); s >>= 3; }
      bool a = m4_fm(nu, K, n, e, o);
      Witness w;
      bool b = m4_m2(nu, K, n, e, o, &w);
      if (a != b) internal_error("(M4) methods disagree: nu=%d base=%lld P=%lld fm=%d m2=%d", nu, base, P, (int)a, (int)b);
      bool c = m4_table(nu, K, n, e, o);
      out[P] = a ? 1 : 0;
      ncomputed++;
      if (a) nallow++;
      if (a && !c) ndef_only++;
      if (!a && c) ntab_only++;
    }
  }
  void init(int K_) {
    K = K_;
    B6 = 1; P8 = 1;
    for (int j = 0; j < K; j++) { B6 *= 6; P8 *= 8; }
    if (K <= 4) {
      full.assign((size_t)(2 * B6 * P8), 0);
#pragma omp parallel for schedule(dynamic, 1)
      for (ll bl = 0; bl < 2 * B6; bl++) block((int)(bl / B6), bl % B6, &full[(size_t)(bl * P8)]);
    } else {
      lazy.reset(new std::atomic<uint8_t*>[2 * B6]);
      for (ll i = 0; i < 2 * B6; i++) lazy[i].store(nullptr);
    }
  }
  const uint8_t* row(int nu, ll base) {
    ll bi = (ll)nu * B6 + base;
    if (K <= 4) return &full[(size_t)(bi * P8)];
    uint8_t* r = lazy[bi].load(std::memory_order_acquire);
    if (r) return r;
    std::lock_guard<std::mutex> g(mu);
    r = lazy[bi].load(std::memory_order_acquire);
    if (r) return r;
    r = new uint8_t[(size_t)P8];
    block(nu, base, r);
    lazy[bi].store(r, std::memory_order_release);
    return r;
  }
};

static const ull NOTFOUND = ~0ULL;

template <int W> static int run(Text& tx, const Hdr& H, const Layout& L) {
  const int k = L.k, K = L.K, nf = L.nf, ntok = nf + 1;
  const ull F = H.F;
  double t0 = now_s();

  std::vector<Rec<W>> recs;
  {
    size_t est = tx.sz / (size_t)(2 * ntok) + 16;
    recs.reserve((size_t)std::min<ull>(H.n, (ull)est));
  }
  struct Oor { std::vector<ull> v; ull id; };
  std::vector<Oor> oor;
  ull first4 = NOTFOUND, first5 = NOTFOUND;
  std::string why4, why5;
  std::vector<ull> rootv;
  std::vector<ull> tok(ntok);
  std::map<std::string, bool> splitcache;
  auto split_h = [&](const ull* hv) -> bool {
    std::string key;
    std::vector<int> h(k, 0);
    for (int C = 1; C <= k - 1; C++) { h[C] = (int)hv[C - 1]; key.push_back((char)h[C]); }
    auto it = splitcache.find(key);
    if (it != splitcache.end()) return it->second;
    bool r = split3(h, k - 1);
    splitcache[key] = r;
    return r;
  };
  auto check4 = [&](const ull* t) -> std::string {
    ull N = t[0];
    if (N > 3 * F) return "N = " + ulls(N) + " exceeds 3F = " + ulls(3 * F);
    u128 S = 0;
    bool any = false;
    for (int C = 1; C <= k - 1; C++) { S += (u128)C * t[C]; if (t[C]) any = true; }
    if (S > (u128)(3 * (k - 1)) || !split_h(t + 1))
      return "H (sum of classes " + u128s(S) + ") does not split into three groups with sums at most k-1 = " + std::to_string(k - 1);
    if (any && (u128)N < (u128)H.r * S + 1)
      return "H is not empty and N = " + ulls(N) + " < r*sum(H)+1 = " + u128s((u128)H.r * S + 1);
    if (N == 0) {
      for (int f = k; f < nf; f++)
        if (t[f] != 0) return "N = 0 but copy " + std::to_string((f - k) / 3 + 1) + " has a nonzero rounded load";
    } else {
      for (int j = 0; j < K; j++) {
        const ull* q = t + k + 3 * j;
        int n = (q[0] > 0) + (q[1] > 0) + (q[2] > 0);
        if (n == 0) return "N >= 1 but copy " + std::to_string(j + 1) + " has no nonempty bin";
        i128 e = (i128)q[0] + q[1] + q[2] - (i128)N;
        if (e < 0 || e > n - 1)
          return "copy " + std::to_string(j + 1) + " has e = " + i128s(e) + " outside [0, n-1] = [0, " + std::to_string(n - 1) + "]";
      }
    }
    return "";
  };
  {
    ull cnt = 0;
    const char *b, *e;
    bool nl;
    while (tx.next(b, e, nl)) {
      if (cnt >= H.n) verdict_fail(1, (long long)cnt, "extra data line (file line " + ulls(tx.lineno) + ") after the " + ulls(H.n) + " state lines");
      if (!nl) verdict_fail(1, (long long)cnt, "the last line does not end with a newline (file truncated?)");
      std::string err;
      if (!parse_nums(b, e, tok.data(), ntok, err)) verdict_fail(1, (long long)cnt, err + " (file line " + ulls(tx.lineno) + ")");
      for (int j = 0; j < K; j++) {
        const ull* q = &tok[k + 3 * j];
        if (q[0] > q[1] || q[1] > q[2])
          verdict_fail(1, (long long)cnt, "triple of copy " + std::to_string(j + 1) + " is not sorted (file line " + ulls(tx.lineno) + ")");
      }
      if (cnt == 0) rootv = tok;
      if (first4 == NOTFOUND) {
        std::string w4 = check4(tok.data());
        if (!w4.empty()) { first4 = cnt; why4 = w4; }
      }
      if (first5 == NOTFOUND) {
        u128 P = 0;
        for (int j = 0; j < K; j++) P += (u128)H.w[j] * tok[k + 3 * j + 2];
        if (P > (u128)tok[nf]) { first5 = cnt; why5 = "payoff sum_j w_j q_{j,3} = " + u128s(P) + " exceeds T = " + ulls(tok[nf]); }
      }
      bool inr = true;
      for (int f = 0; f < nf; f++) if (tok[f] >> L.wid[f]) { inr = false; break; }
      if (inr) {
        Rec<W> rc;
        kzero(rc.key);
        for (int f = 0; f < nf; f++) kput(rc.key, L.pos[f], L.wid[f], tok[f]);
        for (int f = 0; f < nf; f++) ASSERT(kget(rc.key, L.pos[f], L.wid[f]) == tok[f]);
        rc.T = tok[nf];
        rc.id = cnt;
        recs.push_back(rc);
      } else {
        oor.push_back({std::vector<ull>(tok.begin(), tok.begin() + nf), cnt});
      }
      cnt++;
      if (cnt >= (1ULL << 40)) unsupported("more than 2^40 states");
    }
    if (cnt < H.n) verdict_fail(1, (long long)cnt, "the file ends after " + ulls(cnt) + " state lines, the header says n = " + ulls(H.n));
  }
  double t1 = now_s();
  fprintf(stderr, "c3b: read %llu states in %.1f s (key %d bits, %d word(s)); %zu outside the key range\n", (ull)H.n, t1 - t0, L.totbits, W, oor.size());

  for (int f = 0; f < nf; f++)
    if (rootv[f] != 0) verdict_fail(2, 0, "state 0 is not the root (field " + std::to_string(f + 1) + " is " + ulls(rootv[f]) + ", not 0)");
  if (rootv[nf] > H.T0) verdict_fail(2, 0, "the potential of the root T = " + ulls(rootv[nf]) + " exceeds T0 = " + ulls(H.T0));

  __gnu_parallel::sort(recs.begin(), recs.end(), [](const Rec<W>& a, const Rec<W>& b) { return kless(a.key, b.key); });
  {
    ull bestSecond = NOTFOUND, bestFirst = NOTFOUND;
    size_t i = 0;
    while (i < recs.size()) {
      size_t j = i + 1;
      while (j < recs.size() && keq(recs[j].key, recs[i].key)) j++;
      if (j - i >= 2) {
        ull m1 = NOTFOUND, m2 = NOTFOUND;
        for (size_t t = i; t < j; t++) {
          ull id = recs[t].id;
          if (id < m1) { m2 = m1; m1 = id; } else if (id < m2) m2 = id;
        }
        if (m2 < bestSecond) { bestSecond = m2; bestFirst = m1; }
      }
      i = j;
    }
    std::sort(oor.begin(), oor.end(), [](const Oor& a, const Oor& b) { return a.v < b.v || (a.v == b.v && a.id < b.id); });
    for (size_t t = 1; t < oor.size(); t++)
      if (oor[t].v == oor[t - 1].v) {
        size_t s = t - 1;
        while (s > 0 && oor[s - 1].v == oor[t].v) s--;
        ull m1 = oor[s].id, m2 = oor[s + 1].id;
        if (m2 < bestSecond) { bestSecond = m2; bestFirst = m1; }
      }
    if (bestSecond != NOTFOUND) verdict_fail(3, (long long)bestSecond, "same key as state " + ulls(bestFirst));
  }

  if (first4 != NOTFOUND) verdict_fail(4, (long long)first4, why4);
  if (first5 != NOTFOUND) verdict_fail(5, (long long)first5, why5);
  ASSERT(oor.empty());
  double t2 = now_s();
  fprintf(stderr, "c3b: checks 1-5 passed (%.1f s)\n", t2 - t1);

  const size_t n = recs.size();
  std::vector<Key<W>> keys(n);
  std::vector<ull> Ts(n);
  std::vector<ull> ids(n);
#pragma omp parallel for schedule(static)
  for (size_t i = 0; i < n; i++) { keys[i] = recs[i].key; Ts[i] = recs[i].T; ids[i] = recs[i].id; }
  std::vector<Rec<W>>().swap(recs);

  std::vector<Key<W>> gkeys;
  std::vector<size_t> gstart;
  for (size_t i = 0; i < n; i++) {
    Key<W> g = kgroup(keys[i], L.qbits);
    if (i == 0 || !keq(g, gkeys.back())) { gkeys.push_back(g); gstart.push_back(i); }
  }
  gstart.push_back(n);
  const size_t ng = gkeys.size();

  std::vector<ull> gmask(ng, 0);
  {
    std::map<std::vector<int>, ull> mc;
    for (size_t g = 0; g < ng; g++) {
      std::vector<int> h(k, 0);
      for (int C = 1; C <= k - 1; C++) h[C] = (int)kget(gkeys[g], L.pos[C], L.wid[C]);
      auto it = mc.find(h);
      if (it != mc.end()) { gmask[g] = it->second; continue; }
      ull m = 0;
      for (int C = 1; C <= k - 1; C++) {
        std::vector<int> h2 = h;
        h2[C]++;
        if (split3(h2, k - 1)) m |= 1ULL << C;
      }
      mc[h] = m;
      gmask[g] = m;
    }
  }

  static JointTable JT;
  JT.init(K);
  double t3 = now_s();
  if (K <= 4)
    fprintf(stderr, "c3b: (M4) table K=%d: %lld patterns decided by FM, all equal to the second method, %lld allowed; "
            "vs the interval table: %lld allowed only by the definition, %lld allowed only by the table (%.1f s)\n",
            K, JT.ncomputed.load(), JT.nallow.load(), JT.ndef_only.load(), JT.ntab_only.load(), t3 - t2);

  ll P3 = 1, B6 = 1, P8 = 1;
  for (int j = 0; j < K; j++) { P3 *= 3; B6 *= 6; P8 *= 8; }
  const ll M6 = B6;
  std::vector<ll> pw6(K + 1, 1), pw3(K + 1, 1);
  for (int j = 1; j <= K; j++) { pw6[j] = pw6[j - 1] * 6; pw3[j] = pw3[j - 1] * 3; }

  std::vector<uint32_t> RIDX;
  const bool useR = (P8 * P3 <= (1LL << 22));
  auto ridx_calc = [&](ll P, ll rho) -> ll {
    ll mi = 0;
    for (int j = 0; j < K; j++) {
      int i = (int)((rho / pw3[j]) % 3);
      int o = (int)((P >> (3 * j)) & 7);
      mi += (ll)(2 * i + ((o >> i) & 1)) * pw6[j];
    }
    return mi;
  };
  if (useR) {
    RIDX.resize((size_t)(P8 * P3));
    for (ll P = 0; P < P8; P++)
      for (ll rho = 0; rho < P3; rho++) RIDX[(size_t)(P * P3 + rho)] = (uint32_t)ridx_calc(P, rho);
  }

  std::atomic<ull> firstFail(NOTFOUND);
  std::string failWhy;
  std::mutex failMu;
  ull totalMoves = 0, totalLookups = 0;
  const int wq = L.wid[k];
  const ull qlim = 1ULL << wq;

#pragma omp parallel reduction(+ : totalMoves, totalLookups)
  {
    std::vector<ull> memoT((size_t)M6);
    std::vector<uint32_t> memoS((size_t)M6, 0);
    uint32_t stamp = 0;
    std::vector<int> lst[2];
    std::vector<uint8_t> idle(P8);
    std::vector<Key<W>> cf((size_t)K * 6);
    std::vector<uint8_t> cv((size_t)K * 6);
    ull moves = 0, lookups = 0;

#pragma omp for schedule(dynamic, 1024)
    for (size_t p = 0; p < n; p++) {
      if ((ull)ids[p] > firstFail.load(std::memory_order_relaxed)) continue;
      const Key<W>& key = keys[p];
      const ull T = Ts[p];
      const int N = (int)kget(key, L.pos[0], L.wid[0]);
      int h[64];
      for (int C = 1; C <= k - 1; C++) h[C] = (int)kget(key, L.pos[C], L.wid[C]);
      int q[8][3];
      for (int j = 0; j < K; j++)
        for (int i = 0; i < 3; i++) q[j][i] = (int)kget(key, L.pos[k + 3 * j + i], L.wid[k + 3 * j + i]);
      const size_t gi = (size_t)(std::upper_bound(gstart.begin(), gstart.end(), p) - gstart.begin()) - 1;
      const ull hm = gmask[gi];
      int nzm[8];
      ll base = 0;
      if (N >= 1) {
        for (int j = 0; j < K; j++) {
          int nn = (q[j][0] > 0) + (q[j][1] > 0) + (q[j][2] > 0);
          int ee = q[j][0] + q[j][1] + q[j][2] - N;
          ASSERT(nn >= 1 && ee >= 0 && ee <= nn - 1);
          base += (ll)TYPEIDX[nn][ee] * pw6[j];
          nzm[j] = nzmask(nn);
        }
      }
      lst[0].clear();
      lst[1].clear();
      if (N == 0) lst[1].push_back((int)(P8 - 1));
      else
        for (int nu = 0; nu < 2; nu++) {
          const uint8_t* rw = JT.row(nu, base);
          for (ll P = 0; P < P8; P++) if (rw[P]) lst[nu].push_back((int)P);
        }
      if (N >= 1)
        for (ll P = 0; P < P8; P++) {
          bool id = true;
          for (int j = 0; j < K; j++) if (((~(P >> (3 * j))) & nzm[j] & 7) == 0) { id = false; break; }
          idle[(size_t)P] = id;
        }
      bool failed = false;
      std::string why;
      for (int c = 0; c < (int)F && !failed; c++) {
        const int C = c / (int)H.r;
        if (C >= 1 && !((hm >> C) & 1)) continue;
        for (int nu = 0; nu < 2 && !failed; nu++) {
          if (lst[nu].empty()) continue;
          if ((ull)(N + c + nu) > 3 * F) continue;

          Key<W> gk;
          kzero(gk);
          kput(gk, L.pos[0], L.wid[0], (ull)(N + c + nu));
          for (int C2 = 1; C2 <= k - 1; C2++) {
            ull v = (ull)h[C2] + (C2 == C ? 1 : 0);
            ASSERT((v >> L.wid[C2]) == 0);
            kput(gk, L.pos[C2], L.wid[C2], v);
          }
          size_t glo = 0, ghi = 0;
          {
            size_t lo = 0, hi = ng;
            while (lo < hi) { size_t mid = (lo + hi) >> 1; if (kless(gkeys[mid], gk)) lo = mid + 1; else hi = mid; }
            if (lo < ng && keq(gkeys[lo], gk)) { glo = gstart[lo]; ghi = gstart[lo + 1]; }
          }

          for (int j = 0; j < K; j++)
            for (int i = 0; i < 3; i++)
              for (int o = 0; o < 2; o++) {
                int t3[3] = {q[j][0], q[j][1], q[j][2]};
                t3[i] += c + o;
                std::sort(t3, t3 + 3);
                size_t ci = (size_t)(j * 6 + i * 2 + o);
                kzero(cf[ci]);
                cv[ci] = 1;
                for (int r = 0; r < 3; r++) {
                  if ((ull)t3[r] >= qlim) { cv[ci] = 0; break; }
                  int f = k + 3 * j + r;
                  kput(cf[ci], L.pos[f], L.wid[f], (ull)t3[r]);
                }
              }
          if (++stamp == 0) { std::fill(memoS.begin(), memoS.end(), 0); stamp = 1; }
          auto cell = [&](ll mi) -> ull {
            if (memoS[(size_t)mi] == stamp) return memoT[(size_t)mi];
            ull res = NOTFOUND;
            if (ghi > glo) {
              Key<W> sk = gk;
              bool valid = true;
              ll r = mi;
              for (int j = 0; j < K; j++) {
                size_t ci = (size_t)(j * 6 + (int)(r % 6));
                r /= 6;
                if (!cv[ci]) { valid = false; break; }
                for (int w = 0; w < W; w++) sk.w[w] |= cf[ci].w[w];
              }
              if (valid) {
                lookups++;
                size_t lo = glo, hi = ghi;
                while (lo < hi) { size_t mid = (lo + hi) >> 1; if (kless(keys[mid], sk)) lo = mid + 1; else hi = mid; }
                if (lo < ghi && keq(keys[lo], sk)) res = Ts[lo];
              }
            }
            memoS[(size_t)mi] = stamp;
            memoT[(size_t)mi] = res;
            return res;
          };
          for (int P : lst[nu]) {
            if (c == 0 && nu == 0 && idle[(size_t)P]) continue;
            moves++;
            bool ok = false;
            for (int pass = 0; pass < 2 && !ok; pass++)
              for (ll rho = 0; rho < P3; rho++) {
                ll mi = useR ? (ll)RIDX[(size_t)((ll)P * P3 + rho)] : ridx_calc(P, rho);
                if (pass == 0 && memoS[(size_t)mi] != stamp) continue;
                if (cell(mi) <= T) { ok = true; break; }
              }
            if (!ok) {
              int listed = 0;
              ull best = NOTFOUND;
              for (ll rho = 0; rho < P3; rho++) {
                ll mi = useR ? (ll)RIDX[(size_t)((ll)P * P3 + rho)] : ridx_calc(P, rho);
                ull v = cell(mi);
                if (v != NOTFOUND) { listed++; best = std::min(best, v); }
              }
              std::string os;
              for (int j = 0; j < K; j++) { if (j) os += ","; os += bits3((P >> (3 * j)) & 7); }
              std::string st = "N=" + std::to_string(N) + " q=";
              for (int j = 0; j < K; j++) {
                if (j) st += ",";
                st += "(" + std::to_string(q[j][0]) + "," + std::to_string(q[j][1]) + "," + std::to_string(q[j][2]) + ")";
              }
              why = "move c=" + std::to_string(c) + " nu=" + std::to_string(nu) + " o=(" + os + ") at " + st +
                    " T=" + ulls(T) + ": no response leads to a listed state with T' <= T (" + std::to_string(listed) + " of " +
                    std::to_string(P3) + " responses lead to listed states" + (listed ? ", least T' = " + ulls(best) : std::string()) + ")";
              failed = true;
              break;
            }
          }
        }
      }
      if (failed) {
        std::lock_guard<std::mutex> g(failMu);
        if ((ull)ids[p] < firstFail.load()) { firstFail.store(ids[p]); failWhy = why; }
      }
    }
    totalMoves += moves;
    totalLookups += lookups;
  }
  double t4 = now_s();
  fprintf(stderr, "c3b: check 6 on %zu states, %zu groups, %llu non-idle moves, %llu successor lookups, %d threads (%.1f s)\n", n, ng,
          totalMoves, totalLookups, omp_get_max_threads(), t4 - t3);
  if (firstFail.load() != NOTFOUND) verdict_fail(6, (long long)firstFail.load(), failWhy);

  std::string ws;
  for (int j = 0; j < K; j++) { if (j) ws += ","; ws += ulls(H.w[j]); }
  u128 WF = (u128)H.Wsum * H.F;
  printf("PASS k %llu r %llu weights %s T0 %llu states %llu moves %llu bound %llu/%s\n", H.k, H.r, ws.c_str(), H.T0, H.n, totalMoves, H.T0,
         u128s(WF).c_str());
  fflush(stdout);
  return 0;
}

int main(int argc, char** argv) {
  {
    int t = 0;
    for (int n = 1; n <= 3; n++)
      for (int e = 0; e < n; e++) { TYPEIDX[n][e] = t; TN[t] = n; TE[t] = e; t++; }
  }
  if (argc >= 2 && strcmp(argv[1], "--m4-compare") == 0) {
    int Kmax = (argc >= 3) ? atoi(argv[2]) : 3;
    if (Kmax < 1 || Kmax > 5) { fprintf(stderr, "KMAX must be 1..5\n"); return 2; }
    return m4_compare(Kmax);
  }
  if (argc != 2) {
    fprintf(stderr, "usage: c3b CERTFILE | c3b --m4-compare [KMAX]\n");
    return 2;
  }
  build_copy_proj();
  int fd = open(argv[1], O_RDONLY);
  if (fd < 0) { printf("ERROR: cannot open %s\n", argv[1]); return 2; }
  struct stat st;
  if (fstat(fd, &st) != 0) { printf("ERROR: cannot stat %s\n", argv[1]); return 2; }
  Text tx;
  tx.sz = (size_t)st.st_size;
  if (tx.sz > 0) {
    void* m = mmap(nullptr, tx.sz, PROT_READ, MAP_PRIVATE, fd, 0);
    if (m == MAP_FAILED) { printf("ERROR: cannot map %s\n", argv[1]); return 2; }
    madvise(m, tx.sz, MADV_SEQUENTIAL);
    tx.d = (const char*)m;
  }

  Hdr H;
  {
    const char *b, *e;
    bool nl;
    if (!tx.next(b, e, nl)) verdict_fail(1, -1, "no header line");
    if (!nl) verdict_fail(1, -1, "header: the line does not end with a newline");
    std::vector<std::pair<const char*, const char*>> toks;
    const char* p = b;
    while (true) {
      while (p < e && (*p == ' ' || *p == '\t')) p++;
      if (p >= e) break;
      const char* s = p;
      while (p < e && *p != ' ' && *p != '\t') p++;
      toks.push_back({s, p});
    }
    if (toks.empty() || std::string(toks[0].first, toks[0].second) != "RG3CERT")
      verdict_fail(1, -1, "header: the first line is not 'RG3CERT ...'");
    std::vector<ull> v;
    for (size_t i = 1; i < toks.size(); i++) {
      std::string err;
      ull x;
      if (!parse_nums(toks[i].first, toks[i].second, &x, 1, err)) verdict_fail(1, -1, "header: token " + std::to_string(i + 1) + ": " + err);
      v.push_back(x);
    }
    if (v.size() < 3) verdict_fail(1, -1, "header: too few tokens");
    H.k = v[0]; H.r = v[1]; H.K = v[2];
    if (H.K < 1 || H.K > 8) verdict_fail(1, -1, "header: K = " + ulls(H.K) + " is not in 1..8");
    if (v.size() != 3 + H.K + 2) verdict_fail(1, -1, "header: " + std::to_string(toks.size()) + " tokens, expected " + ulls(6 + H.K));
    if (H.k < 2) verdict_fail(1, -1, "header: k = " + ulls(H.k) + " < 2");
    if (H.r < 1) verdict_fail(1, -1, "header: r = 0");
    H.Wsum = 0;
    for (ull j = 0; j < H.K; j++) {
      ull w = v[3 + j];
      if (w < 1) verdict_fail(1, -1, "header: weight w_" + ulls(j + 1) + " = 0");
      H.w.push_back(w);
      H.Wsum += w;
    }
    H.T0 = v[3 + H.K];
    H.n = v[4 + H.K];
    if (H.n < 1) verdict_fail(1, -1, "header: n = 0");
    if (H.k > 64) unsupported("k = " + ulls(H.k) + " > 64");
    if (H.r > 4096 || H.k * H.r > 4096) unsupported("F = k r > 4096");
    H.F = H.k * H.r;
  }
  Layout L;
  L.build(H);
  fprintf(stderr, "c3b: k=%llu r=%llu F=%llu K=%llu W=%llu T0=%llu n=%llu\n", H.k, H.r, H.F, H.K, H.Wsum, H.T0, H.n);
  switch (L.words) {
    case 1: return run<1>(tx, H, L);
    case 2: return run<2>(tx, H, L);
    case 3: return run<3>(tx, H, L);
    case 4: return run<4>(tx, H, L);
    case 5: return run<5>(tx, H, L);
    case 6: return run<6>(tx, H, L);
    case 7: return run<7>(tx, H, L);
    case 8: return run<8>(tx, H, L);
    default: unsupported("state key needs " + std::to_string(L.totbits) + " bits (more than 512)");
  }
}
