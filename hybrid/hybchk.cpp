// hybchk.cpp: checks a hybrid certificate, for m <= 4 bins and K <= 3 copies. Shares no code with the others.
// g++ -O2 -std=c++17 -o hybchk hybchk.cpp && ./hybchk [-profile] [-strict] FILE
// -profile: states are similar when their multisets have the same profile. -strict: (J3) for moves with one common point.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
typedef long long ll;

static const int MAXM = 4, MAXK = 3, MAXC = 32;
static int M = 3, K = 2, KC = 0, R = 0, F = 0, MF = 0;
static ll Wt[MAXK], T0 = 0, Wsum = 0;
static bool STRICT = false, PROFILE = false, COUNTSTRICT = false;

[[noreturn]] static void die(const char* fmt, ...) {
  va_list ap; va_start(ap, fmt); fprintf(stdout, "ERROR: "); vfprintf(stdout, fmt, ap);
  fprintf(stdout, "\n"); va_end(ap); fflush(stdout); exit(2);
}

struct Tri { int n, e, b; };

static bool bp_test(int nu, const Tri* tr, int cnt, int m) {
  for (int d = 1; d <= m; ++d)
    for (int a = 0; a <= d; ++a) {
      ll mu = d;
      if (nu == 1) mu = min(mu, (ll)a);
      ll ml = 0;
      if (nu == 0) ml = max(ml, (ll)a);
      for (int j = 0; j < cnt; ++j) {
        mu = min(mu, (ll)(tr[j].n - tr[j].b) * a + (ll)(tr[j].b - tr[j].e) * d);
        ml = max(ml, (ll)tr[j].b * a - (ll)tr[j].e * d);
      }
      if (mu > ml) return true;
    }
  return false;
}

static bool witness_ok(int nu, const Tri* tr, int cnt, ll tn, ll xn, ll den) {
  if (den <= 0) return false;
  if (!(tn > 0 && tn <= den)) return false;
  if (!(xn >= 0 && xn < den)) return false;
  if (nu != (tn > xn ? 1 : 0)) return false;
  for (int j = 0; j < cnt; ++j) {
    ll n = tr[j].n, e = tr[j].e, b = tr[j].b;
    if (!(b * tn <= e * den + xn)) return false;
    if (!(e * den + xn < b * den + (n - b) * tn)) return false;
    if (b >= 1 && !(tn < den)) return false;
  }
  return true;
}

struct Row { ll a0, a1, a2, rhs; };
static bool lp_test(int nu, const Tri* tr, int cnt, ll* wt, ll* wx, ll* wden) {
  Row rows[32]; int nr = 0;
  rows[nr++] = {-1, 0, 1, 0};
  rows[nr++] = {1, 0, 0, 1};
  rows[nr++] = {0, -1, 0, 0};
  rows[nr++] = {0, 1, 1, 1};
  if (nu == 1) rows[nr++] = {-1, 1, 1, 0};
  else rows[nr++] = {1, -1, 0, 0};
  for (int j = 0; j < cnt; ++j) {
    ll n = tr[j].n, e = tr[j].e, b = tr[j].b;
    rows[nr++] = {b, -1, 0, e};
    rows[nr++] = {-(n - b), 1, 1, b - e};
    if (b >= 1) rows[nr++] = {1, 0, 1, 1};
  }
  rows[nr++] = {0, 0, 1, 1};
  rows[nr++] = {0, 0, -1, 1};
  bool found = false; ll bn = 0, bd = 1, btn = 0, bxn = 0;
  for (int i = 0; i < nr; ++i)
    for (int j = i + 1; j < nr; ++j)
      for (int l = j + 1; l < nr; ++l) {
        const Row &A = rows[i], &B = rows[j], &C = rows[l];
        auto det3 = [](ll a, ll b, ll c, ll d, ll e, ll f, ll g, ll h, ll k) {
          return a * (e * k - f * h) - b * (d * k - f * g) + c * (d * h - e * g);
        };
        ll D = det3(A.a0, A.a1, A.a2, B.a0, B.a1, B.a2, C.a0, C.a1, C.a2);
        if (D == 0) continue;
        ll Dt = det3(A.rhs, A.a1, A.a2, B.rhs, B.a1, B.a2, C.rhs, C.a1, C.a2);
        ll Dx = det3(A.a0, A.rhs, A.a2, B.a0, B.rhs, B.a2, C.a0, C.rhs, C.a2);
        ll De = det3(A.a0, A.a1, A.rhs, B.a0, B.a1, B.rhs, C.a0, C.a1, C.rhs);
        if (D < 0) { D = -D; Dt = -Dt; Dx = -Dx; De = -De; }
        bool ok = true;
        for (int r = 0; r < nr && ok; ++r)
          if (rows[r].a0 * Dt + rows[r].a1 * Dx + rows[r].a2 * De > rows[r].rhs * D) ok = false;
        if (!ok) continue;
        if (!found || De * bd > bn * D) { found = true; bn = De; bd = D; btn = Dt; bxn = Dx; }
      }
  if (!found || bn <= 0) return false;
  *wt = btn; *wx = bxn; *wden = bd;
  return true;
}

static long long g_lp_calls = 0, g_disagree = 0;
static bool decide(int nu, const Tri* tr, int cnt, int m) {
  ll tn, xn, den;
  bool lp = lp_test(nu, tr, cnt, &tn, &xn, &den);
  ++g_lp_calls;
  if (lp && !witness_ok(nu, tr, cnt, tn, xn, den)) die("LP witness fails the definition");
  bool bp = bp_test(nu, tr, cnt, m);
  if (lp != bp) {
    ++g_disagree;
    printf("DISAGREE nu=%d", nu);
    for (int j = 0; j < cnt; ++j) printf(" (n=%d,e=%d,b=%d)", tr[j].n, tr[j].e, tr[j].b);
    printf(" lp=%d bp=%d\n", lp, bp);
  }
  return lp;
}

struct HInfo { vector<int> cnt; int sum; int nel; int prof; };
static vector<HInfo> HU;
static vector<vector<array<int, MAXM>>> HV;
static vector<array<int, MAXC>> ADDC;
static map<vector<int>, int> HIDX;
static int NPROF = 0;

static bool brute_split(vector<int> el, int m, int cap) {
  sort(el.rbegin(), el.rend());
  vector<int> load(m, 0);
  set<pair<size_t, vector<int>>> dead;
  function<bool(size_t)> rec = [&](size_t i) -> bool {
    if (i == el.size()) return true;
    vector<int> key = load; sort(key.begin(), key.end());
    if (dead.count({i, key})) return false;
    for (int b = 0; b < m; ++b) {
      bool seen = false;
      for (int b2 = 0; b2 < b; ++b2) if (load[b2] == load[b]) seen = true;
      if (seen) continue;
      if (load[b] + el[i] <= cap) { load[b] += el[i]; if (rec(i + 1)) return true; load[b] -= el[i]; }
    }
    dead.insert({i, key});
    return false;
  };
  return rec(0);
}

static void build_H() {
  if (KC > MAXC) die("k too large");
  int cap = KC - 1;
  HInfo e0; e0.cnt.assign(KC, 0); e0.sum = 0; e0.nel = 0; e0.prof = -1;
  HU.push_back(e0);
  array<int, MAXM> z{}; HV.push_back({z});
  HIDX[e0.cnt] = 0;
  for (size_t h = 0; h < HU.size(); ++h) {
    array<int, MAXC> ad; ad.fill(-1);
    for (int C = 1; C <= KC - 1; ++C) {
      set<array<int, MAXM>> nv;
      for (auto& v : HV[h])
        for (int i = 0; i < M; ++i)
          if (v[i] + C <= cap) { auto w = v; w[i] += C; sort(w.begin(), w.begin() + M); nv.insert(w); }
      if (nv.empty()) continue;
      vector<int> c2 = HU[h].cnt; c2[C]++;
      auto it = HIDX.find(c2);
      vector<array<int, MAXM>> vv(nv.begin(), nv.end());
      if (it == HIDX.end()) {
        HInfo hi; hi.cnt = c2; hi.sum = HU[h].sum + C; hi.nel = HU[h].nel + 1; hi.prof = -1;
        int id = (int)HU.size(); HU.push_back(hi); HV.push_back(vv); HIDX[c2] = id; ad[C] = id;
      } else {
        if (HV[it->second] != vv) die("packing-vector set depends on the path");
        ad[C] = it->second;
      }
    }
    ADDC.push_back(ad);
  }
  for (size_t h = 0; h < HU.size(); ++h) {
    vector<int> el;
    for (int C = 1; C < KC; ++C) for (int x = 0; x < HU[h].cnt[C]; ++x) el.push_back(C);
    if (!brute_split(el, M, cap)) die("H listed but not splittable");
    for (int C = 1; C < KC; ++C) {
      el.push_back(C);
      bool sp = brute_split(el, M, cap);
      el.pop_back();
      if (sp != (ADDC[h][C] >= 0)) die("splittability mismatch");
    }
  }
  map<vector<array<int, MAXM>>, int> PIDX;
  for (size_t h = 0; h < HU.size(); ++h) {
    vector<array<int, MAXM>> mins;
    for (auto& v : HV[h]) {
      bool minimal = true;
      for (auto& w : HV[h]) {
        if (w == v) continue;
        bool le = true;
        for (int i = 0; i < M; ++i) if (w[i] > v[i]) le = false;
        if (le) { minimal = false; break; }
      }
      if (minimal) mins.push_back(v);
    }
    auto it = PIDX.find(mins);
    if (it == PIDX.end()) { int id = (int)PIDX.size(); PIDX[mins] = id; HU[h].prof = id; }
    else HU[h].prof = it->second;
  }
  NPROF = (int)PIDX.size();
}

static bool FEAS1[2][MAXM + 1][MAXM + 1][MAXM + 1];
static vector<uint8_t> ALLOWED[2][MAXM + 1][MAXM + 1];
static int NTRI = 0, TRIID[MAXM + 1][MAXM + 1][MAXM + 1];
static vector<uint8_t> JOINT;

static void build_rules() {
  int full = (1 << M) - 1;
  for (int nu = 0; nu < 2; ++nu)
    for (int n = 1; n <= M; ++n)
      for (int e = 0; e <= n - 1; ++e)
        for (int b = 0; b <= n; ++b) { Tri t{n, e, b}; FEAS1[nu][n][e][b] = decide(nu, &t, 1, M); }
  for (int nu = 0; nu < 2; ++nu)
    for (int n = 1; n <= M; ++n)
      for (int e = 0; e <= n - 1; ++e)
        for (int mask = 0; mask <= full; ++mask) {
          bool okEmpty = true;
          for (int i = 0; i < M - n; ++i) if (!((mask >> i) & 1)) okEmpty = false;
          if (!okEmpty) continue;
          int b = M - __builtin_popcount(mask);
          if (FEAS1[nu][n][e][b]) ALLOWED[nu][n][e].push_back((uint8_t)mask);
        }
  memset(TRIID, -1, sizeof TRIID);
  for (int n = 1; n <= M; ++n) for (int e = 0; e <= n - 1; ++e) for (int b = 0; b <= n; ++b) TRIID[n][e][b] = NTRI++;
  if (STRICT || COUNTSTRICT) {
    size_t sz = 2; for (int j = 0; j < K; ++j) sz *= NTRI;
    JOINT.assign(sz, 0);
    vector<Tri> all;
    for (int n = 1; n <= M; ++n) for (int e = 0; e <= n - 1; ++e) for (int b = 0; b <= n; ++b) all.push_back({n, e, b});
    for (size_t idx = 0; idx < sz; ++idx) {
      size_t r = idx; Tri tr[MAXK];
      for (int j = K - 1; j >= 0; --j) { tr[j] = all[r % NTRI]; r /= NTRI; }
      int nu = (int)r;
      JOINT[idx] = decide(nu, tr, K, M);
    }
  }
}

static int NHK = 0;
static vector<int32_t> BUCKETOF;
static vector<int16_t*> BUCKETS;
static int BSIZE[512], BRAD[512][MAXM];
static const int16_t UNK = -32768, INPROG = -32767;
static long long g_phi_count = 0;
static int g_depth = 0, g_maxdepth = 0;
static size_t g_bucket_bytes = 0;

static inline int hkey(int h) { return PROFILE ? HU[h].prof : h; }
static void init_buckets() {
  NHK = PROFILE ? NPROF : (int)HU.size();
  BUCKETOF.assign((size_t)NHK * (MF + 1), -1);
  for (int N = 0; N <= MF; ++N) {
    int S = N + M - 1, sz = M;
    for (int i = 0; i <= M - 2; ++i) { BRAD[N][i] = S / (M - i) + 1; sz *= BRAD[N][i]; }
    BSIZE[N] = sz;
  }
}
static inline int16_t* bucket(int h, int N) {
  size_t slot = (size_t)hkey(h) * (MF + 1) + N;
  int32_t b = BUCKETOF[slot];
  if (b < 0) {
    int16_t* p = new int16_t[BSIZE[N]];
    for (int i = 0; i < BSIZE[N]; ++i) p[i] = UNK;
    b = (int32_t)BUCKETS.size(); BUCKETS.push_back(p); BUCKETOF[slot] = b;
    g_bucket_bytes += sizeof(int16_t) * BSIZE[N];
  }
  return BUCKETS[b];
}
static inline int qindex(int N, const int* q) {
  int s = 0; for (int i = 0; i < M; ++i) s += q[i];
  int idx = s - N;
  for (int i = 0; i <= M - 2; ++i) idx = idx * BRAD[N][i] + q[i];
  return idx;
}

static int adm1(int h, int N, const int* q) {
  if (h < 0) return 1;
  if (N < 0 || N > MF) return 2;
  if (HU[h].sum > 0 && N < R * HU[h].sum + 1) return 3;
  for (int i = 0; i < M; ++i) if (q[i] < 0) return 4;
  for (int i = 0; i + 1 < M; ++i) if (q[i] > q[i + 1]) return 5;
  int n = 0, s = 0; for (int i = 0; i < M; ++i) { if (q[i] > 0) ++n; s += q[i]; }
  if (N == 0) { if (s != 0) return 6; return 0; }
  if (n < 1) return 7;
  int e = s - N; if (e < 0 || e > n - 1) return 8;
  return 0;
}

static inline void succ_vec(const int* q, int i, int d, int* out) {
  for (int a = 0; a < M; ++a) out[a] = q[a];
  out[i] += d;
  while (i + 1 < M && out[i] > out[i + 1]) { int t = out[i]; out[i] = out[i + 1]; out[i + 1] = t; ++i; }
}

static int phi(int h, int N, const int* q);
static inline int phi_lookup(int16_t* bk, int h, int N, const int* q) {
  int16_t v = bk[qindex(N, q)];
  if (v >= 0) return v;
  return phi(h, N, q);
}

static int phi(int h, int N, const int* q) {
  int code = adm1(h, N, q);
  if (code) die("Phi asked at a non-admissible one-copy state (code %d)", code);
  int16_t* B = bucket(h, N);
  int idx = qindex(N, q);
  if (B[idx] >= 0) return B[idx];
  if (B[idx] == INPROG) die("cycle in the one-copy recursion");
  B[idx] = INPROG;
  if (++g_depth > g_maxdepth) g_maxdepth = g_depth;
  int val = q[M - 1];
  int full = (1 << M) - 1;
  int n = 0, s = 0; for (int i = 0; i < M; ++i) { if (q[i] > 0) ++n; s += q[i]; }
  int e = s - N;
  for (int c = 0; c < F; ++c)
    for (int nu = 0; nu < 2; ++nu) {
      int Np = N + c + nu;
      if (Np > MF) continue;
      if (N == 0 && nu == 0) continue;
      int C = c / R;
      int hp = C >= 1 ? ADDC[h][C] : h;
      if (hp < 0) continue;
      static const vector<uint8_t> fullonly(1, (uint8_t)((1 << M) - 1));
      const vector<uint8_t>& L = (N == 0) ? fullonly : ALLOWED[nu][n][e];
      if (L.empty()) continue;
      int16_t* bk = bucket(hp, Np);
      int P[MAXM][2]; bool hv[MAXM][2] = {};
      for (uint8_t mask : L) {
        if (c == 0 && nu == 0 && mask != full) continue;
        int mn = 1 << 30;
        for (int i = 0; i < M; ++i) {
          int bit = (mask >> i) & 1;
          if (!hv[i][bit]) {
            if (i > 0 && q[i] == q[i - 1] && hv[i - 1][bit]) P[i][bit] = P[i - 1][bit];
            else { int sv[MAXM]; succ_vec(q, i, c + bit, sv); P[i][bit] = phi_lookup(bk, hp, Np, sv); }
            hv[i][bit] = true;
          }
          if (P[i][bit] < mn) mn = P[i][bit];
        }
        if (mn > val) val = mn;
      }
    }
  if (val > 32000) die("Phi overflow");
  B[idx] = (int16_t)val;
  ++g_phi_count;
  --g_depth;
  return val;
}

struct Key { uint64_t a, b; bool operator==(const Key& o) const { return a == o.a && b == o.b; } };
static inline uint64_t mix(uint64_t x) {
  x += 0x9e3779b97f4a7c15ULL; x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL; return x ^ (x >> 31);
}
struct KeySet {
  vector<Key> t; size_t mask = 0, n = 0;
  static Key empty() { return Key{~0ULL, ~0ULL}; }
  void init(size_t cap) { size_t c = 16; while (c < 2 * cap + 16) c <<= 1; t.assign(c, empty()); mask = c - 1; }
  bool insert(const Key& k) {
    size_t i = mix(k.a ^ mix(k.b)) & mask;
    while (!(t[i] == empty())) { if (t[i] == k) return false; i = (i + 1) & mask; }
    t[i] = k; ++n; return true;
  }
  bool has(const Key& k) const {
    size_t i = mix(k.a ^ mix(k.b)) & mask;
    while (!(t[i] == empty())) { if (t[i] == k) return true; i = (i + 1) & mask; }
    return false;
  }
};
static inline Key make_key(int hk, int N, const int (*qs)[MAXM]) {
  uint8_t by[16]; memset(by, 0, 16);
  by[0] = hk & 255; by[1] = (hk >> 8) & 255; by[2] = (hk >> 16) & 255; by[3] = (uint8_t)N;
  int p = 4;
  for (int j = 0; j < K; ++j) for (int i = 0; i < M; ++i) by[p++] = (uint8_t)qs[j][i];
  Key k; memcpy(&k.a, by, 8); memcpy(&k.b, by + 8, 8); return k;
}
static inline int jkey(int h) { return PROFILE ? HU[h].prof : h; }

struct State { int h, N; int q[MAXK][MAXM]; };
static vector<State> STATES;
static KeySet JSET;

static int parse_H(const vector<int>& el, int lineno) {
  vector<int> c(KC, 0);
  for (int x : el) {
    if (x < 1 || x > KC - 1) die("line %d: coarse class %d out of range 1..k-1", lineno, x);
    c[x]++;
  }
  for (size_t i = 1; i < el.size(); ++i) if (el[i] < el[i - 1]) printf("note: line %d has H unsorted\n", lineno);
  auto it = HIDX.find(c);
  if (it == HIDX.end()) return -1;
  return it->second;
}

static void read_file(const char* fn, bool& hdr_ok, long long& nlisted) {
  FILE* f = fopen(fn, "rb");
  if (!f) die("cannot open %s", fn);
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
  vector<char> buf(sz + 1); if (fread(buf.data(), 1, sz, f) != (size_t)sz) die("read error"); buf[sz] = 0; fclose(f);
  char* p = buf.data(); char* end = p + sz;
  auto nextline = [&](char*& ls, char*& le) -> bool {
    if (p >= end) return false;
    ls = p; while (p < end && *p != '\n') ++p; le = p; if (p < end) ++p; return true;
  };
  char *ls, *le; int lineno = 0;
  if (!nextline(ls, le) || *ls != '#') die("first line must be a comment starting with #");
  ++lineno;
  if (!nextline(ls, le)) die("missing header"); ++lineno;
  string hdr(ls, le);
  char tag[16]; long long n = 0;
  {
    char* hp = (char*)hdr.c_str();
    if (sscanf(hp, "%15s", tag) != 1) die("bad header");
    vector<long long> v; char* q = hp + strlen(tag);
    while (*q) { while (*q == ' ' || *q == '\t' || *q == '\r') ++q; if (!*q) break; v.push_back(strtoll(q, &q, 10)); }
    if (!strcmp(tag, "HYB3")) {
      if (v.size() != 6) die("HYB3 header needs k r w1 w2 T0 n");
      M = 3; K = 2; KC = (int)v[0]; R = (int)v[1]; Wt[0] = v[2]; Wt[1] = v[3]; T0 = v[4]; n = v[5];
    } else if (!strcmp(tag, "HYBG")) {
      if (v.size() < 4) die("bad HYBG header");
      M = (int)v[0]; K = (int)v[1];
      if (M < 2 || M > MAXM || K < 1 || K > MAXK) die("m or K out of range");
      if ((int)v.size() != 4 + K + 2) die("HYBG header needs m K k r w_1..w_K T0 n");
      KC = (int)v[2]; R = (int)v[3]; for (int j = 0; j < K; ++j) Wt[j] = v[4 + j]; T0 = v[4 + K]; n = v[5 + K];
    } else die("unknown header tag %s", tag);
    for (long long x : v) if (x < 0 || x > 2147483647LL) die("header value out of range");
    if (KC > MAXC || R > 255) die("k or r out of range");
    for (int j = 0; j < K; ++j) if (Wt[j] > (1 << 20)) die("weight out of range");
  }
  hdr_ok = true;
  if (KC < 1 || R < 1) die("k, r must be >= 1");
  Wsum = 0; for (int j = 0; j < K; ++j) { if (Wt[j] < 0) die("negative weight"); Wsum += Wt[j]; }
  if (Wsum <= 0) die("W must be positive");
  F = KC * R; MF = M * F;
  if (MF + M - 1 > 255) die("m F too large for the byte keys");
  build_H();
  if (HU.size() >= (1u << 24) - 1) die("too many multisets");
  STATES.reserve(n);
  while (nextline(ls, le)) {
    ++lineno;
    bool blank = true; for (char* c = ls; c < le; ++c) if (*c != ' ' && *c != '\r' && *c != '\t') blank = false;
    if (blank) continue;
    vector<pair<char*, char*>> fields; char* a = ls;
    for (char* c = ls; c <= le; ++c) if (c == le || *c == '|') { fields.push_back({a, c}); a = c + 1; }
    if ((int)fields.size() != 2 + K) die("line %d: expected %d fields", lineno, 2 + K);
    auto ints = [&](pair<char*, char*> fld, bool allowDash, bool& dash) {
      vector<int> v; dash = false; char* c = fld.first;
      while (c < fld.second) {
        if (*c == ' ' || *c == '\t' || *c == '\r') { ++c; continue; }
        if (*c == '-' && allowDash && (c + 1 == fld.second || c[1] == ' ' || c[1] == '\r')) { dash = true; ++c; continue; }
        if (*c < '0' || *c > '9') die("line %d: bad character '%c'", lineno, *c);
        int x = 0, nd = 0; while (c < fld.second && *c >= '0' && *c <= '9') { if (++nd > 9) die("line %d: number too long", lineno); x = x * 10 + (*c - '0'); ++c; }
        v.push_back(x);
      }
      return v;
    };
    bool dash;
    vector<int> Nv = ints(fields[0], false, dash);
    if (Nv.size() != 1) die("line %d: bad N", lineno);
    vector<int> Hv = ints(fields[1], true, dash);
    if (dash && !Hv.empty()) die("line %d: '-' together with classes", lineno);
    if (!dash && Hv.empty()) die("line %d: empty H must be written -", lineno);
    State s; s.N = Nv[0]; s.h = parse_H(Hv, lineno);
    for (int j = 0; j < K; ++j) {
      vector<int> qv = ints(fields[2 + j], false, dash);
      if ((int)qv.size() != M) die("line %d: q_%d needs %d entries", lineno, j + 1, M);
      for (int i = 0; i < M; ++i) { if (qv[i] > 255) die("line %d: entry too large", lineno); s.q[j][i] = qv[i]; }
    }
    if (s.N > 255) die("line %d: N too large", lineno);
    STATES.push_back(s);
  }
  nlisted = (long long)STATES.size();
  if (nlisted != n) printf("note: header says n = %lld but %lld state lines were read\n", n, nlisted);
}

static void fullphi_check() {
  struct S1 { int h, N; array<int, MAXM> q; };
  vector<S1> all;
  for (int h = 0; h < (int)HU.size(); ++h)
    for (int N = 0; N <= MF; ++N) {
      if (HU[h].sum > 0 && N < R * HU[h].sum + 1) continue;
      for (int e = 0; e <= M - 1; ++e) {
        int S = N + e;
        array<int, MAXM> q{};
        function<void(int, int, int)> rec = [&](int i, int lo, int rem) {
          if (i == M - 1) { if (rem >= lo) { q[i] = rem; if (adm1(h, N, q.data()) == 0) all.push_back({h, N, q}); } return; }
          for (int v = lo; v * (M - i) <= rem; ++v) { q[i] = v; rec(i + 1, v, rem - v); }
        };
        rec(0, 0, S);
      }
    }
  auto kap = [&](const S1& s) { int sum = 0; for (int i = 0; i < M; ++i) sum += s.q[i]; return make_pair(s.N, sum - s.N); };
  sort(all.begin(), all.end(), [&](const S1& a, const S1& b) { return kap(a) > kap(b); });
  map<tuple<int, int, array<int, MAXM>>, int> val;
  int full = (1 << M) - 1;
  long long mism = 0;
  for (auto& st : all) {
    const int* q = st.q.data(); int h = st.h, N = st.N;
    int v = q[M - 1];
    int n = 0, s = 0; for (int i = 0; i < M; ++i) { if (q[i] > 0) ++n; s += q[i]; }
    int e = s - N;
    for (int c = 0; c < F; ++c) for (int nu = 0; nu < 2; ++nu) {
      int Np = N + c + nu; if (Np > MF) continue;
      if (N == 0 && nu == 0) continue;
      int C = c / R; int hp = C >= 1 ? ADDC[h][C] : h; if (hp < 0) continue;
      for (int mask = 0; mask <= full; ++mask) {
        if (N == 0) { if (mask != full) continue; }
        else {
          bool okE = true; for (int i = 0; i < M - n; ++i) if (!((mask >> i) & 1)) okE = false;
          if (!okE) continue;
          Tri t{n, e, M - __builtin_popcount(mask)}; ll a, b2, d;
          if (!lp_test(nu, &t, 1, &a, &b2, &d)) continue;
        }
        if (c == 0 && nu == 0 && mask != full) continue;
        int mn = 1 << 30;
        for (int i = 0; i < M; ++i) {
          array<int, MAXM> sv{}; succ_vec(q, i, c + ((mask >> i) & 1), sv.data());
          auto it = val.find(make_tuple(hp, Np, sv));
          if (it == val.end()) die("fullphi: successor not computed earlier (order broken)");
          mn = min(mn, it->second);
        }
        v = max(v, mn);
      }
    }
    val[make_tuple(h, N, st.q)] = v;
    if (phi(h, N, q) != v) ++mism;
  }
  printf("fullphi: %zu admissible one-copy states recomputed bottom-up, %lld mismatches with memo\n", all.size(), mism);
  if (mism) die("fullphi mismatch");
}

static void selftest() {
  for (int m = 2; m <= 4; ++m) {
    long long before = g_disagree;
    vector<Tri> wide, adm;
    for (int n = 0; n <= m; ++n) for (int b = 0; b <= n; ++b) for (int e = -m - 1; e <= m + 1; ++e) wide.push_back({n, e, b});
    for (int n = 1; n <= m; ++n) for (int e = 0; e <= n - 1; ++e) for (int b = 0; b <= n; ++b) adm.push_back({n, e, b});
    long long c1 = 0, a1 = 0;
    for (int nu = 0; nu < 2; ++nu) for (auto& t : wide) { ++c1; a1 += decide(nu, &t, 1, m); }
    long long c2 = 0, a2 = 0;
    vector<Tri> mid;
    for (int n = 0; n <= m; ++n) for (int b = 0; b <= n; ++b) for (int e = -1; e <= m; ++e) mid.push_back({n, e, b});
    for (int nu = 0; nu < 2; ++nu) for (auto& t1 : mid) for (auto& t2 : mid) { Tri tr[2] = {t1, t2}; ++c2; a2 += decide(nu, tr, 2, m); }
    long long c3 = 0, a3 = 0;
    for (int nu = 0; nu < 2; ++nu) for (auto& t1 : adm) for (auto& t2 : adm) for (auto& t3 : adm) { Tri tr[3] = {t1, t2, t3}; ++c3; a3 += decide(nu, tr, 3, m); }
    long long k1 = 0, k2 = 0;
    for (int nu = 0; nu < 2; ++nu) for (auto& t1 : adm) { k1 += bp_test(nu, &t1, 1, m); for (auto& t2 : adm) { Tri tr[2] = {t1, t2}; k2 += bp_test(nu, tr, 2, m); } }
    printf("selftest m=%d: K=1 wide %lld combos (%lld feasible), K=2 %lld (%lld), K=3 admissible %lld (%lld); "
           "admissible ordered allowed: K=1 %lld of %zu, K=2 %lld, K=3 %lld; disagreements %lld\n",
           m, c1, a1, c2, a2, c3, a3, k1, 2 * adm.size(), k2, a3, g_disagree - before);
  }
  printf("selftest: %lld LP decisions, %lld disagreements with Lemma 3.3(iv)\n", g_lp_calls, g_disagree);
}

static map<pair<uint64_t, uint64_t>, int> PSI;
typedef pair<pair<int, int>, array<uint8_t, MAXK>> GMove;
static void gen_moves(const State& s, vector<GMove>& out) {
  out.clear();
  int full = (1 << M) - 1, h = s.h, N = s.N, n[MAXK], e[MAXK];
  for (int j = 0; j < K; ++j) { int nn = 0, ss = 0; for (int i = 0; i < M; ++i) { if (s.q[j][i] > 0) ++nn; ss += s.q[j][i]; } n[j] = nn; e[j] = ss - N; }
  static const vector<uint8_t> fo(1, (uint8_t)((1 << M) - 1));
  for (int c = 0; c < F; ++c)
    for (int nu = 0; nu < 2; ++nu) {
      if (N + c + nu > MF || (N == 0 && nu == 0)) continue;
      int C = c / R; if (C >= 1 && ADDC[h][C] < 0) continue;
      const vector<uint8_t>* L[MAXK]; bool any = true;
      for (int j = 0; j < K; ++j) { L[j] = N == 0 ? &fo : &ALLOWED[nu][n[j]][e[j]]; if (L[j]->empty()) any = false; }
      if (!any) continue;
      int idx[MAXK] = {0, 0, 0};
      while (true) {
        array<uint8_t, MAXK> mk{}; bool allZero = true;
        for (int j = 0; j < K; ++j) { mk[j] = (*L[j])[idx[j]]; if (mk[j] == full) allZero = false; }
        bool ok = !(c == 0 && nu == 0 && allZero);
        if (ok && STRICT && N >= 1) {
          size_t ji = nu;
          for (int j = 0; j < K; ++j) ji = ji * NTRI + TRIID[n[j]][e[j]][M - __builtin_popcount(mk[j])];
          ok = JOINT[ji];
        }
        if (ok) out.push_back({{c, nu}, mk});
        int j = K - 1;
        while (j >= 0 && ++idx[j] == (int)L[j]->size()) { idx[j] = 0; --j; }
        if (j < 0) break;
      }
    }
}
static State gen_succ(const State& s, const GMove& mv, const int* ri) {
  State t; int c = mv.first.first, nu = mv.first.second;
  t.N = s.N + c + nu; t.h = c / R >= 1 ? ADDC[s.h][c / R] : s.h;
  for (int j = 0; j < K; ++j) succ_vec(s.q[j], ri[j], c + ((mv.second[j] >> ri[j]) & 1), t.q[j]);
  return t;
}
static ll gen_ub(const State& s) { ll u = 0; for (int j = 0; j < K; ++j) u += Wt[j] * phi(s.h, s.N, s.q[j]); return u; }
static int psi(const State& s) {
  Key k = make_key(s.h, s.N, s.q);
  auto it = PSI.find({k.a, k.b}); if (it != PSI.end()) return it->second;
  ll v = 0; for (int j = 0; j < K; ++j) v += Wt[j] * s.q[j][M - 1];
  vector<GMove> mv; gen_moves(s, mv);
  for (auto& a : mv) {
    int best = 1 << 30, ri[MAXK] = {0, 0, 0};
    while (true) {
      best = min(best, psi(gen_succ(s, a, ri)));
      int j = K - 1; while (j >= 0 && ++ri[j] == M) { ri[j] = 0; --j; } if (j < 0) break;
    }
    if (best > v) v = best;
  }
  PSI[{k.a, k.b}] = (int)v;
  return (int)v;
}
static int generate(int argc, char** argv, int i0) {
  if (argc - i0 < 5) die("-gen m K k r w_1..w_K T0|auto OUTFILE");
  M = atoi(argv[i0]); K = atoi(argv[i0 + 1]); KC = atoi(argv[i0 + 2]); R = atoi(argv[i0 + 3]);
  if (M < 2 || M > MAXM || K < 1 || K > MAXK) die("m or K out of range");
  if (argc - i0 != 6 + K) die("-gen m K k r w_1..w_K T0|auto OUTFILE");
  Wsum = 0; for (int j = 0; j < K; ++j) { Wt[j] = atoll(argv[i0 + 4 + j]); Wsum += Wt[j]; }
  F = KC * R; MF = M * F;
  build_H(); build_rules(); init_buckets();
  State root{}; root.h = 0; root.N = 0;
  int val = psi(root);
  const char* ts = argv[i0 + 4 + K]; ll T = strcmp(ts, "auto") ? atoll(ts) : val;
  printf("gen: m=%d K=%d k=%d r=%d joint %s value Psi(root)=%d, UB(root)=%lld, T0=%lld, %zu joint values\n",
         M, K, KC, R, STRICT ? "strict" : "relaxed", val, gen_ub(root), T, PSI.size());
  int nleaf = getenv("GEN_NLEAF") ? atoi(getenv("GEN_NLEAF")) : 0;
  vector<State> J; set<pair<uint64_t, uint64_t>> inJ;
  auto add = [&](const State& s) { Key k = make_key(s.h, s.N, s.q); if (inJ.insert({k.a, k.b}).second) J.push_back(s); };
  if (gen_ub(root) > T || nleaf > 0) add(root);
  for (size_t x = 0; x < J.size(); ++x) {
    State s = J[x]; vector<GMove> mv; gen_moves(s, mv);
    for (auto& a : mv) {
      bool leaf = false; int best = 1 << 30; State bs{}; int ri[MAXK] = {0, 0, 0};
      while (true) {
        State t = gen_succ(s, a, ri);
        if (gen_ub(t) <= T && t.N >= nleaf) { leaf = true; break; }
        int p = psi(t); if (p < best) { best = p; bs = t; }
        int j = K - 1; while (j >= 0 && ++ri[j] == M) { ri[j] = 0; --j; } if (j < 0) break;
      }
      if (!leaf) add(bs);
    }
  }
  FILE* f = fopen(argv[i0 + 5 + K], "w"); if (!f) die("cannot write");
  fprintf(f, "# hybrid test certificate from hybchk -gen\nHYBG %d %d %d %d", M, K, KC, R);
  for (int j = 0; j < K; ++j) fprintf(f, " %lld", Wt[j]);
  fprintf(f, " %lld %zu\n", T, J.size());
  for (auto& s : J) {
    fprintf(f, "%d |", s.N); bool any = false;
    for (int C = 1; C < KC; ++C) for (int y = 0; y < HU[s.h].cnt[C]; ++y) { fprintf(f, " %d", C); any = true; }
    if (!any) fprintf(f, " -");
    for (int j = 0; j < K; ++j) { fprintf(f, " |"); for (int i = 0; i < M; ++i) fprintf(f, " %d", s.q[j][i]); }
    fprintf(f, "\n");
  }
  fclose(f);
  printf("gen: wrote %zu joint states to %s\n", J.size(), argv[i0 + 5 + K]);
  return 0;
}

int main(int argc, char** argv) {
  const char* fn = nullptr; long long maxfail = 20; bool fullphi = false;
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "-strict")) STRICT = true;
    else if (!strcmp(argv[i], "-profile")) PROFILE = true;
    else if (!strcmp(argv[i], "-countstrict")) COUNTSTRICT = true;
    else if (!strcmp(argv[i], "-fullphi")) fullphi = true;
    else if (!strcmp(argv[i], "-maxfail") && i + 1 < argc) maxfail = atoll(argv[++i]);
    else if (!strcmp(argv[i], "-selftest")) { selftest(); return g_disagree ? 1 : 0; }
    else if (!strcmp(argv[i], "-gen")) return generate(argc, argv, i + 1);
    else fn = argv[i];
  }
  if (!fn) { printf("usage: hybchk [-strict] [-profile] [-countstrict] [-fullphi] [-maxfail n] FILE | -selftest\n"); return 2; }
  auto t0 = chrono::steady_clock::now();
  bool hdr = false; long long nl = 0;
  read_file(fn, hdr, nl);
  build_rules();
  init_buckets();
  printf("file %s\n", fn);
  printf("game: m=%d K=%d k=%d r=%d F=%d mF=%d weights", M, K, KC, R, F, MF);
  for (int j = 0; j < K; ++j) printf(" %lld", Wt[j]);
  printf(" W=%lld T0=%lld bound T0/(WF)=%lld/%lld rule=%s Hmode=%s\n", Wsum, T0, T0, Wsum * F,
         STRICT ? "strict" : "relaxed", PROFILE ? "profile" : "exact");
  printf("multisets H (m-splittable): %zu, profiles: %d\n", HU.size(), NPROF);
  {
    int allowedRows = 0, rows = 0;
    for (int nu = 0; nu < 2; ++nu) for (int n = 1; n <= M; ++n) for (int e = 0; e <= n - 1; ++e) for (int b = 0; b <= n; ++b) { ++rows; allowedRows += FEAS1[nu][n][e][b]; }
    printf("one-copy (M4) rows (nu,n,e,b) on admissible (n,e): %d allowed of %d; LP vs Lemma 3.3 disagreements: %lld\n", allowedRows, rows, g_disagree);
    if (g_disagree) die("the two deciders of (M4) disagree");
  }

  long long nfail = 0;
  auto fail = [&](const char* what, const State& s, const char* extra) {
    ++nfail;
    if (nfail <= maxfail) {
      printf("FAIL %s at N=%d H=", what, s.N);
      if (s.h < 0) printf("(non-splittable)"); else {
        bool any = false; for (int C = 1; C < KC; ++C) for (int x = 0; x < HU[s.h].cnt[C]; ++x) { printf("%s%d", any ? "," : "", C); any = true; }
        if (!any) printf("-");
      }
      for (int j = 0; j < K; ++j) { printf(" |"); for (int i = 0; i < M; ++i) printf(" %d", s.q[j][i]); }
      printf(" %s\n", extra);
    }
  };

  JSET.init(STATES.size());
  long long dup = 0, nonadm = 0;
  for (auto& s : STATES) {
    int code = 0;
    if (s.h < 0) code = 1;
    else for (int j = 0; j < K && !code; ++j) code = adm1(s.h, s.N, s.q[j]);
    if (code) { ++nonadm; char ex[64]; snprintf(ex, 64, "(code %d)", code); fail("ADMISSIBLE", s, ex); continue; }
    if (!JSET.insert(make_key(jkey(s.h), s.N, s.q))) ++dup;
  }
  printf("listed states: %lld, distinct admissible: %zu, duplicates: %lld, non-admissible: %lld\n", nl, JSET.n, dup, nonadm);

  State root{}; root.h = 0; root.N = 0;
  bool rootIn = JSET.has(make_key(jkey(0), 0, root.q));
  ll ubRoot = 0; for (int j = 0; j < K; ++j) ubRoot += Wt[j] * phi(0, 0, root.q[j]);
  printf("root: in J = %s, UB(root) = %lld (one-copy Phi(root) = %d)\n", rootIn ? "yes" : "no", ubRoot, phi(0, 0, root.q[0]));
  if (!(rootIn || ubRoot <= T0)) fail("J1", root, "(root neither listed nor a leaf)");

  long long moves = 0, leafMoves = 0, jMoves = 0, failMoves = 0, strictMoves = 0, groups = 0;
  long long j2fail = 0;
  int full = (1 << M) - 1;
  const vector<uint8_t> FULLONLY(1, (uint8_t)full);
  int NOPT = 2 * M; int GSZ = 1; for (int j = 0; j < K; ++j) GSZ *= NOPT;
  vector<uint64_t> gstamp(GSZ, 0); vector<uint8_t> gval(GSZ, 0); uint64_t stamp = 0;
  for (size_t si = 0; si < STATES.size(); ++si) {
    const State& s = STATES[si];
    if (s.h < 0) continue;
    bool adm = true; for (int j = 0; j < K; ++j) if (adm1(s.h, s.N, s.q[j])) adm = false;
    if (!adm) continue;
    ll pay = 0; for (int j = 0; j < K; ++j) pay += Wt[j] * s.q[j][M - 1];
    if (pay > T0) { ++j2fail; fail("J2", s, "(payoff above T0)"); }
    int h = s.h, N = s.N;
    int n[MAXK], e[MAXK];
    for (int j = 0; j < K; ++j) { int nn = 0, ss = 0; for (int i = 0; i < M; ++i) { if (s.q[j][i] > 0) ++nn; ss += s.q[j][i]; } n[j] = nn; e[j] = ss - N; }
    for (int c = 0; c < F; ++c)
      for (int nu = 0; nu < 2; ++nu) {
        int Np = N + c + nu;
        if (Np > MF) continue;
        if (N == 0 && nu == 0) continue;
        int C = c / R;
        int hp = C >= 1 ? ADDC[h][C] : h;
        if (hp < 0) continue;
        const vector<uint8_t>* L[MAXK]; bool any = true;
        for (int j = 0; j < K; ++j) { L[j] = (N == 0) ? &FULLONLY : &ALLOWED[nu][n[j]][e[j]]; if (L[j]->empty()) any = false; }
        if (!any) continue;
        ++groups; ++stamp;
        int16_t* bk = bucket(hp, Np);
        int sv[MAXK][2 * MAXM][MAXM]; int P[MAXK][2 * MAXM]; bool hv[MAXK][2 * MAXM];
        memset(hv, 0, sizeof hv);
        auto getP = [&](int j, int x) -> int {
          if (!hv[j][x]) {
            int i = x >> 1, bit = x & 1;
            succ_vec(s.q[j], i, c + bit, sv[j][x]);
            int code = adm1(hp, Np, sv[j][x]);
            if (code) die("successor not admissible (code %d)", code);
            P[j][x] = phi_lookup(bk, hp, Np, sv[j][x]);
            hv[j][x] = true;
          }
          return P[j][x];
        };
        int mins[MAXK][1 << MAXM];
        for (int j = 0; j < K; ++j)
          for (uint8_t mask : *L[j]) {
            int mn = 1 << 30;
            for (int i = 0; i < M; ++i) { int v = getP(j, 2 * i + ((mask >> i) & 1)); if (v < mn) mn = v; }
            mins[j][mask] = mn;
          }
        int idxs[MAXK] = {0, 0, 0};
        while (true) {
          uint8_t mk[MAXK]; bool allHaveZero = true; ll ub = 0;
          for (int j = 0; j < K; ++j) { mk[j] = (*L[j])[idxs[j]]; if (mk[j] == full) allHaveZero = false; ub += Wt[j] * mins[j][mk[j]]; }
          bool idle = (c == 0 && nu == 0 && allHaveZero);
          bool allowed = true;
          if (!idle && (STRICT || COUNTSTRICT) && N >= 1) {
            size_t ji = nu;
            for (int j = 0; j < K; ++j) ji = ji * NTRI + TRIID[n[j]][e[j]][M - __builtin_popcount(mk[j])];
            bool st = JOINT[ji];
            if (st) ++strictMoves;
            if (STRICT && !st) allowed = false;
          } else if (!idle && N == 0) ++strictMoves;
          if (!idle && allowed) {
            ++moves;
            if (ub <= T0) ++leafMoves;
            else {
              bool found = false;
              int ri[MAXK] = {0, 0, 0};
              while (!found) {
                int gi = 0;
                for (int j = 0; j < K; ++j) gi = gi * NOPT + (2 * ri[j] + ((mk[j] >> ri[j]) & 1));
                if (gstamp[gi] != stamp) {
                  int qs[MAXK][MAXM];
                  for (int j = 0; j < K; ++j) { int x = 2 * ri[j] + ((mk[j] >> ri[j]) & 1); getP(j, x); memcpy(qs[j], sv[j][x], sizeof(int) * M); }
                  gval[gi] = JSET.has(make_key(jkey(hp), Np, qs));
                  gstamp[gi] = stamp;
                }
                if (gval[gi]) { found = true; break; }
                int j = K - 1;
                while (j >= 0 && ++ri[j] == M) { ri[j] = 0; --j; }
                if (j < 0) break;
              }
              if (found) ++jMoves;
              else {
                ++failMoves;
                char ex[160]; int p = snprintf(ex, 160, "(move c=%d nu=%d bits", c, nu);
                for (int j = 0; j < K; ++j) { p += snprintf(ex + p, 160 - p, " "); for (int i = 0; i < M; ++i) p += snprintf(ex + p, 160 - p, "%d", (mk[j] >> i) & 1); }
                snprintf(ex + p, 160 - p, ": no response into J or to a leaf)");
                fail("J3", s, ex);
              }
            }
          }
          int j = K - 1;
          while (j >= 0 && ++idxs[j] == (int)L[j]->size()) { idxs[j] = 0; --j; }
          if (j < 0) break;
        }
      }
    if ((si + 1) % 500000 == 0) {
      double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
      printf("progress %zu states, %lld moves, %lld one-copy values, %.1f s\n", si + 1, moves, g_phi_count, el);
      fflush(stdout);
    }
  }
  if (fullphi) fullphi_check();
  double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("counts: joint states %zu, (c,nu) groups %lld, non-idle %s moves %lld (answered by a leaf %lld, only through J %lld, unanswered %lld)\n",
         JSET.n, groups, STRICT ? "strict" : "relaxed", moves, leafMoves, jMoves, failMoves);
  if (STRICT || COUNTSTRICT) printf("counts: of these, moves allowed by the strict rule (common point): %lld\n", strictMoves);
  printf("counts: one-copy values computed %lld, buckets %zu (%.1f MB), max recursion depth %d, LP decisions %lld\n",
         g_phi_count, BUCKETS.size(), g_bucket_bytes / 1e6, g_maxdepth, g_lp_calls);
  printf("checks: J2 failures %lld, J3 failures %lld, non-admissible %lld, total failures %lld, time %.1f s\n",
         j2fail, failMoves, nonadm, nfail, el);
  if (nfail == 0) printf("PASS %s hybrid certificate: bound %lld/%lld\n", STRICT ? "strict" : "relaxed", T0, Wsum * F);
  else printf("FAIL %s hybrid certificate (%lld failures)\n", STRICT ? "strict" : "relaxed", nfail);
  return nfail ? 1 : 0;
}
