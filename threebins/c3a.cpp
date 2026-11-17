// c3a.cpp: checks a certificate of the rounded lottery game for three bins (paper, App. F), as written by rg3.cpp.
// g++ -O2 -std=c++17 -fopenmp -o c3a c3a.cpp && ./c3a FILE
// Prints one line, PASS (exit 0) or FAIL (exit 1).
//
// File: a line RG3CERT k r K w_1..w_K T0 n, then n states, the root first:
//   N h_1..h_{k-1} q_{1,1} q_{1,2} q_{1,3} ... q_{K,1} q_{K,2} q_{K,3} T
// N rounded total, h_C jobs of class C, q_j sorted rounded loads of copy j, T potential.
// Checks: (1) format; (2) root all zero with T <= T0; (3) no state twice; (4) each state valid (Lemma F.1 (i),
// (ii)); (5) sum_j w_j q_{j,3} <= T; (6) every move that is not skipped has a response to a listed state with
// potential at most T. Moves are decided by eliminating x from (M4). '#' lines are comments.
#include <algorithm>
#include <atomic>
#include <cerrno>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <sys/types.h>
#include <omp.h>

typedef long long ll;
typedef unsigned long long ull;
typedef __int128 i128;
typedef unsigned __int128 u128;

static const ll LIM_k = 64;
static const ll LIM_F = 4096;

static std::string S(ll x) { return std::to_string(x); }
static std::string SU(u128 x) {
  if (x == 0) return "0";
  std::string s;
  while (x > 0) { s.push_back((char)('0' + (int)(x % 10))); x /= 10; }
  std::reverse(s.begin(), s.end());
  return s;
}
[[noreturn]] static void failExit(int check, const std::string& state, const std::string& reason) {
  printf("FAIL check %d state %s: %s\n", check, state.c_str(), reason.c_str());
  fflush(stdout);
  exit(1);
}
[[noreturn]] static void internalError(const std::string& what) {
  printf("ERROR internal: %s\n", what.c_str());
  fflush(stdout);
  exit(3);
}
#define REQUIRE(c)                                                                                  \
  do {                                                                                              \
    if (!(c)) internalError(std::string("assertion failed: ") + #c + " (line " + std::to_string(__LINE__) + ")"); \
  } while (0)
static double wallNow() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}
static inline void sort3(ll* a) {
  if (a[0] > a[1]) std::swap(a[0], a[1]);
  if (a[1] > a[2]) std::swap(a[1], a[2]);
  if (a[0] > a[1]) std::swap(a[0], a[1]);
}

static int TY[4][3][4];
static int TYn[20], TYe[20], TYb[20];
static int NTYPES = 0;
static void initTypes() {
  for (int a = 0; a < 4; a++)
    for (int b = 0; b < 3; b++)
      for (int c = 0; c < 4; c++) TY[a][b][c] = -1;
  NTYPES = 0;
  for (int n = 1; n <= 3; n++)
    for (int e = 0; e <= n - 1; e++)
      for (int b = 0; b <= n; b++) {
        TY[n][e][b] = NTYPES;
        TYn[NTYPES] = n; TYe[NTYPES] = e; TYb[NTYPES] = b;
        NTYPES++;
      }
  REQUIRE(NTYPES == 20);
}

struct Fr { ll p, q; };
static inline bool frLess(const Fr& a, const Fr& b) { return (i128)a.p * b.q < (i128)b.p * a.q; }

static bool eliminate(const int* Lm, const int* Ld, int nL, const int* Um, const int* Ud, int nU) {
  Fr lo{0, 1}, hi{1, 1};
  for (int i = 0; i < nL; i++)
    for (int j = 0; j < nU; j++) {
      const ll a = (ll)Lm[i] - Um[j], rhs = (ll)Ld[i] - Ud[j];
      if (a == 0) {
        if (rhs <= 0) return false;
      } else if (a > 0) {
        const Fr f{rhs, a};
        if (frLess(f, hi)) hi = f;
      } else {
        const Fr f{-rhs, -a};
        if (frLess(lo, f)) lo = f;
      }
    }
  return frLess(lo, hi);
}

static void baseBounds(int nu, int* Lm, int* Ld, int& nL, int* Um, int* Ud, int& nU) {
  nL = 0; nU = 0;
  Lm[nL] = 0; Ld[nL] = 0; nL++;
  Um[nU] = 0; Ud[nU] = -1; nU++;
  if (nu == 1) { Um[nU] = 1; Ud[nU] = 0; nU++; }
  else { Lm[nL] = 1; Ld[nL] = 0; nL++; }
}

static bool fmTwoSided(int nu, uint32_t mask) {
  int Lm[24], Ld[24], Um[24], Ud[24], nL, nU;
  baseBounds(nu, Lm, Ld, nL, Um, Ud, nU);
  for (int ty = 0; ty < NTYPES; ty++)
    if ((mask >> ty) & 1u) {
      const int n = TYn[ty], e = TYe[ty], b = TYb[ty];
      Lm[nL] = b; Ld[nL] = e; nL++;
      Um[nU] = n - b; Ud[nU] = e - b; nU++;
    }
  return eliminate(Lm, Ld, nL, Um, Ud, nU);
}

static bool fmOneSided(int nu, uint32_t mask) {
  int Lm[24], Ld[24], Um[24], Ud[24], nL, nU;
  baseBounds(nu, Lm, Ld, nL, Um, Ud, nU);
  for (int ty = 0; ty < NTYPES; ty++)
    if ((mask >> ty) & 1u) {
      const int n = TYn[ty], e = TYe[ty], b = TYb[ty];
      if (b <= e) { Um[nU] = n - b; Ud[nU] = e - b; nU++; }
      else { Lm[nL] = b; Ld[nL] = e; nL++; }
    }
  return eliminate(Lm, Ld, nL, Um, Ud, nU);
}

static bool tableAllowed(int nu, uint32_t mask) {
  int lo = 1, hi = 4;
  for (int ty = 0; ty < NTYPES; ty++)
    if ((mask >> ty) & 1u) {
      const int n = TYn[ty], e = TYe[ty], b = TYb[ty], eps = e - nu;
      int a, z;
      if (eps == -1) { if (b != 0) return false; a = 1; z = 4; }
      else if (eps == n - 1) { if (b != n) return false; a = 1; z = 4; }
      else if (n == 2 && eps == 0) { static const int I[3][2] = {{3, 4}, {1, 4}, {1, 2}}; a = I[b][0]; z = I[b][1]; }
      else if (n == 3 && eps == 0) { static const int I[4][2] = {{2, 4}, {1, 4}, {1, 2}, {1, 1}}; a = I[b][0]; z = I[b][1]; }
      else if (n == 3 && eps == 1) { static const int I[4][2] = {{4, 4}, {3, 4}, {1, 4}, {1, 3}}; a = I[b][0]; z = I[b][1]; }
      else internalError("table case");
      lo = std::max(lo, a);
      hi = std::min(hi, z);
    }
  return lo <= hi;
}

static std::vector<uint8_t> FMC[2];
static void buildFMC() {
  FMC[0].assign((size_t)1 << 20, 0);
  FMC[1].assign((size_t)1 << 20, 0);
#pragma omp parallel for schedule(static)
  for (ll m = 0; m < (1LL << 21); m++) {
    const int nu = (int)(m >> 20);
    const uint32_t mask = (uint32_t)(m & 0xFFFFF);
    FMC[nu][mask] = fmTwoSided(nu, mask) ? 1 : 0;
  }
}

static bool splits3(const uint8_t* h, int k) {
  const int cap = k - 1;
  long total = 0;
  for (int C = 1; C <= k - 1; C++) total += (long)C * h[C - 1];
  if (total > 3L * cap) return false;
  const int W = cap + 1;
  std::vector<uint8_t> cur((size_t)W * W, 0), nxt((size_t)W * W, 0);
  cur[0] = 1;
  long s = 0;
  for (int C = k - 1; C >= 1; C--)
    for (int rep = 0; rep < h[C - 1]; rep++) {
      std::fill(nxt.begin(), nxt.end(), 0);
      bool any = false;
      for (int a = 0; a <= cap; a++)
        for (int b = a; b <= cap; b++) {
          if (!cur[(size_t)a * W + b]) continue;
          const long c3 = s - a - b;
          for (int g = 0; g < 3; g++) {
            long M[3] = {a, b, c3};
            M[g] += C;
            if (M[g] > cap) continue;
            if (M[0] > M[1]) std::swap(M[0], M[1]);
            if (M[1] > M[2]) std::swap(M[1], M[2]);
            if (M[0] > M[1]) std::swap(M[0], M[1]);
            nxt[(size_t)M[0] * W + M[1]] = 1;
            any = true;
          }
        }
      if (!any) return false;
      s += C;
      std::swap(cur, nxt);
    }
  return true;
}

struct Params {
  ll k = 0, r = 0, K = 0, F = 0, T0 = 0, n = 0;
  ll w[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  u128 W = 0;
  ll RN = 0;
  ll U1 = 0, V1 = 0;
  ll RT = 0;
};
static Params P;

static void setRadices() {
  P.RN = 3 * P.F + 1;
  P.U1 = P.F + 1;
  P.V1 = (3 * P.F + 2) / 2 + 1;
  P.RT = 3 * P.U1 * P.V1;
}

static inline ll encodeTriple(ll N, ll a, ll b, ll c) {
  const ll e = a + b + c - N;
  if (e < 0 || e > 2) return -1;
  if (a < 0 || a >= P.U1 || b < 0 || b >= P.V1) return -1;
  return (e * P.U1 + a) * P.V1 + b;
}
static inline void decodeTriple(ll N, ll code, ll* t) {
  const ll b = code % P.V1;
  code /= P.V1;
  const ll a = code % P.U1;
  const ll e = code / P.U1;
  t[0] = a; t[1] = b; t[2] = N + e - a - b;
}

static const uint32_t NOH = 0xFFFFFFFFu;
static std::vector<uint32_t> sH;
static std::vector<uint16_t> sN;
static std::vector<uint32_t> sCode;
static std::vector<ll> sT;

static std::unordered_map<std::string, uint32_t> hDict;
static std::vector<std::string> hList;
static std::vector<uint8_t> hSplit;
static std::vector<ll> hSum;
static std::vector<uint8_t> splitPlus;
static std::vector<ll> plusIdx;

static std::vector<ll> invRaw;
static std::vector<ll> invId;

struct FirstViol {
  ll id = -1;
  std::string why;
};
static FirstViol v2, v4, v5;

static std::string lastHb;
static uint32_t lastHidx = NOH;
static uint32_t hIndex(const std::string& hb) {
  if (lastHidx != NOH && hb == lastHb) return lastHidx;
  auto it = hDict.find(hb);
  uint32_t idx;
  if (it != hDict.end()) {
    idx = it->second;
  } else {
    REQUIRE(hList.size() < 0xFFFFFF00u);
    idx = (uint32_t)hList.size();
    hDict.emplace(hb, idx);
    hList.push_back(hb);
    hSplit.push_back(splits3((const uint8_t*)hb.data(), (int)P.k) ? 1 : 0);
    ll sum = 0;
    for (ll C = 1; C <= P.k - 1; C++) sum += C * (ll)(uint8_t)hb[C - 1];
    hSum.push_back(sum);
  }
  lastHb = hb;
  lastHidx = idx;
  return idx;
}

static bool checkAbstract(ll N, const ll* h, const ll* q, std::string& why, uint32_t& hidx) {
  const ll k = P.k, K = P.K, F = P.F;
  if (N > 3 * F) { why = "N=" + S(N) + " exceeds 3F=" + S(3 * F); return false; }
  const ll cap3 = 3 * (k - 1);
  for (ll C = 1; C <= k - 1; C++)
    if (h[C - 1] > cap3) {
      why = "H does not split into three groups with sums <= k-1 (h_" + S(C) + "=" + S(h[C - 1]) + ")";
      return false;
    }
  std::string hb((size_t)(k - 1), '\0');
  for (ll C = 1; C <= k - 1; C++) hb[C - 1] = (char)(uint8_t)h[C - 1];
  const uint32_t idx = hIndex(hb);
  if (!hSplit[idx]) { why = "H does not split into three groups with sums <= k-1"; return false; }
  const ll sumH = hSum[idx];
  if (sumH > 0 && N < P.r * sumH + 1) {
    why = "H is not empty and N=" + S(N) + " < r*sum(H)+1=" + S(P.r * sumH + 1);
    return false;
  }
  for (ll j = 0; j < K; j++) {
    const ll* t = q + 3 * j;
    if (N == 0) {
      if (t[0] != 0 || t[1] != 0 || t[2] != 0) {
        why = "N=0 but copy " + S(j + 1) + " has a nonzero rounded load";
        return false;
      }
    } else {
      const ll nj = (t[0] > 0) + (t[1] > 0) + (t[2] > 0);
      const ll ej = t[0] + t[1] + t[2] - N;
      if (nj < 1) { why = "N>=1 but copy " + S(j + 1) + " has no nonempty bin"; return false; }
      if (ej < 0 || ej > nj - 1) {
        why = "copy " + S(j + 1) + " has e=" + S(ej) + " outside [0, n_j-1=" + S(nj - 1) + "]";
        return false;
      }
    }
  }
  hidx = idx;
  return true;
}

static void processState(ll id, const ll* vals) {
  const ll k = P.k, K = P.K;
  const ll N = vals[0];
  const ll* h = vals + 1;
  const ll* q = vals + k;
  const ll T = vals[k + 3 * K];
  if (id == 0) {
    bool root = (N == 0);
    for (ll i = 1; i < k + 3 * K; i++)
      if (vals[i] != 0) root = false;
    if (!root) { v2.id = 0; v2.why = "state 0 is not the root (N, all h_C and all q must be 0)"; }
    else if (T > P.T0) { v2.id = 0; v2.why = "the potential T=" + S(T) + " of the root exceeds T0=" + S(P.T0); }
  }
  i128 pay = 0;
  for (ll j = 0; j < K; j++) pay += (i128)P.w[j] * (i128)q[3 * j + 2];
  if (pay > (i128)T && v5.id < 0) {
    v5.id = id;
    v5.why = "payoff sum_j w_j q_{j,3}=" + SU((u128)pay) + " exceeds T=" + S(T);
  }
  std::string why;
  uint32_t hidx = NOH;
  if (!checkAbstract(N, h, q, why, hidx)) {
    if (v4.id < 0) { v4.id = id; v4.why = why; }
    invId.push_back(id);
    for (ll i = 0; i < k + 3 * K; i++) invRaw.push_back(vals[i]);
    sH.push_back(NOH);
    sN.push_back(0);
    for (ll j = 0; j < K; j++) sCode.push_back(0);
    sT.push_back(T);
    return;
  }
  REQUIRE(N >= 0 && N <= 3 * P.F && N < 65536);
  sH.push_back(hidx);
  sN.push_back((uint16_t)N);
  for (ll j = 0; j < K; j++) {
    const ll c = encodeTriple(N, q[3 * j], q[3 * j + 1], q[3 * j + 2]);
    REQUIRE(c >= 0 && c < P.RT && c <= 0xFFFFFFFFLL);
    sCode.push_back((uint32_t)c);
  }
  sT.push_back(T);
}

static inline uint64_t fmix64(uint64_t x) {
  x ^= x >> 33; x *= 0xff51afd7ed558ccdULL;
  x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL;
  x ^= x >> 33;
  return x;
}
static inline uint64_t hashKey(uint64_t x) { return fmix64(x); }
static inline uint64_t hashKey(u128 x) {
  return fmix64((uint64_t)x ^ fmix64((uint64_t)(x >> 64) ^ 0x9e3779b97f4a7c15ULL));
}

template <class KeyT>
struct Table {
  struct Slot { KeyT key; ll T; };
  Slot* s = nullptr;
  size_t cap = 0, mask = 0;
  static KeyT empty() { return ~(KeyT)0; }
  void init(size_t n) {
    cap = 16;
    while (cap < 2 * n) cap <<= 1;
    mask = cap - 1;
    s = (Slot*)malloc(cap * sizeof(Slot));
    if (!s) internalError("out of memory for the hash table");
    const KeyT E = empty();
#pragma omp parallel for schedule(static)
    for (ll i = 0; i < (ll)cap; i++) { s[i].key = E; s[i].T = 0; }
  }
  inline size_t home(KeyT k) const { return (size_t)(hashKey(k) & mask); }
  inline void prefetch(KeyT k) const { __builtin_prefetch(&s[home(k)]); }
  bool insert(KeyT k, ll T) {
    const KeyT E = empty();
    size_t i = home(k);
    for (;;) {
      if (s[i].key == E) { s[i].key = k; s[i].T = T; return true; }
      if (s[i].key == k) return false;
      i = (i + 1) & mask;
    }
  }
  inline const Slot* find(KeyT k) const {
    const KeyT E = empty();
    size_t i = home(k);
    for (;;) {
      if (s[i].key == k) return &s[i];
      if (s[i].key == E) return nullptr;
      i = (i + 1) & mask;
    }
  }
};

template <class KeyT>
struct KeySpace { KeyT multH, multN, multCopy[8]; };

template <class KeyT>
static inline KeyT stateKey(const KeySpace<KeyT>& ks, ll id) {
  KeyT key = (KeyT)sH[id] * ks.multH + (KeyT)sN[id] * ks.multN;
  const uint32_t* cd = &sCode[(size_t)id * P.K];
  for (ll j = 0; j < P.K; j++) key += (KeyT)cd[j] * ks.multCopy[j];
  return key;
}

struct Ctx {
  std::vector<uint64_t> memoGen;
  std::vector<uint8_t> memoGood;
  uint64_t gen = 0;
  std::vector<uint8_t> tup[2];
  std::vector<uint8_t> tupHZ[2];
  ull moves = 0;
  explicit Ctx(int K) {
    size_t m = 1;
    for (int j = 0; j < K; j++) m *= 6;
    memoGen.assign(m, 0);
    memoGood.assign(m, 0);
  }
};

static void enumTuples(int j, int K, uint32_t mask, bool allHZ, int nu, bool N0, uint8_t* cur,
                       const bool (*valid)[8], const uint32_t (*tbit)[8], const bool (*hz)[8],
                       std::vector<uint8_t>& out, std::vector<uint8_t>& outHZ) {
  if (j == K) {
    out.insert(out.end(), cur, cur + K);
    outHZ.push_back(allHZ ? 1 : 0);
    return;
  }
  for (int o = 0; o < 8; o++) {
    if (!valid[j][o]) continue;
    const uint32_t m2 = mask | tbit[j][o];
    if (!N0 && !FMC[nu][m2]) continue;
    cur[j] = (uint8_t)o;
    enumTuples(j + 1, K, m2, allHZ && hz[j][o], nu, N0, cur, valid, tbit, hz, out, outHZ);
  }
}

static std::string bitsStr(int o) {
  std::string s;
  for (int i = 0; i < 3; i++) s.push_back((char)('0' + ((o >> i) & 1)));
  return s;
}

template <class KeyT>
static bool checkState(ll id, Ctx& cx, const KeySpace<KeyT>& ks, const Table<KeyT>& tab, std::string* why) {
  const int K = (int)P.K;
  const ll F = P.F, r = P.r, km1 = P.k - 1;
  const uint32_t hidx = sH[id];
  const ll N = sN[id];
  const ll T = sT[id];
  REQUIRE(hidx != NOH);
  ll q[8][3];
  int nn[8], ee[8];
  for (int j = 0; j < K; j++) {
    decodeTriple(N, sCode[(size_t)id * K + j], q[j]);
    REQUIRE(q[j][0] >= 0 && q[j][0] <= q[j][1] && q[j][1] <= q[j][2]);
    nn[j] = (q[j][0] > 0) + (q[j][1] > 0) + (q[j][2] > 0);
    ee[j] = (int)(q[j][0] + q[j][1] + q[j][2] - N);
  }
  const bool N0 = (N == 0);
  bool valid[8][8], hz[8][8];
  uint32_t tbit[8][8];
  for (int j = 0; j < K; j++)
    for (int o = 0; o < 8; o++) {
      if (N0) {
        valid[j][o] = (o == 7);
        tbit[j][o] = 0;
        hz[j][o] = false;
        continue;
      }
      bool ok = true;
      int b = 0;
      for (int i = 0; i < 3; i++) {
        const int bit = (o >> i) & 1;
        if (q[j][i] == 0) { if (bit == 0) ok = false; }
        else if (bit == 0) b++;
      }
      valid[j][o] = ok;
      hz[j][o] = (b >= 1);
      if (ok) {
        REQUIRE(nn[j] >= 1 && nn[j] <= 3 && ee[j] >= 0 && ee[j] <= nn[j] - 1);
        const int ty = TY[nn[j]][ee[j]][b];
        REQUIRE(ty >= 0);
        tbit[j][o] = 1u << ty;
      } else {
        tbit[j][o] = 0;
      }
    }
  uint8_t cur[8];
  for (int nu = 0; nu < 2; nu++) {
    cx.tup[nu].clear();
    cx.tupHZ[nu].clear();
    if (N0 && nu == 0) continue;
    enumTuples(0, K, 0u, true, nu, N0, cur, valid, tbit, hz, cx.tup[nu], cx.tupHZ[nu]);
  }
  for (ll c = 0; c <= F - 1; c++) {
    for (int nu = 0; nu < 2; nu++) {
      if (N0 && nu == 0) continue;
      const ll Nn = N + c + nu;
      if (Nn > 3 * F) continue;
      const ll C = c / r;
      ll hn = hidx;
      if (C >= 1) {
        const size_t t = (size_t)hidx * km1 + (C - 1);
        if (!splitPlus[t]) continue;
        hn = plusIdx[t];
      }
      const size_t ntup = cx.tupHZ[nu].size();
      if (ntup == 0) continue;
      ll sc[8][3][2];
      for (int j = 0; j < K; j++)
        for (int i = 0; i < 3; i++)
          for (int bit = 0; bit < 2; bit++) {
            ll a[3] = {q[j][0], q[j][1], q[j][2]};
            a[i] += c + bit;
            sort3(a);
            sc[j][i][bit] = encodeTriple(Nn, a[0], a[1], a[2]);
          }
      KeyT base = 0;
      if (hn >= 0) base = (KeyT)hn * ks.multH + (KeyT)Nn * ks.multN;
      cx.gen++;
      const uint8_t* tp = cx.tup[nu].data();
      for (size_t ti = 0; ti < ntup; ti++, tp += K) {
        if (c == 0 && nu == 0 && cx.tupHZ[nu][ti]) continue;
        cx.moves++;
        int ii[8] = {0, 0, 0, 0, 0, 0, 0, 0};
        bool ok = false;
        for (;;) {
          size_t combo = 0;
          for (int j = 0; j < K; j++) combo = combo * 6 + (size_t)(2 * ii[j] + ((tp[j] >> ii[j]) & 1));
          if (cx.memoGen[combo] != cx.gen) {
            bool good = false;
            if (hn >= 0) {
              KeyT key = base;
              bool enc = true;
              for (int j = 0; j < K; j++) {
                const ll cd = sc[j][ii[j]][(tp[j] >> ii[j]) & 1];
                if (cd < 0) { enc = false; break; }
                key += (KeyT)cd * ks.multCopy[j];
              }
              if (enc) {
                const auto* sl = tab.find(key);
                good = (sl != nullptr && sl->T <= T);
              }
            }
            cx.memoGen[combo] = cx.gen;
            cx.memoGood[combo] = good ? 1 : 0;
          }
          if (cx.memoGood[combo]) { ok = true; break; }
          int j = K - 1;
          while (j >= 0 && ii[j] == 2) { ii[j] = 0; j--; }
          if (j < 0) break;
          ii[j]++;
        }
        if (!ok) {
          if (why) {

            std::string d = "N=" + S(N) + " H=(";
            const std::string& hb = hList[hidx];
            for (size_t x = 0; x < hb.size(); x++) d += (x ? "," : "") + S((uint8_t)hb[x]);
            d += ") q=";
            for (int j = 0; j < K; j++) d += "(" + S(q[j][0]) + "," + S(q[j][1]) + "," + S(q[j][2]) + ")";
            d += " T=" + S(T) + "; move c=" + S(c) + " nu=" + S(nu) + " bits(rank 1,2,3)=";
            for (int j = 0; j < K; j++) d += (j ? "/" : "") + bitsStr(tp[j]);
            ll listed = 0, total = 0, leastT = LLONG_MAX;
            int jj[8] = {0, 0, 0, 0, 0, 0, 0, 0};
            for (;;) {
              total++;
              if (hn >= 0) {
                KeyT key = base;
                bool enc = true;
                for (int j = 0; j < K; j++) {
                  const ll cd = sc[j][jj[j]][(tp[j] >> jj[j]) & 1];
                  if (cd < 0) { enc = false; break; }
                  key += (KeyT)cd * ks.multCopy[j];
                }
                if (enc) {
                  const auto* sl = tab.find(key);
                  if (sl) { listed++; leastT = std::min(leastT, sl->T); }
                }
              }
              int j = K - 1;
              while (j >= 0 && jj[j] == 2) { jj[j] = 0; j--; }
              if (j < 0) break;
              jj[j]++;
            }
            d += ": no response leads to a listed state with potential <= " + S(T) + " (" + S(listed) + " of " +
                 S(total) + " responses reach a listed state";
            if (listed > 0) d += ", least potential " + S(leastT);
            if (hn < 0) d += "; no listed state has H + {" + S(C) + "}";
            d += ")";
            *why = d;
          }
          return false;
        }
      }
    }
  }
  return true;
}

template <class KeyT>
static int runChecks(ll n, double tStart) {
  const ll K = P.K;
  KeySpace<KeyT> ks;
  {
    KeyT m = 1;
    for (ll j = K - 1; j >= 0; j--) { ks.multCopy[j] = m; m = m * (KeyT)P.RT; }
    ks.multN = m;
    ks.multH = m * (KeyT)P.RN;
  }
  fprintf(stderr, "[c3a] %lld states, %zu distinct H, %d-bit keys, %d threads, parse %.1f s\n", n, hList.size(),
          (int)(8 * sizeof(KeyT)), omp_get_max_threads(), wallNow() - tStart);

  const double t3 = wallNow();
  Table<KeyT> tab;
  tab.init((size_t)n);
  ll dupV = -1;
  for (ll id = 0; id < n; id++) {
    const ll pf = id + 16;
    if (pf < n && sH[pf] != NOH) tab.prefetch(stateKey(ks, pf));
    if (sH[id] == NOH) continue;
    if (!tab.insert(stateKey(ks, id), sT[id])) { dupV = id; break; }
  }
  ll dupI = -1, dupIof = -1;
  if (invId.size() >= 2) {
    const size_t RW = (size_t)(P.k + 3 * K);
    std::vector<size_t> ord(invId.size());
    for (size_t i = 0; i < ord.size(); i++) ord[i] = i;
    auto cmpRaw = [&](size_t a, size_t b) -> int {
      for (size_t t = 0; t < RW; t++) {
        const ll x = invRaw[a * RW + t], y = invRaw[b * RW + t];
        if (x != y) return x < y ? -1 : 1;
      }
      return 0;
    };
    std::sort(ord.begin(), ord.end(), [&](size_t a, size_t b) {
      const int c = cmpRaw(a, b);
      if (c != 0) return c < 0;
      return invId[a] < invId[b];
    });
    size_t i = 0;
    while (i < ord.size()) {
      size_t j = i;
      while (j + 1 < ord.size() && cmpRaw(ord[i], ord[j + 1]) == 0) j++;
      if (j > i && (dupI < 0 || invId[ord[i + 1]] < dupI)) { dupI = invId[ord[i + 1]]; dupIof = invId[ord[i]]; }
      i = j + 1;
    }
  }
  ll dup = -1, dupOf = -1;
  if (dupV >= 0) {
    dup = dupV;
    const KeyT kk = stateKey(ks, dupV);
    for (ll id = 0; id < dupV; id++)
      if (sH[id] != NOH && stateKey(ks, id) == kk) { dupOf = id; break; }
  }
  if (dupI >= 0 && (dup < 0 || dupI < dup)) { dup = dupI; dupOf = dupIof; }
  if (dup >= 0) failExit(3, S(dup), "same key as state " + S(dupOf));
  fprintf(stderr, "[c3a] check 3 (unique keys, table of %zu slots) %.1f s\n", tab.cap, wallNow() - t3);

  if (v4.id >= 0) failExit(4, S(v4.id), v4.why);
  if (v5.id >= 0) failExit(5, S(v5.id), v5.why);

  const double t6 = wallNow();
  const ll numH = (ll)hList.size(), km1 = P.k - 1;
  splitPlus.assign((size_t)(numH * km1), 0);
  plusIdx.assign((size_t)(numH * km1), -1);
#pragma omp parallel for schedule(dynamic, 16)
  for (ll hi = 0; hi < numH; hi++) {
    const std::string& h2 = hList[hi];
    for (ll C = 1; C <= km1; C++) {
      const size_t t = (size_t)(hi * km1 + (C - 1));
      const int val = (int)(uint8_t)h2[C - 1] + 1;
      if (val > 3 * km1) { splitPlus[t] = 0; plusIdx[t] = -1; continue; }
      std::string h3 = h2;
      h3[C - 1] = (char)(uint8_t)val;
      auto it = hDict.find(h3);
      if (it != hDict.end()) { plusIdx[t] = it->second; splitPlus[t] = hSplit[it->second]; }
      else { plusIdx[t] = -1; splitPlus[t] = splits3((const uint8_t*)h3.data(), (int)P.k) ? 1 : 0; }
    }
  }
  buildFMC();
  std::atomic<ll> minFail(LLONG_MAX);
  std::atomic<ll> done(0);
  ull totalMoves = 0;
#pragma omp parallel reduction(+ : totalMoves)
  {
    Ctx cx((int)K);
    ll local = 0;
#pragma omp for schedule(dynamic, 256)
    for (ll id = 0; id < n; id++) {
      if (id > minFail.load(std::memory_order_relaxed)) continue;
      if (!checkState<KeyT>(id, cx, ks, tab, nullptr)) {
        ll cur = minFail.load();
        while (id < cur && !minFail.compare_exchange_weak(cur, id)) {
        }
      }
      if (((++local) & 65535) == 0) {
        const ll d = done.fetch_add(65536) + 65536;
        if ((d & ((1LL << 24) - 1)) == 0)
          fprintf(stderr, "[c3a] check 6: about %lld of %lld states, %.0f s\n", d, n, wallNow() - t6);
      }
    }
    totalMoves += cx.moves;
  }
  if (minFail.load() != LLONG_MAX) {
    const ll f = minFail.load();
    Ctx cx((int)K);
    std::string why;
    const bool again = checkState<KeyT>(f, cx, ks, tab, &why);
    REQUIRE(!again);
    failExit(6, S(f), why);
  }
  fprintf(stderr, "[c3a] check 6 (moves) %.1f s, total %.1f s\n", wallNow() - t6, wallNow() - tStart);
  std::string ws;
  for (ll j = 0; j < K; j++) ws += (j ? "," : "") + S(P.w[j]);
  printf("PASS k %lld r %lld weights %s T0 %lld states %lld moves %llu bound %lld/%s\n", P.k, P.r, ws.c_str(), P.T0,
         n, totalMoves, P.T0, SU(P.W * (u128)P.F).c_str());
  fflush(stdout);
  return 0;
}

static inline bool parseNum(const char* s, const char* e, ll& v) {
  const ll len = e - s;
  if (len < 1 || len > 18) return false;
  ll x = 0;
  for (; s < e; s++) {
    const unsigned d = (unsigned)(unsigned char)*s - (unsigned)'0';
    if (d > 9) return false;
    x = x * 10 + (ll)d;
  }
  v = x;
  return true;
}

static char* readFile(const char* path, size_t& len, std::string& err) {
  FILE* f = fopen(path, "rb");
  if (!f) { err = std::string("cannot open ") + path + ": " + strerror(errno); return nullptr; }
  size_t cap = (size_t)1 << 20;
  if (fseeko(f, 0, SEEK_END) == 0) {
    const off_t sz = ftello(f);
    if (sz > 0) cap = (size_t)sz + 1;
    if (fseeko(f, 0, SEEK_SET) != 0) { err = "cannot seek in the file"; fclose(f); return nullptr; }
  }
  char* buf = (char*)malloc(cap);
  if (!buf) { err = "out of memory while reading the file"; fclose(f); return nullptr; }
  len = 0;
  for (;;) {
    if (len == cap) {
      const size_t ncap = cap * 2;
      char* nb = (char*)realloc(buf, ncap);
      if (!nb) { free(buf); err = "out of memory while reading the file"; fclose(f); return nullptr; }
      buf = nb;
      cap = ncap;
    }
    const size_t got = fread(buf + len, 1, cap - len, f);
    len += got;
    if (got == 0) break;
  }
  const bool bad = ferror(f) != 0;
  fclose(f);
  if (bad) { free(buf); err = "read error"; return nullptr; }
  return buf;
}

static bool splitBrute(const std::vector<int>& items, int cap, size_t i, int* L) {
  if (i == items.size()) return true;
  for (int g = 0; g < 3; g++)
    if (L[g] + items[i] <= cap) {
      L[g] += items[i];
      const bool ok = splitBrute(items, cap, i + 1, L);
      L[g] -= items[i];
      if (ok) return true;
    }
  return false;
}

static int selftest() {
  int bad = 0;

  ll cnt[2] = {0, 0}, mis1 = 0, mis2 = 0;
  for (int nu = 0; nu < 2; nu++)
    for (uint32_t mask = 0; mask < (1u << 20); mask++) {
      const bool a = fmTwoSided(nu, mask), b = fmOneSided(nu, mask), c = tableAllowed(nu, mask);
      if (a != b) mis1++;
      if (a != c) mis2++;
      cnt[nu] += a;
    }
  printf("selftest 1: two-sided vs one-sided mismatches %lld, vs interval table mismatches %lld\n", mis1, mis2);
  printf("selftest 1: allowed sets nu=0 %lld, nu=1 %lld (expected 2816 each)\n", cnt[0], cnt[1]);
  if (mis1 || mis2 || cnt[0] != 2816 || cnt[1] != 2816) bad++;

  for (int D : {18, 60, 120}) {
    std::vector<uint32_t> sat[2];
    for (int i = 1; i <= D - 1; i++)
      for (int j = 0; j <= D - 1; j++) {
        const int nu = (i > j) ? 1 : 0;
        uint32_t m = 0;
        for (int ty = 0; ty < 20; ty++) {
          const ll n = TYn[ty], e = TYe[ty], b = TYb[ty];
          if (b * i <= e * D + j && e * D + j < (n - b) * i + b * D) m |= 1u << ty;
        }
        sat[nu].push_back(m);
      }
    for (int nu = 0; nu < 2; nu++) {
      std::sort(sat[nu].begin(), sat[nu].end());
      sat[nu].erase(std::unique(sat[nu].begin(), sat[nu].end()), sat[nu].end());
    }
    ll mis = 0;
    for (int nu = 0; nu < 2; nu++)
      for (uint32_t mask = 0; mask < (1u << 20); mask++) {
        bool g = false;
        for (uint32_t s : sat[nu])
          if ((s & mask) == mask) { g = true; break; }
        if (g != fmTwoSided(nu, mask)) mis++;
      }
    printf("selftest 2: grid D=%d: %zu+%zu distinct point masks, mismatches with the decision %lld\n", D,
           sat[0].size(), sat[1].size(), mis);
    if (mis) bad++;
  }

  {
    std::mt19937_64 g(12345);
    ll tests = 0, mis = 0;
    for (int k = 2; k <= 8; k++)
      for (int rep = 0; rep < 4000; rep++) {
        std::vector<uint8_t> h(k - 1, 0);
        std::vector<int> items;
        const int m = (int)(g() % 11);
        for (int t = 0; t < m; t++) {
          const int C = 1 + (int)(g() % (k - 1));
          h[C - 1]++;
          items.push_back(C);
        }
        std::sort(items.rbegin(), items.rend());
        int L[3] = {0, 0, 0};
        const bool a = splits3(h.data(), k), b = splitBrute(items, k - 1, 0, L);
        tests++;
        if (a != b) mis++;
      }
    printf("selftest 3: split test vs brute force: %lld cases, %lld mismatches\n", tests, mis);
    if (mis) bad++;
  }

  {
    ll mis = 0, tested = 0;
    for (ll F : {1LL, 2LL, 5LL, 12LL, 27LL, 64LL}) {
      P.F = F;
      setRadices();
      for (ll N = 0; N <= 3 * F; N++) {
        std::unordered_set<ll> seen;
        for (ll e = 0; e <= 2; e++)
          for (ll a = 0; 3 * a <= N + e; a++)
            for (ll b = a; a + 2 * b <= N + e; b++) {
              const ll c = N + e - a - b;
              if (c < b) continue;
              const ll code = encodeTriple(N, a, b, c);
              ll t[3];
              tested++;
              if (code < 0 || code >= P.RT) { mis++; continue; }
              decodeTriple(N, code, t);
              if (t[0] != a || t[1] != b || t[2] != c) mis++;
              if (!seen.insert(code).second) mis++;
            }
      }
    }
    printf("selftest 4: triple codes: %lld triples, %lld errors\n", tested, mis);
    if (mis) bad++;
  }

  {
    Table<uint64_t> t64;
    t64.init(100000);
    Table<u128> t128;
    t128.init(100000);
    std::mt19937_64 g(777);
    std::vector<uint64_t> keys;
    ll mis = 0;
    for (int i = 0; i < 100000; i++) {
      const uint64_t key = g() >> 1;
      keys.push_back(key);
      const bool ins = t64.insert(key, i);
      const bool ins2 = t128.insert(((u128)key << 64) | (u128)(key * 3u), i);
      if (!ins || !ins2) mis++;
    }
    for (int i = 0; i < 100000; i++) {
      const auto* a = t64.find(keys[i]);
      const auto* b = t128.find(((u128)keys[i] << 64) | (u128)(keys[i] * 3u));
      if (!a || a->T != i || !b || b->T != i) mis++;
      if (t64.insert(keys[i], 5)) mis++;
      if (t64.find(keys[i] ^ (1ULL << 63))) mis++;
    }
    printf("selftest 5: hash tables: %lld errors\n", mis);
    if (mis) bad++;
  }
  printf("SELFTEST %s\n", bad ? "FAIL" : "PASS");
  return bad ? 1 : 0;
}

int main(int argc, char** argv) {
  initTypes();
  if (argc == 2 && strcmp(argv[1], "--selftest") == 0) return selftest();
  if (argc != 2) {
    fprintf(stderr, "usage: %s <certificate> | --selftest\n", argv[0]);
    return 2;
  }
  const double tStart = wallNow();
  size_t len = 0;
  std::string err;
  char* buf = readFile(argv[1], len, err);
  if (!buf) failExit(1, "-", err);

  const char* p = buf;
  const char* const end = buf + len;
  ll lineNo = 0, nStates = 0, expectTok = 0;
  bool haveHeader = false;
  const int MAXT = 128;
  const char* tS[MAXT];
  const char* tE[MAXT];
  ll vals[MAXT];
  while (p < end) {
    const char* nl = (const char*)memchr(p, '\n', (size_t)(end - p));
    const char* le = nl ? nl : end;
    lineNo++;
    const char* s = p;
    while (s < le && (*s == ' ' || *s == '\t')) s++;
    if (!nl) failExit(1, haveHeader ? S(nStates) : "-", "line " + S(lineNo) + " does not end with a newline");
    p = nl + 1;
    if (s == le || *s == '#') continue;
    int nt = 0;
    bool tooMany = false;
    while (s < le) {
      if (*s == ' ' || *s == '\t') { s++; continue; }
      if (nt == MAXT) { tooMany = true; break; }
      tS[nt] = s;
      while (s < le && *s != ' ' && *s != '\t') s++;
      tE[nt] = s;
      nt++;
    }
    if (!haveHeader) {
      const std::string L = "line " + S(lineNo) + ": ";
      if (!(tE[0] - tS[0] == 7 && memcmp(tS[0], "RG3CERT", 7) == 0))
        failExit(1, "-", L + "the first line that is not a comment must start with RG3CERT");
      if (tooMany) failExit(1, "-", L + "too many tokens in the header");
      if (nt < 4) failExit(1, "-", L + "the header is too short");
      for (int i = 1; i < nt; i++)
        if (!parseNum(tS[i], tE[i], vals[i]))
          failExit(1, "-", L + "header token " + S(i + 1) + " is not a decimal integer of at most 18 digits");
      P.k = vals[1]; P.r = vals[2]; P.K = vals[3];
      if (P.K < 1 || P.K > 8) failExit(1, "-", L + "K=" + S(P.K) + " is not in 1..8");
      if (nt != P.K + 6) failExit(1, "-", L + "the header has " + S(nt) + " tokens, expected K+6=" + S(P.K + 6));
      P.W = 0;
      for (ll j = 0; j < P.K; j++) { P.w[j] = vals[4 + j]; P.W += (u128)P.w[j]; }
      P.T0 = vals[4 + P.K];
      P.n = vals[5 + P.K];
      if (P.k < 2) failExit(1, "-", L + "k=" + S(P.k) + " < 2");
      if (P.r < 1) failExit(1, "-", L + "r=0");
      for (ll j = 0; j < P.K; j++)
        if (P.w[j] < 1) failExit(1, "-", L + "weight w_" + S(j + 1) + "=0");
      if (P.n < 1) failExit(1, "-", L + "n=0");
      if (P.k > LIM_k) failExit(1, "-", L + "checker limit: k=" + S(P.k) + " > " + S(LIM_k));
      if ((i128)P.k * (i128)P.r > (i128)LIM_F) failExit(1, "-", L + "checker limit: F=k*r > " + S(LIM_F));
      P.F = P.k * P.r;
      setRadices();
      expectTok = P.k + 3 * P.K + 1;
      const ll est = (ll)(len / (size_t)(2 * expectTok)) + 1;
      const ll res = std::min(P.n, est);
      sH.reserve((size_t)res); sN.reserve((size_t)res); sT.reserve((size_t)res);
      sCode.reserve((size_t)(res * P.K));
      haveHeader = true;
      continue;
    }
    if (nStates >= P.n)
      failExit(1, S(nStates), "line " + S(lineNo) + ": more than n=" + S(P.n) + " state lines");
    if (tooMany || nt != expectTok)
      failExit(1, S(nStates), "line " + S(lineNo) + ": " + (tooMany ? std::string("too many") : S(nt)) +
                                  " tokens, expected " + S(expectTok));
    for (int i = 0; i < nt; i++)
      if (!parseNum(tS[i], tE[i], vals[i]))
        failExit(1, S(nStates), "line " + S(lineNo) + ": token " + S(i + 1) +
                                    " is not a decimal integer of at most 18 digits");
    const ll* q = vals + P.k;
    for (ll j = 0; j < P.K; j++)
      if (!(q[3 * j] <= q[3 * j + 1] && q[3 * j + 1] <= q[3 * j + 2]))
        failExit(1, S(nStates), "line " + S(lineNo) + ": the triple of copy " + S(j + 1) + " is not sorted");
    processState(nStates, vals);
    nStates++;
  }
  if (!haveHeader) failExit(1, "-", "no header line");
  if (nStates < P.n)
    failExit(1, S(nStates), "the file ends after " + S(nStates) + " state lines, the header says n=" + S(P.n));
  free(buf);

  if (v2.id >= 0) failExit(2, "0", v2.why);

  u128 prod = (u128)std::max<ll>((ll)hList.size(), 1);
  bool over = __builtin_mul_overflow(prod, (u128)P.RN, &prod);
  for (ll j = 0; j < P.K && !over; j++) over = __builtin_mul_overflow(prod, (u128)P.RT, &prod);
  const char* f128 = getenv("C3A_FORCE128");
  const bool force128 = f128 && strcmp(f128, "1") == 0;
  if (!over && prod <= (u128)UINT64_MAX && !force128) return runChecks<uint64_t>(nStates, tStart);
  if (!over) return runChecks<u128>(nStates, tStart);
  failExit(3, "-", "checker limit: the state keys need more than 128 bits");
}
