// sim3.cpp: runs the lottery of an rg3.cpp certificate on real inputs with exact loads (paper, App. F).
// At every job it checks that the state is listed, that the move is answered and that the cost is within the bound.
// g++ -O2 -std=c++17 -fopenmp -o sim3 sim3.cpp && ./sim3 FILE [threads=T]
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <array>
#include <map>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <atomic>
#include <chrono>
#include <sys/types.h>
#include <omp.h>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;
typedef __int128 i128;

static const int MAXK = 8;
static const int MAXCLS = 64;
static const int KLMAX = MAXCLS + 3 * MAXK;

static double wall() {
  return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();
}
static string s128(i128 v) {
  if (v == 0) return "0";
  bool neg = v < 0;
  if (neg) v = -v;
  string s;
  while (v > 0) { s += char('0' + (int)(v % 10)); v /= 10; }
  if (neg) s += '-';
  reverse(s.begin(), s.end());
  return s;
}
static string fracs(i128 p, i128 q) {
  i128 a = p < 0 ? -p : p, b = q;
  while (b) { i128 t = a % b; a = b; b = t; }
  if (a == 0) a = 1;
  return s128(p / a) + "/" + s128(q / a);
}

struct Rng {
  ull s[4];
  static ull smix(ull& x) {
    ull z = (x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
  }
  explicit Rng(ull seed = 1, ull stream = 0) {
    ull x = seed * 0x2545F4914F6CDD1DULL ^ (stream * 0xD1B54A32D192ED03ULL) ^ 0x8BADF00DULL;
    for (int i = 0; i < 4; i++) s[i] = smix(x);
  }
  static inline ull rotl(ull x, int k) { return (x << k) | (x >> (64 - k)); }
  ull next() {
    ull res = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
    return res;
  }
  ll range(ll lo, ll hi) {
    if (hi <= lo) return lo;
    ull span = (ull)(hi - lo) + 1ULL;
    return lo + (ll)(next() % span);
  }
  double uni() { return (double)(next() >> 11) * (1.0 / 9007199254740992.0); }
  bool coin(double p) { return uni() < p; }
};

static bool parse_nums(const char* s, ssize_t len, vector<ull>& out, string& why) {
  out.clear();
  ssize_t i = 0;
  auto blank = [](char ch) { return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n'; };
  while (true) {
    while (i < len && blank(s[i])) i++;
    if (i >= len) break;
    if (s[i] < '0' || s[i] > '9') { why = string("unexpected character '") + s[i] + "'"; return false; }
    ull v = 0;
    int nd = 0;
    while (i < len && s[i] >= '0' && s[i] <= '9') {
      v = v * 10 + (ull)(s[i] - '0');
      i++;
      if (++nd > 18) { why = "number with more than 18 digits"; return false; }
    }
    if (i < len && !blank(s[i])) { why = string("unexpected character '") + s[i] + "'"; return false; }
    out.push_back(v);
  }
  return true;
}

struct Cert {
  string path, err;
  int k = 0, r = 0, K = 0, F = 0, klen = 0;
  ll W = 0, T0 = 0, n = 0, w[MAXK];
  vector<uint16_t> keys;
  vector<ll> pot;
  vector<ull> slot;
  ull mask = 0;
  ll dup = 0, big = 0, unsorted = 0, rootId = -1;

  static ull hk(const uint16_t* a, int len) {
    ull h = 0x243F6A8885A308D3ULL ^ ((ull)len * 0x9E3779B97F4A7C15ULL);
    int i = 0;
    for (; i + 4 <= len; i += 4) {
      ull v = (ull)a[i] | ((ull)a[i + 1] << 16) | ((ull)a[i + 2] << 32) | ((ull)a[i + 3] << 48);
      h = (h ^ v) * 0x9E3779B97F4A7C15ULL;
      h ^= h >> 31;
    }
    ull v = 0;
    int sh = 0;
    for (; i < len; i++, sh += 16) v |= (ull)a[i] << sh;
    h = (h ^ v) * 0xBF58476D1CE4E5B9ULL;
    h ^= h >> 29;
    h *= 0x94D049BB133111EBULL;
    h ^= h >> 32;
    return h;
  }
  ll find(const uint16_t* key) const {
    ull h = hk(key, klen), tag = h >> 36, i = h & mask;
    while (true) {
      ull s = slot[i];
      if (!s) return -1;
      if ((s >> 36) == tag) {
        ll id = (ll)(s & 0xfffffffffULL) - 1;
        if (!memcmp(&keys[(size_t)id * klen], key, (size_t)klen * 2)) return id;
      }
      i = (i + 1) & mask;
    }
  }
  bool load(const string& p) {
    path = p;
    FILE* f = fopen(p.c_str(), "r");
    if (!f) { err = "cannot open file"; return false; }
    char* line = nullptr;
    size_t cap = 0;
    ssize_t len;
    bool hdr = false;
    ll cnt = 0, lineno = 0;
    vector<ull> tok;
    string why;
    vector<char> skip;
    while ((len = getline(&line, &cap, f)) != -1) {
      lineno++;
      ssize_t i = 0;
      while (i < len && (line[i] == ' ' || line[i] == '\t' || line[i] == '\r' || line[i] == '\n')) i++;
      if (i >= len || line[i] == '#') continue;
      if (!hdr) {
        if (len - i < 7 || strncmp(line + i, "RG3CERT", 7) != 0 ||
            (len - i > 7 && !(line[i + 7] == ' ' || line[i + 7] == '\t' || line[i + 7] == '\r' || line[i + 7] == '\n'))) {
          err = "line " + to_string(lineno) + ": first line is not an RG3CERT header";
          break;
        }
        if (!parse_nums(line + i + 7, len - i - 7, tok, why)) { err = "header: " + why; break; }
        if (tok.size() < 6) { err = "header too short"; break; }
        if (tok[0] < 2 || tok[0] > (ull)MAXCLS) { err = "k out of range for this simulator (2..64)"; break; }
        if (tok[1] < 1 || tok[1] > 1000) { err = "r out of range"; break; }
        if (tok[2] < 1 || tok[2] > (ull)MAXK) { err = "K out of range"; break; }
        k = (int)tok[0]; r = (int)tok[1]; K = (int)tok[2];
        if ((int)tok.size() != 3 + K + 2) {
          err = "header has " + to_string(tok.size()) + " numbers, expected " + to_string(3 + K + 2);
          break;
        }
        W = 0;
        for (int j = 0; j < K; j++) {
          if (tok[3 + j] < 1 || tok[3 + j] > 1000000) { err = "weight out of range (1..10^6 here)"; break; }
          w[j] = (ll)tok[3 + j];
          W += w[j];
        }
        if (!err.empty()) break;
        T0 = (ll)tok[3 + K];
        n = (ll)tok[4 + K];
        if (n < 1 || n > 60000000000LL) { err = "n out of range"; break; }
        F = k * r;
        klen = k + 3 * K;
        if (F > 5000) { err = "F too large for this simulator"; break; }
        keys.assign((size_t)n * klen, 0);
        pot.assign((size_t)n, 0);
        skip.assign((size_t)n, 0);
        hdr = true;
        continue;
      }
      if (cnt >= n) { err = "line " + to_string(lineno) + ": more than n state lines"; break; }
      if (!parse_nums(line + i, len - i, tok, why)) { err = "line " + to_string(lineno) + ": " + why; break; }
      if ((int)tok.size() != klen + 1) {
        err = "line " + to_string(lineno) + ": " + to_string(tok.size()) + " numbers, expected " + to_string(klen + 1);
        break;
      }
      uint16_t* kp = &keys[(size_t)cnt * klen];
      for (int a = 0; a < klen; a++) {
        if (tok[a] > 65535) { skip[cnt] = 1; kp[a] = 65535; }
        else kp[a] = (uint16_t)tok[a];
      }
      if (skip[cnt]) big++;
      for (int j = 0; j < K; j++) {
        const uint16_t* q = kp + k + 3 * j;
        if (!(q[0] <= q[1] && q[1] <= q[2])) { unsorted++; break; }
      }
      pot[cnt] = (ll)tok[klen];
      cnt++;
    }
    free(line);
    fclose(f);
    if (err.empty() && !hdr) err = "no RG3CERT header";
    if (err.empty() && cnt != n) err = "file has " + to_string(cnt) + " state lines, header says " + to_string(n);
    if (!err.empty()) return false;
    ull sz = 16;
    while (sz < (ull)n * 2) sz <<= 1;
    slot.assign(sz, 0);
    mask = sz - 1;
    for (ll id = 0; id < n; id++) {
      if (skip[id]) continue;
      const uint16_t* kp = &keys[(size_t)id * klen];
      ull h = hk(kp, klen), tag = h >> 36, i = h & mask;
      bool isdup = false;
      while (slot[i]) {
        if ((slot[i] >> 36) == tag) {
          ll o = (ll)(slot[i] & 0xfffffffffULL) - 1;
          if (!memcmp(&keys[(size_t)o * klen], kp, (size_t)klen * 2)) { isdup = true; break; }
        }
        i = (i + 1) & mask;
      }
      if (isdup) { dup++; continue; }
      slot[i] = (tag << 36) | (ull)(id + 1);
    }
    uint16_t z[KLMAX];
    memset(z, 0, sizeof z);
    rootId = find(z);
    return true;
  }
};

static bool tab_interval(int n, int e, int b, int nu, int& lo, int& hi) {
  int eps = e - nu;
  if (n < 1 || n > 3 || b < 0 || b > n) return false;
  if (eps == -1) { if (b == 0) { lo = 1; hi = 4; return true; } return false; }
  if (eps == n - 1) { if (b == n) { lo = 1; hi = 4; return true; } return false; }
  static const int T20[3][2] = {{3, 4}, {1, 4}, {1, 2}};
  static const int T30[4][2] = {{2, 4}, {1, 4}, {1, 2}, {1, 1}};
  static const int T31[4][2] = {{4, 4}, {3, 4}, {1, 4}, {1, 3}};
  if (n == 2 && eps == 0) { lo = T20[b][0]; hi = T20[b][1]; return true; }
  if (n == 3 && eps == 0) { lo = T30[b][0]; hi = T30[b][1]; return true; }
  if (n == 3 && eps == 1) { lo = T31[b][0]; hi = T31[b][1]; return true; }
  return false;
}

static bool fm_allowed(int nu, int cnt, const int* tn, const int* te, const int* tb) {
  int Lm[MAXK + 64], Ld[MAXK + 64], Um[MAXK + 64], Ud[MAXK + 64];
  int nl = 0, nup = 0;
  Lm[nl] = 0; Ld[nl] = 0; nl++;
  Um[nup] = 0; Ud[nup] = -1; nup++;
  if (nu) { Um[nup] = 1; Ud[nup] = 0; nup++; }
  else { Lm[nl] = 1; Ld[nl] = 0; nl++; }
  for (int j = 0; j < cnt; j++) {
    if (tb[j] <= te[j]) { Um[nup] = tn[j] - tb[j]; Ud[nup] = te[j] - tb[j]; nup++; }
    else { Lm[nl] = tb[j]; Ld[nl] = te[j]; nl++; }
  }
  ll lop = 0, loq = 1, hip = 1, hiq = 1;
  for (int a = 0; a < nl; a++)
    for (int b = 0; b < nup; b++) {
      ll A = Lm[a] - Um[b], R = Ld[a] - Ud[b];
      if (A == 0) { if (R <= 0) return false; continue; }
      if (A > 0) { if (R * hiq < hip * A) { hip = R; hiq = A; } }
      else { ll p = -R, q = -A; if (p * loq > lop * q) { lop = p; loq = q; } }
    }
  return lop * hiq < hip * loq;
}

static void joint_tests(int N, int nu, int K, const int q[][3], const uint8_t o[][3], bool& fm, bool& tb) {
  if (N == 0) {
    bool ok = (nu == 1);
    for (int j = 0; j < K; j++) for (int i = 0; i < 3; i++) if (!o[j][i]) ok = false;
    fm = tb = ok;
    return;
  }
  int tn[MAXK] = {0}, te[MAXK] = {0}, tbb[MAXK] = {0};
  for (int j = 0; j < K; j++) {
    int n = 0, b = 0, sum = 0;
    bool ez = false;
    for (int i = 0; i < 3; i++) {
      sum += q[j][i];
      if (q[j][i] > 0) { n++; if (!o[j][i]) b++; }
      else if (!o[j][i]) ez = true;
    }
    if (ez) { fm = tb = false; return; }
    tn[j] = n; te[j] = sum - N; tbb[j] = b;
  }
  fm = fm_allowed(nu, K, tn, te, tbb);
  int lo = 1, hi = 4;
  bool ok = true;
  for (int j = 0; j < K && ok; j++) {
    int a, bb;
    if (!tab_interval(tn[j], te[j], tbb[j], nu, a, bb)) { ok = false; break; }
    lo = max(lo, a); hi = min(hi, bb);
  }
  tb = ok && lo <= hi;
}

static bool splits_rec(const int* it, const int* suf, int m, int i, int* g, int cap) {
  if (i == m) return true;
  if (suf[i] > 3 * cap - g[0] - g[1] - g[2]) return false;
  for (int b = 0; b < 3; b++) {
    bool same = false;
    for (int a = 0; a < b; a++) if (g[a] == g[b]) same = true;
    if (same) continue;
    if (g[b] + it[i] <= cap) {
      g[b] += it[i];
      bool ok = splits_rec(it, suf, m, i + 1, g, cap);
      g[b] -= it[i];
      if (ok) return true;
    }
  }
  return false;
}
static bool splits3(const uint16_t* H, int k) {
  int it[3 * MAXCLS + 4], suf[3 * MAXCLS + 5];
  int m = 0;
  ll tot = 0;
  for (int C = k - 1; C >= 1; C--)
    for (int a = 0; a < H[C]; a++) {
      if (m >= 3 * MAXCLS) return false;
      it[m++] = C;
      tot += C;
    }
  if (tot > 3LL * (k - 1)) return false;
  suf[m] = 0;
  for (int i = m - 1; i >= 0; i--) suf[i] = suf[i + 1] + it[i];
  int g[3] = {0, 0, 0};
  return splits_rec(it, suf, m, 0, g, k - 1);
}

struct Feas {
  int B = 0, W = 0, minrow = 0;
  ll tot = 0;
  vector<ull> bits;
  void init(int B_) {
    B = B_;
    W = (B + 1 + 63) / 64;
    bits.assign((size_t)(B + 1) * W, 0ULL);
    bits[0] = 1ULL;
    tot = 0;
    minrow = 0;
  }
  const ull* row(int a) const { return &bits[(size_t)a * W]; }
  ull* row(int a) { return &bits[(size_t)a * W]; }
};

static bool feas_add(const Feas& in, int S, Feas& out) {
  const int B = in.B, W = in.W;
  if (out.B != B || (int)out.bits.size() != (B + 1) * W) {
    out.B = B; out.W = W;
    out.bits.assign((size_t)(B + 1) * W, 0ULL);
  }
  out.tot = in.tot + S;
  const int rb = (B + 1) % 64;
  const ull lastmask = rb == 0 ? ~0ULL : ((1ULL << rb) - 1ULL);
  const int ws = S / 64, bs = S % 64;
  int minrow = -1;
  const ll amax = min<ll>(B, out.tot);
  for (int a = 0; a <= B; a++) {
    ull* dst = out.row(a);
    if (a > amax) { memset(dst, 0, sizeof(ull) * W); continue; }
    const ull* src = in.row(a);

    for (int i = W - 1; i >= 0; --i) {
      int si = i - ws;
      ull v = 0;
      if (si >= 0) {
        v = src[si] << bs;
        if (bs && si - 1 >= 0) v |= src[si - 1] >> (64 - bs);
      }
      dst[i] = v;
    }
    dst[W - 1] &= lastmask;

    if (a >= S) {
      const ull* s2 = in.row(a - S);
      for (int i = 0; i < W; i++) dst[i] |= s2[i];
    }

    ll lo3 = out.tot - B - a;
    if (lo3 <= B) {
      int lo = (int)max<ll>(lo3, 0);
      int wi = lo / 64, bi = lo % 64;
      if (wi < W) {
        dst[wi] |= src[wi] & (~0ULL << bi);
        for (int i = wi + 1; i < W; i++) dst[i] |= src[i];
      }
    }
    if (minrow < 0)
      for (int i = 0; i < W; i++) if (dst[i]) { minrow = a; break; }
  }
  out.minrow = minrow < 0 ? B + 1 : minrow;
  return minrow >= 0;
}

struct RS {
  ll L[MAXK][3];
  ll V, sid, T;
  int N;
  uint16_t H[MAXCLS];
};
struct MoveInfo {
  ll c, t;
  int Cc, nu, Nn;
  int perm[MAXK][3];
  int q[MAXK][3];
  uint8_t o[MAXK][3];
};
static inline void order3(const ll* R, int* p) {
  p[0] = 0; p[1] = 1; p[2] = 2;
  for (int i = 1; i < 3; i++) {
    int v = p[i], j = i - 1;
    while (j >= 0 && (R[p[j]] > R[v] || (R[p[j]] == R[v] && p[j] > v))) { p[j + 1] = p[j]; j--; }
    p[j + 1] = v;
  }
}
static inline void sort3i(int& a, int& b, int& c) {
  if (a > b) swap(a, b);
  if (b > c) swap(b, c);
  if (a > b) swap(a, b);
}
static void compute_move(int K, ll d, int r, const ll L[][3], ll V, int N, ll S, MoveInfo& mv) {
  mv.c = (S - 1) / d;
  mv.t = S - mv.c * d;
  mv.Cc = (int)(mv.c / r);
  ll x = (ll)N * d - V;
  mv.nu = (mv.t > x) ? 1 : 0;
  mv.Nn = N + (int)mv.c + mv.nu;
  for (int j = 0; j < K; j++) {
    ll R[3];
    for (int b = 0; b < 3; b++) R[b] = (L[j][b] + d - 1) / d;
    order3(R, mv.perm[j]);
    for (int i = 0; i < 3; i++) {
      int b = mv.perm[j][i];
      mv.q[j][i] = (int)R[b];
      ll fr = R[b] * d - L[j][b];
      mv.o[j][i] = (mv.t > fr) ? 1 : 0;
    }
  }
}
static bool lemma31ii(int K, ll d, const RS& s) {
  ll x = (ll)s.N * d - s.V;
  if (x < 0 || x >= d) return false;
  for (int j = 0; j < K; j++) {
    int n = 0;
    ll sumR = 0, sumF = 0, sumL = 0;
    for (int b = 0; b < 3; b++) {
      ll L = s.L[j][b];
      if (L < 0) return false;
      ll R = (L + d - 1) / d;
      if (L > 0) n++;
      sumR += R; sumF += R * d - L; sumL += L;
    }
    if (sumL != s.V) return false;
    ll e = sumR - s.N;
    if (s.N == 0) { if (sumR != 0) return false; continue; }
    if (n < 1 || e < 0 || e > n - 1) return false;
    if (sumF != e * d + x) return false;
  }
  return true;
}

enum { ST_OK = 0, ST_NOTLISTED = 1, ST_NORESP = 2, ST_MISMATCH = 3, ST_COST = 4 };
enum { DG_M2 = 1, DG_M3 = 2, DG_M4 = 4, DG_TABFM = 8, DG_L31 = 16, DG_PAY = 32, DG_COSTT = 64 };
static const char* DGNAME[7] = {"M2", "M3", "M4", "table!=elimination", "invariant(ii)", "payoff>potential",
                                "cost>potential"};

static int g_inject = 0;
struct Ctx {
  const Cert* C = nullptr;
  ll d = 1;
  int inject = g_inject;
  unordered_map<string, char> m3;
  bool m3check(const uint16_t* H, int Cc, int k) {
    string key((size_t)2 * k, '\0');
    for (int a = 1; a < k; a++) {
      unsigned v = H[a] + (a == Cc ? 1u : 0u);
      key[2 * a] = (char)(v & 255u);
      key[2 * a + 1] = (char)(v >> 8);
    }
    auto it = m3.find(key);
    if (it != m3.end()) return it->second != 0;
    uint16_t H2[MAXCLS];
    memcpy(H2, H, sizeof(uint16_t) * MAXCLS);
    H2[Cc]++;
    bool ok = splits3(H2, k);
    if (m3.size() > 4000000) m3.clear();
    m3.emplace(key, ok ? 1 : 0);
    return ok;
  }
};
struct StepRes {
  int status, diag;
  ll cost, found;
  bool realListed, novel;
  MoveInfo mv;
  int resp[MAXK];
};

static vector<ull> g_seen;
static inline bool mark_seen(ll id) {
  if (g_seen.empty()) return false;
  ull bit = 1ULL << (id & 63);
  ull* wp = &g_seen[(size_t)(id >> 6)];
  if (__atomic_load_n(wp, __ATOMIC_RELAXED) & bit) return false;
  ull old = __atomic_fetch_or(wp, bit, __ATOMIC_RELAXED);
  return !(old & bit);
}
static ll count_seen() {
  ll c = 0;
  for (ull v : g_seen) c += __builtin_popcountll(v);
  return c;
}

static inline bool done_step(const StepRes& r) { return r.status == ST_OK || r.status == ST_COST; }
static void real_key(const Cert& C, ll d, const RS& s, uint16_t* rk) {
  const int k = C.k, K = C.K;
  rk[0] = (uint16_t)s.N;
  for (int a = 1; a < k; a++) rk[a] = s.H[a];
  for (int j = 0; j < K; j++) {
    int a0 = (int)((s.L[j][0] + d - 1) / d), a1 = (int)((s.L[j][1] + d - 1) / d), a2 = (int)((s.L[j][2] + d - 1) / d);
    sort3i(a0, a1, a2);
    rk[k + 3 * j] = (uint16_t)a0; rk[k + 3 * j + 1] = (uint16_t)a1; rk[k + 3 * j + 2] = (uint16_t)a2;
  }
}
static void root_rs(const Cert& C, RS& s) {
  memset(&s, 0, sizeof(RS));
  s.sid = C.rootId;
  s.T = C.rootId >= 0 ? C.pot[C.rootId] : 0;
}

static void step(Ctx& X, const RS& cur, ll S, RS& nx, StepRes& res) {
  const Cert& C = *X.C;
  const int K = C.K, k = C.k, F = C.F;
  const ll d = X.d;
  res.status = ST_OK; res.diag = 0; res.cost = 0; res.found = -1; res.realListed = true; res.novel = false;
  MoveInfo& mv = res.mv;
  compute_move(K, d, C.r, cur.L, cur.V, cur.N, S, mv);

  {
    const uint16_t* lk = &C.keys[(size_t)cur.sid * C.klen];
    bool same = (lk[0] == (uint16_t)cur.N);
    for (int a = 1; a < k && same; a++) same = (lk[a] == cur.H[a]);
    for (int j = 0; j < K && same; j++)
      for (int i = 0; i < 3; i++) if (lk[k + 3 * j + i] != mv.q[j][i]) { same = false; break; }
    if (!same) { res.status = ST_NOTLISTED; return; }
  }

  if (mv.Nn > 3 * F) res.diag |= DG_M2;
  if (mv.Cc >= 1 && !X.m3check(cur.H, mv.Cc, k)) res.diag |= DG_M3;
  {
    bool fm, tb;
    joint_tests(cur.N, mv.nu, K, mv.q, mv.o, fm, tb);
    if (!fm) res.diag |= DG_M4;
    if (fm != tb) res.diag |= DG_TABFM;
  }

  int nq[MAXK][3][3];
  for (int j = 0; j < K; j++)
    for (int i = 0; i < 3; i++) {
      int a[3] = {mv.q[j][0], mv.q[j][1], mv.q[j][2]};
      int bit = mv.o[j][i];
      if (X.inject == 1 && j == 0) bit ^= 1;
      a[i] += (int)mv.c + bit;
      sort3i(a[0], a[1], a[2]);
      nq[j][i][0] = a[0]; nq[j][i][1] = a[1]; nq[j][i][2] = a[2];
    }
  uint16_t key[KLMAX];
  key[0] = (uint16_t)mv.Nn;
  for (int a = 1; a < k; a++) key[a] = cur.H[a];
  if (mv.Cc >= 1) key[mv.Cc]++;
  int idx[MAXK];
  for (int j = 0; j < K; j++) {
    idx[j] = 0;
    for (int a = 0; a < 3; a++) key[k + 3 * j + a] = (uint16_t)nq[j][0][a];
  }

  ll found = -1;
  while (true) {
    ll id = C.find(key);
    if (id >= 0 && C.pot[id] <= cur.T) { found = id; break; }
    int j = K - 1;
    while (j >= 0) {
      idx[j]++;
      if (idx[j] < 3) {
        for (int a = 0; a < 3; a++) key[k + 3 * j + a] = (uint16_t)nq[j][idx[j]][a];
        break;
      }
      idx[j] = 0;
      for (int a = 0; a < 3; a++) key[k + 3 * j + a] = (uint16_t)nq[j][0][a];
      j--;
    }
    if (j < 0) break;
  }
  if (found < 0) { res.status = ST_NORESP; return; }
  res.found = found;
  res.novel = mark_seen(found);
  for (int j = 0; j < K; j++) res.resp[j] = idx[j] + 1;

  nx = cur;
  for (int j = 0; j < K; j++) {
    int rank = idx[j];
    if (X.inject == 2 && j == 0) rank = (rank + 1) % 3;
    nx.L[j][mv.perm[j][rank]] += S;
  }
  nx.V = cur.V + S;
  nx.N = (int)((nx.V + d - 1) / d);
  if (mv.Cc >= 1) nx.H[mv.Cc]++;
  nx.sid = found;
  nx.T = C.pot[found];

  uint16_t rk[KLMAX];
  real_key(C, d, nx, rk);
  if (memcmp(rk, key, (size_t)C.klen * 2) != 0) {
    res.status = ST_MISMATCH;
    res.realListed = C.find(rk) >= 0;
    return;
  }

  ll cost = 0;
  for (int j = 0; j < K; j++) cost += C.w[j] * max(nx.L[j][0], max(nx.L[j][1], nx.L[j][2]));
  res.cost = cost;
  if ((i128)cost > (i128)C.T0 * d) res.status = ST_COST;

  i128 P = 0;
  for (int j = 0; j < K; j++) P += (i128)C.w[j] * key[k + 3 * j + 2];
  if (P > (i128)nx.T) res.diag |= DG_PAY;
  if ((i128)cost > (i128)nx.T * d) res.diag |= DG_COSTT;
  if (!lemma31ii(K, d, nx)) res.diag |= DG_L31;
}

struct Stats {
  ll inputs = 0, prefixes = 0, fails = 0, diagFails = 0;
  ll byCheck[5] = {0, 0, 0, 0, 0};
  ll byDiag[7] = {0, 0, 0, 0, 0, 0, 0};
  ll worstX = -1, worstD = 1;
  vector<ll> worstIn;
  vector<string> msgs;
  int maxPrint = 100;
  inline void cost(ll X, ll d, const ll* in, int len) {
    if (worstX < 0 || (i128)X * worstD > (i128)worstX * d) {
      worstX = X; worstD = d;
      worstIn.assign(in, in + len);
    }
  }
  void merge(const Stats& o) {
    inputs += o.inputs; prefixes += o.prefixes; fails += o.fails; diagFails += o.diagFails;
    for (int i = 0; i < 5; i++) byCheck[i] += o.byCheck[i];
    for (int i = 0; i < 7; i++) byDiag[i] += o.byDiag[i];
    if (o.worstX >= 0 && (worstX < 0 || (i128)o.worstX * worstD > (i128)worstX * o.worstD)) {
      worstX = o.worstX; worstD = o.worstD; worstIn = o.worstIn;
    }
    for (auto& m : o.msgs) if ((int)msgs.size() < maxPrint) msgs.push_back(m);
  }
};
static string key_str(const uint16_t* key, int k, int K) {
  string s = "N=" + to_string(key[0]) + " H=(";
  for (int a = 1; a < k; a++) { if (a > 1) s += ","; s += to_string(key[a]); }
  s += ") q=";
  for (int j = 0; j < K; j++) {
    if (j) s += "/";
    s += "(" + to_string(key[k + 3 * j]) + "," + to_string(key[k + 3 * j + 1]) + "," + to_string(key[k + 3 * j + 2]) + ")";
  }
  return s;
}
static string input_str(const ll* in, int len, ll d) {
  string s = "d=" + to_string(d) + " sizes=[";
  for (int i = 0; i < len; i++) { if (i) s += ","; s += to_string(in[i]); }
  return s + "]";
}
static string move_str(const MoveInfo& mv, int K) {
  string s = "c=" + to_string(mv.c) + " t=" + to_string(mv.t) + " nu=" + to_string(mv.nu) + " bits=";
  for (int j = 0; j < K; j++) {
    if (j) s += "/";
    for (int i = 0; i < 3; i++) s += char('0' + mv.o[j][i]);
  }
  return s;
}
static void record_fail(Stats& st, char cls, const Ctx& X, const RS& cur, ll S, const StepRes& r, const ll* in, int len) {
  const Cert& C = *X.C;
  st.fails++;
  if (r.status) st.byCheck[r.status]++;
  if (r.diag) {
    st.diagFails++;
    for (int b = 0; b < 7; b++) if (r.diag >> b & 1) st.byDiag[b]++;
  }
  if ((int)st.msgs.size() >= st.maxPrint) return;
  string m = "FAIL class " + string(1, cls);
  if (r.status == ST_NOTLISTED) m += " check 1 (the real state is not the listed state)";
  else if (r.status == ST_NORESP) m += " check 2 (no response: the certificate does not answer this real move)";
  else if (r.status == ST_MISMATCH)
    m += string(" check 3 (real successor differs from the predicted one, real state ") + (r.realListed ? "listed" : "not listed") + ")";
  else if (r.status == ST_COST)
    m += " check 4 (weighted cost " + to_string(r.cost) + "/" + to_string(X.d) + " units > T0 = " + to_string(C.T0) + ")";
  if (r.diag) {
    m += " diagnostics:";
    for (int b = 0; b < 7; b++) if (r.diag >> b & 1) { m += " "; m += DGNAME[b]; }
  }
  m += " | state " + to_string(cur.sid) + " T=" + to_string(cur.T) + " " + key_str(&C.keys[(size_t)cur.sid * C.klen], C.k, C.K);
  m += " | job " + to_string(S) + " " + move_str(r.mv, C.K);
  if (r.found >= 0) {
    m += " response ";
    for (int j = 0; j < C.K; j++) m += to_string(r.resp[j]);
    m += " -> state " + to_string(r.found);
  }
  m += " | input " + input_str(in, len, X.d);
  st.msgs.push_back(m);
}
static bool attains(const Stats& st, const Cert& C) {
  return st.worstX >= 0 && (i128)st.worstX == (i128)C.T0 * st.worstD;
}
static string worst_str(const Stats& st, const Cert& C) {
  if (st.worstX < 0) return "none";
  return fracs(st.worstX, (i128)st.worstD * C.W * C.F);
}
static void print_stats(const string& label, const Stats& st, const Cert& C, double secs) {
  double wv = st.worstX < 0 ? 0.0 : (double)st.worstX / ((double)st.worstD * (double)C.W * (double)C.F);
  printf("%s: inputs %lld prefixes %lld failures %lld [check1 %lld check2 %lld check3 %lld check4 %lld diag %lld] "
         "worst %s = %.6f bound %s = %.6f attained %s time %.1fs\n",
         label.c_str(), st.inputs, st.prefixes, st.fails, st.byCheck[1], st.byCheck[2], st.byCheck[3], st.byCheck[4],
         st.diagFails, worst_str(st, C).c_str(), wv, fracs(C.T0, (i128)C.W * C.F).c_str(),
         (double)C.T0 / ((double)C.W * C.F), attains(st, C) ? "yes" : "no", secs);
  if (st.diagFails) {
    printf("  diagnostics:");
    for (int b = 0; b < 7; b++) if (st.byDiag[b]) printf(" %s %lld", DGNAME[b], st.byDiag[b]);
    printf("\n");
  }
  for (auto& m : st.msgs) printf("  %s\n", m.c_str());
  if (st.fails > (ll)st.msgs.size()) printf("  (%lld more failures not printed)\n", st.fails - (ll)st.msgs.size());
  if (st.worstX >= 0) {
    if (st.worstIn.size() <= 400)
      printf("  worst input: %s (weighted cost %lld/%lld units)\n", input_str(st.worstIn.data(), (int)st.worstIn.size(), st.worstD).c_str(), st.worstX, st.worstD);
    else
      printf("  worst input: %zu jobs with d=%lld (not printed; weighted cost %lld/%lld units)\n", st.worstIn.size(), st.worstD, st.worstX, st.worstD);
  }
  fflush(stdout);
}

static void sim_seq(Ctx& X, const vector<ll>& jobs, Stats& st, char cls) {
  RS a, b;
  root_rs(*X.C, a);
  st.inputs++;
  for (size_t i = 0; i < jobs.size(); i++) {
    StepRes r;
    step(X, a, jobs[i], b, r);
    st.prefixes++;
    if (done_step(r)) st.cost(r.cost, X.d, jobs.data(), (int)i + 1);
    if (r.status || r.diag) { record_fail(st, cls, X, a, jobs[i], r, jobs.data(), (int)i + 1); return; }
    a = b;
  }
}

enum { SY_INT, SY_ABOVE, SY_BELOW, SY_TINY, SY_MICRO, SY_TIE, SY_UNIF, SY_SMALL, SY_LARGE, SY_THIRD, SY_HALF,
       SY_CLASSB, SY_GRID, SY_ONE, NSY };
static const ll DLIST_A[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 24, 28, 30, 36, 40, 42,
                             48, 60, 72, 84, 90, 96, 120, 168, 180, 240, 360, 420, 720, 840, 1260, 2520, 5040, 27720,
                             55440, 720720};
static ll gen_size(int sy, Rng& g, ll d, const Cert& C, ll tieT, ll gstep) {
  const ll F = C.F, B = d * F;
  ll small = g.coin(0.5) ? 1 : g.range(1, max(1LL, d / 64));
  ll s = 1;
  switch (sy) {
    case SY_INT: s = d * g.range(1, F); break;
    case SY_ABOVE: s = d * g.range(0, F - 1) + small; break;
    case SY_BELOW: s = d * g.range(1, F) - small; break;
    case SY_TINY: s = g.range(1, max(1LL, d / 16)); break;
    case SY_MICRO: s = g.range(1, max(1LL, d / 400)); break;
    case SY_TIE: s = (g.coin(0.5) ? 0 : d * g.range(0, F - 1)) + tieT; break;
    case SY_UNIF: s = g.range(1, B); break;
    case SY_SMALL: s = g.range(1, 2 * d); break;
    case SY_LARGE: s = g.range(B / 2 + 1, B); break;
    case SY_THIRD: s = B / 3 + (g.range(0, 2) - 1) * small; break;
    case SY_HALF: s = B / 2 + (g.range(0, 2) - 1) * small; break;
    case SY_CLASSB: s = g.range(1, max(1, C.k - 1)) * (ll)C.r * d + (g.range(0, 2) - 1) * small; break;
    case SY_GRID: s = gstep * g.range(1, max(1LL, B / gstep)); break;
    case SY_ONE: s = d; break;
  }
  if (s < 1) s = 1;
  if (s > B) s = B;
  return s;
}
template <class T> static void shuffle_vec(vector<T>& v, Rng& g) {
  for (size_t i = v.size(); i > 1; i--) swap(v[i - 1], v[(size_t)g.range(0, (ll)i - 1)]);
}
static void build_input_a(const Cert& C, Rng& g, ll& d, vector<ll>& jobs, int maxJobs) {
  const int nD = (int)(sizeof(DLIST_A) / sizeof(DLIST_A[0]));
  d = DLIST_A[g.range(0, nD - 1)];
  const ll B = d * C.F;
  int ns = (int)g.range(1, 3), sy[3];
  for (int i = 0; i < ns; i++) sy[i] = (int)g.range(0, NSY - 1);
  ll tieCand[8] = {d, d / 2, d / 3, 2 * d / 3, d / 4, 3 * d / 4, g.range(1, d), d - 1};
  ll tieT = tieCand[g.range(0, 7)];
  if (tieT < 1) tieT = d;
  ll gstep = d;
  {
    static const int gl[8] = {2, 3, 4, 5, 6, 8, 10, 12};
    int gi = (int)g.range(0, 7);
    if (d % gl[gi] == 0) gstep = d / gl[gi];
  }
  vector<ll> bins[3];
  int total = 0;
  for (int b = 0; b < 3; b++) {
    ll target = g.coin(0.55) ? B : g.range(0, B);
    ll rem = target;
    int tries = 0;
    while (rem > 0 && total < maxJobs) {
      ll s = gen_size(sy[g.range(0, ns - 1)], g, d, C, tieT, gstep);
      if (s > rem) { if (++tries < 6) continue; s = rem; }
      tries = 0;
      bins[b].push_back(s);
      rem -= s;
      total++;
      if (g.coin(0.004)) break;
    }
  }
  for (int b = 0; b < 3; b++) {
    ll sum = 0;
    for (ll s : bins[b]) sum += s;
    if (sum > B) { fprintf(stderr, "internal error: witness packing overflows\n"); exit(3); }
  }
  jobs.clear();
  int ord = (int)g.range(0, 99);
  if (ord >= 76 && ord < 84) {
    int p[3] = {0, 1, 2};
    for (int i = 2; i > 0; i--) swap(p[i], p[g.range(0, i)]);
    for (int i = 0; i < 3; i++) jobs.insert(jobs.end(), bins[p[i]].begin(), bins[p[i]].end());
  } else if (ord >= 84 && ord < 92) {
    size_t mx = max(bins[0].size(), max(bins[1].size(), bins[2].size()));
    for (size_t i = 0; i < mx; i++)
      for (int b = 0; b < 3; b++) if (i < bins[b].size()) jobs.push_back(bins[b][i]);
  } else {
    for (int b = 0; b < 3; b++) jobs.insert(jobs.end(), bins[b].begin(), bins[b].end());
    if (ord < 60) shuffle_vec(jobs, g);
    else if (ord < 68) sort(jobs.begin(), jobs.end());
    else if (ord < 76) sort(jobs.rbegin(), jobs.rend());
    else {
      vector<ll> sm, lg;
      for (ll s : jobs) (s <= d ? sm : lg).push_back(s);
      shuffle_vec(sm, g);
      shuffle_vec(lg, g);
      jobs = sm;
      jobs.insert(jobs.end(), lg.begin(), lg.end());
    }
  }
}
static void run_a(const Cert& C, ll nIn, ull seed, int maxJobs, int nth, Stats& out, int maxPrint) {
  vector<Stats> per(nth);
  for (auto& s : per) s.maxPrint = maxPrint;
#pragma omp parallel num_threads(nth)
  {
    int tid = omp_get_thread_num();
    Ctx X;
    X.C = &C;
    vector<ll> jobs;
#pragma omp for schedule(dynamic, 16)
    for (ll it = 0; it < nIn; it++) {
      Rng g(seed, (ull)it);
      ll d;
      build_input_a(C, g, d, jobs, maxJobs);
      X.d = d;
      sim_seq(X, jobs, per[tid], 'a');
    }
  }
  for (auto& s : per) out.merge(s);
}

struct ExhW {
  Ctx X;
  int m = 0, B = 0;
  vector<Feas> fs;
  vector<RS> rs;
  vector<ll> path;
  Stats st;
};
static void exh_rec(ExhW& E, int depth) {
  const int Smax = E.B - E.fs[depth].minrow;
  for (int S = 1; S <= Smax; S++) {
    E.path[depth] = S;
    StepRes r;
    step(E.X, E.rs[depth], S, E.rs[depth + 1], r);
    E.st.prefixes++;
    if (done_step(r)) E.st.cost(r.cost, E.X.d, E.path.data(), depth + 1);
    if (r.status || r.diag) { record_fail(E.st, 'b', E.X, E.rs[depth], S, r, E.path.data(), depth + 1); continue; }
    if (depth + 1 < E.m) {
      feas_add(E.fs[depth], S, E.fs[depth + 1]);
      exh_rec(E, depth + 1);
    }
  }
}
static void run_b(const Cert& C, int m, ll d, int nth, Stats& out, int maxPrint) {
  const int B = (int)(d * C.F);
  RS root;
  root_rs(C, root);
  Feas f0;
  f0.init(B);
  Ctx X0;
  X0.C = &C;
  X0.d = d;
  Stats st0;
  st0.maxPrint = maxPrint;
  vector<pair<int, int>> tasks;
  vector<ll> path(m + 1, 0);
  for (int S1 = 1; S1 <= B; S1++) {
    path[0] = S1;
    RS a;
    StepRes r;
    step(X0, root, S1, a, r);
    st0.prefixes++;
    if (done_step(r)) st0.cost(r.cost, d, path.data(), 1);
    if (r.status || r.diag) { record_fail(st0, 'b', X0, root, S1, r, path.data(), 1); continue; }
    if (m >= 2) {
      Feas f1;
      feas_add(f0, S1, f1);
      for (int S2 = 1; S2 <= B - f1.minrow; S2++) tasks.push_back({S1, S2});
    }
  }
  vector<Stats> per(nth);
#pragma omp parallel num_threads(nth)
  {
    int tid = omp_get_thread_num();
    ExhW E;
    E.X.C = &C; E.X.d = d; E.m = m; E.B = B;
    E.fs.resize(m + 1);
    E.rs.resize(m + 1);
    E.path.assign(m + 1, 0);
    E.st.maxPrint = maxPrint;
    for (auto& f : E.fs) f.init(B);
    E.rs[0] = root;
#pragma omp for schedule(dynamic, 1)
    for (size_t ti = 0; ti < tasks.size(); ti++) {
      int S1 = tasks[ti].first, S2 = tasks[ti].second;
      StepRes r;
      E.path[0] = S1;
      step(E.X, E.rs[0], S1, E.rs[1], r);
      feas_add(E.fs[0], S1, E.fs[1]);
      E.path[1] = S2;
      step(E.X, E.rs[1], S2, E.rs[2], r);
      E.st.prefixes++;
      if (done_step(r)) E.st.cost(r.cost, d, E.path.data(), 2);
      if (r.status || r.diag) { record_fail(E.st, 'b', E.X, E.rs[1], S2, r, E.path.data(), 2); continue; }
      if (m > 2) {
        feas_add(E.fs[1], S2, E.fs[2]);
        exh_rec(E, 2);
      }
    }
    per[tid] = E.st;
  }
  st0.maxPrint = maxPrint;
  out.merge(st0);
  for (auto& s : per) out.merge(s);
  out.inputs = out.prefixes;
}

static void cnt_rec(vector<Feas>& fs, int depth, int m, int B, ll& cnt) {
  int Smax = B - fs[depth].minrow;
  cnt += Smax;
  if (depth + 1 >= m) return;
  for (int S = 1; S <= Smax; S++) {
    feas_add(fs[depth], S, fs[depth + 1]);
    cnt_rec(fs, depth + 1, m, B, cnt);
  }
}
static ll count_b(int B, int m, ll limit, int nth) {
  Feas f0;
  f0.init(B);
  ll base = B;
  if (m == 1) return base;
  vector<pair<int, int>> tasks;
  for (int S1 = 1; S1 <= B; S1++) {
    Feas f1;
    feas_add(f0, S1, f1);
    base += B - f1.minrow;
    if (m > 2) for (int S2 = 1; S2 <= B - f1.minrow; S2++) tasks.push_back({S1, S2});
  }
  if (m == 2) return base;
  atomic<ll> tot(base);
#pragma omp parallel num_threads(nth)
  {
    vector<Feas> fs(m + 1);
    for (auto& f : fs) f.init(B);
#pragma omp for schedule(dynamic, 1)
    for (size_t ti = 0; ti < tasks.size(); ti++) {
      if (tot.load() > limit) continue;
      feas_add(fs[0], tasks[ti].first, fs[1]);
      feas_add(fs[1], tasks[ti].second, fs[2]);
      ll cnt = 0;
      cnt_rec(fs, 2, m, B, cnt);
      tot += cnt;
    }
  }
  return tot.load();
}

struct Cand {
  int parent, S, nov;
  ll T, P, cost;
  ull h, rnd;
};
static ull rs_hash(const RS& s, int K, int k) {
  ull h = 0x51ED270B27A3B2C1ULL;
  auto mix = [&](ull v) { h ^= v + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); h *= 0xff51afd7ed558ccdULL; h ^= h >> 33; };
  for (int j = 0; j < K; j++) for (int b = 0; b < 3; b++) mix((ull)s.L[j][b]);
  mix((ull)s.V);
  for (int a = 1; a < k; a++) mix(s.H[a]);
  return h;
}
static void tset(const RS& s, ll d, int K, Rng& g, vector<ll>& ts) {
  ts.clear();
  if (d <= 12) {
    for (ll t = 1; t <= d; t++) ts.push_back(t);
    return;
  }
  ts.push_back(1);
  ts.push_back(d);
  ll x = (ll)s.N * d - s.V;
  if (x >= 1) ts.push_back(x);
  ts.push_back(x + 1);
  if (x >= 2) ts.push_back(x - 1);
  for (int j = 0; j < K; j++)
    for (int b = 0; b < 3; b++)
      if (s.L[j][b] > 0) {
        ll R = (s.L[j][b] + d - 1) / d, f = R * d - s.L[j][b];
        if (f >= 1) ts.push_back(f);
        ts.push_back(f + 1);
      }
  static const int gl[4] = {2, 3, 4, 6};
  for (int gi = 0; gi < 4; gi++)
    if (d % gl[gi] == 0)
      for (int a = 1; a < gl[gi]; a++) ts.push_back(a * d / gl[gi]);
  ts.push_back(g.range(1, d));
  ts.push_back(g.range(1, d));
  sort(ts.begin(), ts.end());
  ts.erase(unique(ts.begin(), ts.end()), ts.end());
  while (!ts.empty() && ts.back() > d) ts.pop_back();
  while (!ts.empty() && ts.front() < 1) ts.erase(ts.begin());
}
static void run_c(const Cert& C, ll d, int width, int maxDepth, int mode, ull seed, int nth, Stats& out, int maxPrint) {
  const int B = (int)(d * C.F), K = C.K, k = C.k;
  vector<RS> nodes(1);
  vector<Feas> feas(1);
  vector<vector<ll>> paths(1);
  root_rs(C, nodes[0]);
  feas[0].init(B);
  vector<Ctx> ctx(nth);
  for (auto& x : ctx) { x.C = &C; x.d = d; }
  vector<Stats> per(nth);
  for (auto& s : per) s.maxPrint = maxPrint;
  Rng gsel(seed, 0x5E1EC7ULL);
  for (int depth = 0; depth < maxDepth && !nodes.empty(); depth++) {
    vector<vector<Cand>> cands(nth);
#pragma omp parallel num_threads(nth)
    {
      int tid = omp_get_thread_num();
      Ctx& X = ctx[tid];
      Stats& st = per[tid];
      vector<ll> ts, path;
#pragma omp for schedule(dynamic, 4)
      for (size_t i = 0; i < nodes.size(); i++) {
        Rng g(seed ^ 0xABCDEF12345ULL, (ull)depth * 1000003ULL + i);
        int Smax = B - feas[i].minrow;
        if (Smax < 1) continue;
        tset(nodes[i], d, K, g, ts);
        path = paths[i];
        path.push_back(0);
        for (ll t : ts)
          for (ll c = 0; c < C.F; c++) {
            ll S = c * d + t;
            if (S > Smax) break;
            path.back() = S;
            RS ch;
            StepRes r;
            step(X, nodes[i], S, ch, r);
            st.prefixes++;
            if (done_step(r)) st.cost(r.cost, d, path.data(), (int)path.size());
            if (r.status || r.diag) { record_fail(st, 'c', X, nodes[i], S, r, path.data(), (int)path.size()); continue; }
            Cand cd;
            cd.parent = (int)i; cd.S = (int)S; cd.T = ch.T;
            ll P = 0;
            const uint16_t* kk = &C.keys[(size_t)ch.sid * C.klen];
            for (int j = 0; j < K; j++) P += C.w[j] * kk[k + 3 * j + 2];
            cd.P = P; cd.cost = r.cost; cd.h = rs_hash(ch, K, k); cd.rnd = g.next(); cd.nov = r.novel ? 1 : 0;
            cands[tid].push_back(cd);
          }
      }
    }
    vector<Cand> all;
    size_t tot = 0;
    for (auto& v : cands) tot += v.size();
    if (tot == 0) break;
    all.reserve(tot);
    for (auto& v : cands) all.insert(all.end(), v.begin(), v.end());
    cands.clear();
    auto better = [mode](const Cand& a, const Cand& b) {
      switch (mode) {
        case 0:
          if (a.T != b.T) return a.T > b.T;
          if (a.cost != b.cost) return a.cost > b.cost;
          if (a.P != b.P) return a.P > b.P;
          return a.rnd < b.rnd;
        case 1:
          if (a.cost != b.cost) return a.cost > b.cost;
          if (a.P != b.P) return a.P > b.P;
          if (a.T != b.T) return a.T > b.T;
          return a.rnd < b.rnd;
        case 2:
          if (a.P != b.P) return a.P > b.P;
          if (a.T != b.T) return a.T > b.T;
          if (a.cost != b.cost) return a.cost > b.cost;
          return a.rnd < b.rnd;
        case 4:
          if (a.nov != b.nov) return a.nov > b.nov;
          if (a.T != b.T) return a.T > b.T;
          return a.rnd < b.rnd;
        default:
          return a.rnd < b.rnd;
      }
    };
    sort(all.begin(), all.end(), better);
    unordered_set<ull> seen;
    vector<size_t> sel, rest;
    size_t top = (mode == 3) ? (size_t)width : (size_t)(width * 3 / 4);
    for (size_t i = 0; i < all.size(); i++) {
      if (!seen.insert(all[i].h).second) continue;
      if (sel.size() < top) sel.push_back(i);
      else rest.push_back(i);
    }
    shuffle_vec(rest, gsel);
    while (sel.size() < (size_t)width && !rest.empty()) { sel.push_back(rest.back()); rest.pop_back(); }
    vector<RS> nn(sel.size());
    vector<Feas> nf(sel.size());
    vector<vector<ll>> np(sel.size());
#pragma omp parallel for num_threads(nth) schedule(dynamic, 16)
    for (size_t a = 0; a < sel.size(); a++) {
      const Cand& cd = all[sel[a]];
      int tid = omp_get_thread_num();
      StepRes r;
      step(ctx[tid], nodes[cd.parent], cd.S, nn[a], r);
      feas_add(feas[cd.parent], cd.S, nf[a]);
      np[a] = paths[cd.parent];
      np[a].push_back(cd.S);
    }
    nodes.swap(nn);
    feas.swap(nf);
    paths.swap(np);
  }
  per[0].inputs++;
  for (auto& s : per) out.merge(s);
}

enum { G_CONST, G_CONSTBIG, G_EQV, G_EQVP, G_EQL, G_EQLP, G_INTTOT, G_MIX, G_PATTERN, G_RANDSTY, NG };
static const char* GNAME[NG] = {"const", "const+big", "t=<V>", "t=<V>+1", "t=<L>", "t=<L>+1", "integer-totals", "mix",
                                "pattern", "random-styles"};
static ll pick_t(const RS& s, ll d, int K, int kind, Rng& g) {
  ll x = (ll)s.N * d - s.V;
  if (kind == 0) return x >= 1 ? x : d;
  if (kind == 1) return x + 1;
  ll fs[3 * MAXK];
  int nf = 0;
  for (int j = 0; j < K; j++)
    for (int b = 0; b < 3; b++)
      if (s.L[j][b] > 0) {
        ll R = (s.L[j][b] + d - 1) / d, f = R * d - s.L[j][b];
        if (kind == 3 || f >= 1) fs[nf++] = f;
      }
  if (nf == 0) return kind == 2 ? (x >= 1 ? x : d) : x + 1;
  ll f = fs[g.range(0, nf - 1)];
  return kind == 2 ? f : f + 1;
}
static ll with_c(ll t, ll d, ll Smax, Rng& g, double p0) {
  if (t > Smax) return Smax;
  ll cmax = (Smax - t) / d;
  ll c = g.coin(p0) ? 0 : g.range(0, cmax);
  return c * d + t;
}
struct DTask {
  int gen;
  ll d, param;
  ull seed;
};
static void run_d_one(Ctx& X, const DTask& tk, Stats& st) {
  const Cert& C = *X.C;
  const ll d = tk.d;
  const int B = (int)(d * C.F), K = C.K;
  X.d = d;
  Rng g(tk.seed * 7919ULL + 17, (ull)tk.gen * 1000003ULL + (ull)tk.param * 31ULL + (ull)d);
  RS cur, nx;
  root_rs(C, cur);
  Feas fe, f2;
  fe.init(B);
  f2.init(B);
  vector<ll> path;
  st.inputs++;
  ll m0 = (tk.gen == G_CONSTBIG) ? g.range(0, 3LL * B / max(1LL, tk.param)) : 0;
  static const int pnum[13] = {1, 1, 2, 1, 3, 1, 5, 3, 5, 7, 1, 2, 1};
  static const int pden[13] = {2, 3, 3, 4, 4, 6, 6, 8, 12, 12, 5, 5, 12};
  ll tie = g.range(1, d);
  for (int it = 0; it < 4 * B + 10; it++) {
    const int Smax = B - fe.minrow;
    if (Smax < 1) break;
    ll S = 0;
    switch (tk.gen) {
      case G_CONST: S = tk.param; break;
      case G_CONSTBIG:
        if (it < m0) S = min<ll>(tk.param, Smax);
        else { ll ch[4] = {Smax, Smax - 1, (Smax + 1) / 2, Smax / 3 + 1}; S = ch[g.range(0, 3)]; }
        break;
      case G_EQV: S = with_c(pick_t(cur, d, K, 0, g), d, Smax, g, 0.5); break;
      case G_EQVP: S = with_c(pick_t(cur, d, K, 1, g), d, Smax, g, 0.5); break;
      case G_EQL: S = with_c(pick_t(cur, d, K, 2, g), d, Smax, g, 0.5); break;
      case G_EQLP: S = with_c(pick_t(cur, d, K, 3, g), d, Smax, g, 0.5); break;
      case G_INTTOT:
        if (it % 2 == 0) S = g.range(1, max<ll>(1, min<ll>(Smax, max<ll>(1, d / 2))));
        else S = with_c(pick_t(cur, d, K, 0, g), d, Smax, g, 0.7);
        break;
      case G_MIX: {
        int ch = (int)g.range(0, 8);
        if (ch == 0) S = g.range(1, max(1LL, d / 4));
        else if (ch <= 4) S = with_c(pick_t(cur, d, K, ch - 1, g), d, Smax, g, 0.5);
        else if (ch == 5) S = with_c(d, d, Smax, g, 0.3);
        else if (ch == 6) S = g.range(1, Smax);
        else if (ch == 7) S = Smax;
        else S = with_c(tie, d, Smax, g, 0.5);
        break;
      }
      case G_PATTERN: {
        int pi = (int)g.range(0, 12);
        ll base = (ll)B * pnum[pi] / pden[pi];
        ll pert[5] = {0, 1, -1, max(1LL, d / 8), -max(1LL, d / 8)};
        S = base + pert[g.range(0, 4)];
        if (S < 1) S = 1;
        if (S > Smax) S = g.coin(0.5) ? Smax : 0;
        break;
      }
      case G_RANDSTY: {
        ll gstep = d;
        S = gen_size((int)g.range(0, NSY - 1), g, d, C, tie, gstep);
        if (S > Smax) S = g.coin(0.7) ? g.range(1, Smax) : Smax;
        break;
      }
    }
    if (S < 1 || S > Smax) break;
    path.push_back(S);
    StepRes r;
    step(X, cur, S, nx, r);
    st.prefixes++;
    if (done_step(r)) st.cost(r.cost, d, path.data(), (int)path.size());
    if (r.status || r.diag) { record_fail(st, 'd', X, cur, S, r, path.data(), (int)path.size()); return; }
    feas_add(fe, (int)S, f2);
    swap(fe, f2);
    cur = nx;
  }
}
static void run_d(const Cert& C, const vector<ll>& ds, int seeds, int nth, Stats& out, int maxPrint, vector<Stats>* byGen) {
  vector<DTask> tasks;
  for (ll d : ds) {
    const ll B = d * C.F;
    vector<ll> del = {1, 2, 3, d / 7, d / 6, d / 5, d / 4, d / 3, d / 2, d / 2 + 1, 2 * d / 3, d - 1, d, d + 1,
                      3 * d / 2, 2 * d - 1, 2 * d + 1, 3 * d};
    sort(del.begin(), del.end());
    del.erase(unique(del.begin(), del.end()), del.end());
    for (ll x : del) {
      if (x < 1 || x > B) continue;
      tasks.push_back({G_CONST, d, x, 0});
      for (int s = 0; s < max(1, seeds / 10); s++) tasks.push_back({G_CONSTBIG, d, x, (ull)s});
    }
    for (int gen = G_EQV; gen < NG; gen++)
      for (int s = 0; s < seeds; s++) tasks.push_back({gen, d, 0, (ull)s});
  }
  vector<vector<Stats>> per(nth, vector<Stats>(NG));
  for (auto& v : per) for (auto& s : v) s.maxPrint = maxPrint;
#pragma omp parallel num_threads(nth)
  {
    int tid = omp_get_thread_num();
    Ctx X;
    X.C = &C;
#pragma omp for schedule(dynamic, 1)
    for (size_t ti = 0; ti < tasks.size(); ti++) run_d_one(X, tasks[ti], per[tid][tasks[ti].gen]);
  }
  if (byGen) byGen->assign(NG, Stats());
  for (auto& v : per)
    for (int gi = 0; gi < NG; gi++) {
      out.merge(v[gi]);
      if (byGen) { (*byGen)[gi].maxPrint = 0; (*byGen)[gi].merge(v[gi]); }
    }
}

static int selftest(int nth) {
  int bad = 0;

  vector<array<int, 3>> types;
  for (int n = 1; n <= 3; n++)
    for (int e = 0; e <= n - 1; e++)
      for (int b = 0; b <= n; b++) types.push_back({n, e, b});
  printf("selftest 1: %zu types (n,e,b)\n", types.size());
  for (int nu = 0; nu <= 1; nu++) {
    ll allowed = 0, mism = 0;
#pragma omp parallel for num_threads(nth) reduction(+ : allowed, mism) schedule(static, 4096)
    for (int mask = 0; mask < (1 << 20); mask++) {
      int tn[20], te[20], tb[20], cnt = 0;
      for (int i = 0; i < 20; i++)
        if (mask >> i & 1) { tn[cnt] = types[i][0]; te[cnt] = types[i][1]; tb[cnt] = types[i][2]; cnt++; }
      bool tab = true;
      int lo = 1, hi = 4;
      for (int i = 0; i < cnt && tab; i++) {
        int a, b;
        if (!tab_interval(tn[i], te[i], tb[i], nu, a, b)) tab = false;
        else { lo = max(lo, a); hi = min(hi, b); }
      }
      tab = tab && lo <= hi;
      bool fm = fm_allowed(nu, cnt, tn, te, tb);
      if (tab != fm) mism++;
      if (fm) allowed++;
    }
    printf("selftest 1: nu=%d allowed sets %lld (expected 2816) mismatches table/elimination %lld\n", nu, allowed, mism);
    if (mism || allowed != 2816) bad++;
  }

  {
    const int sp[8][4] = {{1, 8, 1, 2}, {1, 5, 1, 2}, {1, 3, 1, 2}, {3, 4, 7, 8},
                          {1, 4, 1, 8}, {1, 2, 1, 4}, {3, 4, 3, 8}, {9, 10, 1, 2}};
    ll errs = 0;
    for (int cell = 0; cell < 8; cell++) {
      ll tp = sp[cell][0], tq = sp[cell][1], xp = sp[cell][2], xq = sp[cell][3];
      int nu = cell >= 4 ? 1 : 0;
      bool xlt = xp * tq < tp * xq;
      if (xlt != (nu == 1)) errs++;
    }
    for (auto& ty : types)
      for (int nu = 0; nu <= 1; nu++) {
        int lo = 0, hi = -1;
        bool has = tab_interval(ty[0], ty[1], ty[2], nu, lo, hi);
        for (int ci = 1; ci <= 4; ci++) {
          int cell = nu * 4 + ci - 1;
          ll tp = sp[cell][0], tq = sp[cell][1], xp = sp[cell][2], xq = sp[cell][3];
          int n = ty[0], e = ty[1], b = ty[2];
          bool sat;
          if (b <= e) sat = xp * tq < ((ll)(n - b) * tp - (ll)(e - b) * tq) * xq;
          else sat = xp * tq >= ((ll)b * tp - (ll)e * tq) * xq;
          bool inI = has && lo <= ci && ci <= hi;
          if (sat != inI) {
            errs++;
            printf("selftest 2: type (%d,%d,%d) nu=%d cell %d: condition %d table %d\n", n, e, b, nu, ci, sat, inI);
          }
        }
      }
    printf("selftest 2: cell sample points against the one-copy condition and the table: %lld errors\n", errs);
    if (errs) bad++;
  }

  {
    ll errs = 0, tests = 0;
#pragma omp parallel for num_threads(nth) reduction(+ : errs, tests) schedule(dynamic, 64)
    for (int trial = 0; trial < 40000; trial++) {
      Rng g(4242, (ull)trial);
      int B = (int)g.range(1, 40), n = (int)g.range(1, 8);
      vector<int> sz(n);
      int mode = (int)g.range(0, 2);
      for (int i = 0; i < n; i++) sz[i] = mode == 0 ? (int)g.range(1, B) : mode == 1 ? (int)g.range(1, max(1, B / 3)) : (int)g.range(max(1, B / 4), max(1, B / 2 + 1));
      Feas f, f2;
      f.init(B);
      for (int len = 1; len <= n; len++) {

        bool feasible = false;
        int bestMin = B + 1;
        int total = 1;
        for (int i = 0; i < len; i++) total *= 3;
        for (int code = 0; code < total; code++) {
          int ld[3] = {0, 0, 0}, cc = code;
          bool ok = true;
          for (int i = 0; i < len; i++) { ld[cc % 3] += sz[i]; cc /= 3; }
          for (int b = 0; b < 3; b++) if (ld[b] > B) ok = false;
          if (ok) { feasible = true; bestMin = min(bestMin, min(ld[0], min(ld[1], ld[2]))); }
        }
        bool got = feas_add(f, sz[len - 1], f2);
        tests++;
        if (got != feasible) { errs++; break; }
        if (!got) break;
        if (f2.minrow != bestMin) { errs++; break; }
        swap(f, f2);
      }
    }
    printf("selftest 3: exact feasibility against brute force: %lld prefix tests, %lld errors\n", tests, errs);
    if (errs) bad++;
  }

  {
    ll errs = 0, moves = 0;
#pragma omp parallel for num_threads(nth) reduction(+ : errs, moves) schedule(dynamic, 64)
    for (int trial = 0; trial < 200000; trial++) {
      Rng g(777, (ull)trial);
      static const ll dl[12] = {1, 2, 3, 4, 5, 6, 8, 12, 24, 60, 720, 5040};
      ll d = dl[g.range(0, 11)];
      int K = (int)g.range(1, MAXK), r = (int)g.range(1, 3), F = (int)g.range(2, 12);
      RS s;
      memset(&s, 0, sizeof s);
      int njobs = (int)g.range(1, 25);
      ll tie = g.range(1, d);
      for (int it = 0; it < njobs; it++) {
        int sty = (int)g.range(0, 5);
        ll S;
        if (sty == 0) S = g.range(1, d * F);
        else if (sty == 1) S = d * g.range(1, F);
        else if (sty == 2) S = g.range(1, max(1LL, d / 3));
        else if (sty == 3) S = d * g.range(0, F - 1) + tie;
        else if (sty == 4) S = d * g.range(0, F - 1) + max(1LL, (ll)s.N * d - s.V);
        else {
          int j = (int)g.range(0, K - 1), b = (int)g.range(0, 2);
          ll R = (s.L[j][b] + d - 1) / d, f = R * d - s.L[j][b];
          S = d * g.range(0, F - 1) + (f >= 1 ? f : d);
        }
        MoveInfo mv;
        compute_move(K, d, r, s.L, s.V, s.N, S, mv);
        bool fm, tb;
        joint_tests(s.N, mv.nu, K, mv.q, mv.o, fm, tb);
        moves++;
        if (!fm || !tb) { errs++; break; }
        RS t = s;
        bool ok = true;
        for (int j = 0; j < K; j++) {
          int i = (int)g.range(0, 2), b = mv.perm[j][i];
          ll Rold = (t.L[j][b] + d - 1) / d;
          t.L[j][b] += S;
          ll Rnew = (t.L[j][b] + d - 1) / d;
          if (Rnew != Rold + mv.c + mv.o[j][i]) ok = false;
        }
        t.V += S;
        t.N = (int)((t.V + d - 1) / d);
        if (t.N != mv.Nn) ok = false;
        if (!lemma31ii(K, d, t)) ok = false;
        if (!ok) { errs++; break; }
        s = t;
      }
    }
    printf("selftest 4: random real loads, invariants and patterns: %lld real moves, %lld errors\n", moves, errs);
    if (errs) bad++;
  }
  printf("selftest %s\n", bad ? "FAILED" : "PASSED");
  return bad ? 1 : 0;
}

static void usage() {
  printf("usage: sim3 selftest [threads=T]\n"
         "       sim3 count F=12 ds=1,2,3,4,6,12 mmax=12 limit=1e12 [threads=T]   (sizes of class b)\n"
         "       sim3 CERT [classes=abcd] [threads=T] [maxprint=100]\n"
         "            [a.n=300000] [a.seed=1] [a.maxjobs=60000]\n"
         "            [b=m:d,m:d,...] or [b.budget=1e9 b.ds=2,3,4,6]   (auto: largest m per d within the budget)\n"
         "            [c.ds=6,12,24] [c.modes=01234] [c.width=3000] [c.depth=60] [c.seeds=1]\n"
         "              modes: 0 potential, 1 cost, 2 payoff, 3 random, 4 novelty (unvisited listed states)\n"
         "            [d.ds=2,3,4,5,6,8,12,24,60] [d.seeds=100]\n"
         "            [inject=1|2] (test hooks: 1 = predicted successors use a flipped bit of copy 1,\n"
         "                          2 = copy 1 puts the job into the bin of the next rank)\n");
}
static vector<ll> parse_list(const string& s) {
  vector<ll> v;
  size_t i = 0;
  while (i < s.size()) {
    size_t j = s.find(',', i);
    if (j == string::npos) j = s.size();
    if (j > i) v.push_back(atoll(s.substr(i, j - i).c_str()));
    i = j + 1;
  }
  return v;
}
int main(int argc, char** argv) {
  setvbuf(stdout, NULL, _IOLBF, 0);
  if (argc < 2) { usage(); return 2; }
  map<string, string> opt;
  for (int i = 2; i < argc; i++) {
    string a = argv[i];
    size_t e = a.find('=');
    if (e == string::npos) { printf("bad option %s\n", a.c_str()); usage(); return 2; }
    opt[a.substr(0, e)] = a.substr(e + 1);
  }
  auto geti = [&](const string& k, ll def) { return opt.count(k) ? (ll)atof(opt[k].c_str()) : def; };
  auto gets = [&](const string& k, const string& def) { return opt.count(k) ? opt[k] : def; };
  int nth = (int)geti("threads", omp_get_max_threads());
  if (nth < 1) nth = 1;
  if (string(argv[1]) == "selftest") return selftest(nth);
  if (string(argv[1]) == "count") {
    int F = (int)geti("F", 12), mmax = (int)geti("mmax", 12);
    ll limit = geti("limit", 1000000000000LL);
    vector<ll> ds = parse_list(gets("ds", "1,2,3,4,6,12"));
    for (ll d : ds)
      for (int m = 1; m <= mmax; m++) {
        double ts = wall();
        ll c = count_b((int)(d * F), m, limit, nth);
        printf("count F=%d d=%lld m=%d prefixes %lld%s (%.1fs)\n", F, d, m, c, c > limit ? " (above limit, stopped)" : "", wall() - ts);
        if (c > limit) break;
      }
    return 0;
  }

  double t0 = wall();
  Cert C;
  string fname = argv[1];
  string base = fname.substr(fname.find_last_of('/') == string::npos ? 0 : fname.find_last_of('/') + 1);
  if (!C.load(fname)) {
    printf("RESULT %s LOADFAIL %s\n", base.c_str(), C.err.c_str());
    return 2;
  }
  int maxPrint = (int)geti("maxprint", 100);
  string wl;
  for (int j = 0; j < C.K; j++) { if (j) wl += ","; wl += to_string(C.w[j]); }
  printf("cert %s: k %d r %d F %d K %d weights %s T0 %lld n %lld bound %s = %.6f (load %.1fs)\n", fname.c_str(), C.k, C.r,
         C.F, C.K, wl.c_str(), C.T0, C.n, fracs(C.T0, (i128)C.W * C.F).c_str(), (double)C.T0 / ((double)C.W * C.F), wall() - t0);
  bool fileProblem = false;
  if (C.dup) { printf("  file problem: %lld duplicate keys (the first one is used)\n", C.dup); fileProblem = true; }
  if (C.big) { printf("  file problem: %lld states with a key value above 65535 (never reached, ignored)\n", C.big); fileProblem = true; }
  if (C.unsorted) { printf("  file problem: %lld states with an unsorted triple (never matched)\n", C.unsorted); fileProblem = true; }
  if (C.rootId < 0) {
    printf("  file problem: the root is not listed\n");
    printf("RESULT %s FAIL root not listed\n", base.c_str());
    return 1;
  }
  if (C.rootId != 0) { printf("  file problem: the root is state %lld, not state 0\n", C.rootId); fileProblem = true; }
  if (C.pot[C.rootId] > C.T0) { printf("  file problem: root potential %lld > T0 %lld\n", C.pot[C.rootId], C.T0); fileProblem = true; }
  printf("  root potential %lld, threads %d\n", C.pot[C.rootId], nth);
  fflush(stdout);
  g_seen.assign((size_t)((C.n + 63) / 64), 0ULL);
  mark_seen(C.rootId);
  auto coverage = [&]() {
    ll s = count_seen();
    printf("  listed states reached by real inputs so far: %lld of %lld (%.2f%%)\n", s, C.n, 100.0 * (double)s / (double)C.n);
    fflush(stdout);
  };

  string classes = gets("classes", "abcd");
  g_inject = (int)geti("inject", 0);
  if (g_inject) printf("  TEST HOOK inject=%d: the simulation is broken on purpose (negative test)\n", g_inject);
  Stats total;
  total.maxPrint = 0;
  string summary;
  auto add_summary = [&](const string& lab, const Stats& st) {
    summary += " | " + lab + " " + to_string(st.prefixes) + " prefixes " + to_string(st.fails) + " fail worst " + worst_str(st, C);
    coverage();
  };
  if (classes.find('a') != string::npos) {
    double ts = wall();
    Stats st;
    st.maxPrint = maxPrint;
    ll nIn = geti("a.n", 300000);
    ull seed = (ull)geti("a.seed", 1);
    int maxJobs = (int)geti("a.maxjobs", 60000);
    run_a(C, nIn, seed, maxJobs, nth, st, maxPrint);
    print_stats("class a (random packings, " + to_string(nIn) + " inputs, seed " + to_string(seed) + ")", st, C, wall() - ts);
    total.merge(st);
    add_summary("a", st);
  }
  if (classes.find('b') != string::npos) {
    vector<pair<int, ll>> runs;
    if (opt.count("b")) {
      string s = opt["b"];
      size_t i = 0;
      while (i < s.size()) {
        size_t j = s.find(',', i);
        if (j == string::npos) j = s.size();
        string item = s.substr(i, j - i);
        size_t c = item.find(':');
        if (c != string::npos) runs.push_back({atoi(item.substr(0, c).c_str()), atoll(item.substr(c + 1).c_str())});
        i = j + 1;
      }
    } else {
      ll budget = geti("b.budget", 1000000000LL);
      vector<ll> ds = parse_list(gets("b.ds", "2,3,4,6"));
      for (ll d : ds) {
        int B = (int)(d * C.F), best = 0;
        for (int m = 2; m <= 30; m++) {
          ll cnt = count_b(B, m, budget, nth);
          if (cnt > budget) break;
          best = m;
        }
        if (best >= 1) runs.push_back({best, d});
      }
    }
    Stats stb;
    stb.maxPrint = maxPrint;
    string lab;
    for (auto& pr : runs) {
      double ts = wall();
      Stats st;
      st.maxPrint = maxPrint;
      run_b(C, pr.first, pr.second, nth, st, maxPrint);
      print_stats("class b (all inputs of at most " + to_string(pr.first) + " jobs on multiples of 1/(" +
                      to_string(pr.second) + "F), d=" + to_string(pr.second) + ")",
                  st, C, wall() - ts);
      stb.merge(st);
      if (!lab.empty()) lab += ",";
      lab += to_string(pr.first) + ":" + to_string(pr.second);
    }
    total.merge(stb);
    add_summary("b(" + lab + ")", stb);
  }
  if (classes.find('c') != string::npos) {
    vector<ll> ds = parse_list(gets("c.ds", "6,12,24"));
    string modes = gets("c.modes", "01234");
    int width = (int)geti("c.width", 3000), depth = (int)geti("c.depth", 60), seeds = (int)geti("c.seeds", 1);
    Stats stc;
    stc.maxPrint = maxPrint;
    for (ll d : ds)
      for (char mc : modes)
        for (int sd = 1; sd <= seeds; sd++) {
          double ts = wall();
          Stats st;
          st.maxPrint = maxPrint;
          run_c(C, d, width, depth, mc - '0', (ull)sd * 1009ULL + (ull)d, nth, st, maxPrint);
          print_stats("class c (beam, d=" + to_string(d) + " mode " + string(1, mc) + " seed " + to_string(sd) +
                          " width " + to_string(width) + " depth " + to_string(depth) + ")",
                      st, C, wall() - ts);
          stc.merge(st);
        }
    print_stats("class c total", stc, C, 0.0);
    total.merge(stc);
    add_summary("c", stc);
  }
  if (classes.find('d') != string::npos) {
    double ts = wall();
    vector<ll> ds = parse_list(gets("d.ds", "2,3,4,5,6,8,12,24,60"));
    int seeds = (int)geti("d.seeds", 100);
    Stats st;
    st.maxPrint = maxPrint;
    vector<Stats> byGen;
    run_d(C, ds, seeds, nth, st, maxPrint, &byGen);
    for (int gi = 0; gi < NG; gi++)
      printf("  class d generator %-15s inputs %lld prefixes %lld failures %lld worst %s attained %s\n", GNAME[gi], byGen[gi].inputs,
             byGen[gi].prefixes, byGen[gi].fails, worst_str(byGen[gi], C).c_str(), attains(byGen[gi], C) ? "yes" : "no");
    print_stats("class d (structured, " + to_string(seeds) + " seeds per generator and d)", st, C, wall() - ts);
    total.merge(st);
    add_summary("d", st);
  }
  bool pass = total.fails == 0;
  printf("RESULT %s %s k=%d r=%d w=%s T0=%lld n=%lld prefixes %lld failures %lld worst %s bound %s attained %s "
         "reached %lld states%s%s time %.0fs\n",
         base.c_str(), pass ? "PASS" : "FAIL", C.k, C.r, wl.c_str(), C.T0, C.n, total.prefixes, total.fails,
         worst_str(total, C).c_str(), fracs(C.T0, (i128)C.W * C.F).c_str(), attains(total, C) ? "yes" : "no",
         count_seen(), fileProblem ? " (file problems noted)" : "", summary.c_str(), wall() - t0);
  return pass ? 0 : 1;
}
