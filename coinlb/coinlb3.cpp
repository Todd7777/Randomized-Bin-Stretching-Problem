// coinlb3.cpp: lower bounds for lotteries with fixed weights, by a grid game in which the copies place every job.
// g++ -O2 -std=c++17 -o coinlb3 coinlb3.cpp && ./coinlb3 -m M -K K -w w_1,..,w_K -g G -t T [-sizes LIST] [-cert FILE]
// Jobs have sizes 1..G in units of 1/G. WIN means the adversary forces sum_j w_j (largest load of copy j) >= T.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <unordered_set>
#include <vector>
#include <sys/resource.h>

static int M = 3, K = 2, G = 6;
static int Wt[4] = {1, 1, 0, 0};
static int Wsum = 2;
static int ORDER = 0;
static bool USEV1 = true;
static int MU = -1;
static bool ALLOW[64];
static bool RESTRICTED = false;
static int IDBITS = 28, LBITS = 8;
static const int LOBITS = 6;
static const int MAXK = 3, MAXM = 4;
static const uint8_t LBMARK = 0xFF;
static double DEADLINE = 1e18;

static double now_s() {
  using namespace std::chrono;
  return duration<double>(steady_clock::now().time_since_epoch()).count();
}
static double maxrss_mb() {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
#ifdef __APPLE__
  return ru.ru_maxrss / 1048576.0;
#else
  return ru.ru_maxrss / 1024.0;
#endif
}
static inline uint64_t mix(uint64_t z) {
  z += 0x9e3779b97f4a7c15ULL;
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
static inline int next_lo(int s) { return (MU < 0 || MU >= G - 1) ? 1 : std::max(1, s - MU); }

struct PackSets {
  int cells = 0, nwords = 0;
  std::vector<uint64_t> pool;
  std::vector<int> N, smax;
  std::vector<int32_t> trans;
  std::vector<uint32_t> itab;
  uint64_t imask = 0, icount = 0;
  int stride[MAXM];
  uint64_t hbits(const uint64_t* w, int n) const {
    uint64_t h = mix((uint64_t)n);
    for (int k = 0; k < nwords; k++) h = mix(h ^ w[k]);
    return h;
  }
  void ireinsert(uint32_t id) {
    uint64_t h = hbits(&pool[(size_t)id * nwords], N[id]) & imask;
    while (itab[h] != 0xFFFFFFFFu) h = (h + 1) & imask;
    itab[h] = id;
  }
  void init() {
    cells = 1;
    for (int i = 0; i < M - 1; i++) { stride[i] = cells; cells *= (G + 1); }
    nwords = (cells + 63) / 64;
    itab.assign(1 << 16, 0xFFFFFFFFu);
    imask = itab.size() - 1;
  }
  void decode(int c, int* b, int n) const {
    int sum = 0;
    for (int i = 0; i < M - 1; i++) { b[i] = c % (G + 1); c /= (G + 1); sum += b[i]; }
    b[M - 1] = n - sum;
  }
  uint32_t intern(const std::vector<uint64_t>& bits, int n) {
    uint64_t h = hbits(bits.data(), n) & imask;
    while (itab[h] != 0xFFFFFFFFu) {
      uint32_t o = itab[h];
      if (N[o] == n && memcmp(&pool[(size_t)o * nwords], bits.data(), nwords * 8) == 0) return o;
      h = (h + 1) & imask;
    }
    uint32_t id = (uint32_t)N.size();
    if ((uint64_t)id >= (1ULL << IDBITS) - 1) { fprintf(stderr, "too many packing sets\n"); printf("RESULT ABORT packsets\n"); exit(4); }
    pool.insert(pool.end(), bits.begin(), bits.end());
    N.push_back(n);
    itab[h] = id;
    if (++icount * 2 > itab.size()) {
      itab.assign(itab.size() * 2, 0xFFFFFFFFu);
      imask = itab.size() - 1;
      for (uint32_t q = 0; q <= id; q++) ireinsert(q);
    }
    int best = G + 1;
    int b[MAXM];
    for (int c = 0; c < cells; c++)
      if (bits[c >> 6] >> (c & 63) & 1) {
        decode(c, b, n);
        for (int i = 0; i < M; i++) best = std::min(best, b[i]);
      }
    smax.push_back(best > G ? 0 : G - best);
    trans.resize(trans.size() + (G + 1), -1);
    return id;
  }
  uint32_t root() {
    std::vector<uint64_t> bits(nwords, 0);
    bits[0] = 1;
    return intern(bits, 0);
  }
  uint32_t child(uint32_t id, int s) {
    int32_t tr = trans[(size_t)id * (G + 1) + s];
    if (tr >= 0) return (uint32_t)tr;
    int n = N[id];
    std::vector<uint64_t> bits(nwords, 0);
    const uint64_t* src = &pool[(size_t)id * nwords];
    int b[MAXM];
    for (int c = 0; c < cells; c++)
      if (src[c >> 6] >> (c & 63) & 1) {
        decode(c, b, n);
        for (int i = 0; i < M; i++)
          if (b[i] + s <= G) {
            int cc = (i < M - 1) ? c + s * stride[i] : c;
            bits[cc >> 6] |= 1ULL << (cc & 63);
          }
      }
    bool any = false;
    for (auto w : bits) any |= (w != 0);
    if (!any) { fprintf(stderr, "internal: infeasible child requested\n"); exit(3); }
    uint32_t cid = intern(bits, n + s);
    trans[(size_t)id * (G + 1) + s] = (int32_t)cid;
    return cid;
  }
};
static PackSets PS;

static inline void sort_desc(uint8_t* L) {
  for (int i = 1; i < M; i++)
    for (int j = i; j > 0 && L[j] > L[j - 1]; j--) std::swap(L[j], L[j - 1]);
}
static inline int copy_guarantee(const uint8_t* L, int R) {
  int a = L[M - 1], b = L[M - 2];
  int gs1 = std::max<int>(L[0], a + R);
  int gg = std::min(G, R);
  int need = a + b + R + gg - 1;
  int X = std::max(b, (need + 1) / 2);
  if (need < 0) X = b;
  int gs2 = std::max<int>(L[0], X);
  return std::min(gs1, gs2);
}

static uint64_t* V1T = nullptr;
static uint64_t V1MASK = 0, V1CAP = 0, V1USED = 0;
static inline uint64_t v1key(uint32_t id, const uint8_t* L, int lo) {
  uint64_t k = id;
  int pos = IDBITS;
  k |= (uint64_t)lo << pos; pos += LOBITS;
  for (int i = 0; i < M - 1; i++) { k |= (uint64_t)L[i] << pos; pos += LBITS; }
  return k;
}
static uint64_t NODES = 0;
static void check_time() {
  if (now_s() > DEADLINE) {
    printf("RESULT ABORT time  nodes %llu  v1 %llu  rss %.0fMB\n", (unsigned long long)NODES,
           (unsigned long long)V1USED, maxrss_mb());
    fflush(stdout);
    exit(6);
  }
}
static int v1(uint32_t id, const uint8_t* L, int lo) {
  const uint64_t k = v1key(id, L, lo);
  const uint64_t KM = (1ULL << 56) - 1;
  uint64_t h = mix(k) & V1MASK;
  while (V1T[h]) {
    if ((V1T[h] & KM) == k) return (int)(V1T[h] >> 56);
    h = (h + 1) & V1MASK;
  }
  if ((V1USED & 0xFFFFF) == 0) check_time();
  int N = PS.N[id], R = M * G - N, smax = PS.smax[id];
  int best = L[0];
  int ub = copy_guarantee(L, R);
  for (int s = smax; s >= lo && best < ub; s--) {
    if (!ALLOW[s]) continue;
    uint32_t cid = PS.child(id, s);
    int clo = next_lo(s);
    int mn = 1 << 20;
    for (int i = M - 1; i >= 0; i--) {
      if (i < M - 1 && L[i] == L[i + 1]) continue;
      uint8_t L2[MAXM];
      memcpy(L2, L, M);
      L2[i] += s;
      sort_desc(L2);
      if (copy_guarantee(L2, R - s) <= best) { mn = best; break; }
      int v = v1(cid, L2, clo);
      if (v < mn) mn = v;
      if (mn <= best) break;
    }
    if (mn > best) best = mn;
  }
  if (V1USED * 10 >= V1CAP * 9) { fprintf(stderr, "V1 table full\n"); printf("RESULT ABORT v1_full\n"); fflush(stdout); exit(4); }
  if (best < 1 || best > 255) { fprintf(stderr, "internal: V1 value out of range\n"); exit(3); }
  h = mix(k) & V1MASK;
  while (V1T[h]) h = (h + 1) & V1MASK;
  V1T[h] = k | ((uint64_t)best << 56);
  V1USED++;
  return best;
}
static int v1move(uint32_t id, const uint8_t* L, int lo, int v) {
  int smax = PS.smax[id];
  for (int s = smax; s >= lo; s--) {
    if (!ALLOW[s]) continue;
    uint32_t cid = PS.child(id, s);
    int clo = next_lo(s);
    bool ok = true;
    for (int i = M - 1; i >= 0 && ok; i--) {
      if (i < M - 1 && L[i] == L[i + 1]) continue;
      uint8_t L2[MAXM];
      memcpy(L2, L, M);
      L2[i] += s;
      sort_desc(L2);
      if (v1(cid, L2, clo) < v) ok = false;
    }
    if (ok) return s;
  }
  return 0;
}

struct St {
  uint32_t id;
  uint8_t lo;
  uint8_t L[MAXK][MAXM];
};
static void canon(St& x) {
  for (int j = 0; j < K; j++) sort_desc(x.L[j]);
  for (int i = 1; i < K; i++)
    for (int j = i; j > 0; j--) {
      int a = j - 1, b = j;
      if (Wt[a] != Wt[b]) break;
      if (std::lexicographical_compare(x.L[a], x.L[a] + M, x.L[b], x.L[b] + M)) {
        uint8_t tmp[MAXM];
        memcpy(tmp, x.L[a], M); memcpy(x.L[a], x.L[b], M); memcpy(x.L[b], tmp, M);
      } else break;
    }
}
static inline int payoff(const St& x) {
  int p = 0;
  for (int j = 0; j < K; j++) p += Wt[j] * x.L[j][0];
  return p;
}
static inline int upper_gs(const St& x) {
  int R = M * G - PS.N[x.id];
  int u = 0;
  for (int j = 0; j < K; j++) u += Wt[j] * copy_guarantee(x.L[j], R);
  return u;
}
static inline void v1bounds(const St& x, int P, int& ub, int& lb, int* jbest, int* vbest) {
  ub = 0; lb = P;
  int jb = -1, vb = 0;
  for (int j = 0; j < K; j++) {
    int v = v1(x.id, x.L[j], x.lo);
    ub += Wt[j] * v;
    int l = P + Wt[j] * (v - x.L[j][0]);
    if (l > lb) { lb = l; jb = j; vb = v; }
  }
  if (jbest) *jbest = jb;
  if (vbest) *vbest = vb;
}

static int KW = 1;
static inline void mkkey(const St& x, uint64_t* k) {
  k[0] = x.id; k[1] = 0;
  int pos = IDBITS;
  auto put = [&](uint64_t v, int nb) {
    if (pos < 64) {
      k[0] |= v << pos;
      if (pos + nb > 64) k[1] |= v >> (64 - pos);
    } else k[1] |= v << (pos - 64);
    pos += nb;
  };
  put(x.lo, LOBITS);
  for (int j = 0; j < K; j++)
    for (int i = 0; i < M - 1; i++) put(x.L[j][i], LBITS);
}
struct Slot1 { uint64_t k0; uint16_t lo, hi; uint8_t mv, used; };
struct Slot2 { uint64_t k0, k1; uint16_t lo, hi; uint8_t mv, used; };
static void* TABRAW = nullptr;
static uint64_t CAP = 0, CAPMASK = 0, NUSED = 0;
struct Ent { uint16_t* lo; uint16_t* hi; uint8_t* mv; };
static bool tfind(const uint64_t* k, Ent* out) {
  uint64_t h = mix(k[0] ^ mix(k[1])) & CAPMASK;
  if (KW == 1) {
    Slot1* T = (Slot1*)TABRAW;
    while (T[h].used) {
      if (T[h].k0 == k[0]) { if (out) *out = {&T[h].lo, &T[h].hi, &T[h].mv}; return true; }
      h = (h + 1) & CAPMASK;
    }
  } else {
    Slot2* T = (Slot2*)TABRAW;
    while (T[h].used) {
      if (T[h].k0 == k[0] && T[h].k1 == k[1]) { if (out) *out = {&T[h].lo, &T[h].hi, &T[h].mv}; return true; }
      h = (h + 1) & CAPMASK;
    }
  }
  return false;
}
static Ent tinsert(const uint64_t* k, int lo, int hi) {
  Ent e;
  if (tfind(k, &e)) return e;
  if (NUSED * 10 >= CAP * 9) {
    fprintf(stderr, "memo full (%llu slots); rerun with larger -cap\n", (unsigned long long)CAP);
    printf("RESULT ABORT memo_full\n");
    fflush(stdout);
    exit(4);
  }
  NUSED++;
  uint64_t h = mix(k[0] ^ mix(k[1])) & CAPMASK;
  if (KW == 1) {
    Slot1* T = (Slot1*)TABRAW;
    while (T[h].used) h = (h + 1) & CAPMASK;
    T[h].k0 = k[0]; T[h].lo = (uint16_t)lo; T[h].hi = (uint16_t)hi; T[h].mv = 0; T[h].used = 1;
    return {&T[h].lo, &T[h].hi, &T[h].mv};
  } else {
    Slot2* T = (Slot2*)TABRAW;
    while (T[h].used) h = (h + 1) & CAPMASK;
    T[h].k0 = k[0]; T[h].k1 = k[1]; T[h].lo = (uint16_t)lo; T[h].hi = (uint16_t)hi; T[h].mv = 0; T[h].used = 1;
    return {&T[h].lo, &T[h].hi, &T[h].mv};
  }
}

static int children(const St& x, uint32_t cid, int s, St* out) {
  int opts[MAXK][MAXM], nopt[MAXK];
  for (int j = 0; j < K; j++) {
    nopt[j] = 0;
    for (int i = 0; i < M; i++)
      if (i == 0 || x.L[j][i] != x.L[j][i - 1]) opts[j][nopt[j]++] = i;
  }
  int n = 0;
  int idx[MAXK] = {0, 0, 0};
  uint64_t seen[64][2];
  while (true) {
    St c = x;
    c.id = cid;
    c.lo = (uint8_t)next_lo(s);
    for (int j = 0; j < K; j++) c.L[j][opts[j][idx[j]]] += s;
    canon(c);
    uint64_t k[2];
    mkkey(c, k);
    bool dup = false;
    for (int q = 0; q < n; q++) if (seen[q][0] == k[0] && seen[q][1] == k[1]) { dup = true; break; }
    if (!dup) { seen[n][0] = k[0]; seen[n][1] = k[1]; out[n++] = c; }
    int j = 0;
    while (j < K) {
      if (++idx[j] < nopt[j]) break;
      idx[j] = 0; j++;
    }
    if (j == K) break;
  }
  return n;
}

static uint64_t V1CUT_LOSE = 0, V1CUT_WIN = 0;
static bool solve(const St& x, int t) {
  int P = payoff(x);
  if (P >= t) return true;
  int U = upper_gs(x);
  if (U < t) return false;
  uint64_t k[2];
  mkkey(x, k);
  Ent e = tinsert(k, P, U + 1);
  if (t <= *e.lo) return true;
  if (t >= *e.hi) return false;
  NODES++;
  if ((NODES & 0xFFFFF) == 0) check_time();
  if (USEV1) {
    int ub, lb;
    v1bounds(x, P, ub, lb, nullptr, nullptr);
    if (ub + 1 < *e.hi) *e.hi = (uint16_t)(ub + 1);
    if (lb > *e.lo) { *e.lo = (uint16_t)lb; *e.mv = LBMARK; }
    if (t <= *e.lo) { V1CUT_WIN++; return true; }
    if (t >= *e.hi) { V1CUT_LOSE++; return false; }
  }
  int smax = PS.smax[x.id];
  const int smin = x.lo;
  while (smax >= smin && smax >= 1 && !ALLOW[smax]) smax--;
  if (smax >= smin && smax >= 1) {
    int Pb = 0;
    for (int j = 0; j < K; j++) Pb += Wt[j] * std::max<int>(x.L[j][0], x.L[j][M - 1] + smax);
    if (Pb > *e.lo) { *e.lo = (uint16_t)Pb; *e.mv = (uint8_t)smax; }
    if (t <= *e.lo) return true;
  }
  int moves[64], nm = 0;
  int pm = (*e.mv >= smin && *e.mv <= smax) ? *e.mv : 0;
  if (pm) moves[nm++] = pm;
  if (ORDER == 0) { for (int s = smax; s >= smin; s--) if (s != pm) moves[nm++] = s; }
  else if (ORDER == 1) { for (int s = smin; s <= smax; s++) if (s != pm) moves[nm++] = s; }
  else {
    int c = (smin + smax) / 2;
    for (int d = 0; d <= smax; d++) {
      int a = c + d, b = c - d;
      if (a >= smin && a <= smax && a != pm) moves[nm++] = a;
      if (d > 0 && b >= smin && b <= smax && b != pm) moves[nm++] = b;
    }
  }
  St ch[64];
  int pend[64], pkey[64];
  for (int mi = 0; mi < nm; mi++) {
    int s = moves[mi];
    if (!ALLOW[s]) continue;
    uint32_t cid = PS.child(x.id, s);
    int nc = children(x, cid, s, ch);
    bool fail = false;
    int np = 0;
    for (int c = 0; c < nc && !fail; c++) {
      int Pc = payoff(ch[c]);
      if (Pc >= t) continue;
      if (upper_gs(ch[c]) < t) { fail = true; break; }
      uint64_t ck[2];
      mkkey(ch[c], ck);
      Ent f;
      if (tfind(ck, &f)) {
        if (t <= *f.lo) continue;
        if (t >= *f.hi) { fail = true; break; }
      }
      int sortkey = Pc;
      if (USEV1) {
        int ub, lb;
        v1bounds(ch[c], Pc, ub, lb, nullptr, nullptr);
        if (ub < t) { fail = true; break; }
        if (lb >= t) continue;
        sortkey = ub;
      }
      pkey[np] = sortkey;
      pend[np++] = c;
    }
    if (fail) continue;
    for (int a = 1; a < np; a++)
      for (int b = a; b > 0 && pkey[b] < pkey[b - 1]; b--) { std::swap(pkey[b], pkey[b - 1]); std::swap(pend[b], pend[b - 1]); }
    for (int q = 0; q < np && !fail; q++)
      if (!solve(ch[pend[q]], t)) fail = true;
    if (!fail) {
      if (t > *e.lo) { *e.lo = (uint16_t)t; *e.mv = (uint8_t)s; }
      return true;
    }
  }
  if (t < *e.hi) *e.hi = (uint16_t)t;
  return false;
}

static std::unordered_set<std::string> EXPORTED;
static std::vector<std::string> LINES;
static uint64_t EXP_LB = 0, EXP_MEMO = 0;
static std::string state_text(const std::vector<int>& cnt, const St& x) {
  std::string s;
  bool first = true;
  for (int v = G; v >= 1; v--)
    for (int r = 0; r < cnt[v]; r++) {
      if (!first) s += ",";
      s += std::to_string(v);
      first = false;
    }
  if (first) s = "-";
  for (int j = 0; j < K; j++) {
    s += " | ";
    for (int i = 0; i < M; i++) {
      if (i) s += ",";
      s += std::to_string(x.L[j][i]);
    }
  }
  return s;
}
static void export_dfs(const St& x, std::vector<int>& cnt, int t) {
  int P = payoff(x);
  if (P >= t) return;
  std::string txt = state_text(cnt, x);
  if (EXPORTED.count(txt)) return;
  int s = 0;
  uint64_t k[2];
  mkkey(x, k);
  Ent e;
  bool have = tfind(k, &e);
  if (have && *e.lo >= t && *e.mv >= 1 && *e.mv <= G) { s = *e.mv; EXP_MEMO++; }
  else if (USEV1) {
    int ub, lb, jb, vb;
    v1bounds(x, P, ub, lb, &jb, &vb);
    if (lb >= t && jb >= 0) {
      s = v1move(x.id, x.L[jb], x.lo, vb);
      EXP_LB++;
    }
  }
  if (s < 1) {
    fprintf(stderr, "export: state without a winning move: %s\n", txt.c_str());
    printf("RESULT ABORT export\n");
    exit(5);
  }
  EXPORTED.insert(txt);
  LINES.push_back(txt + " | " + std::to_string(s));
  uint32_t cid = PS.child(x.id, s);
  St ch[64];
  int nc = children(x, cid, s, ch);
  cnt[s]++;
  for (int c = 0; c < nc; c++) export_dfs(ch[c], cnt, t);
  cnt[s]--;
}

int main(int argc, char** argv) {
  int t1 = -1, tstart = -1, tlo = -1, thi = -1, caplog = 24, v1caplog = 22;
  double tlimit = -1;
  const char* certfile = nullptr;
  std::string wstr = "1,1", allowstr;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto nxt = [&]() { if (i + 1 >= argc) { fprintf(stderr, "missing value for %s\n", a.c_str()); exit(1); } return std::string(argv[++i]); };
    if (a == "-m") M = atoi(nxt().c_str());
    else if (a == "-K") K = atoi(nxt().c_str());
    else if (a == "-g") G = atoi(nxt().c_str());
    else if (a == "-w") wstr = nxt();
    else if (a == "-t") t1 = atoi(nxt().c_str());
    else if (a == "-tstart") tstart = atoi(nxt().c_str());
    else if (a == "-tlo") tlo = atoi(nxt().c_str());
    else if (a == "-thi") thi = atoi(nxt().c_str());
    else if (a == "-cert") certfile = argv[++i];
    else if (a == "-cap") caplog = atoi(nxt().c_str());
    else if (a == "-v1cap") v1caplog = atoi(nxt().c_str());
    else if (a == "-nov1") USEV1 = false;
    else if (a == "-mono") MU = atoi(nxt().c_str());
    else if (a == "-sizes") { allowstr = nxt(); RESTRICTED = true; }
    else if (a == "-tlimit") tlimit = atof(nxt().c_str());
    else if (a == "-order") { std::string o = nxt(); ORDER = o == "asc" ? 1 : o == "mid" ? 2 : 0; }
    else { fprintf(stderr, "unknown option %s\n", a.c_str()); return 1; }
  }
  if (M < 2 || M > MAXM || K < 1 || K > MAXK || G < 1 || G > 63 || M * G > 255) {
    fprintf(stderr, "need 2<=m<=4, 1<=K<=3, 1<=g<=63, m*g<=255\n");
    return 1;
  }
  if (MU >= G - 1) MU = -1;
  for (int s = 0; s < 64; s++) ALLOW[s] = !RESTRICTED;
  if (RESTRICTED) {
    size_t p = 0;
    while (p < allowstr.size()) {
      size_t q = allowstr.find(',', p);
      if (q == std::string::npos) q = allowstr.size();
      std::string tok = allowstr.substr(p, q - p);
      if (!tok.empty() && tok[0] == 'd') {
        int d = atoi(tok.c_str() + 1);
        if (d < 1) { fprintf(stderr, "bad -sizes token %s\n", tok.c_str()); return 1; }
        for (int s = d; s <= G; s += d) ALLOW[s] = true;
      } else if (tok.find('-') != std::string::npos) {
        size_t dash = tok.find('-');
        int a = atoi(tok.substr(0, dash).c_str()), b = atoi(tok.substr(dash + 1).c_str());
        for (int s = std::max(1, a); s <= std::min(G, b); s++) ALLOW[s] = true;
      } else {
        int a = atoi(tok.c_str());
        if (a >= 1 && a <= G) ALLOW[a] = true;
      }
      p = q + 1;
    }
  }
  ALLOW[0] = false;
  {
    int j = 0;
    size_t p = 0;
    while (p <= wstr.size() && j < MAXK) {
      size_t q = wstr.find(',', p);
      if (q == std::string::npos) q = wstr.size();
      Wt[j++] = atoi(wstr.substr(p, q - p).c_str());
      p = q + 1;
    }
    if (j != K) { fprintf(stderr, "need exactly K weights\n"); return 1; }
    Wsum = 0;
    for (int i = 0; i < K; i++) {
      if (Wt[i] < 1) { fprintf(stderr, "weights must be >= 1\n"); return 1; }
      Wsum += Wt[i];
    }
    for (int a2 = 0; a2 < K; a2++)
      for (int b2 = a2 + 2; b2 < K; b2++)
        if (Wt[a2] == Wt[b2] && Wt[a2 + 1] != Wt[a2]) { fprintf(stderr, "give equal weights consecutively\n"); return 1; }
    if (Wsum * M * G > 65000) { fprintf(stderr, "payoff range too large\n"); return 1; }
  }
  LBITS = 1;
  while ((1 << LBITS) <= M * G) LBITS++;
  IDBITS = std::min(28, 56 - LOBITS - LBITS * (M - 1));
  int keybits = IDBITS + LOBITS + LBITS * (M - 1) * K;
  KW = keybits <= 64 ? 1 : 2;
  CAP = 1ULL << caplog;
  CAPMASK = CAP - 1;
  TABRAW = calloc(CAP, KW == 1 ? sizeof(Slot1) : sizeof(Slot2));
  V1CAP = 1ULL << v1caplog;
  V1MASK = V1CAP - 1;
  V1T = (uint64_t*)calloc(V1CAP, sizeof(uint64_t));
  if (!TABRAW || !V1T) { fprintf(stderr, "cannot allocate tables\n"); return 2; }
  PS.init();
  St root;
  memset(&root, 0, sizeof(root));
  root.id = PS.root();
  root.lo = 1;
  int U0 = upper_gs(root);
  double T0 = now_s();
  if (tlimit > 0) DEADLINE = T0 + tlimit;
  printf("PARAMS m %d K %d w", M, K);
  for (int j = 0; j < K; j++) printf(" %d", Wt[j]);
  printf(" g %d W %d mono %d order %d v1 %d cap 2^%d (slot %zu B) v1cap 2^%d idbits %d lbits %d upper_root %d\n", G,
         Wsum, MU, ORDER, (int)USEV1, caplog, KW == 1 ? sizeof(Slot1) : sizeof(Slot2), v1caplog, IDBITS, LBITS, U0);
  printf("SIZES");
  for (int s2 = 1; s2 <= G; s2++) if (ALLOW[s2]) printf(" %d", s2);
  printf("\n");
  fflush(stdout);
  int best_win = -1, best_lose = -1;
  auto test = [&](int t) {
    double a = now_s();
    uint64_t n0 = NODES;
    bool r = solve(root, t);
    printf("TEST t %d (= %d/%d) %s  time %.2fs  nodes %llu  memo %llu  v1 %llu  packsets %zu  v1cuts W%llu L%llu  rss %.0fMB\n",
           t, t, Wsum * G, r ? "WIN" : "LOSE", now_s() - a, (unsigned long long)(NODES - n0),
           (unsigned long long)NUSED, (unsigned long long)V1USED, PS.N.size(), (unsigned long long)V1CUT_WIN,
           (unsigned long long)V1CUT_LOSE, maxrss_mb());
    fflush(stdout);
    return r;
  };
  if (t1 >= 0) {
    if (test(t1)) best_win = t1; else best_lose = t1;
  } else if (tstart >= 0) {
    int t = tstart;
    while (true) {
      if (test(t)) { best_win = t; t++; }
      else { best_lose = t; break; }
    }
  } else {
    if (tlo < 0) tlo = Wsum * G;
    if (thi < 0) thi = U0 + 1;
    int hi = thi;
    if (test(tlo)) best_win = tlo;
    else {
      hi = tlo;
      if (test(Wsum * G)) best_win = Wsum * G;
      else { fprintf(stderr, "internal: W*g not won\n"); return 3; }
    }
    while (hi - best_win > 1) {
      int mid = (best_win + hi) / 2;
      if (test(mid)) best_win = mid; else hi = mid;
    }
    best_lose = hi;
  }
  printf("RESULT m %d K %d w", M, K);
  for (int j = 0; j < K; j++) printf(" %d", Wt[j]);
  printf(" g %d mono %d%s  win %d/%d  lose %d/%d  total_time %.2fs  memo %llu  v1 %llu  rss %.0fMB\n", G, MU,
         RESTRICTED ? " sizes-restricted" : "", best_win, Wsum * G, best_lose, Wsum * G, now_s() - T0, (unsigned long long)NUSED, (unsigned long long)V1USED, maxrss_mb());
  fflush(stdout);
  if (certfile && best_win > 0) {
    double a = now_s();
    std::vector<int> cnt(G + 1, 0);
    export_dfs(root, cnt, best_win);
    FILE* CF = fopen(certfile, "w");
    if (!CF) { fprintf(stderr, "cannot write %s\n", certfile); return 2; }
    fprintf(CF, "COINLB 1\n%d %d %d\n", M, K, G);
    for (int j = 0; j < K; j++) fprintf(CF, "%s%d", j ? " " : "", Wt[j]);
    fprintf(CF, "\nT %d %d\nN %zu\n", best_win, Wsum * G, LINES.size());
    for (auto& l : LINES) fprintf(CF, "%s\n", l.c_str());
    fprintf(CF, "END\n");
    fclose(CF);
    printf("CERT %s states %zu (memo moves %llu, single-copy moves %llu) threshold %d/%d  time %.2fs  rss %.0fMB\n",
           certfile, LINES.size(), (unsigned long long)EXP_MEMO, (unsigned long long)EXP_LB, best_win, Wsum * G,
           now_s() - a, maxrss_mb());
  }
  return 0;
}
