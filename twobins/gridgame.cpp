// gridgame.cpp: exact value of the K-copy grid game for two bins (paper, App. E.3).
// g++ -O2 -fopenmp -std=c++17 -o gridgame gridgame.cpp && ./gridgame k w1,...,wK

#include <chrono>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <new>
#include <string>
#include <unordered_map>
#include <vector>
#include <sys/resource.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef int64_t i64;
typedef uint64_t u64;

static const int MAXK = 31;      // subset sums 0..2k must fit in one 64-bit word
static const int MAXCOPIES = 4;

static int g_k = 0;              // bin capacity in grid units
static int g_K = 0;              // number of copies
static i64 g_w[MAXCOPIES];       // weights
static i64 g_W = 0;              // sum of the weights

static std::vector<std::string> g_key;         // id -> count vector, byte s-1 = number of jobs of size s
static std::vector<int> g_N;                   // id -> total size N
static std::vector<int> g_rank;                // id -> position of the multiset inside its level
static std::vector<int> g_child;               // id*(k+1)+s -> id of H+{s}, or -1 if H+{s} is infeasible
static std::vector<std::vector<int>> g_level;  // N -> ids of the multisets with total N
static std::vector<size_t> g_box;              // N -> (floor(N/2)+1)^K table entries per multiset
static std::vector<i64*> g_tab;                // N -> value table of level N (nullptr if released)

[[noreturn]] static void die(const char* msg) {
  fprintf(stderr, "gridgame: error: %s\n", msg);
  exit(2);
}

static double wall_seconds() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

static long peak_rss_kb() {
  struct rusage ru;
  if (getrusage(RUSAGE_SELF, &ru) != 0) return -1;
  return ru.ru_maxrss;  // kilobytes on Linux
}

// ------------------------------------------------------------------------------- feasibility
// bits has bit t set iff some sub-multiset of H sums to t (only t <= 2k is kept).
static u64 add_job(u64 bits, int s) {
  const u64 mask = (1ULL << (2 * g_k + 1)) - 1;  // 2k+1 <= 63
  return (bits | (bits << s)) & mask;
}

// A multiset with total n and subset-sum bitset bits is feasible iff some sub-multiset sum t
// satisfies n-k <= t <= k (that sub-multiset in one bin, the rest in the other).
static bool feasible(int n, u64 bits) {
  if (n > 2 * g_k) return false;
  const int lo = n > g_k ? n - g_k : 0;
  const int hi = n < g_k ? n : g_k;
  for (int t = lo; t <= hi; ++t)
    if ((bits >> t) & 1ULL) return true;
  return false;
}

// ------------------------------------------------------------------------------- enumeration
// Choose the number of jobs of size s, s = 1..k in turn; stop adding jobs of size s as soon as
// the partial multiset becomes infeasible (every superset is then infeasible as well).
static void enumerate_rec(int s, int n, u64 bits, std::string& cur) {
  if (s > g_k) {
    g_key.push_back(cur);
    g_N.push_back(n);
    return;
  }
  int c = 0;
  for (;;) {
    cur[s - 1] = (char)c;
    enumerate_rec(s + 1, n, bits, cur);
    if (n + s > 2 * g_k) break;
    const u64 nb = add_job(bits, s);
    if (!feasible(n + s, nb)) break;
    n += s;
    bits = nb;
    ++c;
  }
  cur[s - 1] = 0;
}

static void build_multisets() {
  std::string cur((size_t)g_k, '\0');
  enumerate_rec(1, 0, 1ULL, cur);
  const size_t M = g_key.size();
  std::unordered_map<std::string, int> id_of;
  id_of.reserve(2 * M);
  for (size_t i = 0; i < M; ++i)
    if (!id_of.emplace(g_key[i], (int)i).second) die("duplicate multiset in the enumeration");
  g_child.assign(M * (size_t)(g_k + 1), -1);
  g_rank.assign(M, -1);
  g_level.assign((size_t)(2 * g_k + 1), std::vector<int>());
  for (size_t i = 0; i < M; ++i) {
    // Re-derive the total and the subset sums from the stored count vector.
    u64 bits = 1ULL;
    int n = 0;
    for (int s = 1; s <= g_k; ++s)
      for (int c = 0; c < (int)g_key[i][s - 1]; ++c) {
        bits = add_job(bits, s);
        n += s;
      }
    if (n != g_N[i] || !feasible(n, bits)) die("enumerated multiset fails the feasibility re-check");
    for (int s = 1; s <= g_k; ++s) {
      const bool f = feasible(n + s, add_job(bits, s));
      std::string key2 = g_key[i];
      key2[s - 1] = (char)(key2[s - 1] + 1);
      const auto it = id_of.find(key2);
      const int c = (it == id_of.end()) ? -1 : it->second;
      if (f != (c >= 0)) die("child lookup disagrees with the feasibility test");
      g_child[i * (size_t)(g_k + 1) + s] = c;
    }
    g_rank[i] = (int)g_level[n].size();
    g_level[n].push_back((int)i);
  }
}

// ------------------------------------------------------------------------------- evaluation
// Fill out[] (the table of multiset id, total N) from the finished tables of its children.
template <int KK>
static void eval_multiset(int N, int id, i64* out) {
  const int k = g_k;
  const int h = N / 2;
  const size_t L = (size_t)h + 1;
  size_t ps[KK];  // strides of this table
  ps[0] = 1;
  for (int j = 1; j < KK; ++j) ps[j] = ps[j - 1] * L;
  const size_t box = ps[KK - 1] * L;

  // The adversary may stop: S(a) = sum_j w_j (N - a_j).
  {
    int a[KK];
    for (int j = 0; j < KK; ++j) a[j] = 0;
    for (size_t idx = 0; idx < box; ++idx) {
      i64 S = 0;
      for (int j = 0; j < KK; ++j) S += g_w[j] * (i64)(N - a[j]);
      out[idx] = S;
      for (int j = 0; j < KK; ++j) {
        if (a[j] < h) { ++a[j]; break; }
        a[j] = 0;
      }
    }
  }

  // The adversary sends s; the K copies answer with the joint choice that is worst for him.
  constexpr int R = 1 << (KK - 1);  // joint choices of copies 2..K
  int sig[MAXK + 1];
  for (int s = 1; s <= k; ++s) {
    const int c = g_child[(size_t)id * (size_t)(k + 1) + s];
    if (c < 0) continue;  // H+{s} infeasible
    const int N2 = N + s;
    const int h2 = N2 / 2;
    const size_t L2 = (size_t)h2 + 1;
    size_t cs[KK];  // strides of the child table
    cs[0] = 1;
    for (int j = 1; j < KK; ++j) cs[j] = cs[j - 1] * L2;
    const i64* C = g_tab[N2] + (size_t)g_rank[c] * g_box[N2];
    for (int v = 0; v <= h; ++v) {
      const int up = v + s, other = N - v;
      sig[v] = up < other ? up : other;  // "small": new smaller load after s joins the smaller bin
      if (sig[v] < v || sig[v] > h2) die("internal: child index out of range");
    }
    int a[KK];
    for (int j = 0; j < KK; ++j) a[j] = 0;
    size_t B[R];
    for (;;) {
      // Offsets in the child table of the 2^(K-1) joint choices of copies 2..K, for the current
      // (a_2..a_K); "big" keeps a_j, "small" moves it to sig[a_j].
      size_t prow = 0;
      B[0] = 0;
      int n = 1;
      for (int j = 1; j < KK; ++j) {
        prow += (size_t)a[j] * ps[j];
        const size_t o_big = (size_t)a[j] * cs[j];
        const size_t o_small = (size_t)sig[a[j]] * cs[j];
        for (int t = 0; t < n; ++t) {
          B[n + t] = B[t] + o_small;
          B[t] += o_big;
        }
        n <<= 1;
      }
      i64* row = out + prow;
      for (int a0 = 0; a0 <= h; ++a0) {
        const int b_small = sig[a0];
        i64 m = INT64_MAX;
        for (int t = 0; t < R; ++t) {
          const i64 x = C[B[t] + (size_t)a0];
          const i64 y = C[B[t] + (size_t)b_small];
          if (x < m) m = x;
          if (y < m) m = y;
        }
        if (m > row[a0]) row[a0] = m;
      }
      int j = 1;
      while (j < KK && a[j] == h) {
        a[j] = 0;
        ++j;
      }
      if (j >= KK) break;
      ++a[j];
    }
  }
}

template <int KK>
static i64 solve_levels(size_t* peak_table_bytes) {
  const bool verbose = getenv("GRIDGAME_VERBOSE") != nullptr;
  size_t cur = 0, peak = 0;
  g_tab.assign((size_t)(2 * g_k + 1), nullptr);
  for (int N = 2 * g_k; N >= 0; --N) {
    const double t0 = wall_seconds();
    const std::vector<int>& ids = g_level[(size_t)N];
    const size_t cnt = ids.size(), box = g_box[(size_t)N];
    i64* tab = new (std::nothrow) i64[cnt * box + 1];
    if (!tab) die("out of memory while allocating a level table");
    g_tab[(size_t)N] = tab;
    cur += cnt * box * sizeof(i64);
    if (cur > peak) peak = cur;
    const long ncnt = (long)cnt;
#pragma omp parallel for schedule(dynamic, 1)
    for (long r = 0; r < ncnt; ++r) eval_multiset<KK>(N, ids[(size_t)r], tab + (size_t)r * box);
    if (N + g_k <= 2 * g_k) {  // level N+k has no parent below N
      const size_t M = (size_t)(N + g_k);
      cur -= g_level[M].size() * g_box[M] * sizeof(i64);
      delete[] g_tab[M];
      g_tab[M] = nullptr;
    }
    if (verbose)
      fprintf(stderr, "gridgame: level N=%2d  multisets %8zu  entries %12zu  %8.3f s\n", N, cnt,
              cnt * box, wall_seconds() - t0);
  }
  *peak_table_bytes = peak;
  return g_tab[0][0];  // the root: empty multiset, all a_j = 0
}

// ------------------------------------------------------------------------------- main
static bool parse_nonneg(const std::string& s, i64 limit, i64* out) {
  if (s.empty()) return false;
  i64 v = 0;
  for (char ch : s) {
    if (ch < '0' || ch > '9') return false;
    v = v * 10 + (ch - '0');
    if (v > limit) return false;
  }
  *out = v;
  return true;
}

static i64 gcd64(i64 a, i64 b) {
  while (b != 0) {
    const i64 t = a % b;
    a = b;
    b = t;
  }
  return a;
}

int main(int argc, char** argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s k w1,w2,...,wK   (1 <= K <= 4, integer weights >= 0, positive sum)\n",
            argv[0]);
    return 2;
  }
  i64 kv = 0;
  if (!parse_nonneg(argv[1], MAXK, &kv) || kv < 1) die("k must be an integer in 1..31");
  g_k = (int)kv;
  {
    const std::string ws = argv[2];
    size_t pos = 0;
    for (;;) {
      const size_t comma = ws.find(',', pos);
      const std::string tok = ws.substr(pos, comma == std::string::npos ? std::string::npos : comma - pos);
      if (g_K >= MAXCOPIES) die("at most 4 weights are supported");
      i64 v = 0;
      if (!parse_nonneg(tok, (i64)1000000000000LL, &v)) die("weights must be integers in 0..10^12");
      g_w[g_K++] = v;
      if (comma == std::string::npos) break;
      pos = comma + 1;
    }
  }
  for (int j = 0; j < g_K; ++j) g_W += g_w[j];
  if (g_W <= 0) die("the weights must have a positive sum");
  std::string wstr;
  for (int j = 0; j < g_K; ++j) {
    if (j) wstr += ",";
    wstr += std::to_string((long long)g_w[j]);
  }
  int threads = 1;
#ifdef _OPENMP
  threads = omp_get_max_threads();
#endif

  const double t0 = wall_seconds();
  build_multisets();
  const double t1 = wall_seconds();

  // Table sizes; replay the allocate/release order of solve_levels to predict its peak.
  g_box.assign((size_t)(2 * g_k + 1), 0);
  size_t entries = 0, pred_cur = 0, pred_peak = 0;
  for (int N = 0; N <= 2 * g_k; ++N) {
    size_t b = 1;
    for (int j = 0; j < g_K; ++j) b *= (size_t)(N / 2 + 1);
    g_box[(size_t)N] = b;
    entries += g_level[(size_t)N].size() * b;
  }
  for (int N = 2 * g_k; N >= 0; --N) {
    pred_cur += g_level[(size_t)N].size() * g_box[(size_t)N];
    if (pred_cur > pred_peak) pred_peak = pred_cur;
    if (N + g_k <= 2 * g_k) pred_cur -= g_level[(size_t)(N + g_k)].size() * g_box[(size_t)(N + g_k)];
  }
  fprintf(stderr,
          "gridgame: k=%d K=%d weights=%s threads=%d feasible_multisets=%zu table_entries=%zu "
          "predicted_peak_table=%.1f MiB\n",
          g_k, g_K, wstr.c_str(), threads, g_key.size(), entries,
          (double)pred_peak * sizeof(i64) / 1048576.0);

  size_t peak_bytes = 0;
  i64 T = 0;
  switch (g_K) {
    case 1: T = solve_levels<1>(&peak_bytes); break;
    case 2: T = solve_levels<2>(&peak_bytes); break;
    case 3: T = solve_levels<3>(&peak_bytes); break;
    case 4: T = solve_levels<4>(&peak_bytes); break;
    default: die("K must be in 1..4");
  }
  const double t2 = wall_seconds();

  const i64 den = g_W * (i64)g_k;
  const i64 g = gcd64(T, den);
  printf("RESULT k %d weights %s T %" PRId64 " W %" PRId64 " value %" PRId64 "/%" PRId64 " = %" PRId64
         "/%" PRId64 "\n",
         g_k, wstr.c_str(), T, g_W, T, den, T / g, den / g);
  fflush(stdout);
  fprintf(stderr,
          "gridgame: time enumerate=%.3f s solve=%.3f s total=%.3f s; peak table memory=%.1f MiB; "
          "peak RSS=%ld KiB (%.1f MiB)\n",
          t1 - t0, t2 - t1, t2 - t0, (double)peak_bytes / 1048576.0, peak_rss_kb(),
          (double)peak_rss_kb() / 1024.0);
  return 0;
}
