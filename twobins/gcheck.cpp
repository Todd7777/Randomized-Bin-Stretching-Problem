// gcheck.cpp: checks a certificate of a grid game value (paper, App. E.3), as written by gridgame.cpp.
// g++ -O2 -std=c++17 -o gcheck gcheck.cpp && ./gcheck FILE
// Prints one line, PASS (exit 0) or FAIL (exit 1).
//
// File: a line GRIDCERT k K w_1..w_K T n, then n states, id 0 first:
//   N c_1..c_k a_1..a_K v S                 a stop
//   N c_1..c_k a_1..a_K v J s d_0..d_{2^K-1}  a job of size s; d_x is the state after answer x
// c_i jobs of size i (total N), smaller load a_j of copy j, claim v. Bit j-1 of x set: copy j keeps a_j,
// else a_j becomes min(a_j+s, N-a_j). Checks: (1) format; (2) state 0 is empty with v >= T; (3) every
// state is feasible (two bins of size k) with 0 <= a_j <= N/2; (4) a stop pays sum_j w_j (N-a_j) >= v;
// (5) a job keeps the input feasible and every d_x is its successor with claim >= v.
// '#' lines are comments. Integers are at most 1e18 in absolute value, k <= 10000, K <= 20.
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

typedef long long ll;
typedef __int128 wide;

static const ll LIMIT = 1000000000000000000LL;
static const ll KMAX = 10000, KCOPIES_MAX = 20;

static std::string str(ll x) { return std::to_string(x); }

[[noreturn]] static void fail(int check, ll id, const std::string& why) {
  if (id < 0) printf("FAIL check %d header: %s\n", check, why.c_str());
  else printf("FAIL check %d state %lld: %s\n", check, id, why.c_str());
  exit(1);
}

struct Reader {
  FILE* f;
  std::vector<char> buf;
  size_t pos = 0, len = 0;
  char tok[64];
  size_t tlen = 0;
  explicit Reader(FILE* fp) : f(fp), buf(1 << 20) {}

  int peek() {
    if (pos == len) {
      pos = 0;
      len = fread(buf.data(), 1, buf.size(), f);
      if (len == 0) {
        if (ferror(f)) { printf("FAIL io: read error\n"); exit(1); }
        return EOF;
      }
    }
    return (unsigned char)buf[pos];
  }
  static bool blank(int ch) { return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\v' || ch == '\f'; }
  void skip_blanks() { while (blank(peek())) pos++; }

  bool next_line() {
    for (;;) {
      skip_blanks();
      int ch = peek();
      if (ch == EOF) return false;
      if (ch != '\n' && ch != '#') return true;
      while (ch != '\n' && ch != EOF) { pos++; ch = peek(); }
      if (ch == '\n') pos++;
    }
  }
  bool token() {
    skip_blanks();
    int ch = peek();
    if (ch == '\n' || ch == EOF) return false;
    for (tlen = 0; ch != '\n' && ch != EOF && !blank(ch); tlen++) {
      if (tlen < sizeof tok) tok[tlen] = (char)ch;
      pos++;
      ch = peek();
    }
    return true;
  }
  bool end_line() {
    skip_blanks();
    int ch = peek();
    if (ch == '\n') pos++;
    return ch == '\n' || ch == EOF;
  }
  bool is(const char* word) const { return tlen == strlen(word) && memcmp(tok, word, tlen) == 0; }
  bool integer(ll& v) const {
    if (tlen > sizeof tok) return false;
    size_t i = (tok[0] == '+' || tok[0] == '-') ? 1 : 0;
    if (i == tlen) return false;
    ll x = 0;
    for (; i < tlen; i++) {
      if (tok[i] < '0' || tok[i] > '9') return false;
      const int d = tok[i] - '0';
      if (x > (LIMIT - d) / 10) return false;
      x = 10 * x + d;
    }
    v = tok[0] == '-' ? -x : x;
    return true;
  }
  static std::string label(const char* name, ll index) {
    return index < 0 ? std::string(name) : std::string(name) + "_" + str(index);
  }
  ll field(ll id, const char* name, ll index = -1) {
    ll v = 0;
    if (!token()) fail(1, id, "too few tokens: " + label(name, index) + " is missing");
    if (!integer(v)) fail(1, id, label(name, index) + " is not an integer in [-1e18, 1e18]");
    return v;
  }
};

// The jobs (c_i of size i, and one of size e if e >= 1) fit into two bins of size k.
static bool feasible(const ll* c, ll k, ll e, ll tot, std::vector<char>& reach) {
  if (tot > 2 * k) return false;
  std::fill(reach.begin(), reach.end(), 0);
  reach[0] = 1;
  for (ll i = 1; i <= k; i++) {
    const ll m = c[i - 1] + (i == e ? 1 : 0);
    for (ll r = 0; r < m; r++)
      for (ll t = k; t >= i; t--)
        if (reach[t - i]) reach[t] = 1;
  }
  for (ll t = std::max(tot - k, 0LL); t <= k; t++)
    if (reach[t]) return true;
  return false;
}

static int run(const char* path) {
  FILE* f = fopen(path, "rb");
  if (!f) { printf("FAIL io: cannot open the input file\n"); return 1; }
  Reader in(f);

  if (!in.next_line() || !in.token()) fail(1, -1, "the file has no GRIDCERT line");
  if (!in.is("GRIDCERT")) fail(1, -1, "the first line does not start with GRIDCERT");
  const ll k = in.field(-1, "k");
  if (k < 1 || k > KMAX) fail(1, -1, "k = " + str(k) + " is outside 1.." + str(KMAX));
  const ll K = in.field(-1, "K");
  if (K < 1) fail(1, -1, "K < 1");
  if (K > KCOPIES_MAX) fail(1, -1, "K = " + str(K) + " is above this checker's limit " + str(KCOPIES_MAX));
  std::vector<ll> w(K);
  for (ll j = 0; j < K; j++) w[j] = in.field(-1, "w", j + 1);
  const ll T = in.field(-1, "T");
  const ll n = in.field(-1, "n");
  if (!in.end_line()) fail(1, -1, "too many tokens in the header line");
  wide W = 0;
  for (ll j = 0; j < K; j++) {
    if (w[j] < 0) fail(1, -1, "w_" + str(j + 1) + " < 0");
    W += w[j];
  }
  if (W <= 0) fail(1, -1, "W = sum of the weights is 0");
  if (n < 1) fail(1, -1, "n < 1");

  const ll width = k + K + 2, R = 1LL << K;
  std::vector<ll> row, job_s, first, succ;  // first: index of d_0 in succ, -1 for a stop
  ll cnt = 0;
  while (in.next_line()) {
    if (cnt == n) fail(1, n, "extra state line: the header says n = " + str(n));
    const ll id = cnt++;
    row.push_back(in.field(id, "N"));
    for (ll i = 1; i <= k; i++) row.push_back(in.field(id, "c", i));
    for (ll j = 1; j <= K; j++) row.push_back(in.field(id, "a", j));
    row.push_back(in.field(id, "v"));
    if (!in.token()) fail(1, id, "too few tokens: S or J is missing");
    if (in.is("S")) {
      job_s.push_back(0);
      first.push_back(-1);
    } else if (in.is("J")) {
      job_s.push_back(in.field(id, "s"));
      first.push_back((ll)succ.size());
      for (ll x = 0; x < R; x++) succ.push_back(in.field(id, "d", x));
    } else {
      fail(1, id, "the token after v is neither S nor J");
    }
    if (!in.end_line()) fail(1, id, "too many tokens");
  }
  fclose(f);
  if (cnt < n) fail(1, cnt, "missing state line: the file has " + str(cnt) + ", the header says n = " + str(n));

  std::vector<char> reach(k + 1);
  for (ll id = 0; id < n; id++) {
    const ll* r = &row[id * width];
    const ll N = r[0], *c = r + 1, *a = r + 1 + k, v = r[1 + k + K];
    if (id == 0) {
      if (N != 0) fail(2, id, "the root has N != 0");
      for (ll i = 1; i <= k; i++)
        if (c[i - 1] != 0) fail(2, id, "the root has c_" + str(i) + " != 0");
      for (ll j = 1; j <= K; j++)
        if (a[j - 1] != 0) fail(2, id, "the root has a_" + str(j) + " != 0");
      if (v < T) fail(2, id, "the root has v < T");
    }
    for (ll i = 1; i <= k; i++)
      if (c[i - 1] < 0) fail(3, id, "c_" + str(i) + " < 0");
    wide sum = 0;
    for (ll i = 1; i <= k; i++) sum += (wide)i * c[i - 1];
    if (sum != N) fail(3, id, "N != sum_i i*c_i");
    if (N > 2 * k) fail(3, id, "N > 2k");
    if (!feasible(c, k, 0, N, reach)) fail(3, id, "H is not feasible");
    for (ll j = 1; j <= K; j++)
      if (a[j - 1] < 0 || a[j - 1] > N / 2) fail(3, id, "a_" + str(j) + " is outside 0..floor(N/2)");

    if (first[id] < 0) {
      wide S = 0;
      for (ll j = 0; j < K; j++) S += (wide)w[j] * (N - a[j]);
      if (S < v) fail(4, id, "the stop value sum_j w_j (N - a_j) is < v");
      continue;
    }
    const ll s = job_s[id];
    if (s < 1 || s > k) fail(5, id, "s = " + str(s) + " is outside 1..k");
    if (!feasible(c, k, s, N + s, reach)) fail(5, id, "H + {s} is not feasible");
    for (ll x = 0; x < R; x++) {
      const ll d = succ[first[id] + x];
      auto bad = [&](const std::string& what) { fail(5, id, "d_" + str(x) + " = " + str(d) + " " + what); };
      if (d < 0 || d >= n) bad("is not a state id");
      const ll* q = &row[d * width];
      if (q[0] != N + s) bad("has total != N + s");
      for (ll i = 1; i <= k; i++)
        if (q[i] != c[i - 1] + (i == s ? 1 : 0)) bad("has counts != c + e_s (at size " + str(i) + ")");
      for (ll j = 1; j <= K; j++) {
        const bool big = (x >> (j - 1)) & 1;
        const ll want = big ? a[j - 1] : std::min(a[j - 1] + s, N - a[j - 1]);
        if (q[k + j] != want) bad("has a_" + str(j) + " != " + str(want));
      }
      if (q[1 + k + K] < v) bad("has v < v of this state");
    }
  }
  printf("PASS k %lld weights ", k);
  for (ll j = 0; j < K; j++) printf("%s%lld", j ? "," : "", w[j]);
  printf(" T %lld states %lld\n", T, n);
  return 0;
}

int main(int argc, char** argv) {
  if (argc != 2) { printf("FAIL usage: gcheck FILE\n"); return 1; }
  try {
    return run(argv[1]);
  } catch (...) {
    printf("FAIL internal: out of memory\n");
    return 1;
  }
}
