// vcheck.cpp -- second, separately written checker for potential certificates of the rounded two-bin lottery
// game (paper, App. E).  Written from the model, not from the solver; shares no code with
// rg2.cpp or rgcheck.py.  Integer arithmetic only.
//
// usage: vcheck CERT            (OpenMP threads from OMP_NUM_THREADS)
// Accepts iff (a) the root state is listed with the header's root value, (b) every listed state is well formed and
// its payoff sum_j w_j v_j is at most its potential, (c) for every listed state and every legal adversary move
// (fine class c, volume bit nu, overflow pattern of every copy) some joint response leads to a listed state whose
// potential is at most the current one.  Then E[cost] <= T(root) / (W k r) for every real packable input.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <omp.h>
using namespace std;

static int k = -1, r = -1, x2 = -1, K = 0, F, NMAX;
static vector<int> w;
static long long rootT = -1;

struct St { int N; vector<int> H; vector<pair<int,int>> P; };

static string key(int N, const vector<int> &H, const vector<pair<int,int>> &P) {
  string s;
  s.push_back((char)(N & 255)); s.push_back((char)(N >> 8));
  s.push_back((char)H.size());
  for (int c : H) s.push_back((char)c);
  for (auto &p : P) { s.push_back((char)(p.first & 255)); s.push_back((char)(p.first >> 8));
                      s.push_back((char)(p.second & 255)); s.push_back((char)(p.second >> 8)); }
  return s;
}

// can the multiset H (positive ints) be split into two groups, each of sum <= cap?
static bool splits(const vector<int> &H, int cap) {
  int tot = 0; for (int c : H) tot += c;
  if (tot > 2 * cap) return false;
  vector<char> can(cap + 1, 0); can[0] = 1;
  for (int c : H) for (int s = cap; s >= c; s--) if (can[s - c]) can[s] = 1;
  for (int s = 0; s <= cap; s++) if (can[s] && tot - s <= cap) return true;
  return false;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: vcheck CERT\n"); return 2; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror("open"); return 2; }
  vector<St> S; vector<long long> TV;
  unordered_map<string, long long> D;
  static char line[1 << 16];
  if (!fgets(line, sizeof line, f)) { fprintf(stderr, "empty file\n"); return 2; }
  {  // header: "# rounded-game potential certificate: k K r R x2 X weights W mode M root T"
    string h = string(" ") + line; auto grab = [&](const char *name) -> string {
      string pat = string(" ") + name + " "; size_t p = h.find(pat); if (p == string::npos) return "";
      p += pat.size(); size_t q = h.find_first_of(" \n", p); return h.substr(p, q - p); };
    k = atoi(grab("k").c_str()); r = atoi(grab("r").c_str()); x2 = atoi(grab("x2").c_str());
    rootT = atoll(grab("root").c_str());
    if (grab("mode") != "rounded") { fprintf(stderr, "FAIL: only the rounded game is handled\n"); return 1; }
    string ws = grab("weights"); size_t p = 0;
    while (p < ws.size()) { size_t q = ws.find(',', p); if (q == string::npos) q = ws.size(); w.push_back(atoi(ws.substr(p, q - p).c_str())); p = q + 1; }
  }
  K = (int)w.size(); F = k * r; NMAX = 2 * F;
  long long W = 0; for (int x : w) { if (x <= 0) { fprintf(stderr, "FAIL: weight\n"); return 1; } W += x; }
  if (k < 2 || r < 1 || (x2 != 0 && x2 != 1) || K < 1 || K > 8) { fprintf(stderr, "FAIL: header\n"); return 1; }
  while (fgets(line, sizeof line, f)) {
    if (line[0] == '#' || line[0] == '\n') continue;
    char *a = strtok(line, "|"), *b = strtok(NULL, "|"), *c = strtok(NULL, "|\n");
    if (!a || !b || !c) { fprintf(stderr, "FAIL: bad line\n"); return 1; }
    St s; long long T;
    if (sscanf(a, "%d %lld", &s.N, &T) != 2) { fprintf(stderr, "FAIL: bad N T\n"); return 1; }
    { char *q = b; while (*q == ' ') q++;
      if (*q != '-') { char *u = strtok(q, " \t"); while (u) { s.H.push_back(atoi(u)); u = strtok(NULL, " \t"); } } }
    { char *u = strtok(c, " \t\n"); while (u) { int x, y; if (sscanf(u, "%d,%d", &x, &y) != 2) { fprintf(stderr, "FAIL: pair\n"); return 1; }
        s.P.push_back({x, y}); u = strtok(NULL, " \t\n"); } }
    sort(s.H.begin(), s.H.end());
    if ((int)s.P.size() != K) { fprintf(stderr, "FAIL: wrong number of copies\n"); return 1; }
    string kk = key(s.N, s.H, s.P);
    if (D.count(kk)) { fprintf(stderr, "FAIL: duplicate state\n"); return 1; }
    D[kk] = T; S.push_back(s); TV.push_back(T);
  }
  fclose(f);
  {  // (a) root
    vector<int> H0; vector<pair<int,int>> P0(K, {0, 0});
    auto it = D.find(key(0, H0, P0));
    if (it == D.end() || it->second != rootT) { printf("FAIL: root missing or root value differs\n"); return 1; }
  }
  printf("vcheck: k %d r %d x2 %d K %d W %lld, %zu states, root %lld\n", k, r, x2, K, W, S.size(), rootT); fflush(stdout);
  long long fails = 0, moves = 0;
  #pragma omp parallel for schedule(dynamic, 256) reduction(+:fails, moves)
  for (long long i = 0; i < (long long)S.size(); i++) {
    if (fails) continue;
    const St &s = S[i]; long long T = TV[i];
    // (b) well formed, payoff
    bool ok = (s.N >= 0 && s.N <= NMAX);
    for (int c : s.H) if (c < 1 || c > k - 1) ok = false;
    if (ok && !s.H.empty() && !splits(s.H, k - 1)) ok = false;
    vector<int> e(K);
    long long pay = 0;
    for (int j = 0; j < K && ok; j++) {
      int u = s.P[j].first, v = s.P[j].second;
      e[j] = u + v - s.N;
      if (u < 0 || u > v || (e[j] != 0 && e[j] != 1) || (e[j] == 1 && u == 0)) ok = false;
      pay += (long long)w[j] * v;
    }
    if (!ok || pay > T) {
      #pragma omp critical
      printf("FAIL (b) at state %lld (N %d)\n", i, s.N);
      fails++; continue;
    }
    // (c) every legal move
    for (int c = 0; c < F && !fails; c++) for (int nu = 0; nu <= 1; nu++) {
      if (s.N == 0 && nu == 0) continue;
      int N2 = s.N + c + nu; if (N2 > NMAX) continue;
      int C = c / r; vector<int> H2 = s.H;
      if (C >= 1) { H2.push_back(C); sort(H2.begin(), H2.end()); if (!splits(H2, k - 1)) continue; }
      // allowed overflow patterns per copy: o = (o_small, o_big) coded as 2*o_small + o_big
      vector<vector<int>> pats(K); vector<char> freecp(K, 0);
      for (int j = 0; j < K; j++) {
        int u = s.P[j].first;
        if (u == 0) pats[j] = {2 + nu};                    // empty smaller bin: o_small = 1, o_big = nu
        else if (e[j] == 0 && nu == 1) pats[j] = {3};      // both overflow
        else if (e[j] == 1 && nu == 0) pats[j] = {0};      // neither overflows
        else { pats[j] = {0, 1, 2, 3}; freecp[j] = 1; }
      }
      vector<int> idx(K, 0);
      while (true) {
        bool skip = false;
        if (x2) { bool h00 = false, h11 = false;
          for (int j = 0; j < K; j++) if (freecp[j]) { int p = pats[j][idx[j]]; if (p == 0) h00 = true; if (p == 3) h11 = true; }
          if (h00 && h11) skip = true; }
        if (!skip) {
          moves++;
          bool answered = false;
          for (int resp = 0; resp < (1 << K) && !answered; resp++) {
            vector<pair<int,int>> P2(K);
            for (int j = 0; j < K; j++) {
              int u = s.P[j].first, v = s.P[j].second, p = pats[j][idx[j]];
              int os = p >> 1, ob = p & 1;
              if ((resp >> j) & 1) { int b2 = v + c + ob; P2[j] = {u, b2}; }
              else { int a2 = u + c + os; P2[j] = a2 <= v ? make_pair(a2, v) : make_pair(v, a2); }
            }
            auto it = D.find(key(N2, H2, P2));
            if (it != D.end() && it->second <= T) answered = true;
          }
          if (!answered) {
            #pragma omp critical
            printf("FAIL (c) at state %lld (N %d T %lld): move c %d nu %d unanswered\n", i, s.N, T, c, nu);
            fails++; break;
          }
        }
        int j = 0; while (j < K && ++idx[j] == (int)pats[j].size()) { idx[j] = 0; j++; }
        if (j == K) break;
      }
    }
  }
  if (fails) { printf("vcheck: FAIL (%lld failures)\n", fails); return 1; }
  long long den = W * (long long)F, g = rootT; { long long a = rootT, b = den; while (b) { long long t = a % b; a = b; b = t; } g = a; }
  printf("vcheck: PASS. %zu states, %lld answered move patterns. E[cost] <= %lld/%lld = %lld/%lld = %.10f\n",
         S.size(), moves, rootT, den, rootT / g, den / g, (double)rootT / den);
  return 0;
}
