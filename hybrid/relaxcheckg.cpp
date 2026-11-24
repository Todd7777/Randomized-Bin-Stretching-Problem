// relaxcheckg.cpp: checks a relaxed hybrid certificate, for m <= 4 bins and K <= 3 copies.
// g++ -O2 -std=c++17 -o relaxcheckg relaxcheckg.cpp && ./relaxcheckg FILE... [table=1]
// File: "HYBG m K k r w_1 .. w_K T0 n" (or "HYB3 k r w1 w2 T0 n"), then n lines "N | H | q_1 | ... | q_K".
#include <algorithm>
#include <array>
#include <climits>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
typedef unsigned long long u64; typedef array<int, 4> V;
static int m, K, k, r, w[3], T0, F;
struct Fail { string why; };
static void die(const string &s) { throw Fail{s}; }
static bool feas[2][5][4][5]; static int witT[2][5][4][5], witX[2][5][4][5];
static bool bpTest(int nu, int n, int e, int b) {
  for (int d = 1; d <= m; d++) for (int a = 0; a <= d; a++) {
    int U = min(d, (n - b) * a + (b - e) * d), L = max(0, b * a - e * d);
    if (nu) U = min(U, a); else L = max(L, a);
    if (U > L) return true;
  }
  return false;
}
static bool gridTest(int nu, int n, int e, int b, int &ti, int &xi) {
  const int G = 60;
  for (ti = 1; ti <= G; ti++) for (xi = 0; xi < G; xi++) {
    if ((ti > xi) != (nu == 1)) continue;
    if (b * ti > e * G + xi) continue;
    if (!(e * G + xi < b * G + (n - b) * ti)) continue;
    if (b >= 1 && ti == G) continue;
    return true;
  }
  return false;
}
static void buildTable(bool print) {
  int rows = 0, allowed = 0;
  for (int nu = 0; nu < 2; nu++) for (int n = 1; n <= m; n++) for (int e = 0; e <= n - 1; e++) for (int b = 0; b <= n; b++) {
    int ti, xi; bool g = gridTest(nu, n, e, b, ti, xi), p = bpTest(nu, n, e, b);
    if (g != p) die("one-copy table: grid and breakpoint test disagree");
    feas[nu][n][e][b] = g; witT[nu][n][e][b] = ti; witX[nu][n][e][b] = xi; rows++; allowed += g;
    if (print) { if (g) printf("nu %d n %d e %d b %d : allowed, t = %d/60, x = %d/60\n", nu, n, e, b, ti, xi);
                 else printf("nu %d n %d e %d b %d : not allowed\n", nu, n, e, b); }
  }
  if (print) printf("one-copy table for m = %d: %d rows, %d allowed\n", m, rows, allowed);
}
typedef vector<V> Prof; static map<Prof, int> pid; static vector<Prof> profs; static map<pair<int, int>, int> pchild;
static int intern(const Prof &p) { auto it = pid.find(p); if (it != pid.end()) return it->second; if (profs.size() >= (1u << 24)) die("too many profiles"); pid[p] = profs.size(); profs.push_back(p); return profs.size() - 1; }
static V srt(V q) { sort(q.begin(), q.begin() + m); return q; }
static int addC(int p, int C) {
  auto key = make_pair(p, C); auto it = pchild.find(key); if (it != pchild.end()) return it->second;
  set<V> all;
  for (const V &v : profs[p]) for (int i = 0; i < m; i++) if (v[i] + C <= k - 1) { V u = v; u[i] += C; all.insert(srt(u)); }
  Prof out;
  for (const V &v : all) { bool dom = false;
    for (const V &u : all) if (u != v) { bool le = true; for (int i = 0; i < m; i++) if (u[i] > v[i]) le = false; if (le) dom = true; }
    if (!dom) out.push_back(v); }
  int res = out.empty() ? -1 : intern(out); pchild[key] = res; return res;
}
static int nOf(const V &q) { int n = 0; for (int i = 0; i < m; i++) n += q[i] > 0; return n; }
static int sumOf(const V &q) { int s = 0; for (int i = 0; i < m; i++) s += q[i]; return s; }
static V add(V q, int i, int a) { q[i] += a; return srt(q); }
static bool maskAllowed(int N, const V &q, int nu, int mask, bool &someZero) {
  someZero = false;
  if (N == 0) return nu == 1 && mask == (1 << m) - 1;
  int n = nOf(q), e = sumOf(q) - N, b = 0;
  if (n < 1 || e < 0 || e > n - 1) die("inadmissible copy state reached");
  for (int i = 0; i < m; i++) { int bit = (mask >> i) & 1; if (q[i] == 0 && !bit) return false; if (q[i] > 0 && !bit) b++; }
  someZero = b >= 1; return feas[nu][n][e][b];
}
static unordered_map<u64, int> memo;
static u64 key1(int p, int N, const V &q) { u64 x = (u64)p * 256 + N; for (int i = 0; i < m; i++) x = x * 256 + q[i]; return x; }
static int phi(int p, int N, const V &q) {
  u64 kk = key1(p, N, q); auto it = memo.find(kk); if (it != memo.end()) return it->second;
  int val = q[m - 1];
  for (int c = 0; c < F; c++) { int C = c / r, p2 = C ? addC(p, C) : p; if (p2 < 0) continue;
    for (int nu = 0; nu < 2; nu++) { if (N + c + nu > m * F) continue;
      for (int mask = 0; mask < (1 << m); mask++) { bool z; if (!maskAllowed(N, q, nu, mask, z)) continue;
        if (c == 0 && nu == 0 && z) continue;
        int best = INT_MAX; for (int i = 0; i < m; i++) best = min(best, phi(p2, N + c + nu, add(q, i, c + ((mask >> i) & 1))));
        val = max(val, best); } } }
  memo[kk] = val; return val;
}
static string jkey(int p, int N, const V *q) {
  string s; s.push_back((char)(p & 255)); s.push_back((char)((p >> 8) & 255)); s.push_back((char)((p >> 16) & 255)); s.push_back((char)N);
  for (int j = 0; j < K; j++) for (int i = 0; i < m; i++) s.push_back((char)q[j][i]);
  return s;
}
struct St { int p, N; V q[3]; };
static void checkFile(const char *path, bool table) {
  memo.clear(); pid.clear(); profs.clear(); pchild.clear(); m = K = k = r = T0 = F = 0; w[0] = w[1] = w[2] = 0;
  ifstream f(path); if (!f) die("cannot open file"); string line; long long n = -1; vector<St> J;
  while (getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    if (n < 0) { istringstream in(line); string tag; in >> tag;
      if (tag == "HYB3") { m = 3; K = 2; in >> k >> r >> w[0] >> w[1] >> T0 >> n; }
      else if (tag == "HYBG") { in >> m >> K; if (!in || m < 2 || m > 4 || K < 1 || K > 3) die("header"); in >> k >> r; for (int j = 0; j < K; j++) in >> w[j]; in >> T0 >> n; }
      else die("header");
      if (!in || k < 2 || k > 31 || r < 1 || r > 255 || n < 0 || m * k * r + m > 255) die("header");
      for (int j = 0; j < K; j++) if (w[j] < 1 || w[j] > (1 << 20)) die("header");
      F = k * r; V z0 = {0, 0, 0, 0}; intern(Prof{z0}); buildTable(table); continue; }
    replace(line.begin(), line.end(), '|', ' '); istringstream in(line); vector<int> v; string t;
    while (in >> t) { if (t != "-" && (t.size() > 9 || t.find_first_not_of("0123456789") != string::npos)) die("token"); v.push_back(t == "-" ? -1 : stoi(t)); }
    size_t tail = (size_t)m * K;
    if (v.size() < tail + 2) die("line");
    int N = v[0], p = 0, sumH = 0;
    for (size_t i = 1; i + tail < v.size(); i++) { if (v[i] == -1) { if (v.size() != tail + 2) die("H"); continue; }
      if (v[i] < 1 || v[i] > k - 1) die("class"); p = addC(p, v[i]); if (p < 0) die("H not m-splittable"); sumH += v[i]; }
    St st; st.p = p; st.N = N; size_t s = v.size() - tail;
    for (int j = 0; j < K; j++) { V q = {0, 0, 0, 0}; for (int i = 0; i < m; i++) q[i] = v[s + j * m + i];
      if (!is_sorted(q.begin(), q.begin() + m) || q[0] < 0 || q[m - 1] > 255) die("q");
      int nn = nOf(q), e = sumOf(q) - N;
      if (N == 0 ? nn != 0 : (nn < 1 || e < 0 || e > nn - 1)) die("(A2)");
      st.q[j] = q; }
    if (N < 0 || N > m * F || (sumH && N < r * sumH + 1)) die("(A1)");
    J.push_back(st);
  }
  if (n < 0) die("header");
  if ((long long)J.size() != n) die("count");
  unordered_set<string> listed; listed.reserve(J.size() * 2);
  for (auto &st : J) if (!listed.insert(jkey(st.p, st.N, st.q)).second) die("duplicate");
  V z = {0, 0, 0, 0}; V zs[3] = {z, z, z};
  { int ub = 0; for (int j = 0; j < K; j++) ub += w[j] * phi(0, 0, z); if (!listed.count(jkey(0, 0, zs)) && ub > T0) die("J1"); }
  long long moves = 0, leafMoves = 0; int W = 0; for (int j = 0; j < K; j++) W += w[j];
  for (auto &st : J) {
    int p = st.p, N = st.N; const V *q = st.q;
    { int pay = 0; for (int j = 0; j < K; j++) pay += w[j] * q[j][m - 1]; if (pay > T0) die("J2"); }
    for (int c = 0; c < F; c++) { int C = c / r, p2 = C ? addC(p, C) : p; if (p2 < 0) continue;
      for (int nu = 0; nu < 2; nu++) { int N2 = N + c + nu; if (N2 > m * F) continue;
        vector<int> ms[3]; vector<char> zz[3];
        for (int j = 0; j < K; j++) for (int mk = 0; mk < (1 << m); mk++) { bool zf; if (maskAllowed(N, q[j], nu, mk, zf)) { ms[j].push_back(mk); zz[j].push_back(zf); } }
        bool emptyCopy = false; for (int j = 0; j < K; j++) if (ms[j].empty()) emptyCopy = true;
        if (emptyCopy) continue;
        int val[3][2][4]; bool have[3][2][4] = {};
        size_t idx[3] = {0, 0, 0};
        while (true) {
          bool allZ = true; for (int j = 0; j < K; j++) if (!zz[j][idx[j]]) allZ = false;
          if (!(c == 0 && nu == 0 && allZ)) {
            moves++; int tot = 0;
            for (int j = 0; j < K; j++) { int mk = ms[j][idx[j]], best = INT_MAX;
              for (int i = 0; i < m; i++) { int o = (mk >> i) & 1;
                if (!have[j][o][i]) { val[j][o][i] = phi(p2, N2, add(q[j], i, c + o)); have[j][o][i] = true; }
                best = min(best, w[j] * val[j][o][i]); }
              tot += best; }
            bool ok = tot <= T0;
            if (ok) leafMoves++;
            else {
              int R = 1; for (int j = 0; j < K; j++) R *= m;
              for (int x = 0; x < R && !ok; x++) { V q2[3]; int y = x;
                for (int j = K - 1; j >= 0; j--) { int i = y % m; y /= m; q2[j] = add(q[j], i, c + ((ms[j][idx[j]] >> i) & 1)); }
                ok = listed.count(jkey(p2, N2, q2)) > 0; }
            }
            if (!ok) die("J3 at N " + to_string(N));
          }
          int j = K - 1; while (j >= 0) { if (++idx[j] < ms[j].size()) break; idx[j] = 0; j--; }
          if (j < 0) break;
        } } } }
  string ws; for (int j = 0; j < K; j++) { if (j) ws += ","; ws += to_string(w[j]); }
  printf("PASS (relaxed game)  m %d K %d k %d r %d weights %s  T0 %d  bound %d/%d  joint states %zu  moves %lld  leaf-answered %lld  one-copy values %zu\n",
         m, K, k, r, ws.c_str(), T0, T0, W * F, J.size(), moves, leafMoves, memo.size());
}
int main(int argc, char **argv) {
  vector<const char *> files; bool table = false;
  for (int i = 1; i < argc; i++) { if (!strcmp(argv[i], "table=1")) table = true; else files.push_back(argv[i]); }
  if (files.empty()) { fprintf(stderr, "usage: relaxcheckg FILE... [table=1]\n"); return 2; }
  int bad = 0;
  for (const char *fn : files) {
    if (files.size() > 1) { printf("%s: ", fn); fflush(stdout); }
    try { checkFile(fn, table); } catch (const Fail &e) { printf("FAIL %s\n", e.why.c_str()); bad++; }
    fflush(stdout);
  }
  return bad ? 1 : 0;
}
