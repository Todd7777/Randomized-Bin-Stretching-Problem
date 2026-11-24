// relaxcheck.cpp: checks a relaxed hybrid certificate for three bins and two copies.
// g++ -O2 -std=c++17 -o relaxcheck relaxcheck.cpp && ./relaxcheck FILE [table=1]
#include <algorithm>
#include <array>
#include <climits>
#include <cstdio>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>
using namespace std;
typedef unsigned long long u64; typedef array<int, 3> T3;
static int k, r, w1, w2, T0, F;
static void die(const string &s) { printf("FAIL %s\n", s.c_str()); exit(1); }
static bool feas[2][4][3][4]; static int witT[2][4][3][4], witX[2][4][3][4];
static bool bpTest(int nu, int n, int e, int b) {
  for (int d = 1; d <= 3; d++) for (int a = 0; a <= d; a++) {
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
  for (int nu = 0; nu < 2; nu++) for (int n = 1; n <= 3; n++) for (int e = 0; e <= n - 1; e++) for (int b = 0; b <= n; b++) {
    int ti, xi; bool g = gridTest(nu, n, e, b, ti, xi), p = bpTest(nu, n, e, b);
    if (g != p) die("one-copy table: grid and breakpoint test disagree");
    feas[nu][n][e][b] = g; witT[nu][n][e][b] = ti; witX[nu][n][e][b] = xi;
    if (print) { if (g) printf("nu %d n %d e %d b %d : allowed, t = %d/60, x = %d/60\n", nu, n, e, b, ti, xi);
                 else printf("nu %d n %d e %d b %d : not allowed\n", nu, n, e, b); }
  }
}
typedef vector<T3> Prof; static map<Prof, int> pid; static vector<Prof> profs; static map<pair<int, int>, int> pchild;
static int intern(const Prof &p) { auto it = pid.find(p); if (it != pid.end()) return it->second; pid[p] = profs.size(); profs.push_back(p); return profs.size() - 1; }
static int addC(int p, int C) {
  auto key = make_pair(p, C); auto it = pchild.find(key); if (it != pchild.end()) return it->second;
  set<T3> all;
  for (const T3 &v : profs[p]) for (int i = 0; i < 3; i++) if (v[i] + C <= k - 1) { T3 u = v; u[i] += C; sort(u.begin(), u.end()); all.insert(u); }
  Prof out;
  for (const T3 &v : all) { bool dom = false; for (const T3 &u : all) if (u != v && u[0] <= v[0] && u[1] <= v[1] && u[2] <= v[2]) dom = true; if (!dom) out.push_back(v); }
  int res = out.empty() ? -1 : intern(out); pchild[key] = res; return res;
}
static int nOf(const T3 &q) { return (q[0] > 0) + (q[1] > 0) + (q[2] > 0); }
static T3 add(T3 q, int i, int a) { q[i] += a; sort(q.begin(), q.end()); return q; }
static bool maskAllowed(int N, const T3 &q, int nu, int mask, bool &someZero) {
  someZero = false;
  if (N == 0) return nu == 1 && mask == 7;
  int n = nOf(q), e = q[0] + q[1] + q[2] - N, b = 0;
  if (n < 1 || e < 0 || e > n - 1) die("inadmissible copy state reached");
  for (int i = 0; i < 3; i++) { int bit = (mask >> i) & 1; if (q[i] == 0 && !bit) return false; if (q[i] > 0 && !bit) b++; }
  someZero = b >= 1; return feas[nu][n][e][b];
}
static unordered_map<u64, int> memo;
static u64 key1(int p, int N, const T3 &q) { return ((((u64)p * 256 + N) * 256 + q[0]) * 256 + q[1]) * 256 + q[2]; }
static int phi(int p, int N, const T3 &q) {
  u64 kk = key1(p, N, q); auto it = memo.find(kk); if (it != memo.end()) return it->second;
  int val = q[2];
  for (int c = 0; c < F; c++) { int C = c / r, p2 = C ? addC(p, C) : p; if (p2 < 0) continue;
    for (int nu = 0; nu < 2; nu++) { if (N + c + nu > 3 * F) continue;
      for (int mask = 0; mask < 8; mask++) { bool z; if (!maskAllowed(N, q, nu, mask, z)) continue;
        if (c == 0 && nu == 0 && z) continue;
        int best = INT_MAX; for (int i = 0; i < 3; i++) best = min(best, phi(p2, N + c + nu, add(q, i, c + ((mask >> i) & 1))));
        val = max(val, best); } } }
  memo[kk] = val; return val;
}
int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: relaxcheck FILE [table=1]\n"); return 2; }
  ifstream f(argv[1]); string line; long long n = -1; vector<tuple<int, int, T3, T3>> J;
  intern(Prof{T3{0, 0, 0}});
  while (getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    if (n < 0) { istringstream in(line); string tag; in >> tag >> k >> r >> w1 >> w2 >> T0 >> n;
      if (tag != "HYB3" || !in || k < 2 || k > 31 || r < 1 || r > 255 || w1 < 1 || w2 < 1 || w1 > (1 << 20) || w2 > (1 << 20) || 3 * k * r + 3 > 255) die("header");
      F = k * r; buildTable(argc > 2); continue; }
    replace(line.begin(), line.end(), '|', ' '); istringstream in(line); vector<int> v; string t;
    while (in >> t) { if (t != "-" && (t.size() > 9 || t.find_first_not_of("0123456789") != string::npos)) die("token"); v.push_back(t == "-" ? -1 : stoi(t)); }
    if (v.size() < 8) die("line");
    int N = v[0], p = 0, sumH = 0;
    for (size_t i = 1; i + 6 < v.size(); i++) if (v[i] != -1) { if (v[i] < 1 || v[i] > k - 1) die("class"); p = addC(p, v[i]); if (p < 0) die("H not 3-splittable"); sumH += v[i]; }
    size_t s = v.size() - 6; T3 a = {v[s], v[s + 1], v[s + 2]}, b = {v[s + 3], v[s + 4], v[s + 5]};
    for (T3 *q : {&a, &b}) { if (!is_sorted(q->begin(), q->end()) || (*q)[0] < 0 || (*q)[2] > 255) die("q");
      int nn = nOf(*q), e = (*q)[0] + (*q)[1] + (*q)[2] - N;
      if (N == 0 ? nn != 0 : (nn < 1 || e < 0 || e > nn - 1)) die("(A2)"); }
    if (N < 0 || N > 3 * F || (sumH && N < r * sumH + 1)) die("(A1)");
    J.emplace_back(p, N, a, b);
  }
  if ((long long)J.size() != n) die("count");
  set<tuple<int, int, T3, T3>> listed(J.begin(), J.end()); if (listed.size() != J.size()) die("duplicate");
  T3 z = {0, 0, 0};
  if (!listed.count(make_tuple(0, 0, z, z)) && w1 * phi(0, 0, z) + w2 * phi(0, 0, z) > T0) die("J1");
  long long moves = 0;
  for (auto &st : J) {
    int p, N; T3 a, b; tie(p, N, a, b) = st;
    if (w1 * a[2] + w2 * b[2] > T0) die("J2");
    for (int c = 0; c < F; c++) { int C = c / r, p2 = C ? addC(p, C) : p; if (p2 < 0) continue;
      for (int nu = 0; nu < 2; nu++) { int N2 = N + c + nu; if (N2 > 3 * F) continue;
        int va[2][3], vb[2][3]; bool have[2][2][3] = {};
        for (int m1 = 0; m1 < 8; m1++) { bool z1; if (!maskAllowed(N, a, nu, m1, z1)) continue;
          for (int m2 = 0; m2 < 8; m2++) { bool z2; if (!maskAllowed(N, b, nu, m2, z2)) continue;
            if (c == 0 && nu == 0 && z1 && z2) continue;
            moves++; bool ok = false;
            for (int i = 0; i < 3; i++) { int o = (m1 >> i) & 1; if (!have[0][o][i]) { va[o][i] = phi(p2, N2, add(a, i, c + o)); have[0][o][i] = true; }
                                          o = (m2 >> i) & 1; if (!have[1][o][i]) { vb[o][i] = phi(p2, N2, add(b, i, c + o)); have[1][o][i] = true; } }
            for (int i = 0; i < 3 && !ok; i++) for (int j = 0; j < 3 && !ok; j++) ok = w1 * va[(m1 >> i) & 1][i] + w2 * vb[(m2 >> j) & 1][j] <= T0;
            for (int i = 0; i < 3 && !ok; i++) for (int j = 0; j < 3 && !ok; j++) {
              T3 a2 = add(a, i, c + ((m1 >> i) & 1)), b2 = add(b, j, c + ((m2 >> j) & 1));
              ok = listed.count(make_tuple(p2, N2, a2, b2)) > 0; }
            if (!ok) die("J3 at N " + to_string(N));
          } } } } }
  printf("PASS (relaxed game)  k %d r %d weights %d,%d  T0 %d  bound %d/%d  joint states %zu  moves %lld  one-copy values %zu\n",
         k, r, w1, w2, T0, T0, (w1 + w2) * F, J.size(), moves, memo.size());
}
