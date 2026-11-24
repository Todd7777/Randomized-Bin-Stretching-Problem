// hybcheck.cpp: checks a hybrid certificate for three bins and two copies, (J3) for moves with one common point.
// g++ -O2 -std=c++17 -o hybcheck hybcheck.cpp && ./hybcheck FILE
#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
typedef array<int, 3> Q;
typedef vector<Q> Prof;
typedef unsigned long long u64;
static int k, r, w1, w2, T0, F;
static void fail(const string &s) { printf("FAIL %s\n", s.c_str()); exit(1); }

static map<Prof, int> profId; static vector<Prof> profs; static vector<vector<int> > child;
static int internProf(const Prof &p) {
  map<Prof, int>::iterator it = profId.find(p); if (it != profId.end()) return it->second;
  int id = (int)profs.size(); profId[p] = id; profs.push_back(p); child.push_back(vector<int>(k, -2)); return id;
}
static int addClass(int p, int C) {
  if (child[p][C] != -2) return child[p][C];
  vector<Q> t;
  for (size_t z = 0; z < profs[p].size(); z++) for (int i = 0; i < 3; i++) if (profs[p][z][i] + C <= k - 1) {
    Q u = profs[p][z]; u[i] += C; sort(u.begin(), u.end()); t.push_back(u);
  }
  sort(t.begin(), t.end()); t.erase(unique(t.begin(), t.end()), t.end());
  Prof out;
  for (size_t a = 0; a < t.size(); a++) {
    bool dom = false;
    for (size_t b = 0; b < t.size() && !dom; b++) if (b != a && t[b][0] <= t[a][0] && t[b][1] <= t[a][1] && t[b][2] <= t[a][2]) dom = true;
    if (!dom) out.push_back(t[a]);
  }
  int res = out.empty() ? -1 : internProf(out);
  child[p][C] = res; return res;
}

static bool m4(int nu, int cnt, const int *n, const int *e, const int *b) {
  for (int d = 1; d <= 3; d++) for (int a = 0; a <= d; a++) {
    int U = d, L = 0;
    if (nu == 1) U = min(U, a); else L = max(L, a);
    for (int j = 0; j < cnt; j++) { U = min(U, (n[j] - b[j]) * a + (b[j] - e[j]) * d); L = max(L, b[j] * a - e[j] * d); }
    if (U > L) return true;
  }
  return false;
}
struct Copy { Q q; int n, e; };
static Copy mk(int N, const Q &q) { Copy c; c.q = q; c.n = (q[0] > 0) + (q[1] > 0) + (q[2] > 0); c.e = q[0] + q[1] + q[2] - N; return c; }
static bool maskOk(int mask, int n) { for (int i = 0; i < 3 - n; i++) if (!((mask >> i) & 1)) return false; return true; }
static int zerosOf(int mask) { return 3 - __builtin_popcount(mask); }
static Q put(const Q &q, int i, int add) { Q u = q; u[i] += add; sort(u.begin(), u.end()); return u; }

static const u64 NOKEY = ~0ULL;
static u64 key1(int p, int N, const Q &q) {
  int e = q[0] + q[1] + q[2] - N; if (e < 0 || e > 3 || p >= 65536) return NOKEY;
  return ((((u64)p * 256 + N) * 256 + q[0]) * 256 + q[1]) * 4 + e;
}
static unordered_map<u64, int> memo1;
static int phi1(int p, int N, const Q &q) {
  u64 key = key1(p, N, q); if (key == NOKEY) fail("internal: one-copy state outside the key range");
  unordered_map<u64, int>::iterator it = memo1.find(key); if (it != memo1.end()) return it->second;
  Copy z = mk(N, q); int val = q[2];
  for (int c = 0; c < F; c++) {
    int C = c / r, p2 = C >= 1 ? addClass(p, C) : p; if (p2 < 0) continue;
    for (int nu = 0; nu < 2; nu++) {
      if (N + c + nu > 3 * F) continue;
      for (int mask = 0; mask < 8; mask++) {
        if (N == 0) { if (nu != 1 || mask != 7) continue; }
        else {
          if (!maskOk(mask, z.n)) continue;
          int b = zerosOf(mask); if (!m4(nu, 1, &z.n, &z.e, &b)) continue;
          if (c == 0 && nu == 0 && b >= 1) continue;
        }
        int best = 1 << 30;
        for (int i = 0; i < 3; i++) best = min(best, phi1(p2, N + c + nu, put(q, i, c + ((mask >> i) & 1))));
        val = max(val, best);
      }
    }
  }
  memo1[key] = val; return val;
}
static int UB(int p, int N, const Q &a, const Q &b) { return w1 * phi1(p, N, a) + w2 * phi1(p, N, b); }

struct JS { int p, N; Q a, b; };
static u64 key2(const JS &s) {
  u64 h = key1(s.p, s.N, s.a); int e = s.b[0] + s.b[1] + s.b[2] - s.N; if (h == NOKEY || e < 0 || e > 3) return NOKEY;
  return ((h * 256 + s.b[0]) * 256 + s.b[1]) * 4 + e;
}
static vector<u64> tab; static u64 tmask;
static u64 mix(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static bool isListed(u64 key) { if (key == NOKEY) return false; for (u64 h = mix(key) & tmask;; h = (h + 1) & tmask) { if (tab[h] == key) return true; if (tab[h] == NOKEY) return false; } }
static bool addListed(u64 key) { for (u64 h = mix(key) & tmask;; h = (h + 1) & tmask) { if (tab[h] == key) return false; if (tab[h] == NOKEY) { tab[h] = key; return true; } } }
static Q readQ(istringstream &in) { Q q; in >> q[0] >> q[1] >> q[2]; return q; }
static bool admCopy(int N, const Q &q) {
  if (q[0] < 0 || q[0] > q[1] || q[1] > q[2] || q[2] > 255) return false;
  Copy z = mk(N, q); if (N == 0) return q[2] == 0;
  return z.n >= 1 && z.e >= 0 && z.e <= z.n - 1;
}
int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: hybcheck FILE\n"); return 2; }
  ifstream f(argv[1]); if (!f) { perror(argv[1]); return 2; }
  string line; long long n = -1; vector<JS> J;
  while (getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    if (n < 0) {
      istringstream in(line); string tag; in >> tag >> k >> r >> w1 >> w2 >> T0 >> n;
      if (tag != "HYB3" || !in || k < 2 || k > 31 || r < 1 || r > 255 || w1 < 1 || w2 < 1 || w1 > (1 << 20) || w2 > (1 << 20) || 3 * k * r + 2 > 255) fail("header");
      F = k * r; Prof z(1, Q{{0, 0, 0}}); internProf(z); continue;
    }
    for (size_t i = 0; i < line.size(); i++) if (line[i] == '|') line[i] = ' ';
    istringstream in(line); vector<string> tok; string t; while (in >> t) { if (t != "-" && (t.size() > 9 || t.find_first_not_of("0123456789") != string::npos)) fail("token"); tok.push_back(t); }
    if (tok.size() < 8) fail("line format");
    JS s; s.N = atoi(tok[0].c_str()); s.p = 0; int sumH = 0; vector<int> H;
    for (size_t i = 1; i + 6 < tok.size(); i++) if (tok[i] != "-") H.push_back(atoi(tok[i].c_str()));
    sort(H.begin(), H.end());
    for (size_t i = 0; i < H.size(); i++) { if (H[i] < 1 || H[i] > k - 1) fail("J0 class"); s.p = addClass(s.p, H[i]); if (s.p < 0) fail("J0 H does not split"); sumH += H[i]; }
    string rest; for (size_t i = tok.size() - 6; i < tok.size(); i++) rest += tok[i] + " ";
    istringstream in2(rest); s.a = readQ(in2); s.b = readQ(in2);
    for (int i = 0; i < 3; i++) if (s.a[i] < 0 || s.a[i] > 255 || s.b[i] < 0 || s.b[i] > 255) fail("q range");
    if (s.N < 0 || s.N > 3 * F || (sumH && s.N < r * sumH + 1) || !admCopy(s.N, s.a) || !admCopy(s.N, s.b)) fail("J0 not admissible: " + line);
    J.push_back(s);
  }
  if ((long long)J.size() != n) fail("state count");
  u64 cap = 16; while (cap < 2 * J.size() + 16) cap *= 2;
  tab.assign(cap, NOKEY); tmask = cap - 1;
  for (size_t h = 0; h < J.size(); h++) { u64 key = key2(J[h]); if (key == NOKEY) fail("J0 key"); if (!addListed(key)) fail("J0 listed twice"); }
  JS root; root.p = 0; root.N = 0; root.a = root.b = Q{{0, 0, 0}};
  if (!isListed(key2(root)) && UB(0, 0, root.a, root.b) > T0) fail("J1");
  long long nmoves = 0, nleaf = 0;
  for (size_t h = 0; h < J.size(); h++) {
    const JS &s = J[h]; Copy z1 = mk(s.N, s.a), z2 = mk(s.N, s.b);
    if (w1 * s.a[2] + w2 * s.b[2] > T0) fail("J2");
    for (int c = 0; c < F; c++) {
      int C = c / r, p2 = C >= 1 ? addClass(s.p, C) : s.p; if (p2 < 0) continue;
      for (int nu = 0; nu < 2; nu++) {
        int N2 = s.N + c + nu; if (N2 > 3 * F) continue;
        Q sq[2][2][3]; int sv[2][2][3];
        for (int j = 0; j < 2; j++) for (int o = 0; o < 2; o++) for (int i = 0; i < 3; i++) { sq[j][o][i] = put(j ? s.b : s.a, i, c + o); sv[j][o][i] = -1; }
        for (int m1 = 0; m1 < 8; m1++) for (int m2 = 0; m2 < 8; m2++) {
          if (s.N == 0) { if (nu != 1 || m1 != 7 || m2 != 7) continue; }
          else {
            if (!maskOk(m1, z1.n) || !maskOk(m2, z2.n)) continue;
            int nn[2] = {z1.n, z2.n}, ee[2] = {z1.e, z2.e}, bb[2] = {zerosOf(m1), zerosOf(m2)};
            if (!m4(nu, 2, nn, ee, bb)) continue;
            if (c == 0 && nu == 0 && bb[0] >= 1 && bb[1] >= 1) continue;
          }
          nmoves++;
          int v1[3], v2[3]; bool ok = false;
          for (int i = 0; i < 3; i++) {
            int o1 = (m1 >> i) & 1, o2 = (m2 >> i) & 1;
            if (sv[0][o1][i] < 0) sv[0][o1][i] = phi1(p2, N2, sq[0][o1][i]);
            if (sv[1][o2][i] < 0) sv[1][o2][i] = phi1(p2, N2, sq[1][o2][i]);
            v1[i] = sv[0][o1][i]; v2[i] = sv[1][o2][i];
          }
          for (int i = 0; i < 3 && !ok; i++) for (int j = 0; j < 3 && !ok; j++) if (w1 * v1[i] + w2 * v2[j] <= T0) ok = true;
          if (ok) nleaf++;
          for (int i = 0; i < 3 && !ok; i++) for (int j = 0; j < 3 && !ok; j++) {
            JS t; t.p = p2; t.N = N2; t.a = sq[0][(m1 >> i) & 1][i]; t.b = sq[1][(m2 >> j) & 1][j];
            if (isListed(key2(t))) ok = true;
          }
          if (!ok) { char buf[256]; snprintf(buf, sizeof buf, "J3 at state %zu (N %d): move c %d nu %d masks %d %d", h, s.N, c, nu, m1, m2); fail(buf); }
        }
      }
    }
  }
  printf("PASS  k %d r %d weights %d,%d  T0 %d  bound %d/%d = %.6f  joint states %zu  non-idle moves %lld  (%lld answered by a leaf)  one-copy values computed %zu\n",
         k, r, w1, w2, T0, T0, (w1 + w2) * F, (double)T0 / ((w1 + w2) * F), J.size(), nmoves, nleaf, memo1.size());
  return 0;
}
