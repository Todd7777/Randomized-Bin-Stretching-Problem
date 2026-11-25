// cmb.cpp: a second checker of CERTM certificates. Prints one line, PASS (exit 0) or FAIL.
// g++ -O2 -std=c++17 -fopenmp -o cmb cmb.cpp && ./cmb FILE
#include <algorithm>
#include <array>
#include <cerrno>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <new>
#include <string>
#include <vector>
#include <fcntl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef uint64_t u64;
typedef int64_t i64;
typedef unsigned __int128 u128;
typedef __int128 i128;

namespace {

const int LIM_m = 6;
const int LIM_K = 3;
const u64 LIM_k = 64;
const u64 LIM_F = 4096;
const int LIM_W = 4;
const u64 MAXSTORE = 512;
const u64 SIDE_CAP = (u64)1 << 27;
u64 CHUNK = (u64)64 << 20;
const size_t BUFSZ = (size_t)8 << 20;
const u64 NONE = ~(u64)0;

const char* USAGE_TEXT =
    "usage: cmb FILE | cmb --selftest\n"
    "  checks a CERTM certificate (CERTM-SPEC.md v1); FILE must be a regular file\n"
    "  limits: m <= 6, K <= 3, k <= 64, F <= 4096, key <= 256 bits, header <= 512 tokens,\n"
    "    n as memory holds, weights T0 T any number token (< 10^18)\n"
    "  exit: 0 PASS, 1 FAIL C1..C6, 2 FAIL LIMIT/IO/USAGE, 3 FAIL INTERNAL\n";

void out_of_memory() {
  fflush(stderr);
  fputs("FAIL LIMIT line 0: refused: out of memory\n", stdout);
  fflush(stdout);
  _exit(2);
}

std::string dec(u128 v) {
  if (v == 0) return "0";
  char b[48];
  int p = 47;
  b[p] = 0;
  while (v) { b[--p] = char('0' + (int)(v % 10)); v /= 10; }
  return std::string(b + p);
}

double now_s() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

double peak_rss_bytes() {
  struct rusage ru;
  if (getrusage(RUSAGE_SELF, &ru) != 0) return 0;
#ifdef __APPLE__
  return (double)ru.ru_maxrss;
#else
  return (double)ru.ru_maxrss * 1024.0;
#endif
}
double T_START = 0;

[[noreturn]] void finish(const char* cond, u64 line, const std::string& text) {
  int code = 1;
  if (!strcmp(cond, "LIMIT") || !strcmp(cond, "IO") || !strcmp(cond, "USAGE")) code = 2;
  else if (!strcmp(cond, "INTERNAL")) code = 3;
  fflush(stderr);
  printf("FAIL %s line %s: %s\n", cond, dec(line).c_str(), text.c_str());
  fflush(stdout);
  exit(code);
}

int nthreads() {
#ifdef _OPENMP
  return omp_get_max_threads();
#else
  return 1;
#endif
}

int bits_of(u64 x) {
  int b = 0;
  while (x) { b++; x >>= 1; }
  return b;
}

struct Ineq { i64 a, b, c; bool s; };

bool const_ok(i64 c, bool s) { return s ? c > 0 : c >= 0; }

bool fm_feasible(int nu, int K, const int* n, const int* e, const int* b) {
  Ineq sys[8 + 3 * 8];
  int ns = 0;
  sys[ns++] = {1, 0, 0, true};
  sys[ns++] = {-1, 0, 1, false};
  sys[ns++] = {0, 1, 0, false};
  sys[ns++] = {0, -1, 1, true};
  if (nu) sys[ns++] = {1, -1, 0, true};
  else    sys[ns++] = {-1, 1, 0, false};
  for (int j = 0; j < K; j++) {
    sys[ns++] = {-(i64)b[j], 1, (i64)e[j], false};
    sys[ns++] = {(i64)(n[j] - b[j]), -1, (i64)(b[j] - e[j]), true};
    if (b[j] >= 1) sys[ns++] = {-1, 0, 1, true};
  }
  std::vector<Ineq> t1;
  t1.reserve(64);
  for (int i = 0; i < ns; i++)
    if (sys[i].b == 0) t1.push_back(sys[i]);
  for (int i = 0; i < ns; i++) {
    if (sys[i].b <= 0) continue;
    for (int j = 0; j < ns; j++) {
      if (sys[j].b >= 0) continue;
      const Ineq& p = sys[i];
      const Ineq& q = sys[j];
      i64 mp = -q.b, mq = p.b;
      t1.push_back({mp * p.a + mq * q.a, 0, mp * p.c + mq * q.c, p.s || q.s});
    }
  }
  for (const Ineq& z : t1)
    if (z.a == 0 && !const_ok(z.c, z.s)) return false;
  for (const Ineq& p : t1) {
    if (p.a <= 0) continue;
    for (const Ineq& q : t1) {
      if (q.a >= 0) continue;
      i64 mp = -q.a, mq = p.a;
      if (!const_ok(mp * p.c + mq * q.c, p.s || q.s)) return false;
    }
  }
  return true;
}

struct Coupled {
  int m = 0, K = 0;
  u64 TC = 0;
  std::vector<uint8_t> tab;
  void init(int m_, int K_) {
    m = m_; K = K_;
    TC = (u64)m * (u64)m * (u64)(m + 1);
    u64 sz = 2;
    for (int j = 0; j < K; j++) sz *= TC;
    tab.assign(sz, 0);
  }
  u64 code(int n, int e, int b) const { return ((u64)(n - 1) * m + (u64)e) * (u64)(m + 1) + (u64)b; }
  bool get(int nu, const int* n, const int* e, const int* b) {
    u64 idx = (u64)nu;
    for (int j = 0; j < K; j++) idx = idx * TC + code(n[j], e[j], b[j]);
    uint8_t v = __atomic_load_n(&tab[idx], __ATOMIC_RELAXED);
    if (!v) {
      v = fm_feasible(nu, K, n, e, b) ? 2 : 1;
      __atomic_store_n(&tab[idx], v, __ATOMIC_RELAXED);
    }
    return v == 2;
  }
};

struct Tok { u64 val; uint32_t len; uint8_t first; uint8_t num; };

struct Line {
  u64 ntok;
  bool extra_nonnum;
  u64 xz[2];
  bool any;
  bool in;
  u64 cv;
  uint32_t cl;
  uint8_t cf;
  bool cn;
  char kw[8];
  Tok t[MAXSTORE];
  void reset() { ntok = 0; extra_nonnum = false; xz[0] = xz[1] = NONE; any = false; in = false; }
  inline void endtok() {
    bool num = cn && cl <= 18;
    if (ntok < MAXSTORE) {
      Tok& x = t[ntok];
      x.val = cv; x.len = cl; x.first = cf; x.num = num;
    } else if (!num) {
      extra_nonnum = true;
    } else if (cv == 0) {
      if (xz[0] == NONE) xz[0] = ntok;
      else if (xz[1] == NONE) xz[1] = ntok;
    }
    ntok++;
    in = false;
  }
  inline void put(unsigned char ch) {
    any = true;
    if (ch == ' ' || ch == '\t') { if (in) endtok(); return; }
    if (!in) { in = true; cv = 0; cl = 0; cf = ch; cn = true; }
    if (ntok == 0 && cl < 8) kw[cl] = (char)ch;
    if (cl < 19) cl++;
    if (ch >= '0' && ch <= '9') {
      if (cl <= 18) cv = cv * 10 + (u64)(ch - '0');
    } else {
      cn = false;
    }
  }
  bool comment() const { return ntok == 0 || t[0].first == '#'; }
};

void read_at(int fd, char* buf, size_t len, u64 off) {
  size_t done = 0;
  while (done < len) {
    ssize_t r = pread(fd, buf + done, len - done, (off_t)(off + done));
    if (r < 0) {
      if (errno == EINTR) continue;
      finish("IO", 0, std::string("read error: ") + strerror(errno));
    }
    if (r == 0) finish("IO", 0, "unexpected end of file (file changed during the check?)");
    done += (size_t)r;
  }
}

template <class F>
bool scan(int fd, u64 start, u64 end, std::vector<char>& buf, Line& L, F&& f) {
  u64 pos = start;
  L.reset();
  while (pos < end) {
    size_t want = (size_t)std::min<u64>((u64)buf.size(), end - pos);
    read_at(fd, buf.data(), want, pos);
    const unsigned char* p = (const unsigned char*)buf.data();
    for (size_t i = 0; i < want; i++) {
      unsigned char ch = p[i];
      if (ch == '\n') {
        if (L.in) L.endtok();
        if (!f(L, pos + i + 1)) return false;
        L.reset();
      } else {
        L.put(ch);
      }
    }
    pos += want;
  }
  if (L.in) L.endtok();
  return true;
}

struct Params {
  bool rg3 = false;
  int m = 0, k = 0, K = 0;
  u64 r = 0, F = 0, mF = 0;
  u64 w[LIM_K] = {0, 0, 0};
  u64 T0 = 0, n = 0;
  u128 W = 0, WF = 0;
  u64 header_line = 0;
  u64 ntok_state = 0;
};

bool split_ok(const uint16_t* h, int k, int m) {
  std::vector<u64> cur(1, 0), nxt;
  for (int C = k - 1; C >= 1; C--) {
    for (int rep = 0; rep < (int)h[C - 1]; rep++) {
      nxt.clear();
      for (u64 code : cur) {
        int ld[LIM_m];
        for (int i = 0; i < m; i++) ld[i] = (int)((code >> (6 * i)) & 63);
        for (int i = 0; i < m; i++) {
          if (i > 0 && ld[i] == ld[i - 1]) continue;
          if (ld[i] + C > k - 1) continue;
          int nl[LIM_m];
          for (int t = 0; t < m; t++) nl[t] = ld[t];
          nl[i] += C;
          std::sort(nl, nl + m);
          u64 c2 = 0;
          for (int t = 0; t < m; t++) c2 |= (u64)nl[t] << (6 * t);
          nxt.push_back(c2);
        }
      }
      std::sort(nxt.begin(), nxt.end());
      nxt.erase(std::unique(nxt.begin(), nxt.end()), nxt.end());
      if (nxt.empty()) return false;
      cur.swap(nxt);
    }
  }
  return true;
}

struct HDict {
  int L = 0, k = 0, m = 0;
  std::vector<uint16_t> ent;
  std::vector<uint8_t> split, used;
  std::vector<i64> cidx;
  std::vector<i64> slot;
  u64 mask = 0, cnt = 0;
  void init(int k_, int m_) {
    k = k_; m = m_; L = k - 1;
    slot.assign(1024, -1);
    mask = 1023;
  }
  u64 hash(const uint16_t* h) const {
    u64 x = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < L; i++) { x ^= h[i]; x *= 0xFF51AFD7ED558CCDULL; x ^= x >> 32; }
    return x;
  }
  i64 find(const uint16_t* h) const {
    u64 p = hash(h) & mask;
    while (true) {
      i64 s = slot[p];
      if (s < 0) return -1;
      if (!memcmp(&ent[(size_t)s * L], h, sizeof(uint16_t) * (size_t)L)) return s;
      p = (p + 1) & mask;
    }
  }
  void grow() {
    size_t ns = slot.size() * 2;
    slot.assign(ns, -1);
    mask = ns - 1;
    for (u64 s = 0; s < cnt; s++) {
      u64 p = hash(&ent[(size_t)s * L]) & mask;
      while (slot[p] >= 0) p = (p + 1) & mask;
      slot[p] = (i64)s;
    }
  }
  i64 insert(const uint16_t* h) {
    i64 s = find(h);
    if (s >= 0) return s;
    if ((cnt + 1) * 2 > slot.size()) grow();
    s = (i64)cnt++;
    ent.insert(ent.end(), h, h + L);
    split.push_back(split_ok(h, k, m) ? 1 : 0);
    used.push_back(0);
    cidx.push_back(-1);
    u64 p = hash(h) & mask;
    while (slot[p] >= 0) p = (p + 1) & mask;
    slot[p] = s;
    return s;
  }
};

template <class Look>
bool eval_adm(const Params& P, const u64* v, uint16_t* hb, Look&& look, i64& hslot,
              const char*& why) {
  const int m = P.m, k = P.k, K = P.K;
  const u64 N = v[0];
  const u64 bound = (u64)m * (u64)(k - 1);
  bool hempty = true;
  u64 sumH = 0;
  hslot = -1;
  for (int C = 1; C <= k - 1; C++) {
    u64 hc = v[C];
    if (hc) hempty = false;
    if (hc > bound / (u64)C) { why = "H is not m-splittable (C*h_C > m(k-1))"; return false; }
    sumH += (u64)C * hc;
    hb[C - 1] = (uint16_t)hc;
  }
  if (sumH > bound) { why = "H is not m-splittable (sum(H) > m(k-1))"; return false; }
  if (N == 0) {
    if (!hempty) { why = "N = 0 and H is not empty, so N < r*sum(H)+1 (A1)"; return false; }
    for (int x = 0; x < m * K; x++)
      if (v[k + x]) { why = "N = 0 and some entry is not 0 (A2)"; return false; }
    bool sp = true;
    hslot = look(hb, sp);
    if (hslot < 0) { why = "empty H missing from the dictionary"; return false; }
    return true;
  }
  bool sp = false;
  hslot = look(hb, sp);
  if (hslot < 0) { why = "H missing from the dictionary"; return false; }
  if (!sp) { why = "H is not m-splittable (A1)"; return false; }
  if (N > P.mF) { why = "N > mF (A1)"; return false; }
  if (!hempty && (u128)N < (u128)P.r * (u128)sumH + 1) { why = "N < r*sum(H)+1 (A1)"; return false; }
  for (int j = 0; j < K; j++) {
    const u64* q = v + k + j * m;
    int nj = 0;
    u128 sum = 0;
    for (int i = 0; i < m; i++) { if (q[i]) nj++; sum += q[i]; }
    if (nj == 0) { why = "a copy has no nonempty rank while N >= 1 (A2)"; return false; }
    if (sum < (u128)N) { why = "e_j < 0 (A2)"; return false; }
    if (sum - (u128)N > (u128)(nj - 1)) { why = "e_j > n_j - 1 (A2)"; return false; }
  }
  return true;
}

std::string vec_text(const u64* v, int len) {
  std::string s = "(";
  for (int i = 0; i < len; i++) { if (i) s += ","; s += dec(v[i]); }
  return s + ")";
}

std::string state_text(const Params& P, const u64* v) {
  std::string s = "N=" + dec(v[0]) + " h=" + vec_text(v + 1, P.k - 1);
  for (int j = 0; j < P.K; j++) s += " q" + std::to_string(j + 1) + "=" + vec_text(v + P.k + j * P.m, P.m);
  s += " T=" + dec(v[P.k + P.m * P.K]);
  return s;
}

u128 payoff(const Params& P, const u64* v) {
  u128 pay = 0;
  for (int j = 0; j < P.K; j++) pay += (u128)P.w[j] * (u128)v[P.k + j * P.m + P.m - 1];
  return pay;
}

struct Ckpt { u64 off, line, sidx, aidx; };

struct Pass1 {
  Params P;
  bool have_header = false;
  u64 nstates = 0, nadm = 0, lines = 0;
  u64 c2_line = 0, c4_line = 0, c5_line = 0;
  std::string c2_text, c4_text, c5_text;
  std::vector<Ckpt> ck;
  HDict dict;
  u64 maxN = 0, maxT = 0;
  int maxE[LIM_K] = {0, 0, 0};
  int maxQ[LIM_K][LIM_m] = {{0}};
  std::vector<u64> side;
  bool side_over = false;
  u64 side_last_line = 0;
};

[[noreturn]] void c1(u64 line, const std::string& text) { finish("C1", line, text); }

void parse_header(Pass1& S, const Line& L, u64 line) {
  Params& P = S.P;
  const u64 nt = L.ntok;
  bool certm = (L.t[0].len == 5 && !memcmp(L.kw, "CERTM", 5));
  bool rg3 = (L.t[0].len == 7 && !memcmp(L.kw, "RG3CERT", 7));
  if (!certm && !rg3) c1(line, "header keyword is not CERTM or RG3CERT");
  const u64 kpos = certm ? 4 : 3;
  if (nt <= kpos) c1(line, "header has " + dec(nt) + " tokens, too few to give K");
  u64 stored = std::min<u64>(nt, MAXSTORE);
  for (u64 i = 1; i < stored; i++)
    if (!L.t[i].num) c1(line, "header token " + dec(i + 1) + " is not a number token");
  if (L.extra_nonnum) c1(line, "a header token is not a number token");
  const u64 K = L.t[kpos].val;
  const u64 expect = K + (certm ? 7 : 6);
  if (nt != expect)
    c1(line, "header has " + dec(nt) + " tokens, K = " + dec(K) + " needs " + dec(expect));
  u64 m = certm ? L.t[1].val : 3;
  u64 k = L.t[kpos - 2].val, r = L.t[kpos - 1].val;
  if (m < 2) c1(line, "m < 2");
  if (k < 2) c1(line, "k < 2");
  if (r < 1) c1(line, "r < 1");
  if (K < 1) c1(line, "K < 1");
  if (nt > MAXSTORE) {
    for (u64 i = kpos + 1; i < MAXSTORE && i <= kpos + K; i++)
      if (L.t[i].val < 1) c1(line, "weight " + dec(i - kpos) + " is 0");
    if (L.xz[0] != NONE && L.xz[0] <= nt - 3) c1(line, "weight " + dec(L.xz[0] - kpos) + " is 0");
    if (L.xz[0] == nt - 1 || L.xz[1] == nt - 1) c1(line, "n < 1");
    finish("LIMIT", line, "refused: header with more than " + dec(MAXSTORE) + " tokens (K = " + dec(K) + " > 3)");
  }
  for (u64 j = 0; j < K; j++)
    if (L.t[kpos + 1 + j].val < 1) c1(line, "weight " + dec(j + 1) + " is 0");
  u64 T0 = L.t[kpos + 1 + K].val, n = L.t[kpos + 2 + K].val;
  if (n < 1) c1(line, "n < 1");
  if (m > (u64)LIM_m) finish("LIMIT", line, "refused: m = " + dec(m) + " > " + std::to_string(LIM_m));
  if (K > (u64)LIM_K) finish("LIMIT", line, "refused: K = " + dec(K) + " > " + std::to_string(LIM_K));
  if (k > LIM_k) finish("LIMIT", line, "refused: k = " + dec(k) + " > " + dec(LIM_k));
  u128 F = (u128)k * (u128)r;
  if (F > (u128)LIM_F) finish("LIMIT", line, "refused: F = k*r = " + dec(F) + " > " + dec(LIM_F));
  P.rg3 = rg3;
  P.m = (int)m; P.k = (int)k; P.K = (int)K;
  P.r = r; P.F = (u64)F; P.mF = m * (u64)F;
  P.W = 0;
  for (u64 j = 0; j < K; j++) { P.w[j] = L.t[kpos + 1 + j].val; P.W += P.w[j]; }
  P.WF = P.W * (u128)P.F;
  P.T0 = T0; P.n = n;
  P.header_line = line;
  P.ntok_state = k + m * K + 1;
}

void pass1(Pass1& S, int fd, u64 fsize) {
  std::vector<char> buf(BUFSZ);
  std::unique_ptr<Line> Lp(new Line);
  Line& L = *Lp;
  u64 line = 0;
  u64 v[LIM_k + LIM_m * LIM_K + 1];
  uint16_t hb[LIM_k];
  double t0 = now_s();
  auto on_line = [&](Line& Ln, u64 next) -> bool {
    line++;
    if (!Ln.comment()) {
      if (!S.have_header) {
        parse_header(S, Ln, line);
        S.have_header = true;
        S.dict.init(S.P.k, S.P.m);
        S.ck.push_back({next, line + 1, 0, 0});
      } else {
        const Params& P = S.P;
        if (S.nstates >= P.n) c1(line, "more than n = " + dec(P.n) + " state lines");
        if (Ln.ntok != P.ntok_state)
          c1(line, "state line has " + dec(Ln.ntok) + " tokens, expected k+mK+1 = " + dec(P.ntok_state));
        for (u64 i = 0; i < Ln.ntok; i++)
          if (!Ln.t[i].num) c1(line, "token " + dec(i + 1) + " is not a number token");
        const int m = P.m, k = P.k, K = P.K;
        for (u64 i = 0; i < Ln.ntok; i++) v[i] = Ln.t[i].val;
        for (int j = 0; j < K; j++)
          for (int i = 0; i + 1 < m; i++)
            if (v[k + j * m + i] > v[k + j * m + i + 1])
              c1(line, "copy " + std::to_string(j + 1) + " is not nondecreasing");
        const u64 sidx = S.nstates++;
        const u64 T = v[k + m * K];
        if (sidx == 0) {
          bool root = (v[0] == 0);
          for (int x = 1; x < k + m * K; x++) if (v[x]) root = false;
          if (!root) { S.c2_line = line; S.c2_text = "first state line is not the empty state: " + state_text(P, v); }
          else if (T > P.T0) { S.c2_line = line; S.c2_text = "potential " + dec(T) + " of the root exceeds T0 = " + dec(P.T0); }
        }
        i64 hs = -1;
        const char* why = "";
        auto look = [&](const uint16_t* h, bool& sp) -> i64 {
          i64 s = S.dict.insert(h);
          sp = S.dict.split[(size_t)s] != 0;
          return s;
        };
        bool adm = eval_adm(P, v, hb, look, hs, why);
        if (!adm) {
          if (!S.c4_line) { S.c4_line = line; S.c4_text = std::string("state is not admissible, ") + why + ": " + state_text(P, v); }
          if (!S.side_over) {
            if (S.side.size() + (size_t)(k + m * K + 1) > SIDE_CAP) {
              S.side_over = true;
            } else {
              S.side.insert(S.side.end(), v, v + k + m * K);
              S.side.push_back(line);
              S.side_last_line = line;
            }
          }
        }
        u128 pay = payoff(P, v);
        if (pay > (u128)T && !S.c5_line) {
          S.c5_line = line;
          S.c5_text = "pay = " + dec(pay) + " > T: " + state_text(P, v);
        }
        if (adm) {
          S.nadm++;
          S.dict.used[(size_t)hs] = 1;
          if (v[0] > S.maxN) S.maxN = v[0];
          if (T > S.maxT) S.maxT = T;
          for (int j = 0; j < K; j++) {
            const u64* q = v + k + j * m;
            u64 sum = 0;
            for (int i = 0; i < m; i++) sum += q[i];
            int e = (int)(sum - v[0]);
            if (e > S.maxE[j]) S.maxE[j] = e;
            for (int i = 0; i + 1 < m; i++)
              if ((int)q[i] > S.maxQ[j][i]) S.maxQ[j][i] = (int)q[i];
          }
        }
      }
    }
    if (S.have_header && next - S.ck.back().off >= CHUNK)
      S.ck.push_back({next, line + 1, S.nstates, S.nadm});
    return true;
  };
  scan(fd, 0, fsize, buf, L, on_line);
  S.lines = line;
  if (L.any) c1(line + 1, "last line does not end with LF");
  if (!S.have_header) c1(line + 1, "no header line");
  if (S.nstates < S.P.n)
    c1(line + 1, "file ends after " + dec(S.nstates) + " state lines, the header gives n = " + dec(S.P.n));
  S.ck.push_back({fsize, line + 1, S.nstates, S.nadm});
  fprintf(stderr, "INFO pass1 lines %s states %s admissible %s distinct-H %s time %.1fs\n",
          dec(S.lines).c_str(), dec(S.nstates).c_str(), dec(S.nadm).c_str(), dec(S.dict.cnt).c_str(),
          now_s() - t0);
}

template <int W> struct Key { u64 w[W]; };

template <int W> inline void kzero(Key<W>& k) { for (int i = 0; i < W; i++) k.w[i] = 0; }
template <int W> inline void kput(Key<W>& k, int pos, int width, u64 v) {
  if (width == 0) return;
  int wi = W - 1 - (pos >> 6), b = pos & 63;
  k.w[wi] |= v << b;
  if (b + width > 64) k.w[wi - 1] |= v >> (64 - b);
}
template <int W> inline u64 kget(const Key<W>& k, int pos, int width) {
  if (width == 0) return 0;
  int wi = W - 1 - (pos >> 6), b = pos & 63;
  u64 v = k.w[wi] >> b;
  if (b + width > 64) v |= k.w[wi - 1] << (64 - b);
  if (width < 64) v &= ((u64)1 << width) - 1;
  return v;
}
template <int W> inline Key<W> kor(const Key<W>& a, const Key<W>& b) {
  Key<W> c;
  for (int i = 0; i < W; i++) c.w[i] = a.w[i] | b.w[i];
  return c;
}
template <int W> inline bool keq(const Key<W>& a, const Key<W>& b) {
  for (int i = 0; i < W; i++) if (a.w[i] != b.w[i]) return false;
  return true;
}
template <int W> Key<W> kones(int nbits) {
  Key<W> k;
  kzero(k);
  for (int p = 0; p < nbits; p += 64) {
    int wd = std::min(64, nbits - p);
    kput(k, p, wd, wd == 64 ? ~(u64)0 : (((u64)1 << wd) - 1));
  }
  return k;
}

template <int W, class P> struct __attribute__((packed)) Rec { u64 w[W]; P pot; };

template <int W, class P> inline bool rless(const Rec<W, P>& a, const Rec<W, P>& b) {
  for (int i = 0; i < W; i++) if (a.w[i] != b.w[i]) return a.w[i] < b.w[i];
  return false;
}
template <int W, class P> inline bool req(const Rec<W, P>& a, const Rec<W, P>& b) {
  for (int i = 0; i < W; i++) if (a.w[i] != b.w[i]) return false;
  return true;
}
template <int W, class P> inline bool rk_less(const Rec<W, P>& a, const Key<W>& b) {
  for (int i = 0; i < W; i++) if (a.w[i] != b.w[i]) return a.w[i] < b.w[i];
  return false;
}
template <int W, class P> inline bool kr_less(const Key<W>& a, const Rec<W, P>& b) {
  for (int i = 0; i < W; i++) if (a.w[i] != b.w[i]) return a.w[i] < b.w[i];
  return false;
}
template <int W, class P> inline bool rk_eq(const Rec<W, P>& a, const Key<W>& b) {
  for (int i = 0; i < W; i++) if (a.w[i] != b.w[i]) return false;
  return true;
}
template <int W, class P> inline Key<W> rkey(const Rec<W, P>& a) {
  Key<W> k;
  for (int i = 0; i < W; i++) k.w[i] = a.w[i];
  return k;
}

struct Layout {
  int wN = 0, wH = 0, posN = 0, posH = 0;
  int we[LIM_K] = {0}, pe[LIM_K] = {0};
  int wq[LIM_K][LIM_m] = {{0}}, pq[LIM_K][LIM_m] = {{0}};
  int lowc[LIM_K] = {0};
  int B = 0, W = 0;
  u64 maxN = 0, numH = 0;
  int maxE[LIM_K] = {0};
  int maxQ[LIM_K][LIM_m] = {{0}};
};

Layout make_layout(const Pass1& S, u64 numH, int gap) {
  const int m = S.P.m, K = S.P.K;
  Layout Y;
  Y.maxN = S.maxN;
  Y.numH = numH;
  Y.wN = bits_of(S.maxN) + gap;
  Y.wH = bits_of(numH ? numH - 1 : 0) + gap;
  int pos = 0;
  for (int j = K - 1; j >= 0; j--) {
    Y.lowc[j] = pos;
    for (int i = m - 2; i >= 0; i--) {
      Y.maxQ[j][i] = S.maxQ[j][i];
      Y.wq[j][i] = bits_of((u64)S.maxQ[j][i]) + gap;
      Y.pq[j][i] = pos;
      pos += Y.wq[j][i];
    }
    Y.maxE[j] = S.maxE[j];
    Y.we[j] = bits_of((u64)S.maxE[j]) + gap;
    Y.pe[j] = pos;
    pos += Y.we[j];
  }
  Y.posH = pos;
  pos += Y.wH;
  Y.posN = pos;
  pos += Y.wN;
  Y.B = pos;
  Y.W = std::max(1, (pos + 63) / 64);
  return Y;
}

struct Tables {
  int k = 0;
  std::vector<uint8_t> sp;
  std::vector<i64> ix;
  std::vector<i64> ent_of;
  bool splitAdd(u64 H, u64 C) const { return sp[(size_t)(H * (u64)k + C)] != 0; }
  i64 idxAdd(u64 H, u64 C) const { return ix[(size_t)(H * (u64)k + C)]; }
};

template <class T, class Cmp>
void psort_rec(T* a, i64 n, Cmp cmp, int depth) {
  if (n < ((i64)1 << 16) || depth <= 0) { std::sort(a, a + n, cmp); return; }
  T x = a[0], y = a[n / 2], z = a[n - 1];
  T piv = cmp(x, y) ? (cmp(y, z) ? y : (cmp(x, z) ? z : x)) : (cmp(x, z) ? x : (cmp(y, z) ? z : y));
  T* m1 = std::partition(a, a + n, [&](const T& v) { return cmp(v, piv); });
  T* m2 = std::partition(m1, a + n, [&](const T& v) { return !cmp(piv, v); });
  i64 nl = m1 - a, nr = (a + n) - m2;
#ifdef _OPENMP
#pragma omp task
  psort_rec(a, nl, cmp, depth - 1);
#pragma omp task
  psort_rec(m2, nr, cmp, depth - 1);
#pragma omp taskwait
#else
  psort_rec(a, nl, cmp, depth - 1);
  psort_rec(m2, nr, cmp, depth - 1);
#endif
}
template <class T, class Cmp>
void psort(T* a, i64 n, Cmp cmp) {
#ifdef _OPENMP
  int depth = 8;
  for (int t = nthreads(); t > 1; t >>= 1) depth += 2;
#pragma omp parallel
#pragma omp single
  psort_rec(a, n, cmp, depth);
#else
  std::sort(a, a + n, cmp);
#endif
}

inline void bit_set(std::vector<u64>& b, u64 i) {
  __atomic_fetch_or(&b[(size_t)(i >> 6)], (u64)1 << (i & 63), __ATOMIC_RELAXED);
}
inline bool bit_get(const std::vector<u64>& b, u64 i) { return (b[(size_t)(i >> 6)] >> (i & 63)) & 1; }

u64 binom(int n, int b) {
  static const u64 c[7][7] = {{1}, {1, 1}, {1, 2, 1}, {1, 3, 3, 1}, {1, 4, 6, 4, 1},
                              {1, 5, 10, 10, 5, 1}, {1, 6, 15, 20, 15, 6, 1}};
  return c[n][b];
}

std::string bits_text(int o, int m) {
  std::string s;
  for (int i = 0; i < m; i++) s += ((o >> i) & 1) ? '1' : '0';
  return s;
}

struct Ctx {
  int fd = -1;
  u64 fsize = 0;
  Pass1 S;
  Tables TB;
  Layout Y;
  Coupled CP;
};

template <int W, class PT>
struct Engine {
  typedef Rec<W, PT> R;
  Ctx& X;
  const Params& P;
  const Layout& Y;
  const Tables& TB;
  Coupled& CP;
  R* rec = nullptr;
  u64 n = 0;
  std::vector<u64> gtab;
  bool use_gtab = false;
  Key<W> lowmask[LIM_K];
  Key<W> gmask;

  explicit Engine(Ctx& x) : X(x), P(x.S.P), Y(x.Y), TB(x.TB), CP(x.CP) {
    for (int j = 0; j < P.K; j++) lowmask[j] = kones<W>(Y.lowc[j]);
    gmask = kones<W>(Y.posH);
  }
  ~Engine() { delete[] rec; }

  u64 lower(u64 lo, u64 hi, const Key<W>& k) const {
    while (lo < hi) {
      u64 mid = lo + (hi - lo) / 2;
      if (rk_less(rec[mid], k)) lo = mid + 1; else hi = mid;
    }
    return lo;
  }
  u64 upper(u64 lo, u64 hi, const Key<W>& k) const {
    while (lo < hi) {
      u64 mid = lo + (hi - lo) / 2;
      if (kr_less(k, rec[mid])) hi = mid; else lo = mid + 1;
    }
    return lo;
  }
  u64 find(u64 lo, u64 hi, const Key<W>& k) const {
    u64 i = lower(lo, hi, k);
    return (i < hi && rk_eq(rec[i], k)) ? i : NONE;
  }
  Key<W> group_key(u64 N, u64 H) const {
    Key<W> k;
    kzero(k);
    kput(k, Y.posN, Y.wN, N);
    kput(k, Y.posH, Y.wH, H);
    return k;
  }
  bool group_range(u64 N, u64 H, u64& lo, u64& hi) const {
    if (use_gtab) {
      u64 g = (N << Y.wH) | H;
      lo = gtab[(size_t)g];
      hi = gtab[(size_t)g + 1];
    } else {
      Key<W> k0 = group_key(N, H);
      lo = lower(0, n, k0);
      hi = upper(lo, n, kor(k0, gmask));
    }
    return lo < hi;
  }
  void build_gtab() {
    int Pb = Y.wN + Y.wH;
    if (Pb > 30) return;
    u64 G = (u64)1 << Pb;
    if (G > std::max<u64>((u64)1 << 22, 2 * n)) return;
    gtab.assign((size_t)G + 1, 0);
    gtab[(size_t)G] = n;
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
    for (i64 g = 0; g < (i64)G; g++) {
      Key<W> k;
      kzero(k);
      kput(k, Y.posH, Pb, (u64)g);
      gtab[(size_t)g] = lower(0, n, k);
    }
    use_gtab = true;
  }

  bool line_key(const u64* v, Key<W>& key, uint16_t* hb) const {
    const HDict& D = X.S.dict;
    i64 hs;
    const char* why;
    auto look = [&](const uint16_t* h, bool& sp) -> i64 {
      i64 s = D.find(h);
      sp = s >= 0 && D.split[(size_t)s];
      return s;
    };
    if (!eval_adm(P, v, hb, look, hs, why)) return false;
    i64 ci = D.cidx[(size_t)hs];
    if (ci < 0) finish("INTERNAL", 0, "multiset H of an admissible line has no index");
    kzero(key);
    kput(key, Y.posN, Y.wN, v[0]);
    kput(key, Y.posH, Y.wH, (u64)ci);
    const int m = P.m, k = P.k;
    for (int j = 0; j < P.K; j++) {
      const u64* q = v + k + j * m;
      u64 sum = 0;
      for (int i = 0; i < m; i++) sum += q[i];
      u64 e = sum - v[0];
      if (v[0] > Y.maxN || (int)e > Y.maxE[j]) finish("IO", 0, "file changed between passes");
      kput(key, Y.pe[j], Y.we[j], e);
      for (int i = 0; i + 1 < m; i++) {
        if ((int)q[i] > Y.maxQ[j][i]) finish("IO", 0, "file changed between passes");
        kput(key, Y.pq[j][i], Y.wq[j][i], q[i]);
      }
    }
    return true;
  }

  void pass2() {
    double t0 = now_s();
    n = X.S.nadm;
    rec = new (std::nothrow) R[(size_t)n];
    if (!rec) finish("LIMIT", 0, "refused: out of memory for " + dec(n) + " states of " + std::to_string(sizeof(R)) + " bytes");
    const std::vector<Ckpt>& ck = X.S.ck;
    const i64 nch = (i64)ck.size() - 1;
    int bad = 0;
#ifdef _OPENMP
#pragma omp parallel
#endif
    {
      std::vector<char> buf(BUFSZ);
      std::unique_ptr<Line> Lp(new Line);
      u64 v[LIM_k + LIM_m * LIM_K + 1];
      uint16_t hb[LIM_k];
#ifdef _OPENMP
#pragma omp for schedule(dynamic, 1)
#endif
      for (i64 c = 0; c < nch; c++) {
        u64 aidx = ck[(size_t)c].aidx, sidx = ck[(size_t)c].sidx;
        const u64 aend = ck[(size_t)c + 1].aidx;
        bool ok = true;
        scan(X.fd, ck[(size_t)c].off, ck[(size_t)c + 1].off, buf, *Lp, [&](Line& L, u64) -> bool {
          if (L.comment()) return true;
          if (L.ntok != P.ntok_state) { ok = false; return false; }
          for (u64 i = 0; i < L.ntok; i++) v[i] = L.t[i].val;
          Key<W> key;
          if (line_key(v, key, hb)) {
            if (aidx >= aend) { ok = false; return false; }
            for (int i = 0; i < W; i++) rec[aidx].w[i] = key.w[i];
            rec[aidx].pot = (PT)v[P.ntok_state - 1];
            aidx++;
          }
          sidx++;
          return true;
        });
        if (!ok || aidx != aend || sidx != ck[(size_t)c + 1].sidx) {
#ifdef _OPENMP
#pragma omp atomic write
#endif
          bad = 1;
        }
      }
    }
    if (bad) finish("IO", 0, "file changed between passes");
    fprintf(stderr, "INFO pass2 stored %s states time %.1fs\n", dec(n).c_str(), now_s() - t0);
  }

  template <class F>
  void rescan(F&& f) {
    const std::vector<Ckpt>& ck = X.S.ck;
    std::vector<char> buf(BUFSZ);
    std::unique_ptr<Line> Lp(new Line);
    u64 v[LIM_k + LIM_m * LIM_K + 1];
    for (size_t c = 0; c + 1 < ck.size(); c++) {
      u64 line = ck[c].line;
      bool go = scan(X.fd, ck[c].off, ck[c + 1].off, buf, *Lp, [&](Line& L, u64) -> bool {
        u64 ln = line++;
        if (L.comment()) return true;
        for (u64 i = 0; i < L.ntok && i < P.ntok_state; i++) v[i] = L.t[i].val;
        return f(ln, v);
      });
      if (!go) return;
    }
  }

  std::string h_text(u64 H) const {
    const HDict& D = X.S.dict;
    i64 s = TB.ent_of[(size_t)H];
    std::string t = "(";
    for (int i = 0; i < D.L; i++) { if (i) t += ","; t += std::to_string(D.ent[(size_t)s * D.L + i]); }
    return t + ")";
  }

  struct St { u64 N, H, T; int e[LIM_K], nn[LIM_K], q[LIM_K][LIM_m]; };

  St decode(u64 idx) const {
    Key<W> k = rkey(rec[idx]);
    St s;
    const int m = P.m;
    s.N = kget(k, Y.posN, Y.wN);
    s.H = kget(k, Y.posH, Y.wH);
    s.T = (u64)rec[idx].pot;
    for (int j = 0; j < P.K; j++) {
      s.e[j] = (int)kget(k, Y.pe[j], Y.we[j]);
      i64 sum = 0;
      for (int i = 0; i + 1 < m; i++) { s.q[j][i] = (int)kget(k, Y.pq[j][i], Y.wq[j][i]); sum += s.q[j][i]; }
      s.q[j][m - 1] = (int)((i64)s.N + s.e[j] - sum);
      s.nn[j] = 0;
      for (int i = 0; i < m; i++) if (s.q[j][i] > 0) s.nn[j]++;
    }
    return s;
  }

  std::string st_text(const St& s) const {
    std::string t = "N=" + dec(s.N) + " h=" + h_text(s.H);
    for (int j = 0; j < P.K; j++) {
      t += " q" + std::to_string(j + 1) + "=(";
      for (int i = 0; i < P.m; i++) { if (i) t += ","; t += std::to_string(s.q[j][i]); }
      t += ")";
    }
    return t + " T=" + dec(s.T);
  }

  bool succ_copy(const St& s, int j, int i, int beta, u64 c, int nu, Key<W>& ck) const {
    const int m = P.m;
    int v[LIM_m];
    for (int t = 0; t < m; t++) v[t] = s.q[j][t];
    int x = v[i] + (int)c + beta, p = i;
    while (p + 1 < m && v[p + 1] < x) { v[p] = v[p + 1]; p++; }
    v[p] = x;
    int ep = s.e[j] + beta - nu;
    if (ep < 0 || ep > Y.maxE[j]) return false;
    for (int t = 0; t + 1 < m; t++) if (v[t] > Y.maxQ[j][t]) return false;
    kzero(ck);
    kput(ck, Y.pe[j], Y.we[j], (u64)ep);
    for (int t = 0; t + 1 < m; t++) kput(ck, Y.pq[j][t], Y.wq[j][t], (u64)v[t]);
    return true;
  }

  std::string describe(const St& s, u64 c, int nu, const int* o) const {
    const int m = P.m, K = P.K;
    u64 C = c / P.r;
    i64 Hn = C >= 1 ? TB.idxAdd(s.H, C) : (i64)s.H;
    u64 Np = s.N + c + (u64)nu;
    u64 reach = 0, best = NONE, total = 1;
    for (int j = 0; j < K; j++) total *= (u64)m;
    u64 glo = 0, ghi = 0;
    bool grp = Hn >= 0 && Np <= Y.maxN && group_range(Np, (u64)Hn, glo, ghi);
    for (u64 rho = 0; rho < total && grp; rho++) {
      u64 rr = rho;
      Key<W> key = group_key(Np, (u64)Hn);
      bool ok = true;
      for (int j = 0; j < K; j++) {
        int i = (int)(rr % (u64)m);
        rr /= (u64)m;
        Key<W> ck;
        if (!succ_copy(s, j, i, (o[j] >> i) & 1, c, nu, ck)) { ok = false; break; }
        key = kor(key, ck);
      }
      if (!ok) continue;
      u64 f = find(glo, ghi, key);
      if (f == NONE) continue;
      reach++;
      if ((u64)rec[f].pot < best) best = (u64)rec[f].pot;
    }
    std::string t = "state " + st_text(s) + "; move c=" + dec(c) + " nu=" + std::to_string(nu) + " bits ";
    for (int j = 0; j < K; j++) { if (j) t += "/"; t += bits_text(o[j], m); }
    t += " has no answer: " + dec(reach) + " of " + dec(total) + " responses reach a listed state";
    if (reach) t += ", least potential " + dec(best) + " > " + dec(s.T);
    return t;
  }

  bool check_state(u64 idx, u128& A, u128& I, std::string* why) const {
    const int m = P.m, K = P.K;
    const u64 F = P.F, r = P.r, mF = P.mF;
    const St s = decode(idx);
    const u64 T = s.T;

    if (s.N == 0) {
      int ones[LIM_K];
      for (int j = 0; j < K; j++) ones[j] = (1 << m) - 1;
      for (u64 c = 0; c < F; c++) {
        u64 C = c / r;
        if (C >= 1 && !TB.splitAdd(s.H, C)) continue;
        if (s.N + c + 1 > mF) continue;
        A += 1;
        i64 Hn = C >= 1 ? TB.idxAdd(s.H, C) : (i64)s.H;
        u64 Np = c + 1;
        bool ok = false;
        u64 glo, ghi;
        if (Hn >= 0 && Np <= Y.maxN && group_range(Np, (u64)Hn, glo, ghi)) {
          Key<W> key = group_key(Np, (u64)Hn);
          bool enc = true;
          for (int j = 0; j < K && enc; j++) {
            Key<W> ck;
            enc = succ_copy(s, j, m - 1, 1, c, 1, ck);
            key = kor(key, ck);
          }
          if (enc) {
            u64 f = find(glo, ghi, key);
            ok = (f != NONE && (u64)rec[f].pot <= T);
          }
        }
        if (!ok) { if (why) *why = describe(s, c, 1, ones); return false; }
      }
      return true;
    }

    bool allowed[2][343];
    bool possible[2][LIM_K][LIM_m + 1];
    u64 cnt[2] = {0, 0}, idle0 = 0;
    bool need0[2][LIM_K], need1[2][LIM_K];
    for (int nu = 0; nu < 2; nu++) {
      for (int j = 0; j < K; j++) {
        need0[nu][j] = need1[nu][j] = false;
        for (int b = 0; b <= m; b++) possible[nu][j][b] = false;
      }
      int bb[LIM_K] = {0, 0, 0};
      int lim1 = K > 1 ? s.nn[1] : 0, lim2 = K > 2 ? s.nn[2] : 0;
      for (bb[0] = 0; bb[0] <= s.nn[0]; bb[0]++)
        for (bb[1] = 0; bb[1] <= lim1; bb[1]++)
          for (bb[2] = 0; bb[2] <= lim2; bb[2]++) {
            bool ok = CP.get(nu, s.nn, s.e, bb);
            allowed[nu][bb[0] * 49 + bb[1] * 7 + bb[2]] = ok;
            if (!ok) continue;
            u64 prod = 1;
            bool allpos = true;
            for (int j = 0; j < K; j++) {
              prod *= binom(s.nn[j], bb[j]);
              if (bb[j] == 0) allpos = false;
              if (bb[j] >= 1) need0[nu][j] = true;
              if (bb[j] <= s.nn[j] - 1) need1[nu][j] = true;
              possible[nu][j][bb[j]] = true;
            }
            cnt[nu] += prod;
            if (nu == 0 && allpos) idle0 += prod;
          }
    }

    int nv[LIM_K];
    uint8_t vo[LIM_K][64], vb[LIM_K][64];
    for (int j = 0; j < K; j++) {
      int ne = m - s.nn[j];
      int emp = (1 << ne) - 1;
      nv[j] = 0;
      for (int mask = 0; mask < (1 << s.nn[j]); mask++) {
        vo[j][nv[j]] = (uint8_t)(emp | (mask << ne));
        vb[j][nv[j]] = (uint8_t)(s.nn[j] - __builtin_popcount((unsigned)mask));
        nv[j]++;
      }
    }

    for (u64 c = 0; c < F; c++) {
      u64 C = c / r;
      if (C >= 1 && !TB.splitAdd(s.H, C)) continue;
      i64 Hn = C >= 1 ? TB.idxAdd(s.H, C) : (i64)s.H;
      for (int nu = 0; nu < 2; nu++) {
        u64 Np = s.N + c + (u64)nu;
        if (Np > mF) continue;
        if (cnt[nu] == 0) continue;
        const bool zz = (c == 0 && nu == 0);
        A += cnt[nu];
        if (zz) I += idle0;
        if (cnt[nu] - (zz ? idle0 : 0) == 0) continue;

        u64 glo = 0, ghi = 0;
        const bool grp = Hn >= 0 && Np <= Y.maxN && group_range(Np, (u64)Hn, glo, ghi);

        int nc[LIM_K];
        Key<W> ckey[LIM_K][2 * LIM_m];
        bool cabs[LIM_K][2 * LIM_m];
        int8_t cid[LIM_K][LIM_m][2];
        for (int j = 0; j < K; j++) {
          nc[j] = 0;
          int absent = -1;
          for (int i = 0; i < m; i++) {
            for (int beta = 0; beta < 2; beta++) {
              cid[j][i][beta] = -1;
              bool empty = i < m - s.nn[j];
              if (empty && beta == 0) continue;
              if (!empty && beta == 0 && !need0[nu][j]) continue;
              if (!empty && beta == 1 && !need1[nu][j]) continue;
              Key<W> ck;
              if (!grp || !succ_copy(s, j, i, beta, c, nu, ck)) {
                if (absent < 0) { absent = nc[j]; cabs[j][nc[j]] = true; kzero(ckey[j][nc[j]]); nc[j]++; }
                cid[j][i][beta] = (int8_t)absent;
                continue;
              }
              int f = -1;
              for (int a = 0; a < nc[j]; a++)
                if (!cabs[j][a] && keq(ckey[j][a], ck)) { f = a; break; }
              if (f < 0) { f = nc[j]; ckey[j][f] = ck; cabs[j][f] = false; nc[j]++; }
              cid[j][i][beta] = (int8_t)f;
            }
          }
        }

        uint16_t cm[LIM_K][64];
        for (int j = 0; j < K; j++)
          for (int u = 0; u < nv[j]; u++) {
            cm[j][u] = 0;
            if (!possible[nu][j][vb[j][u]]) continue;
            for (int i = 0; i < m; i++) {
              int a = cid[j][i][(vo[j][u] >> i) & 1];
              if (a < 0) finish("INTERNAL", 0, "candidate missing");
              cm[j][u] |= (uint16_t)(1u << a);
            }
          }

        const Key<W> gk = grp ? group_key(Np, (u64)Hn) : Key<W>();
        int fu = -1, fv = -1, fw = -1;
        if (K == 1) {
          uint16_t g1 = 0;
          for (int a = 0; a < nc[0]; a++) {
            if (cabs[0][a]) continue;
            u64 f = find(glo, ghi, kor(gk, ckey[0][a]));
            if (f != NONE && (u64)rec[f].pot <= T) g1 |= (uint16_t)(1u << a);
          }
          for (int u = 0; u < nv[0] && fu < 0; u++) {
            int b0 = vb[0][u];
            if (!allowed[nu][b0 * 49]) continue;
            if (zz && b0 >= 1) continue;
            if (!(cm[0][u] & g1)) fu = u;
          }
        } else if (K == 2) {
          uint16_t row[2 * LIM_m];
          for (int a = 0; a < nc[0]; a++) {
            row[a] = 0;
            if (cabs[0][a]) continue;
            Key<W> pre = kor(gk, ckey[0][a]);
            u64 l1 = lower(glo, ghi, pre);
            u64 h1 = upper(l1, ghi, kor(pre, lowmask[0]));
            if (l1 >= h1) continue;
            for (int b = 0; b < nc[1]; b++) {
              if (cabs[1][b]) continue;
              u64 f = find(l1, h1, kor(pre, ckey[1][b]));
              if (f != NONE && (u64)rec[f].pot <= T) row[a] |= (uint16_t)(1u << b);
            }
          }
          for (int u = 0; u < nv[0] && fu < 0; u++) {
            int b0 = vb[0][u];
            if (!possible[nu][0][b0]) continue;
            uint16_t R1 = 0;
            for (int a = 0; a < nc[0]; a++) if ((cm[0][u] >> a) & 1) R1 |= row[a];
            for (int v2 = 0; v2 < nv[1]; v2++) {
              int b1 = vb[1][v2];
              if (!allowed[nu][b0 * 49 + b1 * 7]) continue;
              if (zz && b0 >= 1 && b1 >= 1) continue;
              if (!(R1 & cm[1][v2])) { fu = u; fv = v2; break; }
            }
          }
        } else {
          uint16_t G[2 * LIM_m][2 * LIM_m];
          for (int a = 0; a < nc[0]; a++) {
            for (int b = 0; b < nc[1]; b++) G[a][b] = 0;
            if (cabs[0][a]) continue;
            Key<W> pre1 = kor(gk, ckey[0][a]);
            u64 l1 = lower(glo, ghi, pre1);
            u64 h1 = upper(l1, ghi, kor(pre1, lowmask[0]));
            if (l1 >= h1) continue;
            for (int b = 0; b < nc[1]; b++) {
              if (cabs[1][b]) continue;
              Key<W> pre2 = kor(pre1, ckey[1][b]);
              u64 l2 = lower(l1, h1, pre2);
              u64 h2 = upper(l2, h1, kor(pre2, lowmask[1]));
              if (l2 >= h2) continue;
              for (int d = 0; d < nc[2]; d++) {
                if (cabs[2][d]) continue;
                u64 f = find(l2, h2, kor(pre2, ckey[2][d]));
                if (f != NONE && (u64)rec[f].pot <= T) G[a][b] |= (uint16_t)(1u << d);
              }
            }
          }
          for (int u = 0; u < nv[0] && fu < 0; u++) {
            int b0 = vb[0][u];
            if (!possible[nu][0][b0]) continue;
            uint16_t S1[2 * LIM_m];
            for (int b = 0; b < nc[1]; b++) {
              S1[b] = 0;
              for (int a = 0; a < nc[0]; a++) if ((cm[0][u] >> a) & 1) S1[b] |= G[a][b];
            }
            for (int v2 = 0; v2 < nv[1] && fu < 0; v2++) {
              int b1 = vb[1][v2];
              if (!possible[nu][1][b1]) continue;
              uint16_t R2 = 0;
              for (int b = 0; b < nc[1]; b++) if ((cm[1][v2] >> b) & 1) R2 |= S1[b];
              for (int w3 = 0; w3 < nv[2]; w3++) {
                int b2 = vb[2][w3];
                if (!allowed[nu][b0 * 49 + b1 * 7 + b2]) continue;
                if (zz && b0 >= 1 && b1 >= 1 && b2 >= 1) continue;
                if (!(R2 & cm[2][w3])) { fu = u; fv = v2; fw = w3; break; }
              }
            }
          }
        }
        if (fu >= 0) {
          if (why) {
            int o[LIM_K] = {vo[0][fu], K > 1 ? vo[1][fv] : 0, K > 2 ? vo[2][fw] : 0};
            *why = describe(s, c, nu, o);
          }
          return false;
        }
      }
    }
    return true;
  }

  void run() {
    pass2();
    double t0 = now_s();
    psort(rec, (i64)n, [](const R& a, const R& b) { return rless(a, b); });
    fprintf(stderr, "INFO sort time %.1fs\n", now_s() - t0);

    std::vector<u64> dup((size_t)((n + 63) / 64), 0);
    u64 ndup = 0;
#ifdef _OPENMP
#pragma omp parallel for schedule(static) reduction(+ : ndup)
#endif
    for (i64 i = 0; i < (i64)n; i++) {
      bool eqn = (u64)i + 1 < n && req(rec[i], rec[i + 1]);
      bool eqp = i > 0 && req(rec[i - 1], rec[i]);
      if (eqn && !eqp) { bit_set(dup, (u64)i); ndup++; }
    }
    u64 L2 = 0, L1 = 0;
    std::string c3text;
    if (ndup) {
      std::vector<u64> seen(dup.size(), 0);
      uint16_t hb[LIM_k];
      Key<W> hit;
      kzero(hit);
      rescan([&](u64 line, const u64* v) -> bool {
        Key<W> key;
        if (!line_key(v, key, hb)) return true;
        u64 i = lower(0, n, key);
        if (!bit_get(dup, i)) return true;
        if (bit_get(seen, i)) { L2 = line; hit = key; c3text = state_text(P, v); return false; }
        bit_set(seen, i);
        return true;
      });
      rescan([&](u64 line, const u64* v) -> bool {
        Key<W> key;
        if (!line_key(v, key, hb)) return true;
        if (keq(key, hit)) { L1 = line; return false; }
        return true;
      });
      if (!L2 || !L1) finish("INTERNAL", 0, "duplicate state not found again");
    }
    std::vector<u64>& sd = X.S.side;
    const size_t st = (size_t)(P.k + P.m * P.K + 1);
    if (!sd.empty()) {
      size_t ns = sd.size() / st;
      std::vector<u64> ord(ns);
      for (size_t i = 0; i < ns; i++) ord[i] = i;
      std::sort(ord.begin(), ord.end(), [&](u64 a, u64 b) {
        for (size_t t = 0; t < st; t++)
          if (sd[a * st + t] != sd[b * st + t]) return sd[a * st + t] < sd[b * st + t];
        return false;
      });
      for (size_t i = 1; i < ns; i++) {
        const u64* a = &sd[ord[i - 1] * st];
        const u64* b = &sd[ord[i] * st];
        bool same = true;
        for (size_t t = 0; t + 1 < st; t++) if (a[t] != b[t]) { same = false; break; }
        if (!same) continue;
        if (i >= 2) {
          const u64* z = &sd[ord[i - 2] * st];
          bool sz = true;
          for (size_t t = 0; t + 1 < st; t++) if (z[t] != a[t]) { sz = false; break; }
          if (sz) continue;
        }
        u64 l2 = b[st - 1], l1 = a[st - 1];
        if (!L2 || l2 < L2) {
          L2 = l2; L1 = l1;
          u64 vv[LIM_k + LIM_m * LIM_K + 1];
          for (size_t t = 0; t + 1 < st; t++) vv[t] = a[t];
          vv[st - 1] = 0;
          c3text = state_text(P, vv);
          c3text = c3text.substr(0, c3text.rfind(" T="));
        }
      }
      if (X.S.side_over && (!L2 || L2 > X.S.side_last_line))
        finish("LIMIT", 0, "refused: too many inadmissible lines to test (C3) among them");
    }
    if (L2) finish("C3", L2, "same state as line " + dec(L1) + ": " + c3text);
    if (X.S.c4_line) finish("C4", X.S.c4_line, X.S.c4_text);
    if (X.S.c5_line) finish("C5", X.S.c5_line, X.S.c5_text);
    { std::vector<u64>().swap(dup); }

    build_gtab();
    double mem = (double)n * sizeof(R) + (double)gtab.size() * 8.0 + (double)((n + 63) / 64) * 8.0;
    fprintf(stderr, "INFO key bits %d words %d potential bytes %d record bytes %d group table %s entries\n",
            Y.B, W, (int)sizeof(PT), (int)sizeof(R), dec(gtab.size()).c_str());
    fprintf(stderr, "INFO bytes-per-state %.2f (records %d, group table %.2f, failure bitmap 0.125)\n",
            mem / (double)n, (int)sizeof(R), (double)gtab.size() * 8.0 / (double)n);
    t0 = now_s();
    std::vector<u64> fail((size_t)((n + 63) / 64), 0);
    u128 A = 0, I = 0;
    u64 nfail = 0, done = 0;
    const int nt = nthreads();
#ifdef _OPENMP
#pragma omp parallel reduction(+ : nfail)
#endif
    {
      u128 a = 0, b = 0;
#ifdef _OPENMP
#pragma omp for schedule(dynamic, 256)
#endif
      for (i64 i = 0; i < (i64)n; i++) {
        if (!check_state((u64)i, a, b, nullptr)) { bit_set(fail, (u64)i); nfail++; }
        if ((i & 0xFFFFF) == 0xFFFFF) {
          u64 d = __atomic_add_fetch(&done, (u64)0x100000, __ATOMIC_RELAXED);
          if ((d & 0x3FFFFFF) == 0)
            fprintf(stderr, "INFO C6 progress %s of %s states %.0fs\n", dec(d).c_str(), dec(n).c_str(), now_s() - t0);
        }
      }
#ifdef _OPENMP
#pragma omp critical
#endif
      { A += a; I += b; }
    }
    fprintf(stderr, "INFO C6 threads %d time %.1fs failing states %s\n", nt, now_s() - t0, dec(nfail).c_str());
    if (nfail) {
      u64 Lf = 0, fidx = 0;
      uint16_t hb[LIM_k];
      rescan([&](u64 line, const u64* v) -> bool {
        Key<W> key;
        if (!line_key(v, key, hb)) return true;
        u64 i = lower(0, n, key);
        if (bit_get(fail, i)) { Lf = line; fidx = i; return false; }
        return true;
      });
      if (!Lf) finish("INTERNAL", 0, "failing state not found again");
      std::string why;
      u128 a = 0, b = 0;
      if (check_state(fidx, a, b, &why)) finish("INTERNAL", Lf, "failing state passes on the second run");
      finish("C6", Lf, why);
    }
    fprintf(stderr, "INFO peak-rss %.0f bytes (%.2f per state) total time %.1fs\n", peak_rss_bytes(),
            peak_rss_bytes() / (double)n, now_s() - T_START);
    fprintf(stderr, "INFO all-moves %s idle %s\n", dec(A).c_str(), dec(I).c_str());
    fflush(stderr);
    std::string ws;
    for (int j = 0; j < P.K; j++) { if (j) ws += ","; ws += dec(P.w[j]); }
    printf("PASS m %d k %d r %s weights %s T0 %s states %s moves %s bound %s/%s\n", P.m, P.k,
           dec(P.r).c_str(), ws.c_str(), dec(P.T0).c_str(), dec(P.n).c_str(), dec(A - I).c_str(),
           dec(P.T0).c_str(), dec(P.WF).c_str());
    fflush(stdout);
    exit(0);
  }
};

template <int W, class PT>
[[noreturn]] void run_with(Ctx& X) {
  Engine<W, PT> E(X);
  E.run();
  exit(0);
}

template <int W>
[[noreturn]] void run_w(Ctx& X) {
  if (X.S.maxT <= 0xFFFFu) run_with<W, uint16_t>(X);
  if (X.S.maxT <= 0xFFFFFFFFu) run_with<W, uint32_t>(X);
  run_with<W, uint64_t>(X);
}

int selftest() {
  bool ok = true;
  struct V { const char* id; int nu, K; int t[3][3]; bool yes; };
  const V vs[] = {
      {"V1", 0, 1, {{4, 2, 0}}, true},
      {"V2", 1, 1, {{4, 1, 4}}, true},
      {"V3", 0, 2, {{4, 0, 0}, {3, 0, 3}}, true},
      {"V4", 1, 3, {{4, 1, 4}, {2, 0, 0}, {1, 0, 0}}, true},
      {"V5", 0, 1, {{4, 3, 4}}, true},
      {"V6", 0, 1, {{4, 0, 0}}, true},
      {"V7", 1, 1, {{4, 0, 4}}, false},
      {"V8", 0, 1, {{4, 3, 0}}, false},
      {"V9", 0, 2, {{2, 0, 0}, {2, 0, 2}}, false},
      {"V10", 0, 2, {{3, 0, 3}, {3, 1, 1}}, false},
      {"V11", 1, 3, {{4, 1, 4}, {4, 2, 0}, {1, 0, 0}}, false},
  };
  for (const V& x : vs) {
    int n[3], e[3], b[3];
    for (int j = 0; j < x.K; j++) { n[j] = x.t[j][0]; e[j] = x.t[j][1]; b[j] = x.t[j][2]; }
    bool got = fm_feasible(x.nu, x.K, n, e, b);
    printf("%s %s %s\n", x.id, got ? "yes" : "no", got == x.yes ? "ok" : "WRONG");
    if (got != x.yes) ok = false;
  }
  const u64 expect[3][6] = {{8, 10, 46, 202, 28, 60}, {20, 28, 348, 4060, 188, 860},
                            {40, 60, 1560, 37692, 810, 7082}};
  for (int m = 2; m <= 6; m++) {
    std::vector<std::array<int, 3>> tr;
    for (int nn = 1; nn <= m; nn++)
      for (int e = 0; e < nn; e++)
        for (int b = 0; b <= nn; b++) tr.push_back({nn, e, b});
    const int T = (int)tr.size();
    u64 c1 = 0, c2 = 0, c3 = 0, s2 = 0, s3 = 0;
    for (int nu = 0; nu < 2; nu++)
      for (int a = 0; a < T; a++) {
        int n[3], e[3], b[3];
        n[0] = tr[a][0]; e[0] = tr[a][1]; b[0] = tr[a][2];
        if (fm_feasible(nu, 1, n, e, b)) c1++;
        for (int bq = 0; bq < T; bq++) {
          n[1] = tr[bq][0]; e[1] = tr[bq][1]; b[1] = tr[bq][2];
          bool y2 = fm_feasible(nu, 2, n, e, b);
          if (y2) { c2++; if (a <= bq) s2++; }
          if (m > 4) continue;
          for (int c = 0; c < T; c++) {
            n[2] = tr[c][0]; e[2] = tr[c][1]; b[2] = tr[c][2];
            if (fm_feasible(nu, 3, n, e, b)) { c3++; if (a <= bq && bq <= c) s3++; }
          }
        }
      }
    if (m <= 4) {
      u64 got[6] = {(u64)T, c1, c2, c3, s2, s3};
      bool same = true;
      for (int i = 0; i < 6; i++) if (got[i] != expect[m - 2][i]) same = false;
      printf("m=%d triples %d K1 %s K2 %s K3 %s K2multi %s K3multi %s %s\n", m, T, dec(c1).c_str(),
             dec(c2).c_str(), dec(c3).c_str(), dec(s2).c_str(), dec(s3).c_str(), same ? "ok" : "WRONG");
      if (!same) ok = false;
    } else {
      printf("m=%d triples %d K1 %s K2 %s K2multi %s (no reference)\n", m, T, dec(c1).c_str(),
             dec(c2).c_str(), dec(s2).c_str());
    }
  }
  printf(ok ? "SELFTEST PASS\n" : "SELFTEST FAIL\n");
  return ok ? 0 : 1;
}

}

int main(int argc, char** argv) {
  T_START = now_s();
  std::set_new_handler(out_of_memory);
  if (argc == 2 && !strcmp(argv[1], "--selftest")) return selftest();
  if (argc != 2) { fputs(USAGE_TEXT, stderr); finish("USAGE", 0, "usage: cmb FILE | cmb --selftest"); }
  if (!strcmp(argv[1], "-")) {
    fputs(USAGE_TEXT, stderr);
    finish("USAGE", 0, "refused: standard input is not supported, the checker reads the file twice");
  }
  if (const char* c = getenv("CMB_TEST_CHUNK")) {
    CHUNK = std::max<u64>(1, strtoull(c, nullptr, 10));
    fprintf(stderr, "INFO test hook CMB_TEST_CHUNK %s\n", dec(CHUNK).c_str());
  }
  Ctx X;
  X.fd = open(argv[1], O_RDONLY);
  if (X.fd < 0) finish("IO", 0, std::string("cannot open ") + argv[1] + ": " + strerror(errno));
  struct stat stt;
  if (fstat(X.fd, &stt) != 0) finish("IO", 0, std::string("cannot stat: ") + strerror(errno));
  if (!S_ISREG(stt.st_mode)) {
    fputs(USAGE_TEXT, stderr);
    finish("USAGE", 0, "refused: the input must be a regular file, it is read twice");
  }
  X.fsize = (u64)stt.st_size;
  fprintf(stderr, "INFO cmb threads %d file %s bytes %s\n", nthreads(), argv[1], dec(X.fsize).c_str());

  Pass1& S = X.S;
  pass1(S, X.fd, X.fsize);
  const Params& P = S.P;
  if (S.c2_line) finish("C2", S.c2_line, S.c2_text);

  u64 numH = 0;
  for (u64 s = 0; s < S.dict.cnt; s++)
    if (S.dict.used[(size_t)s]) S.dict.cidx[(size_t)s] = (i64)numH++;
  X.TB.k = P.k;
  X.TB.ent_of.assign((size_t)numH, -1);
  X.TB.sp.assign((size_t)(numH * (u64)P.k), 0);
  X.TB.ix.assign((size_t)(numH * (u64)P.k), -1);
  {
    const int L = S.dict.L;
    const u64 bound = (u64)P.m * (u64)(P.k - 1);
    std::vector<uint16_t> h(L);
    for (u64 s = 0; s < S.dict.cnt; s++) {
      i64 ci = S.dict.cidx[(size_t)s];
      if (ci < 0) continue;
      X.TB.ent_of[(size_t)ci] = (i64)s;
      for (int C = 1; C <= P.k - 1; C++) {
        for (int i = 0; i < L; i++) h[i] = S.dict.ent[(size_t)s * L + i];
        u64 sum = 0;
        for (int i = 0; i < L; i++) sum += (u64)(i + 1) * h[i];
        h[C - 1]++;
        sum += (u64)C;
        bool sp = false;
        i64 t = S.dict.find(h.data());
        if (t >= 0) sp = S.dict.split[(size_t)t] != 0;
        else if (sum <= bound) sp = split_ok(h.data(), P.k, P.m);
        X.TB.sp[(size_t)(ci * P.k + C)] = sp ? 1 : 0;
        X.TB.ix[(size_t)(ci * P.k + C)] = (sp && t >= 0) ? S.dict.cidx[(size_t)t] : -1;
      }
    }
  }
  int gap = 0;
  if (const char* g = getenv("CMB_TEST_GAP")) gap = std::max(0, std::min(30, atoi(g)));
  X.Y = make_layout(S, numH, gap);
  if (gap) fprintf(stderr, "INFO test hook CMB_TEST_GAP %d\n", gap);
  if (X.Y.W > LIM_W)
    finish("LIMIT", P.header_line, "refused: a state key needs " + std::to_string(X.Y.B) + " bits > " +
                                       std::to_string(64 * LIM_W));
  X.CP.init(P.m, P.K);
  switch (X.Y.W) {
    case 1: run_w<1>(X);
    case 2: run_w<2>(X);
    case 3: run_w<3>(X);
    default: run_w<4>(X);
  }
}
