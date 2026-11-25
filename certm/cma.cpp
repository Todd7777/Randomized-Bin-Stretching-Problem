// cma.cpp: checks a CERTM certificate. Prints one line, PASS (exit 0) or FAIL.
// g++ -O2 -std=c++17 -fopenmp -o cma cma.cpp && ./cma FILE
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <new>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef uint64_t u64;
typedef int64_t i64;
typedef uint32_t u32;
typedef uint16_t u16;
typedef unsigned __int128 u128;
static const u64 NONE = ~0ULL;

static bool quiet = false;

static std::string dec(u128 x) {
    if (x == 0) return "0";
    char b[64];
    int i = 63;
    b[i] = 0;
    while (x) { b[--i] = char('0' + (int)(x % 10)); x /= 10; }
    return std::string(b + i);
}

static void (*g_before_c1)() = nullptr;

[[noreturn]] static void fail(const char* cond, u64 line, const std::string& text) {
    if (g_before_c1 && !strcmp(cond, "C1")) {
        void (*f)() = g_before_c1;
        g_before_c1 = nullptr;
        f();
    }
    printf("FAIL %s line %s: %s\n", cond, dec(line).c_str(), text.c_str());
    fflush(stdout);
    int code = 1;
    if (!strcmp(cond, "LIMIT") || !strcmp(cond, "IO") || !strcmp(cond, "USAGE")) code = 2;
    else if (!strcmp(cond, "INTERNAL")) code = 3;
    exit(code);
}

static void info(const char* fmt, ...) {
    if (quiet) return;
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fflush(stderr);
}

static double now_s() {
    using namespace std::chrono;
    return duration<double>(steady_clock::now().time_since_epoch()).count();
}

static int nthreads() {
#ifdef _OPENMP
    return omp_get_max_threads();
#else
    return 1;
#endif
}
static int tid() {
#ifdef _OPENMP
    return omp_get_thread_num();
#else
    return 0;
#endif
}

static inline int popc(u64 x) { return __builtin_popcountll(x); }
static inline int ctz(u64 x) { return __builtin_ctzll(x); }

static int bits_of(u128 x) {
    int b = 0;
    while (x) { b++; x >>= 1; }
    return b;
}

static inline u64 fmix(u64 k) {
    k ^= k >> 33; k *= 0xff51afd7ed558ccdULL;
    k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL;
    k ^= k >> 33;
    return k;
}
static inline u64 hcode(u64 x) { return fmix(x ^ 0x9e3779b97f4a7c15ULL); }
static inline u64 hcode(u128 x) { return fmix((u64)x ^ fmix((u64)(x >> 64) + 0x9e3779b97f4a7c15ULL)); }

static u64 hash_bytes(const char* p, const char* q) {
    u64 h = 0x243f6a8885a308d3ULL ^ (u64)(q - p);
    while (q - p >= 8) {
        u64 w;
        memcpy(&w, p, 8);
        h = (h ^ w) * 0x9fb21c651e98df25ULL;
        h ^= h >> 31;
        p += 8;
    }
    u64 w = 0;
    memcpy(&w, p, (size_t)(q - p));
    h = (h ^ w) * 0x9fb21c651e98df25ULL;
    return fmix(h);
}

static const int MAXM = 6, MAXK = 3, MAXk = 64;
static const u64 MAXF = 65536;
static const int MAXTOK = MAXk + MAXM * MAXK + 1;
static const int MAXOPT = 2 * MAXM;

static int gm = 0, gk = 0, gK = 0;
static int HL = 0, NTOK = 0;
static u64 gr = 0, gF = 0, gmF = 0;
static u64 gqmax = 0;
static u64 gT0 = 0, gn = 0;
static u64 gw[MAXK] = {0, 0, 0};
static u64 hmax[MAXk];
static std::atomic<int> g_oom(0);

static inline bool blank(char c) { return c == ' ' || c == '\t'; }

static inline bool is_comment(const char* p, const char* e) {
    while (p < e && blank(*p)) p++;
    return p == e || *p == '#';
}

static bool number_token(const char* p, const char* q, u64& v) {
    size_t L = (size_t)(q - p);
    if (L < 1 || L > 18) return false;
    u64 x = 0;
    for (; p < q; p++) {
        unsigned d = (unsigned)(unsigned char)*p - '0';
        if (d > 9) return false;
        x = x * 10 + d;
    }
    v = x;
    return true;
}

static int parse_state_line(const char* p, const char* e, u64* v, std::string* why) {
    while (p < e && blank(*p)) p++;
    if (p == e || *p == '#') return 0;
    u64 cnt = 0;
    while (p < e) {
        const char* t = p;
        u64 x = 0;
        bool num = true;
        while (p < e && !blank(*p)) {
            unsigned d = (unsigned)(unsigned char)*p - '0';
            if (d > 9) num = false;
            else x = x * 10 + d;
            p++;
        }
        if (!num || p - t > 18) {
            if (why) *why = "token " + dec(cnt + 1) + " is not a number token of 1 to 18 digits";
            return 2;
        }
        if (cnt < (u64)NTOK) v[cnt] = x;
        cnt++;
        while (p < e && blank(*p)) p++;
    }
    if (cnt != (u64)NTOK) {
        if (why) *why = "state line has " + dec(cnt) + " tokens, expected k+mK+1 = " + dec(NTOK);
        return 2;
    }
    for (int j = 0; j < gK; j++) {
        const u64* q = v + gk + j * gm;
        for (int i = 0; i + 1 < gm; i++)
            if (q[i] > q[i + 1]) {
                if (why) *why = "copy " + dec(j + 1) + " is not nondecreasing";
                return 2;
            }
    }
    return 1;
}

static std::string state_text(const u64* v) {
    std::string s = "state N=" + dec(v[0]) + " h=(";
    for (int C = 1; C <= HL; C++) s += (C > 1 ? "," : "") + dec(v[C]);
    s += ") q=";
    for (int j = 0; j < gK; j++) {
        s += (j ? "/(" : "(");
        for (int i = 0; i < gm; i++) s += (i ? " " : "") + dec(v[gk + j * gm + i]);
        s += ")";
    }
    s += " T=" + dec(v[NTOK - 1]);
    return s;
}

static bool is_root(const u64* v) {
    for (int i = 0; i < NTOK - 1; i++)
        if (v[i]) return false;
    return true;
}

static void parse_header(const char* p, const char* e, u64 line) {
    std::vector<std::pair<const char*, const char*>> t;
    while (p < e) {
        while (p < e && blank(*p)) p++;
        if (p == e) break;
        const char* s = p;
        while (p < e && !blank(*p)) p++;
        t.push_back({s, p});
    }
    std::string kw(t[0].first, t[0].second);
    bool cm = kw == "CERTM", rg = kw == "RG3CERT";
    if (!cm && !rg) fail("C1", line, "first token of the header is neither CERTM nor RG3CERT");
    std::vector<u64> v(t.size(), 0);
    for (size_t i = 1; i < t.size(); i++)
        if (!number_token(t[i].first, t[i].second, v[i]))
            fail("C1", line, "header token " + dec(i + 1) + " is not a number token");
    size_t kpos = cm ? 4 : 3;
    if (t.size() <= kpos) fail("C1", line, "header too short to hold K");
    u64 K = v[kpos];
    u64 want = K + (cm ? 7 : 6);
    if ((u64)t.size() != want)
        fail("C1", line, "header has " + dec(t.size()) + " tokens, expected " + dec(want));
    u64 m = cm ? v[1] : 3, k = v[kpos - 2], r = v[kpos - 1];
    u64 T0 = v[kpos + 1 + K], n = v[kpos + 2 + K];
    if (m < 2) fail("C1", line, "m < 2");
    if (k < 2) fail("C1", line, "k < 2");
    if (r < 1) fail("C1", line, "r < 1");
    if (K < 1) fail("C1", line, "K < 1");
    for (u64 j = 0; j < K; j++)
        if (v[kpos + 1 + j] < 1) fail("C1", line, "weight " + dec(j + 1) + " is 0");
    if (n < 1) fail("C1", line, "n < 1");
    if (m > (u64)MAXM) fail("LIMIT", line, "refused: m = " + dec(m) + " > " + dec(MAXM));
    if (K > (u64)MAXK) fail("LIMIT", line, "refused: K = " + dec(K) + " > " + dec(MAXK));
    if (k > (u64)MAXk) fail("LIMIT", line, "refused: k = " + dec(k) + " > " + dec(MAXk));
    if (r > MAXF || k * r > MAXF) fail("LIMIT", line, "refused: F = k*r > " + dec(MAXF));
    gm = (int)m; gk = (int)k; gK = (int)K; gr = r; gF = k * r; gmF = m * gF;
    gqmax = gmF + m - 1; gT0 = T0; gn = n;
    for (u64 j = 0; j < K; j++) gw[j] = v[kpos + 1 + j];
    NTOK = gk + gm * gK + 1;
    HL = gk - 1;
    for (int C = 1; C <= HL; C++) hmax[C] = (u64)gm * (u64)(gk - 1) / (u64)C;
}

struct Source {
    std::string path, cmd;
};

struct Reader {
    FILE* f = nullptr;
    bool pipe = false;
    std::vector<char> buf;
    size_t beg = 0, end = 0;
    bool eof = false;

    void open(const Source& s) {
        if (!s.cmd.empty()) { f = popen(s.cmd.c_str(), "r"); pipe = true; }
        else { f = fopen(s.path.c_str(), "rb"); pipe = false; }
        if (!f) fail("IO", 0, "cannot open the input");
        buf.assign((size_t)1 << 20, 0);
        beg = end = 0;
        eof = false;
    }
    void drain_close() {
        if (!f || !pipe) return;
        std::vector<char> tmp((size_t)1 << 20);
        while (fread(tmp.data(), 1, tmp.size(), f) > 0) {}
        int st = pclose(f);
        f = nullptr;
        if (st != 0) fail("IO", 0, "the input command failed");
    }
    void close(bool early) {
        if (!f) return;
        if (pipe) {
            int st = pclose(f);
            f = nullptr;
            if (st != 0 && !early) fail("IO", 0, "the input command failed");
        } else {
            fclose(f);
            f = nullptr;
        }
    }
    void fill(size_t want) {
        if (end - beg >= want || eof) return;
        if (beg > 0) {
            memmove(buf.data(), buf.data() + beg, end - beg);
            end -= beg;
            beg = 0;
        }
        try {
            if (buf.size() < want) buf.resize(want);
        } catch (const std::bad_alloc&) {
            fail("LIMIT", 0, "refused: out of memory for the input buffer");
        }
        while (end < want && !eof) {
            size_t got = fread(buf.data() + end, 1, buf.size() - end, f);
            if (got == 0) {
                if (ferror(f)) fail("IO", 0, "read error");
                eof = true;
            }
            end += got;
        }
    }
    int next_line(const char*& p, const char*& q) {
        size_t scan = 0;
        for (;;) {
            const char* s = buf.data() + beg;
            size_t av = end - beg;
            const char* lf = av > scan ? (const char*)memchr(s + scan, '\n', av - scan) : nullptr;
            if (lf) { p = s; q = lf; beg = (size_t)(lf - buf.data()) + 1; return 1; }
            if (eof) {
                if (av == 0) return 0;
                p = s; q = s + av; beg = end;
                return -1;
            }
            scan = av;
            fill(av + ((size_t)1 << 20));
        }
    }
    int next_block(size_t bs, const char*& p, const char*& q) {
        fill(bs);
        size_t look = std::min(bs, end - beg);
        for (;;) {
            const char* s = buf.data() + beg;
            size_t av = end - beg;
            const char* lf = nullptr;
            for (const char* t = s + look; t > s;) {
                --t;
                if (*t == '\n') { lf = t; break; }
            }
            if (!lf && av > look) lf = (const char*)memchr(s + look, '\n', av - look);
            if (lf) { p = s; q = lf + 1; beg += (size_t)(q - p); return 1; }
            if (eof) {
                if (av == 0) return 0;
                p = s; q = s + av; beg = end;
                return -1;
            }
            look = av;
            fill(av * 2 + ((size_t)1 << 20));
        }
    }
};

typedef std::pair<const char*, const char*> Span;

static u64 count_lf(const char* p, const char* q) {
    u64 n = 0;
    while (p < q) {
        const char* lf = (const char*)memchr(p, '\n', (size_t)(q - p));
        if (!lf) break;
        n++;
        p = lf + 1;
    }
    return n;
}

struct BlockSplit {
    std::vector<Span> sub;
    std::vector<u64> start, hsub, nl;
    u64 lines = 0, hash = 0;
    void make(const char* p, const char* q, size_t ts, u64 firstline) {
        sub.clear();
        while (p < q) {
            const char* c = (size_t)(q - p) > ts ? p + ts : q;
            if (c < q) c = (const char*)memchr(c - 1, '\n', (size_t)(q - (c - 1))) + 1;
            sub.push_back({p, c});
            p = c;
        }
        long ns = (long)sub.size();
        nl.assign(ns, 0);
        hsub.assign(ns, 0);
#pragma omp parallel for schedule(static)
        for (long s = 0; s < ns; s++) {
            nl[s] = count_lf(sub[s].first, sub[s].second);
            hsub[s] = hash_bytes(sub[s].first, sub[s].second);
        }
        start.assign(ns, 0);
        u64 L = firstline;
        hash = 0x452821e638d01377ULL;
        for (long s = 0; s < ns; s++) {
            start[s] = L;
            L += nl[s];
            hash = fmix(hash ^ hsub[s]) + 0x9e3779b97f4a7c15ULL;
        }
        lines = L - firstline;
    }
};

static u64 nth_noncomment_line(const char* p, const char* q, u64 line, u64 idx) {
    while (p < q) {
        const char* lf = (const char*)memchr(p, '\n', (size_t)(q - p));
        if (!is_comment(p, lf)) {
            if (idx == 0) return line;
            idx--;
        }
        p = lf + 1;
        line++;
    }
    return NONE;
}

struct SplitDFS {
    int m, cap;
    std::vector<int> items;
    std::unordered_set<u64> failed;
    bool dfs(size_t idx, int* loads) {
        if (idx == items.size()) return true;
        u64 key = idx;
        for (int b = 0; b < m; b++) key = key * 64 + (u64)loads[b];
        if (failed.count(key)) return false;
        int s = items[idx];
        for (int b = 0; b < m; b++) {
            if (b > 0 && loads[b] == loads[b - 1]) continue;
            if (loads[b] + s > cap) continue;
            int save[MAXM];
            memcpy(save, loads, sizeof(int) * m);
            loads[b] += s;
            std::sort(loads, loads + m, [](int a, int c) { return a > c; });
            if (dfs(idx + 1, loads)) return true;
            memcpy(loads, save, sizeof(int) * m);
        }
        failed.insert(key);
        return false;
    }
};

static bool split_test_mk(const u16* h, int m, int k) {
    u64 total = 0;
    for (int C = 1; C <= k - 1; C++) total += (u64)C * h[C - 1];
    if (total > (u64)m * (u64)(k - 1)) return false;
    SplitDFS S;
    S.m = m;
    S.cap = k - 1;
    for (int C = k - 1; C >= 2; C--)
        for (int t = 0; t < h[C - 1]; t++) S.items.push_back(C);
    int loads[MAXM] = {0, 0, 0, 0, 0, 0};
    return S.dfs(0, loads);
}
static bool split_test(const u16* h) { return split_test_mk(h, gm, gk); }

static inline u64 hashH(const u16* h, int L) {
    u64 x = 0x84222325cbf29ce4ULL;
    for (int i = 0; i < L; i++) x = (x ^ h[i]) * 0x100000001b3ULL;
    return fmix(x);
}

struct DictH {
    int L = 1;
    std::vector<u16> keys;
    std::vector<u32> tab;
    u64 mask = 0;
    size_t sz = 0;
    void init(int L_) { L = L_; tab.assign(256, 0); mask = 255; keys.clear(); sz = 0; }
    const u16* key(size_t i) const { return keys.data() + i * L; }
    i64 find(const u16* h) const {
        u64 p = hashH(h, L) & mask;
        for (;;) {
            u32 x = tab[p];
            if (!x) return -1;
            if (!memcmp(key(x - 1), h, sizeof(u16) * L)) return (i64)x - 1;
            p = (p + 1) & mask;
        }
    }
    void grow() {
        size_t ns = tab.size() * 2;
        tab.assign(ns, 0);
        mask = ns - 1;
        for (size_t i = 0; i < sz; i++) {
            u64 p = hashH(key(i), L) & mask;
            while (tab[p]) p = (p + 1) & mask;
            tab[p] = (u32)(i + 1);
        }
    }
    void insert(const u16* h) {
        if (find(h) >= 0) return;
        if (sz + 1 >= 0x7fffffffULL) fail("LIMIT", 0, "refused: 2^31 distinct multisets H");
        if ((sz + 1) * 2 > tab.size()) grow();
        keys.insert(keys.end(), h, h + L);
        sz++;
        u64 p = hashH(h, L) & mask;
        while (tab[p]) p = (p + 1) & mask;
        tab[p] = (u32)sz;
    }
    size_t bytes() const { return keys.capacity() * sizeof(u16) + tab.capacity() * sizeof(u32); }
};

static DictH DH;
static std::vector<int32_t> addC;

static bool coupled_test(int m, int nu, int cnt, const int* n, const int* e, const int* b) {
    for (int d = 1; d <= m; d++)
        for (int a = 0; a <= d; a++) {
            long mu = d;
            if (nu) mu = std::min<long>(mu, a);
            long ml = 0;
            if (!nu) ml = std::max<long>(ml, a);
            for (int j = 0; j < cnt; j++) {
                mu = std::min<long>(mu, (long)(n[j] - b[j]) * a + (long)(b[j] - e[j]) * d);
                ml = std::max<long>(ml, (long)b[j] * a - (long)e[j] * d);
            }
            if (mu > ml) return true;
        }
    return false;
}

struct Coupled {
    int m = 0, K = 0, NT = 0;
    int id[MAXM + 1][MAXM][MAXM + 1];
    int tn[256], te[256], tb[256];
    std::vector<uint8_t> tab[MAXK + 1];
    void build(int m_, int K_) {
        m = m_; K = K_; NT = 0;
        for (int n = 1; n <= m; n++)
            for (int e = 0; e < n; e++)
                for (int b = 0; b <= n; b++) {
                    id[n][e][b] = NT; tn[NT] = n; te[NT] = e; tb[NT] = b; NT++;
                }
        for (int kk = 1; kk <= K; kk++) {
            u64 sz = 2;
            for (int i = 0; i < kk; i++) sz *= (u64)NT;
            tab[kk].assign(sz, 0);
            long S = (long)sz;
            int NTl = NT, mm = m;
            uint8_t* tp = tab[kk].data();
#pragma omp parallel for schedule(static)
            for (long x = 0; x < S; x++) {
                long y = x;
                int t[MAXK], n[MAXK], e[MAXK], b[MAXK];
                for (int i = kk - 1; i >= 0; i--) { t[i] = (int)(y % NTl); y /= NTl; }
                int nu = (int)y;
                for (int i = 0; i < kk; i++) { n[i] = tn[t[i]]; e[i] = te[t[i]]; b[i] = tb[t[i]]; }
                tp[x] = coupled_test(mm, nu, kk, n, e, b) ? 1 : 0;
            }
        }
    }
    inline bool get(int nu, int kk, const int* t) const {
        u64 x = (u64)nu;
        for (int i = 0; i < kk; i++) x = x * (u64)NT + (u64)t[i];
        return tab[kk][x] != 0;
    }
    size_t bytes() const {
        size_t s = 0;
        for (int i = 1; i <= K; i++) s += tab[i].capacity();
        return s;
    }
};

static Coupled CP;

struct Lin { i64 a, b, c; bool strict; };
static bool fm_feasible(int nu, int cnt, const int* n, const int* e, const int* b) {
    std::vector<Lin> L;
    L.push_back({-1, 0, 0, true});
    L.push_back({1, 0, -1, false});
    L.push_back({0, -1, 0, false});
    L.push_back({0, 1, -1, true});
    if (nu) L.push_back({-1, 1, 0, true});
    else L.push_back({1, -1, 0, false});
    for (int j = 0; j < cnt; j++) {
        L.push_back({b[j], -1, -e[j], false});
        L.push_back({-(i64)(n[j] - b[j]), 1, e[j] - b[j], true});
        if (b[j] >= 1) L.push_back({1, 0, -1, true});
    }
    std::vector<Lin> T1;
    for (const Lin& l : L)
        if (l.b == 0) T1.push_back(l);
    for (const Lin& u : L) {
        if (u.b <= 0) continue;
        for (const Lin& w : L) {
            if (w.b >= 0) continue;
            T1.push_back({-w.b * u.a + u.b * w.a, 0, -w.b * u.c + u.b * w.c, u.strict || w.strict});
        }
    }
    bool haveLo = false, haveHi = false, loS = false, hiS = false;
    i64 loN = 0, loD = 1, hiN = 0, hiD = 1;
    for (const Lin& l : T1) {
        if (l.a == 0) {
            if (l.strict ? !(l.c < 0) : !(l.c <= 0)) return false;
            continue;
        }
        if (l.a > 0) {
            i64 N = -l.c, D = l.a;
            if (!haveHi || N * hiD < hiN * D || (N * hiD == hiN * D && l.strict)) {
                if (haveHi && N * hiD == hiN * D) hiS = hiS || l.strict;
                else hiS = l.strict;
                hiN = N; hiD = D; haveHi = true;
            }
        } else {
            i64 N = l.c, D = -l.a;
            if (!haveLo || N * loD > loN * D || (N * loD == loN * D && l.strict)) {
                if (haveLo && N * loD == loN * D) loS = loS || l.strict;
                else loS = l.strict;
                loN = N; loD = D; haveLo = true;
            }
        }
    }
    if (!haveLo || !haveHi) return true;
    i64 lhs = loN * hiD, rhs = hiN * loD;
    if (lhs < rhs) return true;
    if (lhs == rhs && !loS && !hiS) return true;
    return false;
}

struct SplitCheck {
    int m, k;
    u64 tested = 0, bad = 0;
    std::vector<u16> h;
    void rec(int C, const std::set<std::vector<int>>& S) {
        if (C == 0) {
            tested++;
            if (split_test_mk(h.data(), m, k) != !S.empty()) bad++;
            return;
        }
        std::set<std::vector<int>> cur = S;
        for (int cnt = 0;; cnt++) {
            h[C - 1] = (u16)cnt;
            rec(C - 1, cur);
            if (cur.empty()) break;
            std::set<std::vector<int>> nx;
            for (const auto& t : cur)
                for (int i = 0; i < m; i++)
                    if (t[i] + C <= k - 1) {
                        std::vector<int> u = t;
                        u[i] += C;
                        std::sort(u.begin(), u.end());
                        nx.insert(u);
                    }
            cur.swap(nx);
        }
        h[C - 1] = 0;
    }
};

static int selftest() {
    bool ok = true;
    struct V { int m, nu, cnt; int n[3], e[3], b[3]; bool yes; const char* id; };
    const V vs[] = {
        {4, 0, 1, {4}, {2}, {0}, true, "V1"},
        {4, 1, 1, {4}, {1}, {4}, true, "V2"},
        {4, 0, 2, {4, 3}, {0, 0}, {0, 3}, true, "V3"},
        {4, 1, 3, {4, 2, 1}, {1, 0, 0}, {4, 0, 0}, true, "V4"},
        {4, 0, 1, {4}, {3}, {4}, true, "V5"},
        {4, 0, 1, {4}, {0}, {0}, true, "V6"},
        {4, 1, 1, {4}, {0}, {4}, false, "V7"},
        {4, 0, 1, {4}, {3}, {0}, false, "V8"},
        {4, 0, 2, {2, 2}, {0, 0}, {0, 2}, false, "V9"},
        {4, 0, 2, {3, 3}, {0, 1}, {3, 1}, false, "V10"},
        {4, 1, 3, {4, 4, 1}, {1, 2, 0}, {4, 0, 0}, false, "V11"},
    };
    for (const V& v : vs) {
        bool got = coupled_test(v.m, v.nu, v.cnt, v.n, v.e, v.b);
        bool fm = fm_feasible(v.nu, v.cnt, v.n, v.e, v.b);
        bool got3 = coupled_test(3, v.nu, v.cnt, v.n, v.e, v.b);
        fprintf(stderr, "%-3s COUPLED %-3s FM %-3s expected %-3s (test with d <= 3: %s)\n", v.id,
                got ? "yes" : "no", fm ? "yes" : "no", v.yes ? "yes" : "no", got3 ? "yes" : "no");
        if (got != v.yes || fm != v.yes) ok = false;
    }
    const u64 expect[3][5] = {{10, 46, 202, 28, 60}, {28, 348, 4060, 188, 860},
                              {60, 1560, 37692, 810, 7082}};
    for (int m = 2; m <= 4; m++) {
        Coupled c;
        c.build(m, 3);
        u64 k1 = 0, k2 = 0, k3 = 0, s2 = 0, s3 = 0;
        for (int nu = 0; nu < 2; nu++)
            for (int a = 0; a < c.NT; a++) {
                int t1[1] = {a};
                if (c.get(nu, 1, t1)) k1++;
                for (int b = 0; b < c.NT; b++) {
                    int t2[2] = {a, b};
                    if (c.get(nu, 2, t2)) { k2++; if (a <= b) s2++; }
                    for (int d = 0; d < c.NT; d++) {
                        int t3[3] = {a, b, d};
                        if (c.get(nu, 3, t3)) { k3++; if (a <= b && b <= d) s3++; }
                    }
                }
            }
        fprintf(stderr, "m=%d triples=%d K=1: %llu, K=2: %llu, K=3: %llu, multisets K=2: %llu, K=3: %llu\n",
                m, c.NT, (unsigned long long)k1, (unsigned long long)k2, (unsigned long long)k3,
                (unsigned long long)s2, (unsigned long long)s3);
        const u64* x = expect[m - 2];
        if (k1 != x[0] || k2 != x[1] || k3 != x[2] || s2 != x[3] || s3 != x[4]) ok = false;
    }
    for (int m = 2; m <= 6; m++) {
        Coupled c;
        c.build(m, 1);
        u64 tests = 0, diff = 0;
        int NT = c.NT;
        for (int nu = 0; nu < 2; nu++)
            for (int a = 0; a < NT; a++) {
                for (int b = a; b < NT; b++)
                    for (int d = b; d < NT; d++) {
                        int n[3] = {c.tn[a], c.tn[b], c.tn[d]}, e[3] = {c.te[a], c.te[b], c.te[d]},
                            bb[3] = {c.tb[a], c.tb[b], c.tb[d]};
                        tests++;
                        if (coupled_test(m, nu, 3, n, e, bb) != fm_feasible(nu, 3, n, e, bb)) diff++;
                    }
                for (int b = 0; b < NT; b++) {
                    int n[2] = {c.tn[a], c.tn[b]}, e[2] = {c.te[a], c.te[b]}, bb[2] = {c.tb[a], c.tb[b]};
                    tests += 2;
                    if (coupled_test(m, nu, 2, n, e, bb) != fm_feasible(nu, 2, n, e, bb)) diff++;
                    if (coupled_test(m, nu, 1, n, e, bb) != fm_feasible(nu, 1, n, e, bb)) diff++;
                }
            }
        fprintf(stderr, "m=%d integer test vs Fourier-Motzkin: %llu combinations, %llu differ\n", m,
                (unsigned long long)tests, (unsigned long long)diff);
        if (diff) ok = false;
    }
    const int mk[][2] = {{2, 2}, {2, 5}, {2, 9}, {3, 2}, {3, 6}, {3, 8}, {4, 2}, {4, 6}, {4, 7},
                         {5, 5}, {5, 6}, {6, 4}, {6, 5}};
    for (const auto& x : mk) {
        SplitCheck sc;
        sc.m = x[0];
        sc.k = x[1];
        sc.h.assign((size_t)x[1] - 1, 0);
        std::set<std::vector<int>> S;
        S.insert(std::vector<int>((size_t)x[0], 0));
        sc.rec(x[1] - 1, S);
        fprintf(stderr, "m=%d k=%d m-splittable vs Split of SM2.6: %llu multisets, %llu differ\n", x[0],
                x[1], (unsigned long long)sc.tested, (unsigned long long)sc.bad);
        if (sc.bad) ok = false;
    }
    printf(ok ? "PASS selftest\n" : "FAIL INTERNAL line 0: selftest\n");
    return ok ? 0 : 3;
}

static const char* domain_reason(const u64* v) {
    if (v[0] > gmF) return "(A1) N > mF";
    for (int C = 1; C <= HL; C++)
        if (v[C] > hmax[C]) return "(A1) C*h_C > m(k-1), so H is not m-splittable";
    if (v[0] == 0) {
        for (int C = 1; C <= HL; C++)
            if (v[C]) return "(A1) H is not empty and N = 0 < r*sum(H)+1";
        for (int i = 0; i < gm * gK; i++)
            if (v[gk + i]) return "(A2) N = 0 and an entry is not 0";
        return nullptr;
    }
    for (int i = 0; i < gm * gK; i++)
        if (v[gk + i] > gqmax) return "(A2) an entry exceeds mF+m-1, so e_j > n_j-1";
    return nullptr;
}

static const char* rest_reason(const u64* v, bool splittable) {
    if (!splittable) return "(A1) H is not m-splittable";
    u64 N = v[0], sumH = 0;
    for (int C = 1; C <= HL; C++) sumH += (u64)C * v[C];
    if (sumH > 0 && N < gr * sumH + 1) return "(A1) N < r*sum(H)+1";
    if (N == 0) return nullptr;
    const u64* q = v + gk;
    for (int j = 0; j < gK; j++) {
        u64 s = 0, nj = 0;
        for (int i = 0; i < gm; i++) { s += q[j * gm + i]; if (q[j * gm + i]) nj++; }
        if (nj == 0) return "(A2) N >= 1 and a copy has no nonempty rank";
        if (s < N) return "(A2) e_j < 0";
        if (s - N > nj - 1) return "(A2) e_j > n_j - 1";
    }
    return nullptr;
}

static u128 payoff(const u64* v) {
    u128 pay = 0;
    for (int j = 0; j < gK; j++) pay += (u128)gw[j] * (u128)v[gk + j * gm + gm - 1];
    return pay;
}

struct Ranges {
    u64 nAdm = 0, Nmax = 0, Tmax = 0;
    u64 emax[MAXK] = {0, 0, 0};
    u64 qmx[MAXK][MAXM] = {};
    void add(const u64* v) {
        nAdm++;
        u64 N = v[0];
        Nmax = std::max(Nmax, N);
        Tmax = std::max(Tmax, v[NTOK - 1]);
        for (int j = 0; j < gK; j++) {
            const u64* q = v + gk + j * gm;
            u64 s = 0;
            for (int i = 0; i < gm; i++) s += q[i];
            emax[j] = std::max(emax[j], s - N);
            for (int i = 0; i + 1 < gm; i++) qmx[j][i] = std::max(qmx[j][i], q[i]);
        }
    }
    void merge(const Ranges& o) {
        nAdm += o.nAdm;
        Nmax = std::max(Nmax, o.Nmax);
        Tmax = std::max(Tmax, o.Tmax);
        for (int j = 0; j < MAXK; j++) {
            emax[j] = std::max(emax[j], o.emax[j]);
            for (int i = 0; i < MAXM; i++) qmx[j][i] = std::max(qmx[j][i], o.qmx[j][i]);
        }
    }
};

struct P1Out {
    u64 nc = 0, badIdx = NONE, badLine = NONE;
    std::string badWhy;
    bool hasFirst = false, firstRoot = false;
    u64 firstLine = NONE, firstT = 0;
    std::vector<u64> firstVals;
    u64 c4 = NONE, c5 = NONE;
    std::string c4why, c5why;
    std::vector<u64> c4vals, c5vals;
    Ranges rg;
    std::vector<u16> pendH;
    std::vector<u64> badl;
    void reset() {
        nc = 0; badIdx = badLine = NONE; badWhy.clear();
        hasFirst = firstRoot = false; firstLine = NONE; firstT = 0;
        c4 = c5 = NONE;
        rg = Ranges();
        pendH.clear(); badl.clear();
    }
};

struct TCache {
    std::vector<u16> h;
    std::vector<uint8_t> f;
    void init() { h.assign(((size_t)1 << 12) * HL, 0); f.assign((size_t)1 << 12, 0); }
};

static void pass1_piece(const Span& sp, u64 line, P1Out& o, TCache& tc) {
    o.reset();
    u64 v[MAXTOK];
    u16 hv[MAXk];
    std::string why;
    const char* a = sp.first;
    while (a < sp.second) {
        const char* lf = (const char*)memchr(a, '\n', (size_t)(sp.second - a));
        int st = parse_state_line(a, lf, v, &why);
        if (st != 0) {
            u64 idx = o.nc++;
            if (st == 2) { o.badIdx = idx; o.badLine = line; o.badWhy = why; break; }
            u64 T = v[NTOK - 1];
            if (idx == 0) {
                o.hasFirst = true; o.firstLine = line; o.firstT = T; o.firstRoot = is_root(v);
                o.firstVals.assign(v, v + NTOK);
            }
            u128 pay = payoff(v);
            if (pay > (u128)T && o.c5 == NONE) {
                o.c5 = line;
                o.c5why = "pay(sigma) = " + dec(pay) + " > T";
                o.c5vals.assign(v, v + NTOK);
            }
            const char* r4 = domain_reason(v);
            bool adm = false;
            if (!r4) {
                for (int C = 1; C <= HL; C++) hv[C - 1] = (u16)v[C];
                bool inDict = DH.find(hv) >= 0;
                bool sp_ = true;
                size_t ci = 0;
                if (!inDict) {
                    ci = hashH(hv, HL) & 4095;
                    if (tc.f[ci] && !memcmp(&tc.h[ci * HL], hv, sizeof(u16) * HL)) {
                        sp_ = tc.f[ci] >= 2;
                    } else {
                        sp_ = split_test(hv);
                        memcpy(&tc.h[ci * HL], hv, sizeof(u16) * HL);
                        tc.f[ci] = sp_ ? 2 : 1;
                    }
                }
                r4 = rest_reason(v, sp_);
                if (!r4) {
                    adm = true;
                    o.rg.add(v);
                    if (!inDict && tc.f[ci] == 2) {
                        o.pendH.insert(o.pendH.end(), hv, hv + HL);
                        tc.f[ci] = 3;
                    }
                }
            }
            if (!adm) {
                if (o.c4 == NONE) { o.c4 = line; o.c4why = r4; o.c4vals.assign(v, v + NTOK); }
                o.badl.push_back(line);
                o.badl.insert(o.badl.end(), v, v + NTOK - 1);
            }
        }
        a = lf + 1;
        line++;
    }
}

static u64 hdrline = 0, hdrhash = 0;
static std::vector<u64> bhash;
static size_t BS = (size_t)128 << 20, SUBS = (size_t)64 << 10;
static double LOAD = 0.75;
static int RBITS = -1;
static int FORCE = 0;
static Ranges RG;
static u64 c4line = NONE, c5line = NONE;
static std::string c4why, c5why;
static std::vector<u64> c4vals, c5vals;
static u64 badDupLine = NONE, badDupFirst = NONE;
static std::vector<u64> badDupVals;
static u64 badBytes = 0;

static const u64 MAXBAD = (u64)1 << 24;

static Reader* p1reader = nullptr;
static void p1_drain() {
    if (p1reader) p1reader->drain_close();
}

static void pass1(const Source& src) {
    double t0 = now_s();
    Reader rd;
    rd.open(src);
    p1reader = &rd;
    if (rd.pipe) g_before_c1 = p1_drain;
    const char *p, *q;
    u64 L = 1, h = 0x13198a2e03707344ULL;
    for (;;) {
        int st = rd.next_line(p, q);
        if (st == 0) fail("C1", L, "no header line");
        if (st < 0) fail("C1", L, "the last line does not end with LF");
        h = fmix(h ^ hash_bytes(p, q));
        if (is_comment(p, q)) { L++; continue; }
        parse_header(p, q, L);
        hdrline = L;
        hdrhash = h;
        L++;
        break;
    }
    DH.init(HL);
    int nt = nthreads();
    std::vector<TCache> caches(nt);
    for (auto& c : caches) c.init();
    std::vector<P1Out> outs;
    BlockSplit bs;
    u64 R = 0;
    bool firstRoot = false;
    u64 firstLine = NONE, firstT = 0;
    std::vector<u64> firstVals;
    std::unordered_map<std::string, u64> badMap;
    u64 nbad = 0;
    for (;;) {
        int st = rd.next_block(BS, p, q);
        if (st == 0) break;
        if (st < 0) fail("C1", L, "the last line does not end with LF");
        bs.make(p, q, SUBS, L);
        bhash.push_back(bs.hash);
        long ns = (long)bs.sub.size();
        if ((long)outs.size() < ns) outs.resize(ns);
#pragma omp parallel for schedule(dynamic, 4)
        for (long s = 0; s < ns; s++) {
            try {
                pass1_piece(bs.sub[s], bs.start[s], outs[s], caches[tid()]);
            } catch (const std::bad_alloc&) {
                g_oom = 1;
            }
        }
        if (g_oom) fail("LIMIT", L, "refused: out of memory");
        for (long s = 0; s < ns; s++) {
            P1Out& o = outs[s];
            if (o.badIdx != NONE && R + o.badIdx < gn) fail("C1", o.badLine, o.badWhy);
            if (R + o.nc > gn) {
                u64 ln = nth_noncomment_line(bs.sub[s].first, bs.sub[s].second, bs.start[s], gn - R);
                fail("C1", ln, "more than n = " + dec(gn) + " state lines");
            }
            if (R == 0 && o.nc > 0) {
                firstLine = o.firstLine; firstT = o.firstT; firstRoot = o.firstRoot;
                firstVals = o.firstVals;
            }
            R += o.nc;
            if (o.c4 != NONE && c4line == NONE) { c4line = o.c4; c4why = o.c4why; c4vals = o.c4vals; }
            if (o.c5 != NONE && c5line == NONE) { c5line = o.c5; c5why = o.c5why; c5vals = o.c5vals; }
            RG.merge(o.rg);
            for (size_t i = 0; i < o.pendH.size(); i += (size_t)HL) DH.insert(&o.pendH[i]);
            size_t SS = (size_t)NTOK;
            for (size_t i = 0; i < o.badl.size() && badDupLine == NONE; i += SS) {
                if (++nbad > MAXBAD)
                    fail("LIMIT", o.badl[i], "refused: more than 2^24 inadmissible lines to compare for (C3)");
                std::string key((const char*)&o.badl[i + 1], sizeof(u64) * (SS - 1));
                auto it = badMap.find(key);
                if (it != badMap.end()) {
                    badDupLine = o.badl[i];
                    badDupFirst = it->second;
                    badDupVals.assign(&o.badl[i + 1], &o.badl[i + 1] + (SS - 1));
                } else {
                    badBytes += key.size() + 64;
                    badMap.emplace(std::move(key), o.badl[i]);
                }
            }
        }
        L += bs.lines;
    }
    rd.close(false);
    if (R < gn) fail("C1", L, "fewer than n = " + dec(gn) + " state lines");
    g_before_c1 = nullptr;
    p1reader = nullptr;
    info("INFO pass1 %.2fs: m %d k %d r %llu K %d, %llu state lines, %llu admissible, %zu distinct H\n",
         now_s() - t0, gm, gk, (unsigned long long)gr, gK, (unsigned long long)gn,
         (unsigned long long)RG.nAdm, DH.sz);
    if (!firstRoot)
        fail("C2", firstLine, "the first state line is not the empty state: " + state_text(firstVals.data()));
    if (firstT > gT0)
        fail("C2", firstLine, "T(sigma_0) = " + dec(firstT) + " > T0 = " + dec(gT0) + ": " +
                                  state_text(firstVals.data()));
}

struct Layout {
    u64 RN = 1, RH = 1, Nmax = 0;
    u64 emax[MAXK] = {0, 0, 0};
    u64 qmx[MAXK][MAXM] = {};
    u64 Rq[MAXK][MAXM] = {};
    u128 QR[MAXK] = {1, 1, 1};
    u128 RC[MAXK] = {1, 1, 1};
    u128 R = 1;
    int KB = 0, TB = 0;
};
static Layout LY;

static void make_layout() {
    const u128 LIM = (u128)1 << 126;
    auto mul = [&](u128 a, u128 b) -> u128 {
        if (b && a > LIM / b) fail("LIMIT", 0, "refused: the key of a state exceeds 126 bits");
        return a * b;
    };
    LY.Nmax = RG.Nmax;
    LY.RN = RG.Nmax + 1;
    LY.RH = DH.sz;
    u128 R = mul(LY.RN, LY.RH);
    for (int j = 0; j < gK; j++) {
        LY.emax[j] = RG.emax[j];
        u128 qr = 1;
        for (int i = 0; i + 1 < gm; i++) {
            LY.qmx[j][i] = RG.qmx[j][i];
            LY.Rq[j][i] = RG.qmx[j][i] + 1;
            qr = mul(qr, LY.Rq[j][i]);
        }
        LY.QR[j] = qr;
        LY.RC[j] = mul(qr, (u128)RG.emax[j] + 1);
        R = mul(R, LY.RC[j]);
    }
    LY.R = R;
    LY.KB = bits_of(R);
    LY.TB = std::max(1, bits_of(RG.Tmax));
    if (LY.KB + LY.TB > 128) fail("LIMIT", 0, "refused: key plus potential exceed 128 bits");
}

template <class C> static inline C enc_copy(int j, u64 e, const u64* q) {
    C x = (C)e;
    for (int i = 0; i + 1 < gm; i++) x = x * (C)LY.Rq[j][i] + (C)q[i];
    return x;
}

template <class C> static void dec_code(C x, u64& N, u64& h, u64* e, u64 (*q)[MAXM]) {
    for (int j = gK - 1; j >= 0; j--) {
        C rc = (C)LY.RC[j];
        C sc = x % rc;
        x /= rc;
        for (int i = gm - 2; i >= 0; i--) {
            C r = (C)LY.Rq[j][i];
            q[j][i] = (u64)(sc % r);
            sc /= r;
        }
        e[j] = (u64)sc;
    }
    h = (u64)(x % (C)LY.RH);
    N = (u64)(x / (C)LY.RH);
    for (int j = 0; j < gK; j++) {
        u64 s = 0;
        for (int i = 0; i + 1 < gm; i++) s += q[j][i];
        q[j][gm - 1] = N + e[j] - s;
    }
}

template <class U>
struct Table {
    U* s = nullptr;
    u64 nslots = 0, capr = 0, nreg = 1;
    int rbits = 0, gbits = 0, TB = 0;
    U tmask = 0;
    std::vector<u64> cnt;

    void init(u64 n, double load, int forceR, int TB_) {
        TB = TB_;
        tmask = ((U)1 << TB) - 1;
        int rb = 0;
        if (forceR >= 0) rb = std::min(forceR, 16);
        else while (rb < 16 && (n >> (rb + 1)) >= 8192) rb++;
        rbits = rb;
        nreg = 1ULL << rb;
        gbits = std::min(rbits, 8);
        double per = (double)n / (double)nreg;
        capr = (u64)std::ceil((per + 6.0 * std::sqrt(per) + 64.0) / load);
        nslots = capr * nreg;
        s = (U*)malloc(sizeof(U) * nslots);
        if (!s) fail("LIMIT", 0, "refused: out of memory for " + dec(nslots) + " table slots");
        long ns = (long)nslots;
        U* ss = s;
#pragma omp parallel for schedule(static)
        for (long i = 0; i < ns; i++) ss[i] = 0;
        cnt.assign(nreg, 0);
    }
    inline u64 region(u64 h) const { return rbits ? (h >> (64 - rbits)) : 0; }
    inline u64 group(u64 h) const { return gbits ? (h >> (64 - gbits)) : 0; }
    inline u64 start(u64 h) const { return (u64)(((u128)(h << rbits) * (u128)capr) >> 64); }
    int insert(U slot, u64 h) {
        u64 r = region(h);
        U* b = s + r * capr;
        u64 p = start(h);
        U key = slot >> TB;
        for (u64 k = 0; k < capr; k++) {
            U cur = b[p];
            if (cur == 0) {
                if (cnt[r] + 2 > capr) return 2;
                b[p] = slot;
                cnt[r]++;
                return 0;
            }
            if ((cur >> TB) == key) return 1;
            if (++p == capr) p = 0;
        }
        return 2;
    }
    inline u64 find(U key, u64 h) const {
        const U* b = s + region(h) * capr;
        u64 p = start(h);
        for (;;) {
            U cur = b[p];
            if (cur == 0) return NONE;
            if ((cur >> TB) == key) return (u64)(cur & tmask);
            if (++p == capr) p = 0;
        }
    }
};

struct St {
    u64 N = 0, T = 0, h = 0;
    u32 q[MAXK][MAXM];
};

struct Combo {
    u16 S[MAXK];
    uint8_t c[MAXK];
};

struct MoveRec {
    u64 c = 0;
    int nu = 0;
    int o[MAXK][MAXM];
};

template <class U, class C>
struct Worker {
    const Table<U>* tab = nullptr;
    St s;
    int n[MAXK], e[MAXK], base[MAXK], G[MAXK];
    int glast[MAXK][MAXM];
    bool gemp[MAXK][MAXM];
    int ncls[MAXK];
    u16 cS[MAXK][64];
    uint8_t cB[MAXK][64], cX[MAXK][64];
    u32 cM[MAXK][64];
    int cT[MAXK][64];
    std::vector<Combo> comb[3];
    u64 cnt[2] = {0, 0}, idleCnt = 0;
    C qp[MAXK][MAXOPT];
    u16 qv[MAXK];
    C sc[MAXK][MAXOPT];
    u16 V[MAXK];
    C rc[MAXK];
    u16 good[MAXOPT][MAXOPT], known[MAXOPT][MAXOPT];
    u128 A = 0, I = 0;
    MoveRec fail_mv;
    u64 fail_hp = 0;

    void init(const Table<U>* t) {
        tab = t;
        for (int j = 0; j < MAXK; j++) rc[j] = (C)LY.RC[j];
        for (int j = gK; j < MAXK; j++) {
            ncls[j] = 1; cS[j][0] = 1; cB[j][0] = 0; cX[j][0] = 0; cM[j][0] = 1; cT[j][0] = 0;
            V[j] = 1; sc[j][0] = 0; rc[j] = 1;
        }
    }

    inline u64 lookup(C code) const { return tab->find((U)code + 1, hcode(code)); }

    void setup_copy(int j) {
        const u32* q = s.q[j];
        int nn = 0;
        u64 sum = 0;
        for (int i = 0; i < gm; i++) { if (q[i]) nn++; sum += q[i]; }
        n[j] = nn;
        e[j] = (int)(sum - s.N);
        int b0 = gm - nn;
        base[j] = b0;
        int g = 0, gs[MAXM], gl[MAXM];
        if (b0 > 0) { glast[j][g] = b0 - 1; gemp[j][g] = true; gs[g] = 0; gl[g] = 0; g++; }
        for (int i = b0; i < gm;) {
            int i2 = i;
            while (i2 + 1 < gm && q[i2 + 1] == q[i]) i2++;
            glast[j][g] = i2; gemp[j][g] = false; gs[g] = i - b0; gl[g] = i2 - i + 1; g++;
            i = i2 + 1;
        }
        G[j] = g;
        ncls[j] = 0;
        for (int x = 0; x < (1 << nn); x++) {
            u16 S = 0;
            for (int t = 0; t < g; t++) {
                if (gemp[j][t]) { S |= (u16)(1u << (2 * t + 1)); continue; }
                unsigned Rm = ((1u << gl[t]) - 1) << gs[t];
                unsigned y = (unsigned)x & Rm;
                if (y) S |= (u16)(1u << (2 * t + 1));
                if (y != Rm) S |= (u16)(1u << (2 * t));
            }
            int b = nn - popc((u64)x);
            int f = -1;
            for (int c = 0; c < ncls[j]; c++)
                if (cS[j][c] == S && cB[j][c] == b) { f = c; break; }
            if (f < 0) {
                f = ncls[j]++;
                cS[j][f] = S; cB[j][f] = (uint8_t)b; cX[j][f] = (uint8_t)x; cM[j][f] = 0;
                cT[j][f] = nn ? CP.id[nn][e[j]][b] : 0;
            }
            cM[j][f]++;
        }
    }

    void setup_combos() {
        for (auto& v : comb) v.clear();
        cnt[0] = cnt[1] = idleCnt = 0;
        for (int c0 = 0; c0 < ncls[0]; c0++)
            for (int c1 = 0; c1 < ncls[1]; c1++)
                for (int c2 = 0; c2 < ncls[2]; c2++) {
                    Combo cb;
                    cb.S[0] = cS[0][c0]; cb.S[1] = cS[1][c1]; cb.S[2] = cS[2][c2];
                    cb.c[0] = (uint8_t)c0; cb.c[1] = (uint8_t)c1; cb.c[2] = (uint8_t)c2;
                    u64 mult = (u64)cM[0][c0] * (u64)cM[1][c1] * (u64)cM[2][c2];
                    if (s.N == 0) { comb[1].push_back(cb); cnt[1] += mult; continue; }
                    int t[MAXK];
                    bool idl = true;
                    for (int j = 0; j < gK; j++) {
                        int cj = cb.c[j];
                        t[j] = cT[j][cj];
                        if (cB[j][cj] < 1) idl = false;
                    }
                    if (CP.get(0, gK, t)) {
                        cnt[0] += mult;
                        comb[0].push_back(cb);
                        if (idl) idleCnt += mult;
                        else comb[2].push_back(cb);
                    }
                    if (CP.get(1, gK, t)) { cnt[1] += mult; comb[1].push_back(cb); }
                }
    }

    void make_qp(u64 c) {
        for (int j = 0; j < gK; j++) {
            qv[j] = 0;
            for (int g = 0; g < G[j]; g++)
                for (int beta = 0; beta < 2; beta++) {
                    if (gemp[j][g] && beta == 0) continue;
                    u64 t[MAXM];
                    for (int i = 0; i < gm; i++) t[i] = s.q[j][i];
                    int p = glast[j][g];
                    t[p] += c + (u64)beta;
                    while (p + 1 < gm && t[p] > t[p + 1]) { std::swap(t[p], t[p + 1]); p++; }
                    bool ok = true;
                    C x = 0;
                    for (int i = 0; i + 1 < gm; i++) {
                        if (t[i] > LY.qmx[j][i]) { ok = false; break; }
                        x = x * (C)LY.Rq[j][i] + (C)t[i];
                    }
                    if (!ok) continue;
                    int o = 2 * g + beta;
                    qp[j][o] = x;
                    qv[j] |= (u16)(1u << o);
                }
        }
    }

    void make_sc(int nu) {
        for (int j = 0; j < gK; j++) {
            V[j] = 0;
            for (u64 y = qv[j]; y; y &= y - 1) {
                int o = ctz(y);
                i64 ep = (i64)e[j] + (o & 1) - nu;
                if (ep < 0 || (u64)ep > LY.emax[j]) continue;
                sc[j][o] = (C)(u64)ep * (C)LY.QR[j] + qp[j][o];
                V[j] |= (u16)(1u << o);
            }
        }
    }

    bool answered(const Combo& cb, C basec) {
        u16 S0 = cb.S[0] & V[0], S1 = cb.S[1] & V[1], S2 = cb.S[2] & V[2];
        if (!S0 || !S1 || !S2) return false;
        for (u64 x0 = S0; x0; x0 &= x0 - 1)
            for (u64 x1 = S1; x1; x1 &= x1 - 1)
                if (good[ctz(x0)][ctz(x1)] & S2) return true;
        for (u64 x0 = S0; x0; x0 &= x0 - 1) {
            int u0 = ctz(x0);
            C b0 = (basec + sc[0][u0]) * rc[1];
            for (u64 x1 = S1; x1; x1 &= x1 - 1) {
                int u1 = ctz(x1);
                C b1 = (b0 + sc[1][u1]) * rc[2];
                u16 unk = S2 & (u16)~known[u0][u1];
                for (u64 x2 = unk; x2; x2 &= x2 - 1) {
                    int u2 = ctz(x2);
                    known[u0][u1] |= (u16)(1u << u2);
                    u64 t = lookup(b1 + sc[2][u2]);
                    if (t != NONE && t <= s.T) {
                        good[u0][u1] |= (u16)(1u << u2);
                        return true;
                    }
                }
            }
        }
        return false;
    }

    void set_fail(u64 c, int nu, const Combo& cb, u64 hp) {
        fail_mv.c = c;
        fail_mv.nu = nu;
        fail_hp = hp;
        for (int j = 0; j < gK; j++) {
            int x = cX[j][cb.c[j]];
            for (int i = 0; i < gm; i++) fail_mv.o[j][i] = i < base[j] ? 1 : ((x >> (i - base[j])) & 1);
        }
    }

    bool check(const St& st) {
        s = st;
        for (int j = 0; j < gK; j++) setup_copy(j);
        setup_combos();
        for (u64 c = 0; c < gF; c++) {
            u64 Cc = c / gr;
            i64 hp = (i64)s.h;
            if (Cc >= 1) {
                hp = addC[s.h * (u64)HL + Cc - 1];
                if (hp == -2) continue;
            }
            bool qdone = false;
            for (int nu = 0; nu < 2; nu++) {
                if (s.N == 0 && nu == 0) continue;
                if (s.N + c + (u64)nu > gmF) continue;
                bool z = (c == 0 && nu == 0);
                A += cnt[nu];
                if (z) I += idleCnt;
                const std::vector<Combo>& need = nu ? comb[1] : (z ? comb[2] : comb[0]);
                if (need.empty()) continue;
                u64 Np = s.N + c + (u64)nu;
                if (hp < 0 || Np > LY.Nmax) { set_fail(c, nu, need[0], (u64)hp); return false; }
                if (!qdone) { make_qp(c); qdone = true; }
                make_sc(nu);
                C basec = ((C)Np * (C)LY.RH + (C)(u64)hp) * rc[0];
                memset(good, 0, sizeof(good));
                memset(known, 0, sizeof(known));
                for (const Combo& cb : need)
                    if (!answered(cb, basec)) { set_fail(c, nu, cb, (u64)hp); return false; }
            }
        }
        return true;
    }

    void describe(u64& reach, u64& minT) {
        reach = 0;
        minT = NONE;
        const MoveRec& mv = fail_mv;
        i64 hp = (i64)s.h;
        u64 Cc = mv.c / gr;
        if (Cc >= 1) hp = addC[s.h * (u64)HL + Cc - 1];
        u64 Np = s.N + mv.c + (u64)mv.nu;
        if (hp < 0 || Np > LY.Nmax) return;
        u64 total = 1;
        for (int j = 0; j < gK; j++) total *= (u64)gm;
        for (u64 x = 0; x < total; x++) {
            u64 y = x;
            C code = (C)Np * (C)LY.RH + (C)(u64)hp;
            bool ok = true;
            for (int j = 0; j < gK && ok; j++) {
                int i = (int)(y % (u64)gm);
                y /= (u64)gm;
                u64 t[MAXM], sum = 0;
                for (int a = 0; a < gm; a++) t[a] = s.q[j][a];
                t[i] += mv.c + (u64)mv.o[j][i];
                std::sort(t, t + gm);
                for (int a = 0; a < gm; a++) sum += t[a];
                if (sum < Np || sum - Np > LY.emax[j]) { ok = false; break; }
                for (int a = 0; a + 1 < gm; a++)
                    if (t[a] > LY.qmx[j][a]) ok = false;
                if (!ok) break;
                code = code * (C)LY.RC[j] + enc_copy<C>(j, sum - Np, t);
            }
            if (!ok) continue;
            u64 T = lookup(code);
            if (T != NONE) {
                reach++;
                minT = std::min(minT, T);
            }
        }
    }
};

static std::string move_text(const MoveRec& mv) {
    std::string s = "move c=" + dec(mv.c) + " nu=" + dec(mv.nu) + " bits ";
    for (int j = 0; j < gK; j++) {
        if (j) s += "/";
        for (int i = 0; i < gm; i++) s += char('0' + mv.o[j][i]);
    }
    return s + " (by rank, rank 1 first)";
}

static u64 skip_header(Reader& rd) {
    const char *p, *q;
    u64 L = 1, h = 0x13198a2e03707344ULL;
    for (;;) {
        if (rd.next_line(p, q) != 1) fail("IO", L, "the input changed between passes");
        h = fmix(h ^ hash_bytes(p, q));
        if (L == hdrline) break;
        L++;
    }
    if (h != hdrhash) fail("IO", L, "the input changed between passes");
    return L + 1;
}

template <class C> static C line_code(const u64* v, u64 hidx) {
    C x = (C)v[0] * (C)LY.RH + (C)hidx;
    for (int j = 0; j < gK; j++) {
        const u64* q = v + gk + j * gm;
        u64 s = 0;
        for (int i = 0; i < gm; i++) s += q[i];
        x = x * (C)LY.RC[j] + enc_copy<C>(j, s - v[0], q);
    }
    return x;
}

static i64 adm_index(const u64* v) {
    if (domain_reason(v)) return -1;
    u16 hv[MAXk];
    for (int C = 1; C <= HL; C++) hv[C - 1] = (u16)v[C];
    i64 hi = DH.find(hv);
    if (hi < 0 || rest_reason(v, true)) return -1;
    return hi;
}

template <class U>
struct Rec {
    U slot;
    u64 h, line;
};

static u64 find_equal_line(const Source& src, const u64* v, u64 upto) {
    Reader rd;
    rd.open(src);
    const char *p, *q;
    u64 L = 1;
    u64 w[MAXTOK];
    while (L < upto) {
        if (rd.next_line(p, q) != 1) break;
        if (L > hdrline && parse_state_line(p, q, w, nullptr) == 1 && std::equal(w, w + NTOK - 1, v)) {
            rd.close(true);
            return L;
        }
        L++;
    }
    rd.close(true);
    return NONE;
}

static std::string bytes_txt(double b) {
    char s[64];
    if (b >= 1e9) snprintf(s, sizeof s, "%.2f GB", b / 1e9);
    else if (b >= 1e6) snprintf(s, sizeof s, "%.2f MB", b / 1e6);
    else snprintf(s, sizeof s, "%.0f B", b);
    return s;
}

template <class U, class C>
static int run_rest(const Source& src, bool c6file) {
    double t0 = now_s();
    Table<U> tab;
    tab.init(RG.nAdm, LOAD, RBITS, LY.TB);
    double tabBytes = (double)tab.nslots * (double)sizeof(U);
    info("INFO key: %d bits (N radix %llu, %llu multisets H, copies %s) + potential %d bits, "
         "%zu-byte slots, code %zu bytes; %llu slots in %llu regions (%s)\n",
         LY.KB, (unsigned long long)LY.RN, (unsigned long long)LY.RH,
         [&]() { std::string s; for (int j = 0; j < gK; j++) s += (j ? "x" : "") + dec(LY.RC[j]); return s; }().c_str(),
         LY.TB, sizeof(U), sizeof(C), (unsigned long long)tab.nslots, (unsigned long long)tab.nreg,
         bytes_txt(tabBytes).c_str());

    Reader rd;
    rd.open(src);
    u64 L = skip_header(rd);
    BlockSplit bs;
    std::vector<std::vector<Rec<U>>> recs;
    std::vector<Rec<U>> sorted;
    u64 G = 1ULL << tab.gbits;
    u64 dupLine = NONE;
    U dupSlot = 0;
    size_t bi = 0;
    bool early = false;
    for (;;) {
        const char *p, *q;
        int st = rd.next_block(BS, p, q);
        if (st == 0) break;
        if (st < 0) fail("IO", L, "the input changed between passes");
        bs.make(p, q, SUBS, L);
        if (bi >= bhash.size() || bs.hash != bhash[bi]) fail("IO", L, "the input changed between passes");
        bi++;
        long ns = (long)bs.sub.size();
        if ((long)recs.size() < ns) recs.resize(ns);
        std::atomic<int> bad(0);
        std::atomic<u64> badEnc(NONE);
#pragma omp parallel for schedule(dynamic, 4)
        for (long s = 0; s < ns; s++) try {
            std::vector<Rec<U>>& rv = recs[s];
            rv.clear();
            u64 v[MAXTOK];
            const char* a = bs.sub[s].first;
            u64 line = bs.start[s];
            while (a < bs.sub[s].second) {
                const char* lf = (const char*)memchr(a, '\n', (size_t)(bs.sub[s].second - a));
                int ps = parse_state_line(a, lf, v, nullptr);
                if (ps == 2) { bad = 1; break; }
                if (ps == 1) {
                    i64 hi = adm_index(v);
                    if (hi >= 0) {
                        C code = line_code<C>(v, (u64)hi);
                        u64 N, h, ee[MAXK], qq[MAXK][MAXM];
                        dec_code<C>(code, N, h, ee, qq);
                        bool same = N == v[0] && h == (u64)hi && v[NTOK - 1] <= RG.Tmax;
                        for (int j = 0; j < gK && same; j++)
                            for (int i = 0; i < gm; i++)
                                if (qq[j][i] != v[gk + j * gm + i]) same = false;
                        if (!same || code >= (C)LY.R) {
                            u64 cur = badEnc.load();
                            while (line < cur && !badEnc.compare_exchange_weak(cur, line)) {}
                        }
                        U slot = (((U)code + 1) << LY.TB) | (U)v[NTOK - 1];
                        rv.push_back({slot, hcode(code), line});
                    }
                }
                a = lf + 1;
                line++;
            }
        } catch (const std::bad_alloc&) {
            g_oom = 1;
        }
        if (g_oom) fail("LIMIT", L, "refused: out of memory");
        if (bad) fail("IO", L, "the input changed between passes");
        if (badEnc.load() != NONE) fail("INTERNAL", badEnc.load(), "the key does not decode to the line");
        std::vector<u64> off((size_t)ns * G, 0), gbase(G + 1, 0);
#pragma omp parallel for schedule(static)
        for (long s = 0; s < ns; s++)
            for (const Rec<U>& r : recs[s]) off[(size_t)s * G + tab.group(r.h)]++;
        for (u64 g = 0; g < G; g++) {
            u64 acc = gbase[g];
            for (long s = 0; s < ns; s++) {
                u64 c = off[(size_t)s * G + g];
                off[(size_t)s * G + g] = acc;
                acc += c;
            }
            gbase[g + 1] = acc;
        }
        sorted.resize(gbase[G]);
#pragma omp parallel for schedule(static)
        for (long s = 0; s < ns; s++)
            for (const Rec<U>& r : recs[s]) sorted[off[(size_t)s * G + tab.group(r.h)]++] = r;
        std::vector<u64> gdup(G, NONE);
        std::vector<U> gslot(G, 0);
        std::atomic<int> full(0);
        long Gl = (long)G;
#pragma omp parallel for schedule(dynamic, 1)
        for (long g = 0; g < Gl; g++) {
            for (u64 i = gbase[g]; i < gbase[g + 1]; i++) {
                int r = tab.insert(sorted[i].slot, sorted[i].h);
                if (r == 1) { gdup[g] = sorted[i].line; gslot[g] = sorted[i].slot; break; }
                if (r == 2) { full = 1; break; }
            }
        }
        if (full) fail("LIMIT", L, "refused: a region of the hash table is full (use a lower --load)");
        for (u64 g = 0; g < G; g++)
            if (gdup[g] < dupLine) { dupLine = gdup[g]; dupSlot = gslot[g]; }
        L += bs.lines;
        if (dupLine != NONE) { early = true; break; }
    }
    if (!early && bi != bhash.size()) fail("IO", L, "the input changed between passes");
    if (!early) {
        u64 tot = 0;
        for (u64 r = 0; r < tab.nreg; r++) tot += tab.cnt[r];
        if (tot != RG.nAdm) fail("INTERNAL", 0, "pass 2 stored " + dec(tot) + " states, pass 1 counted " + dec(RG.nAdm));
    }
    rd.close(early);
    recs.clear();
    recs.shrink_to_fit();
    sorted.clear();
    sorted.shrink_to_fit();
    info("INFO pass2 %.2fs\n", now_s() - t0);

    if (dupLine != NONE || badDupLine != NONE) {
        std::vector<u64> vals(NTOK, 0);
        u64 first = NONE, line;
        if (dupLine < badDupLine) {
            line = dupLine;
            C code = (C)((dupSlot >> LY.TB) - 1);
            u64 N, h, ee[MAXK], qq[MAXK][MAXM];
            dec_code<C>(code, N, h, ee, qq);
            vals[0] = N;
            for (int Cc = 1; Cc <= HL; Cc++) vals[Cc] = DH.key(h)[Cc - 1];
            for (int j = 0; j < gK; j++)
                for (int i = 0; i < gm; i++) vals[gk + j * gm + i] = qq[j][i];
            vals[NTOK - 1] = (u64)(dupSlot & tab.tmask);
            first = find_equal_line(src, vals.data(), dupLine);
        } else {
            line = badDupLine;
            first = badDupFirst;
            for (int i = 0; i + 1 < NTOK; i++) vals[i] = badDupVals[i];
        }
        std::string t = state_text(vals.data());
        t = t.substr(0, t.rfind(" T="));
        fail("C3", line, t + ", same state as line " + (first != NONE ? dec(first) : std::string("?")));
    }
    if (c4line != NONE) fail("C4", c4line, c4why + ": " + state_text(c4vals.data()));
    if (c5line != NONE) fail("C5", c5line, c5why + ": " + state_text(c5vals.data()));

    double t1 = now_s();
    CP.build(gm, gK);
    size_t nh = DH.sz;
    addC.assign(nh * (size_t)HL, -2);
    long nhl = (long)nh;
#pragma omp parallel for schedule(dynamic, 16)
    for (long hh = 0; hh < nhl; hh++) try {
        u16 x[MAXk];
        memcpy(x, DH.key((size_t)hh), sizeof(u16) * HL);
        for (int Cc = 1; Cc <= HL; Cc++) {
            x[Cc - 1]++;
            int32_t r = -2;
            if ((u64)x[Cc - 1] <= hmax[Cc]) {
                i64 f = DH.find(x);
                if (f >= 0) r = (int32_t)f;
                else if (split_test(x)) r = -1;
            }
            addC[(size_t)hh * HL + Cc - 1] = r;
            x[Cc - 1]--;
        }
    } catch (const std::bad_alloc&) {
        g_oom = 1;
    }
    if (g_oom) fail("LIMIT", 0, "refused: out of memory");
    double auxBytes = (double)(DH.bytes() + addC.capacity() * sizeof(int32_t) + CP.bytes());
    info("INFO C6 tables %.2fs (%d triples, COUPLED tables %zu bytes)\n", now_s() - t1, CP.NT, CP.bytes());

    double t2 = now_s();
    int nt = nthreads();
    std::vector<Worker<U, C>> wk(nt);
    for (auto& w : wk) w.init(&tab);
    bool failed = false;
    if (!c6file) {
        const u64 CH = 1 << 14;
        u64 nch = (tab.nslots + CH - 1) / CH;
        std::atomic<int> bad(0);
        long nchl = (long)nch;
#pragma omp parallel for schedule(dynamic, 1)
        for (long ch = 0; ch < nchl; ch++) try {
            if (bad.load(std::memory_order_relaxed)) continue;
            Worker<U, C>& w = wk[tid()];
            u64 a = (u64)ch * CH, b = std::min(tab.nslots, a + CH);
            St st;
            for (u64 i = a; i < b; i++) {
                U sl = tab.s[i];
                if (!sl) continue;
                C code = (C)((sl >> LY.TB) - 1);
                u64 ee[MAXK], qq[MAXK][MAXM];
                dec_code<C>(code, st.N, st.h, ee, qq);
                st.T = (u64)(sl & tab.tmask);
                for (int j = 0; j < gK; j++)
                    for (int x = 0; x < gm; x++) st.q[j][x] = (u32)qq[j][x];
                if (!w.check(st)) { bad = 1; break; }
            }
        } catch (const std::bad_alloc&) {
            g_oom = 1;
        }
        if (g_oom) fail("LIMIT", 0, "refused: out of memory");
        failed = bad.load() != 0;
        info("INFO C6 over the table %.2fs%s\n", now_s() - t2, failed ? ": a move has no answer" : "");
    }
    if (c6file || failed) {
        double t3 = now_s();
        for (auto& w : wk) { w.A = 0; w.I = 0; }
        struct FailRec { u64 line = NONE; MoveRec mv; std::vector<u64> vals; u64 reach = 0, minT = NONE; };
        std::vector<FailRec> fr(nt);
        rd.open(src);
        L = skip_header(rd);
        bi = 0;
        u64 failLine = NONE;
        for (;;) {
            const char *p, *q;
            int st = rd.next_block(BS, p, q);
            if (st == 0) break;
            if (st < 0) fail("IO", L, "the input changed between passes");
            bs.make(p, q, SUBS, L);
            if (bi >= bhash.size() || bs.hash != bhash[bi]) fail("IO", L, "the input changed between passes");
            bi++;
            long ns = (long)bs.sub.size();
            std::atomic<u64> best(NONE);
            std::atomic<int> bad(0);
#pragma omp parallel for schedule(dynamic, 1)
            for (long s = 0; s < ns; s++) try {
                if (bs.start[s] >= best.load()) continue;
                Worker<U, C>& w = wk[tid()];
                FailRec& f = fr[tid()];
                u64 v[MAXTOK];
                const char* a = bs.sub[s].first;
                u64 line = bs.start[s];
                while (a < bs.sub[s].second && line < best.load()) {
                    const char* lf = (const char*)memchr(a, '\n', (size_t)(bs.sub[s].second - a));
                    int ps = parse_state_line(a, lf, v, nullptr);
                    if (ps == 2) { bad = 1; break; }
                    if (ps == 1) {
                        i64 hi = adm_index(v);
                        if (hi < 0) { bad = 1; break; }
                        St stt;
                        stt.N = v[0];
                        stt.T = v[NTOK - 1];
                        stt.h = (u64)hi;
                        for (int j = 0; j < gK; j++)
                            for (int i = 0; i < gm; i++) stt.q[j][i] = (u32)v[gk + j * gm + i];
                        if (!w.check(stt)) {
                            if (line < f.line) {
                                f.line = line;
                                f.mv = w.fail_mv;
                                f.vals.assign(v, v + NTOK);
                                w.describe(f.reach, f.minT);
                            }
                            u64 cur = best.load();
                            while (line < cur && !best.compare_exchange_weak(cur, line)) {}
                            break;
                        }
                    }
                    a = lf + 1;
                    line++;
                }
            } catch (const std::bad_alloc&) {
                g_oom = 1;
            }
            if (g_oom) fail("LIMIT", L, "refused: out of memory");
            if (bad) fail("IO", L, "the input changed between passes");
            if (best.load() != NONE) { failLine = best.load(); break; }
            L += bs.lines;
        }
        rd.close(failLine != NONE);
        info("INFO C6 in file order %.2fs\n", now_s() - t3);
        if (failLine != NONE) {
            for (auto& f : fr)
                if (f.line == failLine) {
                    std::string t = state_text(f.vals.data()) + "; " + move_text(f.mv) + " has no answer; " +
                                    dec(f.reach) + " responses reach a listed state" +
                                    (f.reach ? ", least potential " + dec(f.minT) : std::string(""));
                    fail("C6", failLine, t);
                }
            fail("INTERNAL", failLine, "lost the record of a (C6) failure");
        }
        if (failed) fail("INTERNAL", 0, "(C6) failed over the table but not in file order");
        if (bi != bhash.size()) fail("IO", L, "the input changed between passes");
    }
    u128 A = 0, I = 0;
    for (auto& w : wk) { A += w.A; I += w.I; }
    if (I > A) fail("INTERNAL", 0, "move counts disagree");
    u128 M = A - I;
    info("INFO all-moves %s idle %s\n", dec(A).c_str(), dec(I).c_str());
    info("INFO bytes-per-state %.3f (table %.3f in %zu-byte slots at fill %.3f; H dictionary, "
         "H+C and COUPLED tables %.4f)\n",
         (tabBytes + auxBytes) / (double)gn, tabBytes / (double)gn, sizeof(U),
         (double)RG.nAdm / (double)tab.nslots, auxBytes / (double)gn);
    u128 W = 0;
    std::string ws;
    for (int j = 0; j < gK; j++) { W += gw[j]; ws += (j ? "," : "") + dec(gw[j]); }
    printf("PASS m %d k %d r %s weights %s T0 %s states %s moves %s bound %s/%s\n", gm, gk, dec(gr).c_str(),
           ws.c_str(), dec(gT0).c_str(), dec(gn).c_str(), dec(M).c_str(), dec(gT0).c_str(),
           dec(W * (u128)gF).c_str());
    fflush(stdout);
    return 0;
}

static int run(const Source& src, bool c6file);

static void usage() {
    fprintf(stderr,
            "usage: cma [--threads N] [--load X] [--block-mb B] [--sub-kb S] [--c6-file] [-q] FILE\n"
            "       cma [options] --cmd 'COMMAND'   (COMMAND writes the certificate; run once per pass)\n"
            "       cma --selftest\n"
            "limits: 2<=m<=6, 1<=K<=3, k<=64, r<=65536, F=k*r<=65536; numbers < 10^18; key plus\n"
            "        potential <= 128 bits; < 2^31 distinct H; <= 2^24 inadmissible lines; states as\n"
            "        many as memory holds. Standard input '-' is refused (two passes): use --cmd.\n");
}

int main(int argc, char** argv) {
    Source src;
    bool self = false, c6file = false;
    int threads = 0;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        auto need = [&](void) -> std::string {
            if (i + 1 >= argc) { usage(); fail("USAGE", 0, "missing value after " + a); }
            return argv[++i];
        };
        if (a == "--selftest") self = true;
        else if (a == "--threads") threads = atoi(need().c_str());
        else if (a == "--load") LOAD = atof(need().c_str());
        else if (a == "--block-mb") BS = (size_t)std::max(1L, atol(need().c_str())) << 20;
        else if (a == "--block-bytes") BS = (size_t)std::max(16L, atol(need().c_str()));
        else if (a == "--sub-kb") SUBS = (size_t)std::max(1L, atol(need().c_str())) << 10;
        else if (a == "--sub-bytes") SUBS = (size_t)std::max(8L, atol(need().c_str()));
        else if (a == "--rbits") RBITS = atoi(need().c_str());
        else if (a == "--force-types") FORCE = atoi(need().c_str());
        else if (a == "--cmd") src.cmd = need();
        else if (a == "--c6-file") c6file = true;
        else if (a == "-q") quiet = true;
        else if (a == "-") { usage(); fail("USAGE", 0, "standard input is not supported (two passes); use --cmd"); }
        else if (!a.empty() && a[0] == '-') { usage(); fail("USAGE", 0, "unknown option " + a); }
        else if (src.path.empty()) src.path = a;
        else { usage(); fail("USAGE", 0, "more than one input"); }
    }
#ifdef _OPENMP
    if (threads > 0) omp_set_num_threads(threads);
#else
    (void)threads;
#endif
    if (self) return selftest();
    if (src.path.empty() == src.cmd.empty()) { usage(); fail("USAGE", 0, "give one FILE or one --cmd"); }
    if (!(LOAD >= 0.3 && LOAD <= 0.95)) { usage(); fail("USAGE", 0, "--load must lie in [0.3, 0.95]"); }
    try {
        return run(src, c6file);
    } catch (const std::bad_alloc&) {
        fail("LIMIT", 0, "refused: out of memory");
    }
}

static int run(const Source& src, bool c6file) {
    double t0 = now_s();
    info("INFO cma: %d threads\n", nthreads());
    pass1(src);
    make_layout();
    int choice = LY.KB + LY.TB <= 64 ? 0 : (LY.R <= ((u128)1 << 64) ? 1 : 2);
    choice = std::max(choice, std::min(std::max(FORCE, 0), 2));
    int rc;
    if (choice == 0) rc = run_rest<u64, u64>(src, c6file);
    else if (choice == 1) rc = run_rest<u128, u64>(src, c6file);
    else rc = run_rest<u128, u128>(src, c6file);
    info("INFO total %.2fs\n", now_s() - t0);
    return rc;
}
