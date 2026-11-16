// icheck.cpp: checker for certificates of the rounded lottery game (paper, App. E.1).
// Written only from the paper text: Lemma E.1, the definition of a move and a response,
// Definition E.2 and the paragraph after Theorem E.3. Integer arithmetic only.
//
// usage: icheck <certificate file>
// Exit status 0 and a line "RESULT PASS ..." iff (a), (b), (c) of Definition E.2 hold.
//
// State encoding: an abstract state (H, N, (u_j, v_j)_j) is stored as one 64-bit mixed-radix code
//   code = ((Hid * (2F+1) + N) * R + d_1) * R + ... + d_K,   d_j = 2*u_j + e_j,  R = 2*(F+1),
// where Hid indexes the multisets of coarse classes that split as in Lemma E.1(i), and
// e_j = u_j + v_j - N in {0,1}; v_j = N + e_j - u_j is recovered exactly. u_j <= F holds because
// u_j <= v_j and u_j + v_j <= 2F + 1. The set S is an open-addressing hash table (linear probing)
// of 16-byte slots {code+1, T}.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <map>
#include <atomic>
#include <algorithm>
#include <chrono>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/resource.h>
#include <omp.h>

typedef uint64_t u64;
typedef int64_t i64;
typedef unsigned __int128 u128;

static int k, r, F, K, X2;
static std::vector<i64> w;
static i64 W;
static i64 rootClaim = -1;

// ---------- multisets H of coarse classes 1..k-1 that split as in Lemma E.1(i) ----------
static std::vector<std::vector<int>> Hcnt;   // Hcnt[id][C] = multiplicity of class C (index 0 unused)
static std::vector<int> addT;                // addT[id*k + C] = id of H + {C}, or -1 if it does not split

static bool splits(const std::vector<int>& cnt) {
    // exists a sub-multiset with sum s such that s <= k-1 and S - s <= k-1
    int S = 0;
    for (int C = 1; C < k; C++) S += C * cnt[C];
    if (S > 2 * (k - 1)) return false;
    std::vector<char> can(S + 1, 0);
    can[0] = 1;
    for (int C = 1; C < k; C++)
        for (int t = 0; t < cnt[C]; t++)
            for (int s = S; s >= C; s--)
                if (can[s - C]) can[s] = 1;
    for (int s = 0; s <= S; s++)
        if (can[s] && s <= k - 1 && S - s <= k - 1) return true;
    return false;
}

static void buildH() {
    std::map<std::vector<int>, int> id;
    std::vector<int> empty(k, 0);
    Hcnt.push_back(empty);
    id[empty] = 0;
    for (size_t i = 0; i < Hcnt.size(); i++) {
        for (int C = 1; C < k; C++) {
            std::vector<int> nc = Hcnt[i];
            nc[C]++;
            int nid = -1;
            auto it = id.find(nc);
            if (it != id.end()) nid = it->second;
            else if (splits(nc)) {
                nid = (int)Hcnt.size();
                id[nc] = nid;
                Hcnt.push_back(nc);
            }
            if (addT.size() < (i + 1) * (size_t)k) addT.resize((i + 1) * (size_t)k, -1);
            addT[i * k + C] = nid;
        }
    }
    addT.resize(Hcnt.size() * (size_t)k, -1);
}

// ---------- code layout ----------
static u64 RN, RC, MN, MH;
static std::vector<u64> MJ;

static inline u64 encode(int hid, int N, const int* u, const int* e) {
    u64 c = (u64)hid * RN + (u64)N;
    for (int j = 0; j < K; j++) c = c * RC + (u64)(2 * u[j] + e[j]);
    return c;
}
static inline void decode(u64 c, int& hid, int& N, int* u, int* e) {
    for (int j = K - 1; j >= 0; j--) {
        u64 d = c % RC;
        c /= RC;
        u[j] = (int)(d / 2);
        e[j] = (int)(d % 2);
    }
    N = (int)(c % RN);
    hid = (int)(c / RN);
}

// ---------- hash table ----------
struct Slot { u64 key; i64 T; };
static Slot* tab;
static u64 tsize;

static inline u64 mix(u64 x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}
static inline u64 home(u64 key) { return (u64)(((u128)mix(key) * (u128)tsize) >> 64); }

// returns false if the key is already present
static bool tinsert(u64 code, i64 T) {
    u64 kk = code + 1;
    u64 i = home(kk);
    for (;;) {
        u64 cur = __atomic_load_n(&tab[i].key, __ATOMIC_ACQUIRE);
        if (cur == 0) {
            u64 expct = 0;
            if (__atomic_compare_exchange_n(&tab[i].key, &expct, kk, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
                tab[i].T = T;
                return true;
            }
            cur = expct;
        }
        if (cur == kk) return false;
        if (++i == tsize) i = 0;
    }
}
// returns true and sets T if present
static inline bool tfind(u64 code, i64& T) {
    u64 kk = code + 1;
    u64 i = home(kk);
    for (;;) {
        u64 cur = tab[i].key;
        if (cur == kk) { T = tab[i].T; return true; }
        if (cur == 0) return false;
        if (++i == tsize) i = 0;
    }
}

// ---------- error reporting ----------
static std::atomic<int> failed(0);
static std::string failMsg;
static void fail(const std::string& m) {
    int z = 0;
    if (failed.compare_exchange_strong(z, 1)) {
        #pragma omp critical(failmsg)
        failMsg = m;
    }
}

static std::string stateStr(int hid, int N, const int* u, const int* e, i64 T, bool withT) {
    std::string s = std::to_string(N);
    if (withT) s += " " + std::to_string(T);
    s += " |";
    bool any = false;
    for (int C = 1; C < k; C++)
        for (int t = 0; t < Hcnt[hid][C]; t++) { s += " " + std::to_string(C); any = true; }
    if (!any) s += " -";
    s += " |";
    for (int j = 0; j < K; j++) s += " " + std::to_string(u[j]) + "," + std::to_string(N + e[j] - u[j]);
    return s;
}

// ---------- parsing ----------
static bool parseHeader(const std::string& h, std::string& err) {
    if (h.empty() || h[0] != '#') { err = "line 1 is not a '#' header"; return false; }
    std::vector<std::string> tok;
    size_t p = 1;
    while (p < h.size()) {
        while (p < h.size() && (h[p] == ' ' || h[p] == '\t' || h[p] == ':')) p++;
        size_t q = p;
        while (q < h.size() && h[q] != ' ' && h[q] != '\t') q++;
        if (q > p) tok.push_back(h.substr(p, q - p));
        p = q;
    }
    bool hk = false, hr = false, hx = false, hw = false;
    auto toInt = [&](const std::string& s, i64& v) -> bool {
        if (s.empty() || s.size() > 15) return false;
        size_t i = 0; bool neg = false;
        if (s[0] == '-') { neg = true; i = 1; if (s.size() == 1) return false; }
        v = 0;
        for (; i < s.size(); i++) { if (s[i] < '0' || s[i] > '9') return false; v = v * 10 + (s[i] - '0'); }
        if (neg) v = -v;
        return true;
    };
    for (size_t i = 0; i < tok.size(); i++) {
        i64 v;
        if (tok[i] == "k" && i + 1 < tok.size()) { if (!toInt(tok[++i], v)) { err = "bad k"; return false; } k = (int)v; hk = true; }
        else if (tok[i] == "r" && i + 1 < tok.size()) { if (!toInt(tok[++i], v)) { err = "bad r"; return false; } r = (int)v; hr = true; }
        else if (tok[i] == "x2" && i + 1 < tok.size()) { if (!toInt(tok[++i], v)) { err = "bad x2"; return false; } X2 = (int)v; hx = true; }
        else if (tok[i] == "root" && i + 1 < tok.size()) { if (!toInt(tok[++i], v)) { err = "bad root"; return false; } rootClaim = v; }
        else if (tok[i] == "mode" && i + 1 < tok.size()) { if (tok[++i] != "rounded") { err = "mode is not 'rounded'"; return false; } }
        else if (tok[i] == "weights" && i + 1 < tok.size()) {
            std::string s = tok[++i];
            size_t a = 0;
            while (a <= s.size()) {
                size_t b = s.find(',', a);
                if (b == std::string::npos) b = s.size();
                if (!toInt(s.substr(a, b - a), v) || v <= 0) { err = "bad weights"; return false; }
                w.push_back(v);
                a = b + 1;
            }
            hw = true;
        }
    }
    if (!hk || !hr || !hx || !hw || rootClaim < 0) { err = "header lacks k, r, x2, weights or root"; return false; }
    if (k < 2 || r < 1 || (X2 != 0 && X2 != 1)) { err = "header values out of range"; return false; }
    if ((i64)k * r > 1000000) { err = "F too large"; return false; }
    K = (int)w.size();
    if (K < 1 || K > 8) { err = "need 1..8 weights"; return false; }
    F = k * r;
    W = 0;
    for (i64 x : w) W += x;
    return true;
}

// parse a decimal integer (optionally signed), at most 18 digits
static inline bool pint(const char*& p, const char* e, i64& v, bool allowNeg) {
    bool neg = false;
    if (allowNeg && p < e && *p == '-') { neg = true; p++; }
    if (p >= e || *p < '0' || *p > '9') return false;
    v = 0;
    int nd = 0;
    while (p < e && *p >= '0' && *p <= '9') { v = v * 10 + (*p - '0'); p++; if (++nd > 18) return false; }
    if (neg) v = -v;
    return true;
}
static inline bool isws(char c) { return c == ' ' || c == '\t'; }
static inline void skipws(const char*& p, const char* e) { while (p < e && isws(*p)) p++; }
// require at least one whitespace (or end) after a token
static inline bool sep(const char*& p, const char* e) {
    if (p < e && !isws(*p)) return false;
    skipws(p, e);
    return true;
}

// parse one state line [s, e); returns "" on success
static std::string parseLine(const char* s, const char* e, u64& code, i64& T) {
    const char* p = s;
    i64 N, v;
    skipws(p, e);
    if (!pint(p, e, N, false) || !sep(p, e)) return "bad N";
    if (!pint(p, e, T, true) || !sep(p, e)) return "bad T";
    if (p >= e || *p != '|') return "missing first |";
    p++;
    if (!sep(p, e)) return "bad after |";
    if (N < 0 || N > 2 * F) return "N outside 0..2F";
    int hid = 0;
    if (p < e && *p == '-') {
        p++;
        if (!sep(p, e)) return "bad '-'";
    } else {
        int cnt = 0;
        while (p < e && *p != '|') {
            if (!pint(p, e, v, false) || !sep(p, e)) return "bad coarse class";
            if (v < 1 || v > k - 1) return "coarse class outside 1..k-1";
            hid = addT[(size_t)hid * k + v];
            if (hid < 0) return "H does not split into two groups of sum <= k-1 (Lemma E.1(i))";
            cnt++;
        }
        if (cnt == 0) return "empty H field (expected '-')";
    }
    if (p >= e || *p != '|') return "missing second |";
    p++;
    if (!sep(p, e)) return "bad after second |";
    int u[8], ee[8];
    i64 pay = 0;
    for (int j = 0; j < K; j++) {
        i64 a, b;
        if (!pint(p, e, a, false)) return "bad u";
        if (p >= e || *p != ',') return "bad pair";
        p++;
        if (!pint(p, e, b, false)) return "bad v";
        if (!sep(p, e)) return "bad after pair";
        if (a > b) return "u > v";
        i64 ej = a + b - N;
        if (ej != 0 && ej != 1) return "e_j = u_j+v_j-N not in {0,1} (Lemma E.1(ii))";
        if (a == 0 && ej != 0) return "u_j = 0 but e_j = 1 (Lemma E.1(ii))";
        u[j] = (int)a;
        ee[j] = (int)ej;
        pay += w[j] * b;
    }
    if (p != e) return "trailing characters (wrong number of pairs?)";
    if (pay > T) return "payoff sum_j w_j v_j exceeds T (Definition E.2(b))";
    code = encode(hid, (int)N, u, ee);
    return "";
}

static bool readFull(int fd, char* buf, size_t len, off_t off) {
    size_t got = 0;
    while (got < len) {
        ssize_t n = pread(fd, buf + got, len - got, off + (off_t)got);
        if (n <= 0) return false;
        got += (size_t)n;
    }
    return true;
}

static double now() {
    return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

int main(int argc, char** argv) {
    if (argc != 2) { fprintf(stderr, "usage: icheck <certificate>\n"); return 2; }
    double t0 = now();
    const char* path = argv[1];
    int fd = open(path, O_RDONLY);
    if (fd < 0) { printf("RESULT FAIL cannot open %s\n", path); return 1; }
    struct stat st;
    fstat(fd, &st);
    const off_t fsize = st.st_size;

    // header: line 1 '#' header, line 2 '#' comment
    std::string l1, l2;
    off_t off = 0;
    {
        char b[1 << 16];
        size_t n = (size_t)std::min<off_t>(fsize, (off_t)sizeof(b));
        if (!readFull(fd, b, n, 0)) { printf("RESULT FAIL read error\n"); return 1; }
        size_t i = 0;
        while (i < n && b[i] != '\n') i++;
        if (i >= n) { printf("RESULT FAIL no complete header line\n"); return 1; }
        l1.assign(b, i);
        size_t j = i + 1;
        while (j < n && b[j] != '\n') j++;
        if (j >= n) { printf("RESULT FAIL no complete second line\n"); return 1; }
        l2.assign(b + i + 1, j - i - 1);
        off = (off_t)j + 1;
    }
    std::string err;
    if (!parseHeader(l1, err)) { printf("RESULT FAIL header: %s\n", err.c_str()); return 1; }
    if (l2.empty() || l2[0] != '#') { printf("RESULT FAIL line 2 is not a '#' comment\n"); return 1; }
    buildH();
    RN = 2 * (u64)F + 1;
    RC = 2 * ((u64)F + 1);
    MJ.assign(K, 1);
    for (int j = K - 2; j >= 0; j--) MJ[j] = MJ[j + 1] * RC;
    MN = MJ[0] * RC;
    MH = MN * RN;
    {
        u128 top = (u128)Hcnt.size() * (u128)MH;
        if (top >= ((u128)1 << 63)) { printf("RESULT FAIL state code does not fit in 63 bits\n"); return 1; }
    }
    int nth = omp_get_max_threads();
    printf("icheck: file %s\n", path);
    printf("header: k %d r %d F %d x2 %d K %d weights", k, r, F, X2, K);
    for (int j = 0; j < K; j++) printf("%s%lld", j ? "," : " ", (long long)w[j]);
    printf(" W %lld claimed-root %lld\n", (long long)W, (long long)rootClaim);
    printf("splittable multisets H: %zu ; threads %d\n", Hcnt.size(), nth);
    fflush(stdout);

    // ---- pass 1: count lines ----
    const size_t CH = 16u << 20, MAXL = 1u << 16;
    const off_t D = fsize - off;
    const i64 nchunks = (D + (off_t)CH - 1) / (off_t)CH;
    u64 nl = 0;
    {
        std::atomic<int> rerr(0);
        #pragma omp parallel reduction(+ : nl)
        {
            std::vector<char> buf(CH);
            #pragma omp for schedule(dynamic, 1)
            for (i64 c = 0; c < nchunks; c++) {
                off_t a = off + (off_t)c * (off_t)CH;
                size_t len = (size_t)std::min<off_t>((off_t)CH, fsize - a);
                if (!readFull(fd, buf.data(), len, a)) { rerr = 1; continue; }
                const char* q = buf.data();
                const char* e = q + len;
                while ((q = (const char*)memchr(q, '\n', e - q))) { nl++; q++; }
            }
        }
        if (rerr) { printf("RESULT FAIL read error\n"); return 1; }
    }
    u64 maxStates = nl + 1;
    tsize = std::max<u64>(1024, maxStates + maxStates / 2 + maxStates / 8);  // load <= 0.62
    tab = (Slot*)calloc(tsize, sizeof(Slot));
    if (!tab) { printf("RESULT FAIL cannot allocate %llu slots\n", (unsigned long long)tsize); return 1; }
    double t1 = now();
    printf("lines after header: <= %llu ; table %llu slots (%.2f GB) ; count pass %.1fs\n",
           (unsigned long long)maxStates, (unsigned long long)tsize, tsize * 16.0 / 1e9, t1 - t0);
    fflush(stdout);

    // ---- pass 2: parse and insert ----
    u64 nstates = 0;
    {
        #pragma omp parallel reduction(+ : nstates)
        {
            std::vector<char> buf(CH + MAXL + 1);
            #pragma omp for schedule(dynamic, 1)
            for (i64 c = 0; c < nchunks; c++) {
                if (failed) continue;
                off_t a = off + (off_t)c * (off_t)CH;
                off_t b = std::min<off_t>(a + (off_t)CH, fsize);
                off_t ra = (a > off) ? a - 1 : a;              // one byte before, to see the previous '\n'
                off_t rb = std::min<off_t>(b + (off_t)MAXL, fsize);
                if (!readFull(fd, buf.data(), (size_t)(rb - ra), ra)) { fail("read error"); continue; }
                const char* B = buf.data();
                const char* E = B + (rb - ra);
                const char* p = B + (a - ra);
                if (a > off) {                                  // skip the line that started in the previous chunk
                    while (p < E && *(p - 1) != '\n') p++;
                }
                while (p < E && (off_t)(ra + (p - B)) < b) {
                    const char* q = (const char*)memchr(p, '\n', E - p);
                    const char* le;
                    if (!q) {
                        if (rb < fsize) { fail("line longer than 64 KB at byte " + std::to_string((long long)(ra + (p - B)))); break; }
                        le = E;
                    } else le = q;
                    u64 code = 0; i64 T = 0;
                    std::string m = parseLine(p, le, code, T);
                    if (!m.empty()) {
                        fail("malformed or invalid state line at byte " + std::to_string((long long)(ra + (p - B))) +
                             ": " + m + " : '" + std::string(p, std::min<size_t>(le - p, 300)) + "'");
                        break;
                    }
                    if (!tinsert(code, T)) {
                        fail("duplicate state: '" + std::string(p, std::min<size_t>(le - p, 300)) + "'");
                        break;
                    }
                    nstates++;
                    p = q ? q + 1 : E;
                }
            }
        }
    }
    close(fd);
    double t2 = now();
    if (failed) { printf("RESULT FAIL %s\n", failMsg.c_str()); return 1; }
    printf("states: %llu ; parse pass %.1fs\n", (unsigned long long)nstates, t2 - t1);
    fflush(stdout);

    // ---- (a): the root state ----
    int zu[8] = {0}, ze[8] = {0};
    i64 T0;
    if (!tfind(encode(0, 0, zu, ze), T0)) { printf("RESULT FAIL (a): the empty-prefix state is not in the certificate\n"); return 1; }

    // ---- (c): every move at every state has an answering response ----
    u64 moves = 0, lookups = 0;
    const int nresp = 1 << K;
    const int nsucc = 1 << (2 * K);   // successor index: per copy 2 bits (side, overflow bit)
    #pragma omp parallel reduction(+ : moves, lookups)
    {
        std::vector<i64> memoT(nsucc);
        std::vector<u64> memoStamp(nsucc, 0);
        u64 stamp = 0;
        int u[8], e[8], v[8];
        u64 contrib[8][2][2];
        bool okc[8][2][2];
        int npat[8], pat[8][4][2];
        int ctr[8];
        #pragma omp for schedule(dynamic, 4096)
        for (u64 s = 0; s < tsize; s++) {
            if (failed) continue;
            u64 kk = tab[s].key;
            if (!kk) continue;
            const i64 T = tab[s].T;
            int hid, N;
            decode(kk - 1, hid, N, u, e);
            for (int j = 0; j < K; j++) v[j] = N + e[j] - u[j];
            for (int c = 0; c < F && !failed; c++) {
                const int C = c / r;
                const int hn = C >= 1 ? addT[(size_t)hid * k + C] : hid;
                if (hn < 0) continue;                           // new H does not split: not a move
                for (int nu = (N == 0 ? 1 : 0); nu <= 1; nu++) {
                    const int Nn = N + c + nu;
                    if (Nn > 2 * F) continue;                   // new N > 2F: not a move
                    const u64 base = (u64)hn * MH + (u64)Nn * MN;
                    // successor pair of copy j for side (0 lower, 1 upper) and overflow bit b
                    for (int j = 0; j < K; j++)
                        for (int sd = 0; sd < 2; sd++)
                            for (int b = 0; b < 2; b++) {
                                int lo = u[j], hi = v[j];
                                if (sd == 0) lo += c + b; else hi += c + b;
                                if (lo > hi) std::swap(lo, hi);
                                int en = lo + hi - Nn;
                                bool ok = (en == 0 || en == 1) && !(lo == 0 && en == 1) && lo <= F;
                                okc[j][sd][b] = ok;
                                contrib[j][sd][b] = ok ? (u64)(2 * lo + en) * MJ[j] : 0;
                            }
                    // allowed (o_j, o'_j) by Lemma E.1(iii)
                    for (int j = 0; j < K; j++) {
                        if (u[j] == 0) { npat[j] = 1; pat[j][0][0] = 1; pat[j][0][1] = nu; }
                        else if (e[j] == 0 && nu == 1) { npat[j] = 1; pat[j][0][0] = 1; pat[j][0][1] = 1; }
                        else if (e[j] == 1 && nu == 0) { npat[j] = 1; pat[j][0][0] = 0; pat[j][0][1] = 0; }
                        else {
                            npat[j] = 4;
                            for (int q = 0; q < 4; q++) { pat[j][q][0] = q >> 1; pat[j][q][1] = q & 1; }
                        }
                    }
                    stamp++;
                    for (int j = 0; j < K; j++) ctr[j] = 0;
                    for (;;) {
                        // restriction (iv): among copies with u_j > 0 and e_j = nu, not both (0,0) and (1,1)
                        bool skip = false;
                        if (X2) {
                            bool h00 = false, h11 = false;
                            for (int j = 0; j < K; j++)
                                if (u[j] > 0 && e[j] == nu) {
                                    int o = pat[j][ctr[j]][0], o2 = pat[j][ctr[j]][1];
                                    if (o == 0 && o2 == 0) h00 = true;
                                    if (o == 1 && o2 == 1) h11 = true;
                                }
                            skip = h00 && h11;
                        }
                        if (!skip) {
                            moves++;
                            bool answered = false;
                            for (int m = 0; m < nresp && !answered; m++) {
                                u64 code = base;
                                int sidx = 0;
                                bool ok = true;
                                for (int j = 0; j < K; j++) {
                                    int sd = (m >> j) & 1;
                                    int b = pat[j][ctr[j]][sd];
                                    if (!okc[j][sd][b]) { ok = false; break; }
                                    code += contrib[j][sd][b];
                                    sidx = sidx * 4 + sd * 2 + b;
                                }
                                if (!ok) continue;
                                i64 Tn;
                                if (memoStamp[sidx] == stamp) Tn = memoT[sidx];
                                else {
                                    lookups++;
                                    if (!tfind(code, Tn)) Tn = INT64_MAX;
                                    memoStamp[sidx] = stamp;
                                    memoT[sidx] = Tn;
                                }
                                if (Tn != INT64_MAX && Tn <= T) answered = true;
                            }
                            if (!answered) {
                                std::string m = "(c): unanswered move at state '" + stateStr(hid, N, u, e, T, true) +
                                                "' : c " + std::to_string(c) + " (C " + std::to_string(C) + ") nu " +
                                                std::to_string(nu) + " bits";
                                for (int j = 0; j < K; j++)
                                    m += " (" + std::to_string(pat[j][ctr[j]][0]) + "," + std::to_string(pat[j][ctr[j]][1]) + ")";
                                fail(m);
                                break;
                            }
                        }
                        int j = K - 1;
                        while (j >= 0 && ++ctr[j] == npat[j]) { ctr[j] = 0; j--; }
                        if (j < 0) break;
                    }
                    if (failed) break;
                }
            }
        }
    }
    double t3 = now();
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    if (failed) { printf("RESULT FAIL %s\n", failMsg.c_str()); return 1; }
    i64 den = W * F, g = T0, h = den;
    while (h) { i64 t = g % h; g = h; h = t; }
    printf("moves checked: %llu ; successor lookups %llu ; move pass %.1fs ; peak RSS %.2f GB\n",
           (unsigned long long)moves, (unsigned long long)lookups, t3 - t2, ru.ru_maxrss / 1048576.0);
    if (rootClaim != T0) {
        // the header claims the bound; a claim that the state list does not certify is rejected
        printf("RESULT FAIL header claims root %lld but T(sigma_0) = %lld in the state list (all checks of (a)-(c) passed)\n",
               (long long)rootClaim, (long long)T0);
        return 1;
    }
    printf("RESULT PASS states %llu moves %llu T0 %lld W %lld F %d bound %lld/%lld\n",
           (unsigned long long)nstates, (unsigned long long)moves, (long long)T0, (long long)W, F,
           (long long)(T0 / g), (long long)(den / g));
    return 0;
}
