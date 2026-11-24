#!/usr/bin/env python3
# checkcert.py: a second checker of a certificate written by coinlb3.cpp.
# python3 -I checkcert.py CERT
import random
import sys
from fractions import Fraction
from itertools import product

def main():
    raw = [l.rstrip("\n") for l in open(sys.argv[1])]
    lines = [l for l in raw if not l.startswith("#")]
    if lines[0] != "COINLB 1":
        sys.exit("bad magic")
    m, K, g = map(int, lines[1].split())
    w = [int(x) for x in lines[2].split()]
    t = lines[3].split()
    if t[0] != "T":
        sys.exit("bad T line")
    T = Fraction(int(t[1]), int(t[2]))
    t = lines[4].split()
    if t[0] != "N":
        sys.exit("bad N line")
    n = int(t[1])
    if not (m >= 2 and K >= 1 and g >= 1 and len(w) == K and min(w) >= 1 and T > 0):
        sys.exit("bad header")
    body = lines[5:5 + n]
    tail = [x for x in lines[5 + n:] if x.strip() not in ("", "END")]
    if len(body) != n or tail:
        sys.exit("bad count")
    W = sum(w)

    def expected(Ls):
        return sum(Fraction(wj, W) * Fraction(max(L), g) for wj, L in zip(w, Ls))

    def canon(Ls):
        Ls = [tuple(sorted(L, reverse=True)) for L in Ls]
        out = list(Ls)
        for wt in sorted(set(w)):
            idx = [j for j in range(K) if w[j] == wt]
            for j, v in zip(idx, sorted((Ls[j] for j in idx), reverse=True)):
                out[j] = v
        return tuple(out)

    packs = {(): {tuple([0] * m)}}

    def packings(H):
        if H in packs:
            return packs[H]
        prev = packings(H[:-1])
        s = H[-1]
        res = set()
        for P in prev:
            for i in range(m):
                if P[i] + s <= g:
                    Q = list(P)
                    Q[i] += s
                    res.add(tuple(sorted(Q)))
        packs[H] = res
        return res

    def feasible(H):
        Hs = tuple(sorted(H, reverse=True))
        for k in range(1, len(Hs) + 1):
            if not packings(Hs[:k]):
                return False
        return True

    st = {}
    for ln in body:
        f = [x.strip() for x in ln.split("|")]
        if len(f) != K + 2:
            sys.exit("bad fields: " + ln)
        H = () if f[0] == "-" else tuple(int(x) for x in f[0].split(","))
        if any(x < 1 or x > g for x in H) or list(H) != sorted(H, reverse=True):
            sys.exit("bad H: " + ln)
        Ls = tuple(tuple(int(x) for x in f[1 + j].split(",")) for j in range(K))
        if any(len(L) != m or min(L) < 0 or sum(L) != sum(H) for L in Ls):
            sys.exit("bad loads: " + ln)
        if canon(Ls) != Ls:
            sys.exit("not canonical: " + ln)
        if (H, Ls) in st:
            sys.exit("duplicate: " + ln)
        st[(H, Ls)] = int(f[K + 1])

    root = ((), tuple(tuple([0] * m) for _ in range(K)))
    if root not in st:
        sys.exit("root missing")
    rng = random.Random(12345)
    seen = {root}
    stack = [root]
    maxdepth = 0
    nstop = 0
    while stack:
        H, Ls = stack.pop()
        maxdepth = max(maxdepth, len(H))
        s = st[(H, Ls)]
        if not (1 <= s <= g):
            sys.exit("move out of range")
        H2 = tuple(sorted(H + (s,), reverse=True))
        if not feasible(H2):
            sys.exit("infeasible move at %s %s" % (H, Ls))
        perm_bins = [rng.sample(range(m), m) for _ in range(K)]
        relab = [tuple(Ls[j][perm_bins[j][i]] for i in range(m)) for j in range(K)]
        order = list(range(K))
        for wt in set(w):
            idx = [j for j in range(K) if w[j] == wt]
            sh = idx[:]
            rng.shuffle(sh)
            for a, b in zip(idx, sh):
                order[a] = b
        relab = [relab[order[j]] for j in range(K)]
        assert canon(relab) == Ls
        for resp in product(range(m), repeat=K):
            for base in (Ls, relab):
                new = [list(L) for L in base]
                for j in range(K):
                    new[j][resp[j]] += s
                c = canon(new)
                if expected(c) >= T:
                    nstop += 1
                    continue
                if (H2, c) not in st:
                    sys.exit("missing child %s %s" % (H2, c))
                if (H2, c) not in seen:
                    seen.add((H2, c))
                    stack.append((H2, c))
    print("OK %s: m=%d K=%d w=%s g=%d T=%s lines=%d reachable=%d unreachable=%d max_jobs=%d"
          % (sys.argv[1].split("/")[-1], m, K, w, g, T, n, len(seen), n - len(seen), maxdepth + 1))

if __name__ == "__main__":
    main()
