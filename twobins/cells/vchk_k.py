#!/usr/bin/env python3
# A third checker of STRAT3 files.
# python3 vchk_k.py --bound B FILE...
import sys
from fractions import Fraction
from itertools import product

def feasible(sizes, G):
    N = sum(sizes)
    if N > 2 * G:
        return False
    if any(x < 1 or x > G for x in sizes):
        return False
    sums = {0}
    for x in sizes:
        sums |= {t + x for t in sums}
    return any(N - G <= t <= G for t in sums)

def check(path, bound):
    lines = open(path).read().split("\n")
    hdr = lines[0].split()
    if len(hdr) != 5 or hdr[0] != "STRAT3":
        return "bad header"
    G, K, Xn, Xd = map(int, hdr[1:])
    if K < 1 or G < 1 or Xd <= 0:
        return "bad header values"
    X = Fraction(Xn, Xd)
    if bound is not None and X < bound:
        return "target %s below bound %s" % (X, bound)
    vs = []
    table = {}
    i = 1
    ended = False
    for ln in lines[1:]:
        t = ln.strip()
        if not t:
            continue
        if ended:
            return "text after END"
        if t == "END":
            ended = True
            continue
        if t.startswith("v "):
            w = tuple(int(x) for x in t.split()[1:])
            if len(w) != 3 or min(w) < 0 or sum(w) <= 0:
                return "bad weight line"
            vs.append(w)
            continue
        parts = t.split("|")
        if len(parts) != 3:
            return "bad line " + t[:40]
        c = tuple(int(x) for x in parts[0].split())
        a = tuple(int(x) for x in parts[1].split())
        s = parts[2].split()
        if len(c) != G or len(a) != 3 or len(s) != 1:
            return "bad state line"
        key = (c, a)
        if key in table:
            return "duplicate state"
        table[key] = int(s[0])
    if not ended:
        return "no END"
    if len(vs) != K:
        return "need K weight vectors"
    start = (tuple([0] * G), (0, 0, 0))
    seen = {start}
    stack = [start]
    used = set()
    nstop = 0
    minval = None
    while stack:
        c, a = stack.pop()
        sizes = [i + 1 for i in range(G) for _ in range(c[i])]
        N = sum(sizes)
        assert N == sum((i + 1) * c[i] for i in range(G))
        for aj in a:
            if not (0 <= aj and 2 * aj <= N):
                return "bad smaller load"
        if (c, a) in table:
            used.add((c, a))
            s = table[(c, a)]
            if not (1 <= s <= G):
                return "size out of range"
            if not feasible(sizes + [s], G):
                return "infeasible size %d at %s" % (s, sizes)
            c2 = list(c)
            c2[s - 1] += 1
            c2 = tuple(c2)
            for chi in product((0, 1), repeat=3):
                a2 = tuple(a[j] if chi[j] == 1 else min(a[j] + s, N - a[j]) for j in range(3))
                st = (c2, a2)
                if st not in seen:
                    seen.add(st)
                    stack.append(st)
        else:
            nstop += 1
            if N == 0:
                return "root stops"
            for v in vs:
                lhs = sum(v[j] * (N - a[j]) for j in range(3))
                val = Fraction(lhs, G * sum(v))
                if minval is None or val < minval:
                    minval = val
                if Xd * lhs < Xn * G * sum(v):
                    return "stop state %s a=%s fails weight %s: %s < %s" % (sizes, a, v, val, X)
    return ("OK", G, X, vs, len(seen), len(table), len(used), nstop, minval)

if __name__ == "__main__":
    args = sys.argv[1:]
    bound = None
    if args and args[0] == "--bound":
        bound = Fraction(args[1])
        args = args[2:]
    bad = 0
    for p in args:
        r = check(p, bound)
        if isinstance(r, tuple):
            print("PASS", p.split("/")[-1], "G=%d X=%s reached=%d listed=%d used=%d stops=%d minleaf=%s" % (r[1], r[2], r[4], r[5], r[6], r[7], r[8]), "v=" + ";".join(",".join(map(str, v)) for v in r[3]))
        else:
            bad += 1
            print("FAIL", p.split("/")[-1], r)
    print("SUMMARY files=%d fail=%d" % (len(args), bad))
