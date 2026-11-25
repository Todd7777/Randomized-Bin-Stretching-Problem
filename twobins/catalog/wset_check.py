# Two-bin catalog, checked apart from replay_catalog.py: w gives the p in [1/2,1] with value at least T, v the value at p.
# python3 wset_check.py CATALOG.json w T... | v P...
import sys, json, sys
from fractions import Fraction as F
from math import lcm
sys.setrecursionlimit(10000)

def load(path):
    raw = json.load(open(path))
    streams = [[F(x) for x in s] for s in raw]
    return streams

def build(streams):
    U = lcm(*[x.denominator for s in streams for x in s])
    kids = [dict()]; end = [False]
    for s in streams:
        ints = []
        for x in s:
            if not (0 < x <= 1): raise SystemExit("BAD size %s" % x)
            ints.append(int(x * U)); assert ints[-1] == x * U
        tot = sum(ints); sums = {0}
        for v in ints: sums = sums | {a + v for a in sums}
        if not any(a <= U and tot - a <= U for a in sums): raise SystemExit("INFEASIBLE %s" % s)
        n = 0
        for v in ints:
            if v not in kids[n]:
                kids.append(dict()); end.append(False); kids[n][v] = len(kids) - 1
            n = kids[n][v]
        end[n] = True
    return U, kids, end

def norm(iv):
    iv = sorted(iv); out = []
    for a, b in iv:
        if out and a <= out[-1][1]:
            if b > out[-1][1]: out[-1] = (out[-1][0], b)
        else: out.append((a, b))
    return tuple(out)

def inter(X, Y):
    out = []; i = j = 0
    while i < len(X) and j < len(Y):
        a = max(X[i][0], Y[j][0]); b = min(X[i][1], Y[j][1])
        if a <= b: out.append((a, b))
        if X[i][1] < Y[j][1]: i += 1
        else: j += 1
    return tuple(out)

LO, HI = F(1, 2), F(1)

def wset(U, kids, end, T):
    memo = {}
    TU = T * U
    def leafset(ca, cb):
        d = ca - cb; r = TU - cb
        if d == 0: return ((LO, HI),) if r <= 0 else ()
        t = r / d
        if d > 0: a, b = max(LO, t), HI
        else: a, b = LO, min(HI, t)
        return ((a, b),) if a <= b else ()
    def W(n, A, B):
        key = (n, A, B)
        if key in memo: return memo[key]
        parts = []
        if end[n]: parts.extend(leafset(max(A), max(B)))
        for v, c in kids[n].items():
            optsA = {tuple(sorted((A[0] + v, A[1]))), tuple(sorted((A[0], A[1] + v)))}
            optsB = {tuple(sorted((B[0] + v, B[1]))), tuple(sorted((B[0], B[1] + v)))}
            cur = ((LO, HI),)
            for a in optsA:
                for b in optsB:
                    cur = inter(cur, W(c, a, b))
                    if not cur: break
                if not cur: break
            parts.extend(cur)
        r = norm(parts); memo[key] = r; return r
    res = W(0, (0, 0), (0, 0))
    return res, len(memo)

def value(U, kids, end, p):
    memo = {}
    q = 1 - p
    def V(n, A, B):
        key = (n, A, B)
        if key in memo: return memo[key]
        best = None
        if end[n]: best = p * max(A) + q * max(B)
        for v, c in kids[n].items():
            optsA = {tuple(sorted((A[0] + v, A[1]))), tuple(sorted((A[0], A[1] + v)))}
            optsB = {tuple(sorted((B[0] + v, B[1]))), tuple(sorted((B[0], B[1] + v)))}
            m = min(V(c, a, b) for a in optsA for b in optsB)
            if best is None or m > best: best = m
        memo[key] = best; return best
    return V(0, (0, 0), (0, 0)) / U

if __name__ == "__main__":
    path = sys.argv[1]; mode = sys.argv[2]
    U, kids, end = build(load(path))
    print("file", path, "unit", U, "trie nodes", len(kids), "streams", sum(end))
    if mode == "w":
        for t in sys.argv[3:]:
            T = F(t); res, ns = wset(U, kids, end, T)
            full = res == ((LO, HI),)
            print("T", T, float(T), "W =", [(str(a), str(b)) for a, b in res], "FULL" if full else "NOT FULL", "states", ns, flush=True)
    else:
        for s in sys.argv[3:]:
            p = F(s); v = value(U, kids, end, p)
            print("p", p, "V", v, float(v), flush=True)
