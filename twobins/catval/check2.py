#!/usr/bin/env python3
# A second checker of catalog values. Does not use catval.py.
# python3 check2.py prior PRIOR.json --bound V | algo CATALOG.json ALGO.json --bound V
import argparse
import json
import sys
from fractions import Fraction
from itertools import combinations
from math import gcd

def feasible_brute(seq):
    tot = sum(seq)
    n = len(seq)
    for r in range(n + 1):
        for comb in combinations(range(n), r):
            part = sum(seq[i] for i in comb)
            if part <= 1 and tot - part <= 1:
                return True
    return False

def unit_of(seqs):
    u = 1
    for s in seqs:
        for x in s:
            u = u * x.denominator // gcd(u, x.denominator)
    return u

def check_prior(path, bound):
    with open(path) as f:
        data = json.load(f)
    items = [(tuple(Fraction(x) for x in d["stream"]), int(d["w"])) for d in data["prior"]]
    assert all(w > 0 for _, w in items), "nonpositive weight"
    assert len({s for s, _ in items}) == len(items), "duplicate stream"
    assert all(len(s) > 0 and all(x > 0 for x in s) for s, _ in items), "bad stream"
    assert all(len(s) > 12 or feasible_brute(s) for s, _ in items), "infeasible stream"
    assert all(len(s) <= 12 for s, _ in items), "stream too long for the brute-force feasibility test"
    u = unit_of([s for s, _ in items])
    W = sum(w for _, w in items)
    weight = {}
    kids = {}
    for s, w in items:
        si = tuple(int(x * u) for x in s)
        weight[si] = weight.get(si, 0) + w
        for k in range(len(si)):
            kids.setdefault(si[:k], set()).add(si[k])
    sys.setrecursionlimit(100000)
    memo = {}

    def best(prefix, l1, l2):
        key = (prefix, l1, l2)
        r = memo.get(key)
        if r is not None:
            return r
        r = weight.get(prefix, 0) * max(l1, l2)
        for x in kids.get(prefix, ()):
            nxt = prefix + (x,)
            r += min(best(nxt, l1 + x, l2), best(nxt, l1, l2 + x))
        memo[key] = r
        return r

    m = best((), 0, 0)
    value = Fraction(m, W * u)
    print(f"prior {path}: {len(items)} streams, W = {W}, unit 1/{u}, positions {len(memo)}")
    print(f"min over all policies of the expected cost under the prior = {value} ~ {float(value):.15f}")
    ok = value >= bound
    print(f"bound {bound}: {'PASS' if ok else 'FAIL'}")
    return ok

def check_algo(cpath, spath, bound):
    with open(cpath) as f:
        streams = [tuple(Fraction(x) for x in s) for s in json.load(f)]
    with open(spath) as f:
        recs = json.load(f)["records"]
    assert all(len(s) <= 12 for s in streams), "stream too long for the brute-force feasibility test"
    assert all(feasible_brute(s) for s in streams), "infeasible stream"
    P = {}
    for pre, small, p in recs:
        key = (tuple(Fraction(x) for x in pre), Fraction(small))
        pv = Fraction(p)
        assert 0 <= pv <= 1, "probability outside [0,1]"
        assert key not in P or P[key] == pv, "conflicting records"
        P[key] = pv
    worst = Fraction(0)
    arg = None
    for s in set(streams):
        dist = {(Fraction(0), Fraction(0)): Fraction(1)}
        for i, x in enumerate(s):
            pre = s[:i + 1]
            nd = {}
            for (l1, l2), pr in dist.items():
                if l1 == l2:
                    k = (l1 + x, l2)
                    nd[k] = nd.get(k, 0) + pr
                    continue
                p = P[(pre, min(l1, l2))]
                if l1 < l2:
                    on_small, on_large = (l1 + x, l2), (l1, l2 + x)
                else:
                    on_small, on_large = (l1, l2 + x), (l1 + x, l2)
                if p:
                    nd[on_small] = nd.get(on_small, 0) + pr * p
                if 1 - p:
                    nd[on_large] = nd.get(on_large, 0) + pr * (1 - p)
            dist = nd
        assert sum(dist.values()) == 1
        ec = sum(pr * max(l1, l2) for (l1, l2), pr in dist.items())
        if ec > worst:
            worst, arg = ec, s
    print(f"algorithm {spath} on {cpath}: {len(set(streams))} streams, {len(P)} records")
    print(f"largest expected cost = {worst} ~ {float(worst):.15f}, on {tuple(str(x) for x in arg)}")
    ok = worst <= bound
    print(f"bound {bound}: {'PASS' if ok else 'FAIL'}")
    return ok

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["prior", "algo"])
    ap.add_argument("files", nargs="+")
    ap.add_argument("--bound", type=Fraction, required=True)
    a = ap.parse_args()
    if a.mode == "prior":
        ok = check_prior(a.files[0], a.bound)
    else:
        ok = check_algo(a.files[0], a.files[1], a.bound)
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
