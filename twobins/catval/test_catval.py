#!/usr/bin/env python3
# Tests catval.py against brute force over all policies.
# python3 test_catval.py [--random N] [--seed S]
import argparse
import itertools
import os
import random
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import catval

def prefixes(C):
    P = set()
    for s in C:
        for i in range(1, len(s) + 1):
            P.add(tuple(s[:i]))
    return sorted(P, key=lambda p: (len(p), p))

def run_cost(pol, s):
    loads = [Fr(0), Fr(0)]
    for i in range(1, len(s) + 1):
        loads[pol[tuple(s[:i])]] += s[i - 1]
    return max(loads)

def brute(C):
    P = prefixes(C)
    Cs = sorted(set(tuple(s) for s in C))
    mats = []
    for bits in itertools.product((0, 1), repeat=len(P)):
        pol = dict(zip(P, bits))
        mats.append([run_cost(pol, s) for s in Cs])
    return Cs, mats

def matrix_value(mats):
    import numpy as np
    from scipy.optimize import linprog
    n, k = len(mats), len(mats[0])
    c = np.zeros(n + 1); c[-1] = 1
    A = np.zeros((k, n + 1))
    for i in range(n):
        for j in range(k):
            A[j, i] = float(mats[i][j])
    A[:, -1] = -1
    Aeq = np.zeros((1, n + 1)); Aeq[0, :n] = 1
    res = linprog(c, A_ub=A, b_ub=np.zeros(k), A_eq=Aeq, b_eq=[1], bounds=[(0, None)] * n + [(None, None)],
                  method="highs")
    return res.fun

def catval_value(C):
    import numpy as np
    from scipy.optimize import linprog
    cat = catval.Catalog([tuple(s) for s in C])
    c, A_ub, b_ub, A_eq, b_eq, E = catval.build_lp(cat)
    bounds = [(0, None)] * (A_eq.shape[1] - 1) + [(None, None)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    assert res.status == 0
    marg = -res.ineqlin.marginals
    mu = {cat.term[q]: float(marg[i]) for i, q in enumerate(cat.terminals) if marg[i] > 1e-12}
    w = catval.round_prior(mu, 10 ** 6)
    lower = Fraction_lower = Fr(cat.best_response(w), sum(w.values()) * cat.L)
    S = cat.nstates
    Q = 2 ** 30
    pnum = []
    e = S
    for g, (ps, cn, cs) in enumerate(cat.groups):
        zz = [max(0.0, float(res.x[e + k])) for k in range(len(cs))]
        e += len(cs)
        tz = sum(zz)
        if tz <= 0:
            nums = [Q] + [0] * (len(cs) - 1)
        else:
            nums = [int(round(v / tz * Q)) for v in zz]
            nums[-1] = Q - sum(nums[:-1])
            if nums[-1] < 0:
                nums[0] += nums[-1]; nums[-1] = 0
        pnum.append(nums)
    upper = max(cat.expected_costs(pnum, Q).values())
    return res.fun, lower, upper, cat

def exact_br_check(C, Cs, mats, rng):
    cat = catval.Catalog([tuple(s) for s in C])
    w = {k: rng.randint(0, 9) for k in range(len(cat.streams))}
    if sum(w.values()) == 0:
        w[0] = 1
    for k, s in enumerate(cat.streams):
        assert tuple(Fr(v, cat.L) for v in s) == Cs[k]
    bf = min(sum(w[k] * row[k] for k in range(len(Cs))) for row in mats)
    cv = Fr(cat.best_response(w), cat.L)
    cv2, costs = cat.best_response_policy(w)
    assert Fr(cv2, cat.L) == cv
    assert sum(w[k] * Fr(costs[k], cat.L) for k in costs) == cv
    return bf == cv, bf, cv

def F(*xs, d=1):
    return tuple(Fr(x, d) for x in xs)

def random_catalog(rng, g, maxlen, nstreams, maxprefix):
    for _ in range(1000):
        C = set()
        for _ in range(nstreams):
            n = rng.randint(1, maxlen)
            s = []
            for _ in range(n):
                s.append(Fr(rng.randint(1, g), g))
                if not catval.feasible_int([int(v * g) for v in s], g):
                    s.pop()
                    break
            if s:
                C.add(tuple(s))
        C = sorted(C)
        if C and len(prefixes(C)) <= maxprefix:
            return C
    raise RuntimeError

def tree_catalog(rng, g, nstreams, maxprefix):
    for _ in range(1000):
        C = []
        for _ in range(nstreams):
            base = list(rng.choice(C)[:rng.randint(1, 3)]) if C and rng.random() < 0.8 else []
            s = base[:]
            for _ in range(rng.randint(1, 4)):
                s.append(Fr(rng.randint(1, g), g))
                if not catval.feasible_int([int(v * g) for v in s], g):
                    s.pop()
                    break
            if s:
                C.append(tuple(s))
        C = sorted(set(C))
        if C and len(prefixes(C)) <= maxprefix:
            return C
    raise RuntimeError

def full_catalog(rng, g, nstreams, maxprefix):
    for _ in range(3000):
        C = []
        for _ in range(nstreams):
            base = list(rng.choice(C)[:rng.randint(1, 3)]) if C and rng.random() < 0.85 else []
            s = base[:]
            while sum(s) < 2 and len(s) < 6:
                rest = 2 - sum(s)
                x = Fr(rng.randint(1, g), g)
                if rng.random() < 0.4 or x > rest:
                    x = min(rest, Fr(1)) if rng.random() < 0.7 else x
                if x > rest:
                    x = rest
                s.append(x)
            if not catval.feasible_int([int(v * g) for v in s], g):
                continue
            C.append(tuple(s))
        C = sorted(set(C))
        if len(C) >= 2 and len(prefixes(C)) <= maxprefix:
            return C
    raise RuntimeError

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--random", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    bad = 0
    vals = []
    known = [
        ("ex76 B2,C2", [F(1, 1, 1, 3, d=3), F(1, 1, 2, 2, d=3)], Fr(7, 6)),
        ("single (1/2)^4", [F(1, 1, 1, 1, d=2)], Fr(1)),
        ("single (1/3,1/3,1/3)", [F(1, 1, 1, d=3)], Fr(2, 3)),
        ("single infeasible-free (1/3,1/3,2/3,2/3)", [F(1, 1, 2, 2, d=3)], Fr(1)),
        ("B2 only", [F(1, 1, 1, 3, d=3)], Fr(1)),
        ("prefix pair (1/3,1/3) and (1/3,1/3,1)", [F(1, 1, d=3), F(1, 1, 3, d=3)], Fr(1)),
        ("no conflict", [F(1, 1, 2, d=2), F(1, 1, 1, 1, d=2)], Fr(1)),
        ("ex76 + prefix", [F(1, d=3), F(1, 1, 1, 3, d=3), F(1, 1, 2, 2, d=3)], Fr(7, 6)),
    ]
    for name, C, val in known:
        Cs, mats = brute(C)
        bv = matrix_value(mats)
        lv, lo, up, cat = catval_value(C)
        ok = abs(bv - float(val)) < 1e-9 and abs(lv - float(val)) < 1e-9 and lo <= val <= up and lo == val
        print(f"known {name}: expected {val}, brute {bv:.12f}, catval LP {lv:.12f}, LOWER {lo}, "
              f"UPPER {float(up):.12f} -> {'OK' if ok else 'BAD'}")
        bad += not ok
    for t in range(args.random):
        g = rng.choice([2, 3, 4, 5, 6])
        if t % 3 == 1:
            C = random_catalog(rng, g, rng.randint(2, 5), rng.randint(1, 5), 13)
        elif t % 3 == 2:
            C = full_catalog(rng, g, rng.randint(2, 5), 14)
        else:
            C = tree_catalog(rng, g, rng.randint(2, 6), 14)
        vals.append(bv if False else None)
        Cs, mats = brute(C)
        bv = matrix_value(mats)
        lv, lo, up, cat = catval_value(C)
        vals[-1] = round(bv, 9)
        ok1 = abs(bv - lv) < 1e-7 and float(lo) <= bv + 1e-7 and float(up) >= bv - 1e-7 \
            and float(up - lo) < 1e-5
        ok2, bf, cv = exact_br_check(C, Cs, mats, rng)
        if not (ok1 and ok2):
            bad += 1
            print(f"random {t}: BAD brute {bv} catval {lv} lower {lo} upper {float(up)} br {bf} vs {cv} C={C}")
        elif t % 25 == 0:
            print(f"random {t}: g={g} streams {len(Cs)} prefixes {len(prefixes(C))} policies {len(mats)} "
                  f"value {bv:.9f} catval {lv:.9f} LOWER {float(lo):.9f} UPPER {float(up):.9f} exactBR {bf} OK")
    from collections import Counter
    print("random values (most common):", Counter(vals).most_common(12))
    print("random cases with value > 1:", sum(1 for v in vals if v is not None and v > 1 + 1e-9),
          "distinct values > 1:", sorted({v for v in vals if v is not None and v > 1 + 1e-9}))
    print(f"tests done: {len(known)} known + {args.random} random, BAD = {bad}")
    print("ALL OK" if bad == 0 else "FAILURES")

if __name__ == "__main__":
    main()
