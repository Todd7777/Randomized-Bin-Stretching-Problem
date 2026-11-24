"""Value of a two-bin catalog game as a piecewise linear function of p.
python3 catalog_value_bound.py CATALOG.json --bound B [--describe]"""
import argparse
import json
import sys
from fractions import Fraction
from itertools import combinations
from math import lcm

def feasible(seq):
    total = sum(seq)
    sums = {Fraction(0)}
    for x in seq:
        sums |= {s + x for s in sums if s + x <= 1}
    return any(total - s <= 1 for s in sums)

def evaluate(f, x):
    for (x0, y0), (x1, y1) in zip(f, f[1:]):
        if x0 <= x <= x1:
            return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
    raise ValueError(x)

def drop_collinear(points):
    out = [points[0]]
    for i in range(1, len(points) - 1):
        (x0, y0), (x1, y1), (x2, y2) = out[-1], points[i], points[i + 1]
        if (y1 - y0) * (x2 - x1) != (y2 - y1) * (x1 - x0):
            out.append(points[i])
    out.append(points[-1])
    return tuple(out)

def combine(f, g, pick):
    xs = sorted({x for x, _ in f} | {x for x, _ in g})
    points = []
    previous = None
    for x in xs:
        a, b = evaluate(f, x), evaluate(g, x)
        if previous is not None:
            px, pa, pb = previous
            if (pa - pb) * (a - b) < 0:
                t = (pa - pb) / ((pa - pb) - (a - b))
                points.append((px + (x - px) * t, pa + (a - pa) * t))
        points.append((x, pick(a, b)))
        previous = (x, a, b)
    return drop_collinear(points)

def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("catalog")
    parser.add_argument("--describe", action="store_true")
    parser.add_argument("--bound", type=Fraction, required=True)
    args = parser.parse_args()
    with open(args.catalog, encoding="utf-8") as stream:
        inputs = [tuple(Fraction(x) for x in seq) for seq in json.load(stream)]

    assert len(set(inputs)) == len(inputs), "duplicate input"
    assert all(0 < x <= 1 for seq in inputs for x in seq), "size outside (0,1]"
    assert all(feasible(seq) for seq in inputs), "infeasible input"
    catalog = set(inputs)
    assert not any(seq[:k] in catalog for seq in inputs for k in range(len(seq))), "an input is a prefix of another"
    children = {}
    for seq in inputs:
        for k in range(len(seq)):
            children.setdefault(seq[:k], set()).add(seq[k])
    print(f"inputs: {len(inputs)}, longest: {max(map(len, inputs))} jobs, "
          f"totals: {sorted({str(sum(s)) for s in inputs})}, internal nodes: {len(children)}")

    memo = {}

    def value(prefix, loads1, loads2):
        key = (prefix, loads1, loads2)
        if key in memo:
            return memo[key]
        if prefix not in children:
            c1, c2 = max(loads1), max(loads2)
            result = ((Fraction(0), c2), (Fraction(1), c1))
        else:
            result = None
            for x in sorted(children[prefix]):
                worst = None
                for bin1 in (0, 1):
                    next1 = (loads1[0] + x, loads1[1]) if bin1 == 0 else (loads1[0], loads1[1] + x)
                    for bin2 in (0, 1):
                        next2 = (loads2[0] + x, loads2[1]) if bin2 == 0 else (loads2[0], loads2[1] + x)
                        v = value(prefix + (x,), next1, next2)
                        worst = v if worst is None else combine(worst, v, min)
                result = worst if result is None else combine(result, worst, max)
        memo[key] = result
        return result

    sys.setrecursionlimit(10000)
    zero = (Fraction(0), Fraction(0))
    root = value((), zero, zero)
    print(f"explicit-load positions: {len(memo)}, knots of V on [0,1]: {len(root)}")
    assert all(evaluate(root, 1 - x) == y for x, y in root), "V is not symmetric"
    half = [(x, y) for x, y in root if x >= Fraction(1, 2)]
    low = min(y for _, y in half)
    where = [x for x, y in half if y == low]
    print("knots of V on [1/2,1]:")
    for x, y in half:
        print(f"  p = {str(x):8} V = {str(y):9} ~ {float(y):.6f}")
    print(f"min of V on [1/2,1]: {low}, attained at the knots {[str(x) for x in where]}")
    print(f"V(1/2) = {evaluate(root, Fraction(1, 2))}, V(1) = {evaluate(root, Fraction(1))}")
    ok = low >= args.bound
    print(f"bound {args.bound}: min of V on [1/2,1] {'>=' if ok else '<'} bound")

    def minimax(p):
        cache = {}

        def go(prefix, loads1, loads2):
            key = (prefix, loads1, loads2)
            if key in cache:
                return cache[key]
            if prefix not in children:
                r = p * max(loads1) + (1 - p) * max(loads2)
            else:
                r = None
                for x in children[prefix]:
                    worst = None
                    for bin1 in (0, 1):
                        next1 = (loads1[0] + x, loads1[1]) if bin1 == 0 else (loads1[0], loads1[1] + x)
                        for bin2 in (0, 1):
                            next2 = (loads2[0] + x, loads2[1]) if bin2 == 0 else (loads2[0], loads2[1] + x)
                            v = go(prefix + (x,), next1, next2)
                            worst = v if worst is None else min(worst, v)
                    r = worst if r is None else max(r, worst)
            cache[key] = r
            return r
        return go((), zero, zero)

    ok &= all(minimax(x) == y for x, y in half)
    grid = min(minimax(Fraction(i, 172)) for i in range(86, 173))
    print(f"plain minimax agrees at every knot on [1/2,1]; its minimum over p = i/172, 86 <= i <= 172: {grid}")
    ok &= grid >= args.bound

    if args.describe:
        groups = {}
        for seq in inputs:
            groups.setdefault(seq[0], []).append(seq)
        print("catalog in integer units, grouped by the first job:")
        for first in sorted(groups):
            unit = lcm(*(x.denominator for seq in groups[first] for x in seq))
            print(f"  unit 1/{unit}: " + ", ".join("(" + ",".join(str(int(x * unit)) for x in seq) + ")"
                                                  for seq in groups[first]))
        two = [seq for seq in inputs if sum(seq) == 2]
        unit_then_fill = [seq for seq in two if seq[-2] == 1]
        close_pair = [seq for seq in two if seq[-2] != 1 and abs(seq[-1] - seq[-2]) <= Fraction(1, 24)]
        other = [seq for seq in inputs if seq not in two]
        prefixes = {seq[:-2] for seq in two}
        print(f"  total 2: {len(two)} inputs; ending with a job of size 1 and a last job: {len(unit_then_fill)}; "
              f"ending with two jobs that differ by at most 1/24: {len(close_pair)}; "
              f"distinct prefixes before the last two jobs: {len(prefixes)}")
        print(f"  other inputs: {[tuple(str(x) for x in seq) for seq in other]}")
        print(f"  (42-stream check, not required here: {len(unit_then_fill) + len(close_pair) == len(two)})")

    print("PASS" if ok else "FAIL")
    raise SystemExit(0 if ok else 1)

if __name__ == "__main__":
    main()
