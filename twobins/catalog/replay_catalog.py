"""Two-bin catalog: the p in [1/2,1] at which every pair of policies costs at least the bound.
python3 replay_catalog.py CATALOG.json [--bound B] [--at P]"""
import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from math import lcm
from pathlib import Path

def merge(intervals):
    result = []
    for lower, upper in sorted(intervals):
        if result and lower <= result[-1][1]:
            result[-1] = (result[-1][0], max(upper, result[-1][1]))
        else:
            result.append((lower, upper))
    return tuple(result)

def replay(streams, bound):
    grid = lcm(*(x.denominator for seq in streams for x in seq))
    root = {}
    for seq in streams:
        node = root
        total = 0
        attainable = {0}
        for x in seq:
            size = int(x * grid)
            if not 0 < size <= grid:
                raise ValueError("job size outside (0,1]")
            total += size
            attainable |= {a + size for a in attainable if a + size <= grid}
            node = node.setdefault(size, {})
        if not any(total - a <= grid for a in attainable):
            raise ValueError("infeasible input")
    def freeze(node):
        return tuple((size, freeze(child)) for size, child in node.items())

    whole = ((Fraction(1, 2), Fraction(1)),)
    target = bound * grid
    @lru_cache(None)
    def win(node, total, a, b):
        if not node:
            left, right = whole[0]
            if a == b:
                return whole if total - b >= target else ()
            crossing = (target - total + b) / (b - a)
            if b > a:
                left = max(left, crossing)
            else:
                right = min(right, crossing)
            return ((left, right),) if left <= right else ()
        may_choose = []
        for size, child in node:
            replies = product((a, min(a + size, total - a)),
                              (b, min(b + size, total - b)))
            must_cover = whole
            for next_a, next_b in set(replies):
                child_win = win(child, total + size, next_a, next_b)
                must_cover = merge((max(l1, l2), min(r1, r2))
                                   for l1, r1 in must_cover for l2, r2 in child_win
                                   if max(l1, l2) <= min(r1, r2))
                if not must_cover:
                    break
            may_choose.extend(must_cover)
        return merge(may_choose)
    result = win(freeze(root), 0, 0, 0)
    return result, win.cache_info().currsize

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog", type=Path)
    parser.add_argument("--bound", type=Fraction, default=Fraction(52, 43))
    parser.add_argument("--at", type=Fraction, default=None,
                        help="check the bound only at this probability in [1/2,1], e.g. --bound 11/9 --at 1/2")
    args = parser.parse_args()
    seqs = [tuple(Fraction(x) for x in seq)
            for seq in json.loads(args.catalog.read_text())]
    intervals, states = replay(seqs, args.bound)
    if args.at is not None:
        if not any(lower <= args.at <= upper for lower, upper in intervals):
            raise SystemExit(f"The bound fails at p = {args.at}. Covered: {intervals}")
        print(f"PASS {args.bound} at p = {args.at}; {len(seqs)} feasible inputs")
        raise SystemExit(0)
    if intervals != ((Fraction(1, 2), Fraction(1)),):
        raise SystemExit(f"Only these probability intervals are covered: {intervals}")
    print(f"PASS {args.bound}; {len(seqs)} feasible inputs; "
          f"up to {max(map(len, seqs))} jobs; {states} subproblems; p in [1/2,1]")
