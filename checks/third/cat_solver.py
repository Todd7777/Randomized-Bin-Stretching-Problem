from fractions import Fraction as F
from functools import lru_cache
import itertools, sys
sys.setrecursionlimit(1000000)

class Trie:
    def __init__(self, streams):
        self.streams = [tuple(s) for s in streams]
        self.kids = [dict()]
        self.ends = [[]]
        self.below = [[]]
        for i, s in enumerate(self.streams):
            v = 0
            self.below[0].append(i)
            for z in s:
                if z not in self.kids[v]:
                    self.kids.append(dict()); self.ends.append([]); self.below.append([])
                    self.kids[v][z] = len(self.kids) - 1
                v = self.kids[v][z]
                self.below[v].append(i)
            self.ends[v].append(i)

def moves(loads, z):
    seen = set(); out = []
    for b in range(len(loads)):
        if loads[b] in seen: continue
        seen.add(loads[b])
        nl = list(loads); nl[b] += z
        out.append(tuple(sorted(nl, reverse=True)))
    return out

def min_weighted(streams, m, w):
    T = Trie(streams)
    memo = {}
    def rec(v, loads):
        key = (v, loads)
        if key in memo: return memo[key]
        tot = sum(w[i] for i in T.ends[v]) * loads[0]
        for z, c in T.kids[v].items():
            tot += min(rec(c, nl) for nl in moves(loads, z))
        memo[key] = tot
        return tot
    return rec(0, tuple([0]*m))

def frontier(streams, m):
    T = Trie(streams)
    k = len(streams)
    memo = {}
    def pareto(vs):
        vs = sorted(set(vs))
        keep = []
        for v in vs:
            if not any(all(a <= b for a, b in zip(u, v)) for u in keep):
                keep.append(v)
        return keep
    def rec(v, loads):
        key = (v, loads)
        if key in memo: return memo[key]
        idx = T.below[v]
        pos = {i: j for j, i in enumerate(idx)}
        base = [None]*len(idx)
        for i in T.ends[v]: base[pos[i]] = loads[0]
        partials = [tuple(base)]
        for z, c in T.kids[v].items():
            opts = set()
            for nl in moves(loads, z):
                opts.update(rec(c, nl))
            opts = pareto(list(opts))
            cidx = T.below[c]
            newp = []
            for p in partials:
                for o in opts:
                    q = list(p)
                    for j, i in enumerate(cidx): q[pos[i]] = o[j]
                    newp.append(tuple(q))
            partials = newp
        res = pareto(partials)
        memo[key] = res
        return res
    res = rec(0, tuple([0]*m))
    return res

def attainable(streams, m, c):
    T = Trie(streams)
    memo = {}
    def rec(v, loads):
        if loads[0] > min(c[i] for i in T.below[v]): return False
        key = (v, loads)
        if key in memo: return memo[key]
        ok = all(any(rec(ch, nl) for nl in moves(loads, z)) for z, ch in T.kids[v].items())
        memo[key] = ok
        return ok
    return rec(0, tuple([0]*m))

def feasible(stream, m, g):
    s = sorted(stream, reverse=True)
    if any(x > g for x in s): return False
    loads = [0]*m
    def dfs(i):
        if i == len(s): return True
        seen = set()
        for b in range(m):
            if loads[b] in seen: continue
            seen.add(loads[b])
            if loads[b] + s[i] <= g:
                loads[b] += s[i]
                if dfs(i+1): return True
                loads[b] -= s[i]
        return False
    return dfs(0)
