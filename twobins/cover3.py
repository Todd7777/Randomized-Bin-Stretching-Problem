#!/usr/bin/env python3
# cover3.py SOLVER KIND GRIDS L D0 MAXD OUT JOBS: every lottery over three algorithms costs at least L
# (paper, App. E.3). KIND: gg (gridgame) or rg2 (rg2 mode=grid). Example: ./gridgame gg 12,15 47/40 30 960 out 8
import sys, os, re, math, subprocess, json
from fractions import Fraction as Fr
from concurrent.futures import ThreadPoolExecutor

solver, kind, grids = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(',')]
L, D0, MAXD, out, jobs = Fr(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7], int(sys.argv[8])
os.makedirs(out, exist_ok=True)
vals = {}                                   # (g, reduced sorted weights) -> Fraction
cachef = os.path.join(out, 'values.tsv')
if os.path.exists(cachef):
    for line in open(cachef):
        g, w, T, W = line.split()
        vals[(int(g), tuple(map(int, w.split(','))))] = Fr(int(T), int(W) * int(g))

def key(p):
    t = sorted([x for x in p if x > 0], reverse=True)
    d = 0
    for x in t: d = math.gcd(d, x)
    return tuple(x // d for x in t)

def run(job):
    g, w = job
    ws = ','.join(map(str, w))
    cmd = [solver, str(g), ws] + (['mode=grid', 'maxgb=12'] if kind == 'rg2' else [])
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, env=dict(os.environ, OMP_NUM_THREADS='1'))
    m = (re.search(r'T\(root\) = (\d+), W = (\d+)', r.stdout) if kind == 'rg2'
         else re.search(r'\bT (\d+) W (\d+)', r.stdout))
    if not m: raise RuntimeError('no result for %s %s: %s %s' % (g, ws, r.stdout[-300:], r.stderr[-300:]))
    T, W = int(m.group(1)), int(m.group(2))
    assert W == sum(w), (w, W)
    return g, w, T, W

def need(points):
    todo = sorted({(g, key(p)) for p in points for g in grids} - set(vals))
    if not todo: return
    with ThreadPoolExecutor(jobs) as ex, open(cachef, 'a') as f:
        for g, w, T, W in ex.map(run, todo):
            vals[(g, w)] = Fr(T, W * g)
            f.write('%d %s %d %d\n' % (g, ','.join(map(str, w)), T, W)); f.flush()

def v(p): return max(vals[(g, key(p))] for g in grids)

def initial(D):
    tris = []
    for i in range(D):
        for j in range(D - i):
            l = D - 1 - i - j                                   # up triangle
            tris.append((D, (i + 1, j, l), (i, j + 1, l), (i, j, l + 1)))
            if l >= 1:                                          # down triangle (i+j+l' = D-2 with l' = l-1)
                tris.append((D, (i + 1, j + 1, l - 1), (i + 1, j, l), (i, j + 1, l)))
    return tris

def split(t):
    D, A, B, C = t
    A2, B2, C2 = tuple(2 * x for x in A), tuple(2 * x for x in B), tuple(2 * x for x in C)
    AB = tuple(x + y for x, y in zip(A, B)); BC = tuple(x + y for x, y in zip(B, C)); CA = tuple(x + y for x, y in zip(C, A))
    return [(2 * D, A2, AB, CA), (2 * D, AB, B2, BC), (2 * D, CA, BC, C2), (2 * D, AB, BC, CA)]

queue, certified, failed, rnd = initial(D0), 0, [], 0
assert len(queue) == D0 * D0
worst = None
while queue:
    rnd += 1
    need([p for t in queue for p in t[1:]])
    nxt = []
    for t in queue:
        D = t[0]; m = min(v(p) for p in t[1:]); slack = m - Fr(2, 3 * D) - L
        if slack >= 0:
            certified += 1
            if worst is None or m - Fr(2, 3 * D) < worst[0]: worst = (m - Fr(2, 3 * D), t)
        elif 2 * D > MAXD: failed.append(t)
        else: nxt += split(t)
    print('round %d: %d triangles in, %d certified so far, %d failed, %d next, %d values' % (rnd, len(queue), certified, len(failed), len(nxt), len(vals)), flush=True)
    queue = nxt

mins = sorted(((x, g, w) for (g, w), x in vals.items()), key=lambda z: z[0])[:12]
res = {'L': str(L), 'grids': grids, 'D0': D0, 'MAXD': MAXD, 'certified_triangles': certified, 'failed': len(failed),
       'values': len(vals), 'worst_certified_margin': [str(worst[0]), worst[1]] if worst else None,
       'failed_examples': failed[:20], 'lowest_values': [[str(x), float(x), g, list(w)] for x, g, w in mins]}
json.dump(res, open(os.path.join(out, 'result.json'), 'w'), indent=1)
print('RESULT L %s %s: certified %d triangles, failed %d, %d solver values' % (L, 'HOLDS' if not failed else 'NOT SHOWN', certified, len(failed), len(vals)))
