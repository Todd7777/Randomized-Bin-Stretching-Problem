#!/usr/bin/env python3
# cover2.py SOLVER GRIDS L D0 MAXD OUT JOBS THREADS: every lottery over two algorithms costs at least L
# (paper, App. E.3). Example: python3 cover2.py ./gridgame 12,15,18,21,24,27 29/24 20 1280 out 4 12
import sys, os, re, math, subprocess, json
from fractions import Fraction as Fr
from concurrent.futures import ThreadPoolExecutor

solver, grids = sys.argv[1], [int(x) for x in sys.argv[2].split(',')]
L, D0, MAXD, out, jobs, threads = Fr(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6], int(sys.argv[7]), sys.argv[8]
assert D0 % 2 == 0
os.makedirs(out, exist_ok=True)
vals = {}
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
    r = subprocess.run([solver, str(g), ws], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True,
                       env=dict(os.environ, OMP_NUM_THREADS=threads))
    m = re.search(r'\bT (\d+) W (\d+)', r.stdout)
    if not m: raise RuntimeError('no result for %s %s: %s %s' % (g, ws, r.stdout[-300:], r.stderr[-300:]))
    T, W = int(m.group(1)), int(m.group(2))
    assert W == sum(w), (w, W)
    return g, w, T, W

def need(points):
    todo = sorted({(g, key(p)) for p in points for g in grids} - set(vals), key=lambda z: (z[0], z[1]))
    if not todo: return
    with ThreadPoolExecutor(jobs) as ex, open(cachef, 'a') as f:
        for g, w, T, W in ex.map(run, todo):
            vals[(g, w)] = Fr(T, W * g)
            f.write('%d %s %d %d\n' % (g, ','.join(map(str, w)), T, W)); f.flush()

def v(p): return max(vals[(g, key(p))] for g in grids)

queue = [(D0, a) for a in range(D0 // 2, D0)]          # interval [a/D, (a+1)/D] of p, endpoints (a, D-a), (a+1, D-a-1)
certified, failed, rnd, worst = 0, [], 0, None
while queue:
    rnd += 1
    need([q for D, a in queue for q in ((a, D - a), (a + 1, D - a - 1))])
    nxt = []
    for D, a in queue:
        m = min(v((a, D - a)), v((a + 1, D - a - 1))); slack = m - Fr(1, 2 * D) - L
        if slack >= 0:
            certified += 1
            if worst is None or m - Fr(1, 2 * D) < worst[0]: worst = (m - Fr(1, 2 * D), (D, a))
        elif 2 * D > MAXD: failed.append((D, a))
        else: nxt += [(2 * D, 2 * a), (2 * D, 2 * a + 1)]
    print('round %d: %d intervals in, %d certified so far, %d failed, %d next, %d values' % (rnd, len(queue), certified, len(failed), len(nxt), len(vals)), flush=True)
    queue = nxt

lowest = {}
for (g, w), x in vals.items():
    if w not in lowest or x > lowest[w][0]: lowest[w] = (x, g)
mins = sorted(((x, g, w) for w, (x, g) in lowest.items()), key=lambda z: z[0])[:12]
res = {'L': str(L), 'grids': grids, 'D0': D0, 'MAXD': MAXD, 'certified_intervals': certified, 'failed': len(failed),
       'values': len(vals), 'worst_certified_margin': [str(worst[0]), worst[1]] if worst else None,
       'failed_examples': failed[:20], 'lowest_v': [[str(x), float(x), g, list(w)] for x, g, w in mins]}
json.dump(res, open(os.path.join(out, 'result.json'), 'w'), indent=1)
print('RESULT L %s %s: certified %d intervals, failed %d, %d solver values' % (L, 'HOLDS' if not failed else 'NOT SHOWN', certified, len(failed), len(vals)))
