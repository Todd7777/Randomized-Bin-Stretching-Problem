# Checks STRAT3 files: one adversary strategy against three policies on two bins, at every corner of its cell.
# python3 chk3a.py FILE...
import sys
from fractions import Fraction as Q
from collections import deque

def subset_sums(counts):
    sums = {0}
    for size, c in enumerate(counts, start=1):
        for _ in range(c):
            sums |= {s + size for s in sums}
    return sums

def check(path):
    lines = [ln.strip() for ln in open(path) if ln.strip() and not ln.startswith('#')]
    head = lines[0].split()
    if head[0] != 'STRAT3':
        return f'FAIL {path}: bad header'
    G, nv, Tn, Td = map(int, head[1:5])
    if not (1 <= G <= 62 and nv >= 1 and Tn > 0 and Td > 0):
        return f'FAIL {path}: bad parameters'
    V = []
    for k in range(nv):
        t = lines[1 + k].split()
        if t[0] != 'v' or len(t) != 4:
            return f'FAIL {path}: bad vertex line'
        v = tuple(int(x) for x in t[1:])
        if min(v) < 0 or sum(v) <= 0:
            return f'FAIL {path}: bad vertex weights'
        V.append(v)
    strat = {}
    for ln in lines[1 + nv:]:
        if ln == 'END':
            break
        a, b, c = ln.split('|')
        counts = tuple(int(x) for x in a.split())
        loads = tuple(int(x) for x in b.split())
        x = int(c)
        if len(counts) != G or len(loads) != 3 or min(counts) < 0:
            return f'FAIL {path}: bad state line {ln}'
        key = (counts, loads)
        if key in strat:
            return f'FAIL {path}: state listed twice {ln}'
        strat[key] = x
    if lines[-1] != 'END':
        return f'FAIL {path}: no END'

    def stops(N, loads):
        return all(Td * sum(vj * (N - aj) for vj, aj in zip(v, loads)) >= Tn * G * sum(v) for v in V)

    start = (tuple([0] * G), (0, 0, 0))
    seen = {start}
    queue = deque([start])
    leaves = 0
    used = set()
    worst = [None] * nv
    maxjobs = 0
    while queue:
        counts, loads = queue.popleft()
        N = sum(i * c for i, c in enumerate(counts, start=1))
        if any(not (0 <= a <= N - a) for a in loads):
            return f'FAIL {path}: impossible loads {counts} {loads}'
        maxjobs = max(maxjobs, sum(counts))
        if stops(N, loads):
            leaves += 1
            for k, v in enumerate(V):
                val = Q(sum(vj * (N - aj) for vj, aj in zip(v, loads)), G * sum(v))
                worst[k] = val if worst[k] is None else min(worst[k], val)
            continue
        key = (counts, loads)
        if key not in strat:
            return f'FAIL {path}: state not listed and not a stop: {counts} {loads}'
        used.add(key)
        x = strat[key]
        if not 1 <= x <= G:
            return f'FAIL {path}: size out of range at {key}'
        if not any(N - s <= G for s in subset_sums(counts) if s + x <= G):
            return f'FAIL {path}: infeasible size {x} at {key}'
        new_counts = list(counts)
        new_counts[x - 1] += 1
        new_counts = tuple(new_counts)
        options = []
        for a in loads:
            o = {a, min(a + x, N - a)}
            options.append(sorted(o))
        for a1 in options[0]:
            for a2 in options[1]:
                for a3 in options[2]:
                    nxt = (new_counts, (a1, a2, a3))
                    if nxt not in seen:
                        seen.add(nxt)
                        queue.append(nxt)
    unused = len(strat) - len(used)
    ws = ' '.join(f'{v}:{w}' for v, w in zip(V, worst))
    return (f'PASS {path}: G {G} target {Tn}/{Td} vertices {nv} states {len(seen)} leaves {leaves} '
            f'listed {len(strat)} unused {unused} max jobs {maxjobs} | min leaf value per vertex {ws}')

def main():
    ok = True
    for path in sys.argv[1:]:
        r = check(path)
        print(r)
        ok &= r.startswith('PASS')
    print('ALL PASS' if ok else 'SOME FAIL')
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
