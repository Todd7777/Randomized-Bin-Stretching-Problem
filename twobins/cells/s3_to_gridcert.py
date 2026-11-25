# Writes a STRAT3 file as one GRIDCERT file per corner of its cell, for ../gcheck.cpp.
# python3 s3_to_gridcert.py FILE.s3 PREFIX
import sys
from collections import deque

path, prefix = sys.argv[1], sys.argv[2]
L = [ln.strip() for ln in open(path) if ln.strip()]
G, nv, Tn, Td = map(int, L[0].split()[1:5])
V = [tuple(int(x) for x in L[1 + k].split()[1:4]) for k in range(nv)]
strat = {}
for ln in L[1 + nv:]:
    if ln == 'END':
        break
    a, b, c = ln.split('|')
    strat[(tuple(int(x) for x in a.split()), tuple(int(x) for x in b.split()))] = int(c)

def stop(N, a):
    return all(Td * sum(v[j] * (N - a[j]) for j in range(3)) >= Tn * G * sum(v) for v in V)

ids = {}
order = []
root = (tuple([0] * G), (0, 0, 0))
ids[root] = 0
order.append(root)
q = deque([root])
lines = []
body = {}
while q:
    st = q.popleft()
    counts, a = st
    N = sum((i + 1) * c for i, c in enumerate(counts))
    if stop(N, a):
        body[st] = None
        continue
    x = strat[st]
    nc = list(counts)
    nc[x - 1] += 1
    nc = tuple(nc)
    succ = []
    for chi in range(8):
        b = tuple(a[j] if (chi >> j) & 1 else min(a[j] + x, N - a[j]) for j in range(3))
        nxt = (nc, b)
        if nxt not in ids:
            ids[nxt] = len(order)
            order.append(nxt)
            q.append(nxt)
        succ.append(ids[nxt])
    body[st] = (x, succ)
for k, v in enumerate(V):
    w = [Td * vj for vj in v]
    theta = Tn * G * sum(v)
    with open(f'{prefix}.v{k}.cert', 'w') as f:
        f.write(f'GRIDCERT {G} 3 {w[0]} {w[1]} {w[2]} {theta} {len(order)}\n')
        for st in order:
            counts, a = st
            N = sum((i + 1) * c for i, c in enumerate(counts))
            head = f'{N} ' + ' '.join(map(str, counts)) + f' {a[0]} {a[1]} {a[2]} {theta}'
            if body[st] is None:
                f.write(head + ' S\n')
            else:
                x, succ = body[st]
                f.write(head + f' J {x} ' + ' '.join(map(str, succ)) + '\n')
print(f'{path}: {len(order)} states, {nv} certificates')
