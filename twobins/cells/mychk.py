# A fourth checker of STRAT3 files.
# python3 mychk.py B FILE...
import sys
from fractions import Fraction as F

def run(path, X):
    with open(path) as fh:
        raw = [l.strip() for l in fh]
    raw = [l for l in raw if l and not l.startswith('#')]
    h = raw[0].split()
    if h[0] != 'STRAT3':
        return 'FAIL header'
    g, nv, tn, td = (int(t) for t in h[1:5])
    if F(tn, td) < X:
        return 'FAIL header bound %s below %s' % (F(tn, td), X)
    P = []
    for k in range(nv):
        t = raw[1 + k].split()
        assert t[0] == 'v' and len(t) == 4
        v = [int(x) for x in t[1:]]
        if min(v) < 0 or sum(v) == 0:
            return 'FAIL corner'
        P.append(tuple(F(x, sum(v)) for x in v))
    if raw[-1] != 'END':
        return 'FAIL no END'
    S = {}
    for l in raw[1 + nv:-1]:
        a, b, c = l.split('|')
        cnt = tuple(int(x) for x in a.split())
        ld = tuple(int(x) for x in b.split())
        if len(cnt) != g or len(ld) != 3:
            return 'FAIL line'
        if (cnt, ld) in S:
            return 'FAIL duplicate'
        S[(cnt, ld)] = int(c)
    gX = X * g
    least = [None] * nv
    full = (1 << (g + 1)) - 1
    start = (tuple([0] * g), (0, 0, 0))
    stack = [(start, 1)]
    seen = {start}
    nleaf = 0
    while stack:
        (cnt, ld), mask = stack.pop()
        N = sum((i + 1) * c for i, c in enumerate(cnt))
        if N > 2 * g or any(not (0 <= a and 2 * a <= N) for a in ld):
            return 'FAIL bad state'
        if not any((mask >> t) & 1 for t in range(max(0, N - g), g + 1)):
            return 'FAIL infeasible state reached'
        vals = [sum(p[j] * (N - ld[j]) for j in range(3)) for p in P]
        if all(val >= gX for val in vals):
            nleaf += 1
            for i, val in enumerate(vals):
                if least[i] is None or val < least[i]:
                    least[i] = val
            continue
        if (cnt, ld) not in S:
            return 'FAIL reached unlisted non-leaf %s %s N=%d' % (cnt, ld, N)
        s = S[(cnt, ld)]
        if not (1 <= s <= g):
            return 'FAIL size out of range'
        m2 = mask | (mask << s)
        N2 = N + s
        if not any((m2 >> t) & 1 for t in range(max(0, N2 - g), g + 1)):
            return 'FAIL infeasible size %d at %s %s' % (s, cnt, ld)
        c2 = list(cnt); c2[s - 1] += 1; c2 = tuple(c2)
        for chi in range(8):
            nl = []
            for j in range(3):
                a = ld[j]
                if (chi >> j) & 1:
                    nl.append(a)
                else:
                    nl.append(min(a + s, N - a))
            st = (c2, tuple(nl))
            if st not in seen:
                seen.add(st)
                stack.append((st, m2))
    lv = [str(x / g) for x in least]
    return 'PASS g=%d corners=%d visited=%d leaves=%d listed=%d minval=%s' % (g, nv, len(seen), nleaf, len(S), min(F(x) / g for x in least))

if __name__ == '__main__':
    X = F(sys.argv[1])
    bad = 0
    for p in sys.argv[2:]:
        r = run(p, X)
        if not r.startswith('PASS'):
            bad += 1
        print(p.split('/')[-1], r, flush=True)
    print('SUMMARY files=%d fail=%d' % (len(sys.argv) - 2, bad))
