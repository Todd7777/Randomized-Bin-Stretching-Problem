# A third cover checker, by horizontal slabs.
# python3 mycover.py FILE...
import sys
from fractions import Fraction as F
from itertools import combinations

def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

def hull(pts):
    pts = sorted(set(pts))
    if len(pts) <= 2:
        return pts
    start = pts[0]
    H = [start]
    cur = start
    while True:
        cand = None
        for q in pts:
            if q == cur:
                continue
            if cand is None:
                cand = q; continue
            c = cross(cur, cand, q)
            if c < 0 or (c == 0 and (q[0]-cur[0])**2 + (q[1]-cur[1])**2 > (cand[0]-cur[0])**2 + (cand[1]-cur[1])**2):
                cand = q
        if cand == start:
            break
        H.append(cand); cur = cand
        if len(H) > len(pts):
            raise RuntimeError('hull loop')
    return H

def chord_edges(H, y):
    xs = []
    n = len(H)
    for i in range(n):
        a, b = H[i], H[(i + 1) % n] if n > 1 else H[i]
        if (a[1] - y) * (b[1] - y) <= 0:
            if a[1] == b[1]:
                if a[1] == y:
                    xs += [a[0], b[0]]
            else:
                xs.append(a[0] + (b[0] - a[0]) * (y - a[1]) / (b[1] - a[1]))
    return (min(xs), max(xs)) if xs else None

def chord_pairs(P, y):
    xs = []
    for a in P:
        if a[1] == y:
            xs.append(a[0])
    for a, b in combinations(P, 2):
        if (a[1] - y) * (b[1] - y) < 0:
            xs.append(a[0] + (b[0] - a[0]) * (y - a[1]) / (b[1] - a[1]))
    return (min(xs), max(xs)) if xs else None

def seg_int_y(a, b, c, d):
    r = (b[0]-a[0], b[1]-a[1]); s = (d[0]-c[0], d[1]-c[1])
    den = r[0]*s[1] - r[1]*s[0]
    qp = (c[0]-a[0], c[1]-a[1])
    if den == 0:
        return []
    t = (qp[0]*s[1] - qp[1]*s[0]) / den
    u = (qp[0]*r[1] - qp[1]*r[0]) / den
    if 0 <= t <= 1 and 0 <= u <= 1:
        return [a[1] + t * r[1]]
    return []

def main(files):
    cells = []
    bad_out = 0
    for f in files:
        P = []
        for l in open(f):
            t = l.split()
            if t and t[0] == 'v':
                v = [int(x) for x in t[1:4]]
                W = sum(v)
                p = [F(x, W) for x in v]
                if min(p) < 0:
                    print('corner outside simplex', f, v); return 1
                if not (p[0] >= p[1] >= p[2]):
                    bad_out += 1
                P.append((p[1], p[2]))
        cells.append((f, P, hull(P)))
    for f, P, H in cells:
        for q in P:
            if q in H:
                continue
            n = len(H)
            if n >= 3 and not all(cross(H[i], H[(i+1)%n], q) >= 0 for i in range(n)):
                print('hull error', f); return 1
    Dv = [(F(0), F(0)), (F(1, 2), F(0)), (F(1, 3), F(1, 3))]
    edges = [(Dv[i], Dv[(i+1)%3]) for i in range(3)]
    for f, P, H in cells:
        n = len(H)
        if n >= 2:
            edges += [(H[i], H[(i+1)%n]) for i in range(n)]
    ev = {F(0), F(1, 3)}
    for f, P, H in cells:
        for q in H:
            if 0 <= q[1] <= F(1, 3):
                ev.add(q[1])
    E = [(min(a[1], b[1]), max(a[1], b[1]), min(a[0], b[0]), max(a[0], b[0]), a, b) for a, b in edges]
    E.sort()
    cnt = 0
    for i in range(len(E)):
        y0, y1, x0, x1, a, b = E[i]
        for k in range(i + 1, len(E)):
            z0, z1, u0, u1, c, d = E[k]
            if z0 > y1:
                break
            if u0 > x1 or u1 < x0:
                continue
            for y in seg_int_y(a, b, c, d):
                cnt += 1
                if 0 <= y <= F(1, 3):
                    ev.add(y)
    ev = sorted(ev)
    gaps = 0
    for lo, hi in zip(ev, ev[1:]):
        y = (lo + hi) / 2
        L, R = y, (1 - y) / 2
        iv = []
        for f, P, H in cells:
            c1 = chord_edges(H, y) if len(H) >= 3 else chord_pairs(P, y)
            c2 = chord_pairs(P, y)
            if c1 != c2:
                print('chord mismatch', f, y, c1, c2); return 1
            if c1:
                iv.append(c1)
        iv.sort()
        reach = L
        for a, b in iv:
            if a > reach:
                break
            reach = max(reach, b)
        if reach < R:
            gaps += 1
            print('GAP at y=%s (%.6f): covered up to x=%s of [%s, %s]' % (y, float(y), reach, L, R))
            if gaps > 5:
                break
    print('cells=%d corners=%d corners_outside_D=%d edges=%d events=%d slabs=%d gaps=%d -> %s' % (
        len(cells), sum(len(P) for _, P, _ in cells), bad_out, len(edges), len(ev), len(ev) - 1, gaps,
        'COVER PASS' if gaps == 0 else 'COVER FAIL'))
    return 0 if gaps == 0 else 1

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
