# A second cover checker, by vertical slabs.
# python3 covP2.py B FILE...
import sys
from fractions import Fraction as F

def parse(path):
    rows = [r.split() for r in open(path).read().splitlines() if r.strip()]
    assert rows[0][0] == 'STRAT3'
    k = int(rows[0][2])
    target = F(int(rows[0][3]), int(rows[0][4]))
    pts = []
    for r in rows[1:1 + k]:
        assert r[0] == 'v'
        w = [int(z) for z in r[1:4]]
        tot = sum(w)
        assert tot > 0 and min(w) >= 0
        pts.append((F(w[0], tot), F(w[1], tot), F(w[2], tot)))
    return target, pts

def orient(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

def jarvis(points):
    P = sorted(set(points))
    if len(P) < 3:
        return P
    start = P[0]
    H = [start]
    cur = start
    while True:
        cand = P[0] if P[0] != cur else P[1]
        for q in P:
            if q == cur:
                continue
            o = orient(cur, cand, q)
            if o < 0 or (o == 0 and (q[0] - cur[0]) ** 2 + (q[1] - cur[1]) ** 2 > (cand[0] - cur[0]) ** 2 + (cand[1] - cur[1]) ** 2):
                cand = q
        if cand == start:
            break
        H.append(cand)
        cur = cand
        if len(H) > len(P):
            raise RuntimeError('hull loop')
    return H

def seg_cross_x(s, t):
    (x1, y1), (x2, y2) = s
    (x3, y3), (x4, y4) = t
    d = (x2 - x1) * (y4 - y3) - (y2 - y1) * (x4 - x3)
    if d == 0:
        return []
    u = ((x3 - x1) * (y4 - y3) - (y3 - y1) * (x4 - x3)) / d
    v = ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1)) / d
    if 0 <= u <= 1 and 0 <= v <= 1:
        return [x1 + u * (x2 - x1)]
    return []

def main():
    bound = F(sys.argv[1])
    cells = []
    for path in sys.argv[2:]:
        target, pts = parse(path)
        if target < bound:
            print(f'FAIL covP2: target of {path} below {bound}'); sys.exit(1)
        for p in pts:
            if not (p[0] >= p[1] and p[1] >= p[2] and p[2] >= 0):
                print(f'FAIL covP2: corner of {path} outside D'); sys.exit(1)
        H = jarvis([(p[0], p[1]) for p in pts])
        if len(H) >= 3:
            cells.append(H)
    Dc = [(F(1, 3), F(1, 3)), (F(1), F(0)), (F(1, 2), F(1, 2))]
    segs = []
    for H in cells + [Dc]:
        for i in range(len(H)):
            a, b = H[i], H[(i + 1) % len(H)]
            segs.append((a, b) if a <= b else (b, a))
    Z = set()
    for H in cells + [Dc]:
        for p in H:
            Z.add(p[0])
    segs.sort(key=lambda s: s[0][0])
    for i, s in enumerate(segs):
        for t in segs[i + 1:]:
            if t[0][0] > s[1][0]:
                break
            if max(s[0][1], s[1][1]) < min(t[0][1], t[1][1]) or max(t[0][1], t[1][1]) < min(s[0][1], s[1][1]):
                continue
            for x in seg_cross_x(s, t):
                Z.add(x)
    Z = sorted(z for z in Z if F(1, 3) <= z <= 1)
    assert Z[0] == F(1, 3) and Z[-1] == 1
    spans = [(min(p[0] for p in H), max(p[0] for p in H), H) for H in cells]
    spans.sort(key=lambda t: t[0])
    nslab = 0
    for xa, xb in zip(Z, Z[1:]):
        xm = (xa + xb) / 2
        nslab += 1
        lo, hi = (1 - xm) / 2, min(xm, 1 - xm)
        ivs = []
        for x0, x1, H in spans:
            if x0 >= xm:
                break
            if x1 <= xm:
                continue
            ys = []
            for i in range(len(H)):
                a, b = H[i], H[(i + 1) % len(H)]
                if (a[0] - xm) * (b[0] - xm) < 0:
                    ys.append(a[1] + (b[1] - a[1]) * (xm - a[0]) / (b[0] - a[0]))
            ivs.append((min(ys), max(ys)))
        ivs.sort()
        reach = lo
        for a, b in ivs:
            if a > reach:
                break
            reach = max(reach, b)
            if reach >= hi:
                break
        if reach < hi:
            print(f'FAIL covP2: at x = {xm} ~ {float(xm):.6f} the cells do not cover y in [{float(lo):.6f}, {float(hi):.6f}], '
                  f'reach {float(reach):.6f}')
            sys.exit(1)
    print(f'PASS covP2: {len(cells)} cells of positive area cover D, {nslab} slabs, all targets >= {bound}')

if __name__ == '__main__':
    main()
