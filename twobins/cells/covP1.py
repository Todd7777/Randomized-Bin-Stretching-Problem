# Checks that the cells of STRAT3 files cover p1 >= p2 >= p3 >= 0 and that every target is at least B.
# python3 covP1.py B FILE...
import sys
from fractions import Fraction as F

def read_cell(path):
    with open(path) as fh:
        head = fh.readline().split()
        assert head[0] == 'STRAT3' and len(head) == 5, f'{path}: header'
        k, tn, td = int(head[2]), int(head[3]), int(head[4])
        pts = []
        for _ in range(k):
            t = fh.readline().split()
            assert t[0] == 'v' and len(t) == 4, f'{path}: vertex line'
            a, b, c = (int(z) for z in t[1:])
            s = a + b + c
            assert min(a, b, c) >= 0 and s > 0, f'{path}: weights'
            pts.append((F(a, s), F(b, s), F(c, s)))
    return F(tn, td), pts

def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

def hull(points):
    pts = sorted(set((p[0], p[1]) for p in points))
    if len(pts) < 3:
        return pts
    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]

def area2(poly):
    return sum(poly[i][0] * poly[(i + 1) % len(poly)][1] - poly[(i + 1) % len(poly)][0] * poly[i][1]
               for i in range(len(poly)))

def cut(poly, a, b, keep_left):
    res = []
    n = len(poly)
    for i in range(n):
        p, q = poly[i], poly[(i + 1) % n]
        sp, sq = cross(a, b, p), cross(a, b, q)
        if not keep_left:
            sp, sq = -sp, -sq
        if sp >= 0:
            res.append(p)
        if (sp > 0 and sq < 0) or (sp < 0 and sq > 0):
            t = sp / (sp - sq)
            res.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return res

def minus(piece, cell):
    out, rest = [], piece
    for i in range(len(cell)):
        a, b = cell[i], cell[(i + 1) % len(cell)]
        o = cut(rest, a, b, keep_left=False)
        if len(o) >= 3 and area2(o) != 0:
            out.append(o)
        rest = cut(rest, a, b, keep_left=True)
        if len(rest) < 3 or area2(rest) == 0:
            break
    return out

def main():
    bound = F(sys.argv[1])
    D = hull([(F(1, 3), F(1, 3)), (F(1, 2), F(1, 2)), (F(1), F(0))])
    left = [D]
    total = F(0)
    for path in sys.argv[2:]:
        t, pts = read_cell(path)
        if t < bound:
            print(f'FAIL covP1: {path} target {t} < {bound}'); sys.exit(1)
        for p in pts:
            if not (p[0] >= p[1] >= p[2] >= 0):
                print(f'FAIL covP1: {path} corner {p} outside D'); sys.exit(1)
        C = hull(pts)
        if len(C) < 3:
            continue
        total += area2(C) / 2
        new = []
        for P in left:
            new += minus(P, C)
        left = new
    rem = sum((abs(area2(P)) / 2 for P in left), F(0))
    if rem == 0:
        print(f'PASS covP1: {len(sys.argv) - 2} cells cover D (area 1/12), all targets >= {bound}; '
              f'sum of cell areas / area of D = {float(total * 12):.4f}')
    else:
        print(f'FAIL covP1: uncovered area {rem} in {len(left)} pieces, first {[tuple(map(float, q)) for q in left[0]]}')
        sys.exit(1)

if __name__ == '__main__':
    main()
