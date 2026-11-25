# A second checker of STRAT3 files, with labelled bins.
# python3 chk3b.py FILE...
import sys
from fractions import Fraction as Q
from functools import lru_cache

def parse(path):
    with open(path) as f:
        rows = [r.split('#')[0].strip() for r in f]
    rows = [r for r in rows if r]
    t = rows[0].split()
    assert t[0] == 'STRAT3' and len(t) == 5, 'header'
    G, nv, tn, td = (int(z) for z in t[1:])
    assert 1 <= G <= 62 and nv >= 1 and tn > 0 and td > 0, 'parameters'
    verts = []
    for r in rows[1:1 + nv]:
        t = r.split()
        assert t[0] == 'v' and len(t) == 4, 'vertex line'
        w = [int(z) for z in t[1:]]
        assert min(w) >= 0 and sum(w) > 0, 'vertex weights'
        verts.append(tuple(Q(z, sum(w)) for z in w))
    assert rows[-1] == 'END', 'END'
    table = {}
    for r in rows[1 + nv:-1]:
        parts = r.split('|')
        assert len(parts) == 3, 'state line'
        cnt = tuple(int(z) for z in parts[0].split())
        sm = tuple(int(z) for z in parts[1].split())
        assert len(cnt) == G and len(sm) == 3, 'state line length'
        assert (cnt, sm) not in table, 'duplicate state'
        table[(cnt, sm)] = int(parts[2])
    return G, Q(tn, td), verts, table

def splittable(G, cnt):
    sizes = [(i + 1, c) for i, c in enumerate(cnt) if c]
    total = sum(s * c for s, c in sizes)
    if total > 2 * G:
        return False

    @lru_cache(maxsize=None)
    def go(k, load):
        if k == len(sizes):
            return load <= G and total - load <= G
        s, c = sizes[k]
        return any(go(k + 1, load + s * t) for t in range(c + 1) if load + s * t <= G)
    return go(0, 0)

def check(path):
    G, xi, verts, table = parse(path)
    target = xi * G
    memo = {}
    stats = {'leaves': 0, 'internal': 0}
    used = set()
    sys.setrecursionlimit(10000)

    def walk(cnt, bins):
        key = (cnt, bins)
        if key in memo:
            return
        memo[key] = True
        top = tuple(max(b) for b in bins)
        if all(sum(p * c for p, c in zip(vert, top)) >= target for vert in verts):
            stats['leaves'] += 1
            return
        stats['internal'] += 1
        small = tuple(min(b) for b in bins)
        look = (cnt, small)
        if look not in table:
            raise AssertionError(f'no move listed at {cnt} {small}')
        used.add(look)
        x = table[look]
        assert 1 <= x <= G, 'size out of range'
        new = list(cnt)
        new[x - 1] += 1
        new = tuple(new)
        assert splittable(G, new), f'infeasible size {x} at {cnt}'
        for choice in range(8):
            nb = []
            for j in range(3):
                b0, b1 = bins[j]
                nb.append((b0 + x, b1) if (choice >> j) & 1 == 0 else (b0, b1 + x))
            walk(new, tuple(nb))

    try:
        walk(tuple([0] * G), ((0, 0), (0, 0), (0, 0)))
    except AssertionError as e:
        return f'FAIL {path}: {e}'
    return (f'PASS {path}: G {G} target {xi} vertices {len(verts)} labelled states {len(memo)} '
            f'leaves {stats["leaves"]} internal {stats["internal"]} listed {len(table)} used {len(used)}')

def main():
    ok = True
    for path in sys.argv[1:]:
        r = check(path)
        print(r)
        ok = ok and r.startswith('PASS')
    print('ALL PASS' if ok else 'SOME FAIL')
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
