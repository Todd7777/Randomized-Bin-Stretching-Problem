# A third check of the priors: every policy has expected cost at least 7/6.
# python3 priorcheck.py PRIOR.json...
import sys, json, glob
from fractions import Fraction as F
from functools import lru_cache
def feasible(s):
    S=sum(s); sums={F(0)}
    for x in s: sums|={a+x for a in sums}
    return S<=2 and any(S-1<=a<=1 for a in sums)
def value(streams):
    W=sum(w for _,w in streams)
    for s,_ in streams: assert feasible(s), s
    trie={}
    ends={}
    for s,w in streams:
        ends[s]=ends.get(s,0)+w
        for i in range(1,len(s)+1): trie.setdefault(s[:i-1],set()).add(s[i-1])
    @lru_cache(None)
    def best(node,a,b):
        tot=ends.get(node,0)*max(a,b)
        for x in trie.get(node,()):
            c=node+(x,)
            tot+=min(best(c,*sorted((a+x,b))),best(c,*sorted((a,b+x))))
        return tot
    return F(best((),F(0),F(0)),W)
def grid(lines,g):
    out=[]
    for L in lines:
        L=L.strip()
        if not L or L.startswith('#'): continue
        s,w=L.split()
        out.append((tuple(F(int(t),g) for t in s.split(',')),int(w)))
    return out
def show(name,st,expect):
    v=value(st); print(f"{name}: {v} expect {expect} {'OK' if v==F(expect) else 'MISMATCH'}")
show('ex76',[((F(1,3),F(1,3),F(1)),1),((F(1,3),F(1,3),F(2,3),F(2,3)),1)],'7/6')
show('g4',grid(['1,1,1,1,4 1','1,1,1,3,2 1'],4),'9/8')
show('g5',grid(['2,1,1,1,5 1','2,1,1,3,3 2','2,1,1,4,2 1'],5),'23/20')
show('g7',grid(['2,1,2,2,7 1','2,1,2,5,4 1'],7),'8/7')
show('g8alt',grid(['3,3,5,5 2','3,3,1,1,8 1','3,3,1,2,7 1'],8),'37/32')
show('cv(1/13,1/26)',grid(['6,3,3,8,14,18,78 1','6,3,3,8,14,18,52,52 1'],78),'7/6')
show('cv(2/17,4/51)',grid(['6,4,11,8,5,12,51 1','6,4,11,8,5,34,34 1'],51),'7/6')
show('cv(5/27,5/27)',grid(['5,5,4,4,4,2,27 1','5,5,4,4,18,18 1'],27),'7/6')
bad=0
for f in sys.argv[1:]:
    d=json.load(open(f)); st=[(tuple(F(x) for x in p['stream']),p['w']) for p in d['prior']]
    v=value(st)
    if v!=F(d['lower']) or v!=F(7,6): bad+=1; print('BAD',f,v)
    else: print(f+':', v)
print('catval priors checked:',len(sys.argv[1:]),'bad',bad)
sys.exit(1 if bad or not sys.argv[1:] else 0)
