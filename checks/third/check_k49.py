import sys, json, time, math
from cat_solver import *
from fractions import Fraction as F
d=json.load(open(sys.argv[1]+'/r3_k49_cap60.json'))
g=d['capacity']; m=d['bins']
S=[tuple(s) for s in d['streams']]
print('n', len(S), 'distinct', len(set(S)), 'cap', g)
okp = all(len(p)==len(s) and all(sum(z for z,b in zip(s,p) if b==k)<=g for k in range(m)) for s,p in zip(S,d['packing']))
print('stated packings valid', okp)
pr=[F(x) for x in d['prior']]
den=1
for q in pr: den=den*q.denominator//math.gcd(den,q.denominator)
w=tuple(int(q*den) for q in pr)
assert all(F(wi,den)==q for wi,q in zip(w,pr))
t=time.time()
mw=min_weighted(S,m,w)
val=F(mw,den)/g
print('prior bound (capacity units)', val, val==F(d['value']), float(val), '%.1fs'%(time.time()-t))
print('> 1.20202:', val > F(120202,100000))
L=[(tuple(x['costs']),F(x['weight'])) for x in d['lottery']]
t=time.time()
att=[attainable(S,m,c) for c,_ in L]
print('lottery rows attainable', all(att), '%.1fs'%(time.time()-t))
mix=[sum(wt*c[j] for c,wt in L)/g for j in range(len(S))]
print('max mixture', max(mix), max(mix)==val, ' min', min(mix))
T=Trie(S)
shared=sum(1 for v in range(1,len(T.kids)) if len(T.below[v])>=2)
print('trie nodes', len(T.kids)-1, 'shared prefixes', shared)
