import sys, json, math, time
from cat_solver import *
from fractions import Fraction as F
CATS=sys.argv[1]
files=[("cat_lp_m3_g3.json",3,F(7,6),2),("cat_lp_m3_g4_grb.json",4,F(19,16),3),("cat_lp_m3_g5_grb.json",5,F(47,40),4),
       ("cat_lp_m3_g6_nocross_vertex.json",6,F(143,120),9),("cat_lp2_m3_g7_full.json",7,F(403,336),6),
       ("cat_lp2_m3_g8_full.json",8,F(55,46),8),("cat_lp2_m3_g9_full.json",9,F(6971,5823),26),
       ("cat_lp2_m3_g10_nocross_vertex.json",10,F(1781,1485),14)]
for fn,g,val,ns in files:
    d=json.load(open(CATS+'/'+fn))
    cap=d.get('g',d.get('capacity'))
    S=[tuple(s) for s in d['streams']]
    pr=[F(x) for x in d['prior']]
    pos=[s for s,p in zip(S,pr) if p>0]
    den=1
    for q in pr: den=den*q.denominator//math.gcd(den,q.denominator)
    w=tuple(int(q*den) for q in pr)
    t=time.time()
    lb=F(min_weighted(S,3,w),den)/cap
    lot=[]
    for item in d['mixture']:
        if isinstance(item,dict): lot.append((tuple(item['costs']),F(item['weight'])))
        else: lot.append((tuple(item[0]),F(item[1])))
    att=all(attainable(S,3,c) for c,_ in lot)
    ub=max(sum(wt*c[j] for c,wt in lot) for j in range(len(S)))/cap
    feas=all(feasible(s,3,cap) for s in S)
    print(fn, 'cap',cap,'==g',cap==g,'streams',len(S),'positive',len(pos),'claimed',ns,'feasible',feas,'lb',lb,'ub',ub,'==val',lb==val==ub,'att',att,'%.1fs'%(time.time()-t))
