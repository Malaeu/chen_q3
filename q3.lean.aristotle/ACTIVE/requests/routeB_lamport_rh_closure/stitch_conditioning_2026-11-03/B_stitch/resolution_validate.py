from resolution_control import *
from stitch import source
from functools import lru_cache
mp.mp.dps=100;m=40;mesh=256;L=mp.log(m);a=mp.log(m-1);delta=L-a
pts=sorted([mp.mpf(k)/mesh for k in range(int(mp.floor(L*mesh))+1)]+[a+j*delta/4 for j in range(5)]);length=[pts[i+1]-pts[i] for i in range(len(pts)-1)];d=len(length);gf=float_source('dh');gg,_=source('dh',L);g=lru_cache(None)(gg);rows=[]
pairs=[(0,0),(0,937),(0,938),(0,d-1),(936,937),(937,937),(937,938),(937,d-1),(938,938),(938,d-1),(d-2,d-1),(d-1,d-1)]
for i,j in pairs:
 value=(g(pts[i+1]-pts[j+1])-g(pts[i+1]-pts[j])-g(pts[i]-pts[j+1])+g(pts[i]-pts[j]))/mp.sqrt(length[i]*length[j]);x=np.array(list(map(float,pts)));ll=np.diff(x)
 val=(gf(x[i+1]-x[j+1])-gf(x[i+1]-x[j])-gf(x[i]-x[j+1])+gf(x[i]-x[j]))/np.sqrt(ll[i]*ll[j]);err=abs(mp.mpf(float(val))-value)
 rows.append(dict(i=i,j=j,MP100=mp.nstr(value,95),float64=float(val),absolute_discrepancy=mp.nstr(err,30)))
assert max(mp.mpf(r['absolute_discrepancy']) for r in rows)<mp.mpf('1e-7')
with (P/'resolution_source_checks.csv').open('w',newline='') as f:
 wr=csv.DictWriter(f,fieldnames=rows[0]);wr.writeheader();wr.writerows(rows)
print('source maxdifference',mp.nstr(max(mp.mpf(r['absolute_discrepancy']) for r in rows),25))
