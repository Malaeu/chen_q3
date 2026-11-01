import push as c
import json,csv
mp=c.mp
L=mp.log(8);K,D=c.matrices(L,68);E=c.even(K,68,68)
rows=[]
for N in (48,52,56,60,64,68):
 ev,V=mp.eigsy(E[:N+1,:N+1]);v=V[:,0]
 edge=(v[0]+mp.sqrt(2)*mp.fsum(v[j] for j in range(1,N+1)))/mp.sqrt(L)
 edge2=edge**2;R=edge2/ev[0]
 row=dict(N=N,L=mp.nstr(L,mp.mp.dps),dps=mp.mp.dps,order=c.ORDER,lambda0=mp.nstr(ev[0],mp.mp.dps),edge_squared=mp.nstr(edge2,mp.mp.dps),R=mp.nstr(R,mp.mp.dps),R_over_L=mp.nstr(R/L,mp.mp.dps))
 rows.append(row);print(json.dumps(row),flush=True)
 (c.OUT/f'push_edge_dps{mp.mp.dps}_gl{c.ORDER}.json').write_text(json.dumps(rows,indent=2)+'\n')
with (c.OUT/f'push_edge_dps{mp.mp.dps}_gl{c.ORDER}.csv').open('w') as f:
 cw=csv.DictWriter(f,fieldnames=list(rows[0]));cw.writeheader();cw.writerows(rows)
