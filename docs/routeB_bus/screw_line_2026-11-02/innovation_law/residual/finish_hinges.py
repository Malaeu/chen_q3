"""Attach precision and past-inertia labels, summarize the hinge diagnostic."""
import csv,json
from pathlib import Path
from residual import *
mp.mp.dps=80
rows=list(csv.DictReader((ROOT/'hinges.csv').open()));indices={}
for mesh in (32,64):
    h=mp.mpf(1)/mesh
    for world in ('zeta','dh','plant'):
        g,_=g_function(world,mp.mpf(6))
        r=r_from([g(k*h) for k in range(6*mesh+1)])
        states=levinson(r,set(range(1,6*mesh+1)))
        indices[world,mesh]={k:s[3] for k,s in states.items()}
for r in rows:
    r['source_dps']=80;r['predictor_precision']='float64 with selected MP80 replays'
    r['past_negative_index']=indices[r['world'],int(r['mesh'])][int(r['history'])]
    r['variational_minimum']=r['past_negative_index']==0
write('hinges.csv',rows)
summary=[]
for mesh in (32,64):
    for world in ('zeta','dh','plant'):
        rs=[r for r in rows if int(r['mesh'])==mesh and r['world']==world]
        summary.append(dict(world=world,mesh=mesh,rows=len(rs),positive_jump=sum(mp.mpf(r['predicted_jump'])>mp.mpf('1e-12') for r in rs),negative_jump=sum(mp.mpf(r['predicted_jump'])<-mp.mpf('1e-12') for r in rs),zero_jump=sum(abs(mp.mpf(r['predicted_jump']))<=mp.mpf('1e-12') for r in rs),max_jump_error=st(max(mp.mpf(r['absolute_error']) for r in rs)),max_linear_residual=max(float(r['toeplitz_solve_residual']) for r in rs),minimizer_rows=sum(r['variational_minimum'] for r in rs)))
(ROOT/'hinge_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
