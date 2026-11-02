"""Boundary derivatives and heat-curve probes from saved resolution ground vectors."""
from pathlib import Path
import sys,json,csv
import numpy as np
import mpmath as mp
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(OUT.parent));import heat_fit as heat

def write_csv(path,rows):
    with path.open('w',newline='') as f:
        cw=csv.DictWriter(f,fieldnames=list(rows[0]));cw.writeheader();cw.writerows(rows)

def main():
    source=json.loads((OUT/'main_results.json').read_text());mp.mp.dps=source['results'][0]['dps'];fmt=lambda x:mp.nstr(x,mp.mp.dps)
    points=[];gridrows=[];boundaries=[]
    for wm in(8,12):
        cells=[r for r in source['results'] if r['window_m']==wm];NN=max(r['N'] for r in cells);L=mp.log(wm)
        cache=Path(cells[0]['spectral_cache']['path']);tt,ww=heat.spectral_nodes(cells[0]['spectral_order'],cells[0]['T'],4,cache)
        BW=heat.projection_matrix(dict(m=NN,L=L),tt,ww)
        for cell in cells:
            N=cell['N'];B=BW[:N+1,:];f=mp.matrix(cell['ground_even_coefficients'])
            for st in('0','0.0001','0.001','0.003','0.01'):
                s=mp.mpf(st);p,dp=heat.heat_vectors(B,tt,s);a=mp.fdot(f,p);b=mp.fdot(p,p);W=a*a/b
                derivative=2*a*(mp.fdot(f,dp)*b-a*mp.fdot(p,dp))/(b*b)
                row=dict(window_m=wm,N=N,s=st,W=fmt(W),residual_squared=fmt(1-W),W_derivative=fmt(derivative),residual_squared_derivative=fmt(-derivative),dps=mp.mp.dps)
                points.append(row)
                if s==0:
                    boundaries.append(dict(window_m=wm,N=N,at_boundary=mp.mpf(cell['s_star'])==0,Wprime0=fmt(derivative),residual_squared_right_derivative=fmt(-derivative),boundary_KKT_for_maximum=derivative<=0,all_s_ge_1_overlap_upper=cell['all_s_ge_1_overlap_upper']))
            bn=np.array(B.tolist(),dtype=float);fn=np.array(list(f),dtype=float);tn=np.array([float(t*t) for t in tt])
            grid=np.unique(np.concatenate(([0.],np.linspace(0,.02,201),np.geomspace(.02,1.,81))))
            for s in grid:
                p=bn@np.exp(-s*tn);dot=np.dot(fn,p);W=dot*dot/np.dot(p,p);e=fn-p*dot/np.dot(p,p)
                gridrows.append(dict(window_m=wm,N=N,s=s,W_float=W,residual_squared_float=np.dot(e,e),scope='float64 search only; high-precision values in curve_probes.csv'))
            print('BOUNDARY',wm,N,boundaries[-1]['Wprime0'],flush=True)
    write_csv(OUT/'curve_probes.csv',points);write_csv(OUT/'boundary_conditions.csv',boundaries);write_csv(OUT/'grid.csv',gridrows)
    (OUT/'boundary_checks.json').write_text(json.dumps(dict(boundaries=boundaries,probes=points,scope='Boundary KKT and sampled curve; no interval proof of compact global optimum'),indent=2)+'\n')
if __name__=='__main__':main()
