"""Prespecified exponential fit, mesh comparison and source checks."""
from pathlib import Path
import csv,json
import mpmath as mp
from scan import source
OUT=Path(__file__).resolve().parent
mp.mp.dps=100

def fit(rows,lo,hi):
    pair=[(mp.mpf(r['t']),mp.log(mp.mpf(r['sigma2']))) for r in rows if lo<=mp.mpf(r['t'])<=hi and mp.mpf(r['sigma2'])>0]
    xx=[x for x,y in pair];yy=[y for x,y in pair];N=len(xx)
    xb=mp.fsum(xx)/N;yb=mp.fsum(yy)/N
    slope=mp.fsum((x-xb)*(y-yb) for x,y in pair)/mp.fsum((x-xb)**2 for x in xx)
    intercept=yb-slope*xb;res=[y-intercept-slope*x for x,y in pair]
    R2=1-mp.fsum(v*v for v in res)/mp.fsum((y-yb)**2 for y in yy)
    rel=max(abs(v) for v in res)/(abs(slope)*(hi-lo))
    return {'lo':lo,'hi':hi,'points':N,'slope':float(slope),'intercept':float(intercept),'r_squared':float(R2),'max_residual_over_fitted_range':float(rel),'within_grid_pass':bool(R2>=mp.mpf('.99') and rel<=mp.mpf('.1'))}

def main():
    fits=[];summary=[];monotonic=[]
    for mesh in (32,64,128,256):
        for world in ('zeta','dh','plant'):
            path=OUT/f'{world}_mesh{mesh}_dps100.csv'
            if not path.exists():continue
            rows=list(csv.DictReader(path.open()));data=json.loads(path.with_suffix('.json').read_text())
            if world=='zeta':
                for lo,hi in ((1,3),(3,6),(1,6)):fits.append({'mesh':mesh,**fit(rows,lo,hi)})
            positive_prefix=[r for r in rows if r['positive_history']=='True']
            monotonic.append({'mesh':mesh,'world':world,'positive_prefix_rows':len(positive_prefix),'positive_prefix_nonincreasing':all(mp.mpf(b['sigma2'])<=mp.mpf(a['sigma2']) for a,b in zip(positive_prefix,positive_prefix[1:])),'largest_positive_history_abs_reflection':float(max(abs(mp.mpf(r['reflection'])) for r in positive_prefix))})
            summary.append({'mesh':mesh,'world':world,'first_negative_time':data['first_negative_time'],'first_negative_prefix':data['first_negative_prefix'],'negative_inertia_final':data['negative_inertia_final'],'sigma2_initial':data['first_sigma2'],'sigma2_final':data['last_sigma2'],'final_over_local':rows[-1]['sigma2_over_local']})
    for name,rows in [('fits',fits),('summary',summary),('monotonic',monotonic)]:
        with (OUT/(name+'.csv')).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    cross=[]
    for lo,hi in ((1,3),(3,6),(1,6)):
        block=[r for r in fits if r['lo']==lo and r['hi']==hi];slopes=sorted(abs(r['slope']) for r in block);median=(slopes[1]+slopes[2])/2 if len(slopes)==4 else sum(slopes)/len(slopes)
        frac=(max(slopes)-min(slopes))/median
        cross.append({'lo':lo,'hi':hi,'slope_range_over_median_absolute_slope':frac,'across_mesh_pass':frac<=.1,'all_within_mesh_pass':all(r['within_grid_pass'] for r in block)})
    source_checks=[]
    for world in ('zeta','dh','plant'):
        g,atoms=source(world,6);alpha=mp.mpf('1.5') if world=='dh' else mp.mpf('.5')
        c=-mp.euler-mp.log(8*mp.pi/(5 if world=='dh' else 1))+(1 if world=='dh' else -1)*mp.pi/2
        for t in (mp.mpf(1)/256,mp.log(2),mp.log(8),mp.mpf(6)):
            integrand=lambda s:mp.mpf('.5') if not s else s*mp.exp(-alpha*s)/(-mp.expm1(-2*s))
            arch=2*mp.quad(integrand,[0,t])+2*t*mp.quad(lambda s:mp.exp(-alpha*s)/(-mp.expm1(-2*s)),[t,mp.inf])
            arith=-2*mp.fsum(weight*(t-a) for a,weight,n in atoms if a<t)
            pole=32*mp.sinh(t/4)**2 if world!='dh' else 0
            direct=-(c*t+arch+arith+pole)/2
            if world=='plant':
                w=2*mp.pi/mp.log(2)+mp.j/4;direct+=4*mp.re((mp.cos(w*t)-1)/w**2)
            source_checks.append({'world':world,'t':mp.nstr(t,30),'error':mp.nstr(abs(direct-g(t)),30)})
    precision=[]
    for world in ('zeta','dh','plant'):
        low=OUT/f'{world}_mesh256_dps100.csv';high=OUT/f'{world}_mesh256_dps160.csv'
        if not high.exists():continue
        aa=list(csv.DictReader(low.open()));bb=list(csv.DictReader(high.open()))
        change=max(abs(mp.mpf(a['sigma2'])-mp.mpf(b['sigma2']))/abs(mp.mpf(b['sigma2'])) for a,b in zip(aa,bb))
        precision.append({'world':world,'mesh':256,'rows':len(aa),'max_relative_sigma_change':mp.nstr(change,30),'all_negative_inertia_match':all(a['negative_inertia']==b['negative_inertia'] for a,b in zip(aa,bb))})
    result={'status':'DIAGNOSTIC_NEVER_A_PROOF','exponential_law_tests':cross,'source_integral_checks':source_checks,'precision_checks':precision}
    (OUT/'analysis.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
