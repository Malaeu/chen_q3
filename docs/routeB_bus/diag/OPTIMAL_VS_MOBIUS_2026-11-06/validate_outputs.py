# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5", "scipy==1.17.0", "mpmath==1.3.0"]
# ///
"""Independent table checks and high-precision spot checks of saved intensities."""
import csv,gzip,json,math,time
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr,rankdata
import mpmath as mp
H=Path(__file__).resolve().parent
def read(n):return list(csv.DictReader((H/n).open()))
def main():
    start=time.monotonic(); coeff=read('part_a_coefficients.csv');zeros=read('per_zero.csv');j4=read('part_b_j4.csv')
    for N in [500,1000,2000,5000]:
        assert len([r for r in coeff if int(r['N'])==N])==N-1
    z5000=[r for r in zeros if int(r['N'])==5000]
    rng=np.random.default_rng(20261106);perms=np.asarray([rng.permutation(len(z5000)) for _ in range(1000)])
    checked=[]
    for N in [500,1000,2000,5000]:
        zr=[r for r in zeros if int(r['N'])==N];w=np.array([float(r['W_j']) for r in zr]);rw=rankdata(w);rw-=rw.mean()
        assert len(zr)==649
        assert all(float(r['cell_left'])<=float(r['gamma'])<=float(r['cell_right']) for r in zr)
        for variable,col in [('inverse_derivative_squared','inverse_derivative_sq'),('raw_local_min_gap','local_min_gap')]:
            x=np.array([float(r[col]) for r in zr]);rho=float(spearmanr(w,x).statistic);rx=rankdata(x);rx-=rx.mean();null=(rw[perms]@rx)/np.sqrt((rw@rw)*(rx@rx));p=(1+sum(abs(null)>=abs(rho)))/1001
            archived=next(r for r in j4 if int(r['N'])==N and r['variable']==variable)
            assert abs(rho-float(archived['rho']))<1e-12
            assert abs(p-float(archived['permutation_p_two_sided']))<1e-12
            checked.append({'N':N,'variable':variable,'rho':rho,'p':p})
    report={'coefficient_rows':len(coeff),'per_zero_rows':len(zeros),'permutation_replay':checked,'spot_checks':[]}
    # Spot-check direct zeta and the centered sum at independently evaluated mp40.
    chosen={};count=0
    with gzip.open(H/'t_grid.csv.gz','rt') as f:
        reader=csv.DictReader(f);columns=reader.fieldnames
        for row in reader:
            count+=1;t=float(row['t'])
            for target in [0.,500.,1000.]:
                if target not in chosen or abs(t-target)<abs(float(chosen[target]['t'])-target):chosen[target]=row
    report['grid_rows']=count;report['grid_columns']=columns
    mp.mp.dps=40
    for N in [500,5000]:
        cs=[r for r in coeff if int(r['N'])==N]
        ns=[int(r['n']) for r in cs];logs=[mp.log(n) for n in ns]
        for row in chosen.values():
            t=mp.mpf(float(row['t']));s=mp.mpf('.5')+1j*t;zeta=mp.zeta(s)
            terms=[mp.exp(-s*l)-mp.mpf(1)/n for n,l in zip(ns,logs)]
            for kind,col in [('opt','c_opt'),('taper','a_mobius_taper')]:
                D=mp.fsum(mp.mpf(float(r[col]))*v for r,v in zip(cs,terms))
                intensity=float(abs(1-zeta*D)**2);saved=float(row[f'I_{kind}_{N}']);error=abs(intensity-saved)
                assert error<=1e-9*max(1,abs(intensity)),(N,kind,t,error)
                report['spot_checks'].append({'N':N,'kind':kind,'t':float(t),'mp40_intensity':intensity,'saved_intensity':saved,'abs_difference':error})
    (H/'OUTPUT_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'[##############################] 100% ETA 0s table/permutation replay PASS ({time.monotonic()-start:.2f}s)')
if __name__=='__main__':main()
