"""Constant carrier control: no eigenproblem and no source-seeded root discovery."""
from pathlib import Path
import sys,csv,json
import mpmath as mp
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P/'roots'))
from census import references,match
def main():
    mp.mp.dps=220;rows=[]
    for m in [16,24,40,80,160,300]:
        L=mp.log(m);om=2*mp.pi/L;Omega=m*om
        for label,T in [('primary',(1+(1+mp.log(L))/(4*L))*Omega),('Omega',Omega),('0.8Omega',mp.mpf('.8')*Omega)]:
            # f=1/sqrt(L) on the literal window has exactly the positive sinc zeros.
            nmax=m-1 if label=='Omega' else ((4*m+4)//5-1 if label=='0.8Omega' else int(mp.ceil(T/om))-1)
            roots=[dict(z_re_mp=n*om,z_im_mp=mp.mpf(0),root_id=f'lattice_{n}',kind='forced_external' if n>m else 'internal_constant_zero') for n in range(1,nmax+1)]
            for world in ['zeta','dh','plant']:
                pairs,s=match(roots,references(world),T)
                rows.append(dict(world=world,m=m,cutoff=label,T=mp.nstr(T,30),control='unit_L2_constant_carrier',source_count=s['source_count'],fourier_count=s['fourier_strip_count'],assigned_count=s['matched_count'],matched_under_1e_6=s['matched_under_1e_6'],source_unrecovered_at_1e_6=s['source_unrecovered_at_1e_6'],max_abs_deviation=s['max_abs_deviation']))
    with (P/'CARRIER_CONTROL.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    (P/'CARRIER_CONTROL.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',scope='Six selected windows, all three worlds/cutoffs; no new eigenproblem.',rows=len(rows),max_close_source_matches=max(r['matched_under_1e_6'] for r in rows)),indent=2)+'\n')
    print('control rows',len(rows),'max close matches',max(r['matched_under_1e_6'] for r in rows))
if __name__=='__main__':main()
