"""Finite Vieta/boundary-curvature check. No new eigensolve or source bound."""
from pathlib import Path
import json,csv,hashlib,argparse
import mpmath as mp
P=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--all',action='store_true');a=ap.parse_args();rows=[]
    for path in sorted((P/'roots/results').glob('*.json')):
        z=json.loads(path.read_text());m=z['m'];world=z['world'];parity=z['parity']
        if world not in ['zeta','dh','plant']:continue
        if not a.all and m not in [16,24,40,80,160,300]:continue
        f=P/'spectra/vectors'/f'{world}_m{m}.json';raw=f.read_bytes();s=json.loads(raw)
        if hashlib.sha256(raw).hexdigest()!=z['source_vector_sha256']:continue
        mp.mp.dps=max(240,int(s['precision_dps'])+60);L=mp.mpf(s['L']);om=2*mp.pi/L
        c=list(map(mp.mpf,s['v_'+parity+'0']));nmax=m;sum_modes=om**2*m*(m+1)*(2*m+1)/6
        if parity=='even':
            boundary=(c[0]+mp.sqrt(2)*mp.fsum(c[1:]))/mp.sqrt(L)
            deriv=-mp.sqrt(2/L)*mp.fsum(c[n]*(n*om)**2 for n in range(1,m+1))
            label='f_second_over_f'
        else:
            boundary=mp.sqrt(2/L)*mp.fsum(c[n-1]*n*om for n in range(1,m+1))
            deriv=-mp.sqrt(2/L)*mp.fsum(c[n-1]*(n*om)**3 for n in range(1,m+1))
            label='f_third_over_f_prime'
        if not boundary:continue
        ratio=deriv/boundary;poly=[r for r in z['roots'] if r['kind'].startswith('polynomial')]
        zroots=[mp.mpc(r['z_re'],r['z_im']) for r in poly];value=mp.fsum(t*t for t in zroots);expected=sum_modes+ratio
        rel=abs(value-expected)/max(1,abs(value),abs(expected));assert rel<mp.mpf('1e-130'),(m,world,parity,rel)
        positive=[mp.re(t) for t in zroots if mp.im(t)==0 and mp.re(t)>0]
        T=(1+(1+mp.log(L))/(4*L))*m*om
        rows.append(dict(world=world,m=m,parity=parity,degree=len(poly),boundary_ratio_kind=label,boundary_value_or_first_derivative=mp.nstr(boundary,30),boundary_curvature_ratio=mp.nstr(ratio,30),sum_squared_numerator_roots=mp.nstr(mp.re(value),30),Vieta_relative_replay_error=mp.nstr(rel,15),largest_positive_numerator_root=mp.nstr(max(positive),30) if positive else '',largest_positive_root_over_T=mp.nstr(max(positive)/T,20) if positive else '',positive_numerator_roots_beyond_T=sum(x>=T for x in positive)))
    with (P/'BOUNDARY_ROOTS.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    (P/'BOUNDARY_ROOTS.json').write_text(json.dumps(dict(status='FINITE_VIETA_REPLAY_PASS',scope='All tested frozen-vector numerator polynomials; one-sided interior derivatives at b=L/2. Universal finite algebra, not an arithmetic inequality.',rows=len(rows),max_relative_error=max(float(r['Vieta_relative_replay_error']) for r in rows),full_grid=a.all),indent=2)+'\n')
    print('Vieta rows',len(rows),'maximum relative error',max(float(r['Vieta_relative_replay_error']) for r in rows))
if __name__=='__main__':main()
