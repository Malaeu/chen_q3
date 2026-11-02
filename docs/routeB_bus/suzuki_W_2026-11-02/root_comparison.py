"""Add independent nearest-zeta-zero comparisons; never force bijections."""
from pathlib import Path
import csv,bisect,statistics,math
P=Path(__file__).resolve().parent
Z=P.parent/'capacity_matrix_2026-11-02/zeros.csv'
refs=[float(r['gamma']) for r in csv.DictReader(Z.open())]
path=P/'W/real_W_roots.csv';rows=list(csv.DictReader(path.open()))
for r in rows:
    t=float(r['root']);j=bisect.bisect_left(refs,t);candidates=range(max(0,j-1),min(len(refs),j+1));k=min(candidates,key=lambda k:abs(refs[k]-t))
    r['nearest_zeta_zero']=format(refs[k],'.17g');r['distance_to_zeta_zero']=format(abs(t-refs[k]),'.17g')
with path.open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
groups={}
for r in rows:groups.setdefault((r['world'],int(r['m']),int(r['theta_index'])),[]).append(r)
out=[]
for (world,m,theta),rs in sorted(groups.items()):
    cutoff=.8*2*math.pi*m/math.log(m)
    positive=[r for r in rs if float(r['root'])>0]
    out.append(dict(world=world,m=m,theta_index=theta,W_reported_nonnegative_roots=len(rs),seeded_origin_count=len(rs)-len(positive),W_positive_sign_change_roots=len(positive),zeta_zeros_in_same_positive_band=sum(g<=cutoff for g in refs),median_distance_to_zeta_zero=statistics.median(float(r['distance_to_zeta_zero']) for r in positive),median_distance_to_zeta_xi_prime_zero=statistics.median(float(r['distance']) for r in positive),reference_scope='zeta references for both worlds; no one-to-one or completeness claim'))
with (P/'W/root_comparison_summary.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=out[0]);w.writeheader();w.writerows(out)
for r in out:
    if r['theta_index']==8 and r['m'] in (20,240):print(r)
