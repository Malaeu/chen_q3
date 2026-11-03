"""Summaries of saved observations only; no new spectral experiment."""
from pathlib import Path
from collections import defaultdict
import csv,json,statistics
P=Path(__file__).resolve().parent
def read(path):return list(csv.DictReader(path.open()))
def write(name,rows):
    with (P/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
groups=defaultdict(list)
for r in read(P/'spectra'/'scalar_profiles.csv'):
    if int(r['cut'])==400:groups[r['world'],int(r['rep']),int(r['mesh'])].append(r)
monotonic=[];endpoints=defaultdict(list)
for (world,rep,mesh),rs in groups.items():
    rs.sort(key=lambda r:float(r['a']))
    increase=max((float(b['mu_endpoint'])-float(a['mu_endpoint']) for a,b in zip(rs,rs[1:])),default=0)
    monotonic.append(dict(world=world,rep=rep,mesh=mesh,rows=len(rs),maximum_increase=increase,nonincreasing_to_1e10=increase<=1e-10))
    for r in rs:
        a=float(r['a'])
        if a in [1,3,6]:endpoints[world,mesh,a].append(float(r['mu_endpoint']))
rows=[dict(world=w,mesh=m,a=a,replicates=len(v),median_mu1=statistics.median(v),min_mu1=min(v),max_mu1=max(v)) for (w,m,a),v in sorted(endpoints.items())]
blocks=defaultdict(list)
for r in read(P/'spectra'/'future_blocks.csv'):
    if int(r['cut'])==400 and r['status']=='FINITE_SAMPLED':blocks[r['world'],int(r['mesh']),int(r['a']),int(r['q'])].append(float(r['mu']))
br=[dict(world=w,mesh=m,a=a,q=q,replicates=len(v),median_mu=statistics.median(v),min_mu=min(v),max_mu=max(v)) for (w,m,a,q),v in sorted(blocks.items())]
reference=P.parent/'extension_margin'/'uniform'/'future_refinement.csv'
for r in read(reference):
    if r['world']=='zeta' and r['status']=='FINITE_SAMPLED' and float(r['a']) in [1,3,6]:
        x=float(r['mu']);q=int(r['q']);m=int(r['mesh']);a=float(r['a'])
        br.append(dict(world='arithmetic_zeta_reference',mesh=m,a=a,q=q,replicates=1,median_mu=x,min_mu=x,max_mu=x))
        if q==1:rows.append(dict(world='arithmetic_zeta_reference',mesh=m,a=a,replicates=1,median_mu1=x,min_mu1=x,max_mu1=x))
write('history_endpoints.csv',rows);write('future_summary.csv',br);write('history_monotonicity.csv',monotonic)
(P/'POSTPROCESS.json').write_text(json.dumps(dict(saved_world_profiles=len(groups),all_nonincreasing_to_1e10=all(x['nonincreasing_to_1e10'] for x in monotonic),endpoint_rows=len(rows),future_summary_rows=len(br),note='Descriptive summaries of existing registered measurements, not a new hypothesis test.'),indent=2)+'\n')
print(json.dumps([r for r in rows if r['mesh']==256],indent=2))
