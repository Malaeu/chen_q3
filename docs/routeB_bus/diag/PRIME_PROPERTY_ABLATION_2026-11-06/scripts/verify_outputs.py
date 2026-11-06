# /// script
# requires-python = ">=3.11"
# ///
"""Cross-file acceptance checks; does not certify floating point or asymptotics."""
from pathlib import Path
import csv,json,math,statistics
ROOT=Path(__file__).resolve().parents[1]
def read(p):
 with p.open() as f:return list(csv.DictReader(f))
def main():
 pre=json.loads((ROOT/'PREREGISTRATION.json').read_text())
 names=['S0','S5']+[f'S1_seed{s}' for s in pre['seeds']['S1']]+[f'S2_y{y}_seed{s}' for y in pre['hybrid_y'] for s in pre['seeds']['S2']]+[f'S3_seed{s}' for s in pre['seeds']['S3']]+[f'S4_seed{s}' for s in pre['seeds']['S4']]
 checks={}
 for name in names:
  rows=read(ROOT/f'{name}.csv'); xs=[float(r['X']) for r in rows]; ws=[float(r['W']) for r in rows]
  assert all(math.isfinite(v) for v in xs+ws)
  assert all(b>a for a,b in zip(xs,xs[1:])),name
  assert xs[-1]==pre['limits'][name[:2]],name
  integ=[w*math.log(x) for w,x in zip(ws,xs)]
  assert all(b>=a-1e-10*max(1,abs(a)) for a,b in zip(integ,integ[1:])),name
  for k in range(1,int(round(math.log10(xs[-1])))+1):
   assert any(abs(x-10**k)<=1e-10*10**k for x in xs),(name,k)
  sr=read(ROOT/f'{name}_samples.csv'); assert len(sr)==1000*round(math.log10(xs[-1])),(name,len(sr))
  decades=read(ROOT/f'{name}_decades.csv')
  for d in decades:
   if int(d['sample_count'])==0:continue  # separate endpoint bucket, no log measure
   vals=[float(v['ratio']) for v in sr if float(d['x_lo'])<=float(v['x'])<float(d['x_hi'])]
   assert len(vals)==int(d['sample_count']),(name,d['decade'])
   mean_key='ratio_mean' if 'ratio_mean' in d else 'mean_ratio'
   var_key='ratio_variance' if 'ratio_variance' in d else 'variance_ratio'
   assert math.isclose(float(d[mean_key]),statistics.mean(vals),rel_tol=1e-10,abs_tol=1e-12),(name,d['decade'],'mean')
   assert math.isclose(float(d[var_key]),statistics.pvariance(vals),rel_tol=1e-10,abs_tol=1e-12),(name,d['decade'],'variance')
  if name in ('S0','S5'):
   vals=pre['judges']['J1' if name=='S0' else 'J2']['M10k' if name=='S0' else 'L10k']
   for k in range(1,9):
    r=min(rows,key=lambda r:abs(float(r['X'])-10**k));assert int(float(r['M']))==vals[k],(name,k,r)
  if name.startswith(('S1','S2','S3')):
   ns=[float(r['N']) for r in rows];assert all(b>=a for a,b in zip(ns,ns[1:])),name
   rho=ns[-1]/xs[-1]
   for r in rows:
    x=float(r['X']);n=float(r['N']);assert abs(float(r['N_over_x'])-n/x)<1e-9
    assert abs(float(r['count_error'])-(n-rho*x))<1e-6*max(1,abs(n-rho*x)),name
  checks[name]={'grid_rows':len(rows),'sample_rows':len(sr),'X_max':xs[-1],'integral_monotone':True}
 result={'status':'PASS','systems':checks,'limits':'Internal consistency and published checkpoints only; independent enumerator judges in FAKE_CHECKS.json and true checks.'}
 (ROOT/'OUTPUT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS: 24 systems, limits, grids, samples, monotone integrals, OEIS checkpoints, counting errors')
if __name__=='__main__':main()
