"""Reconstruct exact checked decimal endpoints and compare brackets using rationals.
No transform evaluations or new root searches, except deterministic replay of the
single supplemental imaginary Newton sequence to recover its saved-point digits.
"""
from pathlib import Path
from fractions import Fraction
import json,sys,resource,os,hashlib
resource.setrlimit(resource.RLIMIT_CPU,(3,3))
import mpmath as mp
mp.mp.dps=220;P=Path(__file__).resolve().parent;path=Path(os.environ.get('GROUND_ROOT_BRACKET_OUTPUT',str(P/'low_bracket_validation_m300.json')));out=json.loads(path.read_text());eps=mp.mpf('1e-100')
for row in out['rows']:
 res=json.loads((P/'results'/f"{row['world']}_{row['parity']}_m300.json").read_text());source=Path(res['source_vector_path']);source=source if source.exists() else P.parent/'spectra/vectors'/source.name;source_blob=source.read_bytes();assert hashlib.sha256(source_blob).hexdigest()==res['source_vector_sha256'];d=json.loads(source_blob);Om=2*mp.pi*300/mp.mpf(d['L_low']);pairs={q['root_id']:q for q in res['precision_replay']['pairs']};intervals=[]
 for q in row['checks']:
  if q['root_id'] in pairs:
   r=pairs[q['root_id']];u=mp.re((mp.mpc(r['low_z_re'],r['low_z_im'])/Om)**2)
  else:
   assert row['world']=='dh' and row['parity']=='even';c=list(map(mp.mpf,d['v_even0_low']));a=[mp.mpf(n*n)/(300*300) for n in range(1,301)];u=mp.mpf(next(r for r in res['roots'] if r['root_id']==q['root_id'])['u_re'])
   for it in range(10):
    r=c[0]+mp.sqrt(2)*mp.fsum(cn*u/(u-an) for cn,an in zip(c[1:],a));rp=mp.sqrt(2)*mp.fsum(-cn*an/(u-an)**2 for cn,an in zip(c[1:],a));du=r/rp;u-=du
    if abs(du)<mp.mpf('1e-165'):break
  assert mp.nstr(u,180)==q['u_center'];left=mp.nstr(u-eps,205);right=mp.nstr(u+eps,205);lo,hi=Fraction(left),Fraction(right);polefree=all(not(lo<=Fraction(n*n,90000)<=hi) for n in range(1,301));assert polefree
  q.update(checked_u_left_decimal=left,checked_u_right_decimal=right,exact_rational_pole_free=True);intervals.append((lo,hi))
 intervals.sort();assert all(hi<lo2 for (lo,hi),(lo2,hi2) in zip(intervals,intervals[1:]));row['exact_rational_bracket_disjointness']=True
out['checked_endpoints_scope']='Checked 205-digit decimal endpoint strings reconstructed deterministically from frozen low-vector replay coordinates and L_low at the original 220-digit working precision. The original Arb sign tests enclose these exact decimals. Pole exclusion and pairwise disjointness rechecked with exact Python Fraction arithmetic.'
tmp=path.with_suffix('.exacttmp');tmp.write_text(json.dumps(out,indent=2)+'\n');tmp.replace(path);print('Exact endpoints/pole exclusion/disjointness PASS all five m300 low censuses')
