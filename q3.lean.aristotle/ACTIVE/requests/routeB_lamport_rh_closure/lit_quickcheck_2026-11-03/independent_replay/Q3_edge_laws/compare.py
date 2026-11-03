"""Reject the unproved identification of finite Rellich slopes with continuum traces."""
import argparse,csv,json,hashlib
from pathlib import Path
import mpmath as mp
p=argparse.ArgumentParser();p.add_argument('--rellich-root',type=Path,required=True);a=p.parse_args();mp.mp.dps=70
rows=[]
for world,m,q in [('zeta',160,89),('zeta',200,115),('zeta',240,139),('dh',160,89),('dh',160,144),('dh',200,115),('dh',200,180),('dh',240,139),('dh',240,216)]:
 fs=[f for f in a.rellich_root.glob(f'{world}_m{m}_q{q}_dps*.json') if 'coarse' not in f.name]
 f=max(fs,key=lambda f:int(f.name.split('dps')[1].split('_')[0]));d=json.loads(f.read_text())
 slope=mp.mpf(d['source_left_virial'])+mp.mpf(d['projector_correction']);implied=-slope/mp.log(m)
 rows.append(dict(world=world,m=m,q=q,lambda_finite=d['saved_rayleigh'],endpoint=d['edge'],compressed_dilation_slope=mp.nstr(slope,40),inadmissible_implied_A_squared=mp.nstr(implied,40),negative_implied_trace_squared=implied<0,verdict='DIFFERENT_OBJECT',input=f.name,input_sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
with Path(__file__).with_name('comparison.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
print('Nine finite-slope comparisons saved; none asserted as continuum traces')
