#!/usr/bin/env python3
"""Independent overlap comparison with a restored canonical SCREW_LINE packet."""
from pathlib import Path
import argparse,csv,hashlib,json
import mpmath as mp
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--canonical-root',type=Path,required=True);a=ap.parse_args()
mp.mp.dps=150
ours={(d['world'],d['m']):d for f in (P/'native_cells').glob('*_dps220_gl256.json') for d in [json.loads(f.read_text())]}
assert len(ours)==442
manifest=json.loads((a.canonical_root/'DATA_MANIFEST.json').read_text())
for name in ['kernels/kernels.csv','kernels/inertia.csv']:
    b=(a.canonical_root/name).read_bytes();rec=next(r for r in manifest['members'] if r['path']==name)
    assert len(b)==rec['bytes'] and hashlib.sha256(b).hexdigest()==rec['sha256']
errs=[];cross=[]
for row in csv.DictReader((a.canonical_root/'kernels/kernels.csv').open()):
    if row['gauge']=='physical':continue
    d=ours[row['world'],int(row['m'])]
    j=0 if row['gauge']=='endpoint' else [mp.mpf('.5'),mp.mpf(1),mp.mpf(2)].index(mp.mpf(row['eta']))+1
    for key,ourskey,target in [('K','K',errs),('endpoint_cross','endpoint_cross',cross)]:
        x,y=mp.mpf(d[ourskey][j]),mp.mpf(row[key]);target.append(abs(x-y)/max(abs(x),abs(y),mp.mpf('1e-100')))
assert len(errs)==len(cross)==1768
count=0
for row in csv.DictReader((a.canonical_root/'kernels/inertia.csv').open()):
    d=ours[row['world'],int(row['m'])];count+=1
    assert (int(row['q']),int(row['negative']),int(row['positive']))==(d['q'],d['negative_pivots'],d['positive_pivots'])
assert count==442 and max(errs)<mp.mpf('1e-55') and max(cross)<mp.mpf('1e-55')
print(json.dumps({'status':'PASS','inertias':count,'kernels':len(errs),'cross_kernels':len(cross),'max_relative_K_error':mp.nstr(max(errs),100),'max_relative_cross_error':mp.nstr(max(cross),100)},indent=2))
