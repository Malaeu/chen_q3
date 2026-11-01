"""DIAGNOSTIC_NEVER_A_PROOF: compare independently integrated exterior rows."""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=160
D=Path(__file__).resolve().parent
pairs=[(12,100,64,100,128),(16,100,96,100,128),(24,100,128,140,160)]
rows=[]
for m,d1,o1,d2,o2 in pairs:
 pa=D/f'exterior_m{m}_dps{d1}_gl{o1}.json';pb=D/f'exterior_m{m}_dps{d2}_gl{o2}.json'
 if not pa.exists() or not pb.exists():continue
 a=json.loads(pa.read_text());b=json.loads(pb.read_text());out={'m':m,'baseline':pa.name,'validation':pb.name,'status':'DIAGNOSTIC_NEVER_A_PROOF'}
 for key in ['h_out_form','W_form','W_coeff','raw_difference','projection_correction','X']:
  u=mp.matrix(a[key]);v=mp.matrix(b[key]);err=u-v
  out[key]={'max_abs_difference':mp.nstr(max(abs(x) for x in err),50),'relative_L2_difference':mp.nstr(mp.norm(err)/mp.norm(v),50),'validation_L2_norm':mp.nstr(mp.norm(v),50)}
 rows.append(out)
(D/'exterior_validation.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
