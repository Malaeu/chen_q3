"""Compare large-cell 120/128 and160/160 threshold quantities."""
from pathlib import Path
import json,sys
import mpmath as mp
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent/'phase_space_V'));from v_forms import build_forms
m,q=map(int,sys.argv[1:]);v=json.loads((P/f'large_validation_m{m}_q{q}.json').read_text());main=json.loads((P/f'cell_m{m}_dps120_gl128.json').read_text());s=next(x for x in main['passing_sectors'] if x['q']==q)
forms=build_forms(m,m,120,128);mp.mp.dps=180;A=mp.matrix(v['matrix_A']);difference=forms['K']-A
out=dict(m=m,q=q,matrix_max_entry_difference=mp.nstr(max(abs(x) for x in difference),100),matrix_Frobenius_difference=mp.nstr(mp.norm(difference),100))
for key in ['delta','lambda_r','sigma_min_squared','lambda_r_minus_delta']:
 x=mp.mpf(s[key]);y=mp.mpf(v[key]);out[key+'_relative_difference']=mp.nstr(abs(x/y-1),100);out[key+'_absolute_difference']=mp.nstr(abs(x-y),100)
out['matrix_error_over_saturation_gap']=mp.nstr(mp.norm(difference)/mp.mpf(v['lambda_r_minus_delta']),100)
a=mp.matrix(s['weak_left_vector']);b=mp.matrix(v['weak_left_vector']);out['weak_left_vector_distance_up_to_sign']=mp.nstr(min(mp.norm(a-b),mp.norm(a+b)),100)
(P/f'large_comparison_m{m}_q{q}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
