from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).resolve().parent))
from extend import fast
P=Path(__file__).resolve().parent;d=json.loads((P/'dh_zeros_600.json').read_text());out=[]
for rec in d['contour_bands']:
 if rec['off_line_upper_count_needed']==0:continue
 a=rec['low'];prev=fast(a);br=[];step=.01
 for j in range(1,int((rec['high']-a)/step)+1):
  b=a+j*step;v=fast(b)
  if prev*v<0:br.append([b-step,b])
  prev=v
 row=dict(low=a,high=rec['high'],step=step,bracket_count=len(br),coarse_line_count=rec['line_count'],brackets=br);out.append(row);print(row,flush=True)
(P/'fine_line_check.json').write_text(json.dumps(out,indent=2)+'\n')
