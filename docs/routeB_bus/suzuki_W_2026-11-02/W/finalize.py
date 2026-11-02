from pathlib import Path
import json,csv,shutil
P=Path(__file__).resolve().parent
raw=P/'all_cells.json'
if raw.exists():
 data=json.loads(raw.read_text());shutil.copyfile(raw,'/tmp/suzuki_all_cells_raw.json');raw.unlink()
else:data=json.loads(Path('/tmp/suzuki_all_cells_raw.json').read_text())
scalar=[{k:v for k,v in d.items() if not isinstance(v,list)} for d in data]
def write(name,rows):
 if not rows:return
 with (P/name).open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
write('all_m_scalars.csv',scalar)
selected=[];rootrows=[]
refs=list(csv.DictReader((P.parent/'theory/xi_prime_zeros.csv').open()))
print('reference schema',refs[0])
for path in sorted(P.glob('diagnostic_*.json')):
 if path.name.endswith('_fixed20.json'):continue
 d=json.loads(path.read_text());selected+=d['selected']
 for item in d['real_roots']:
  for x in item['roots']:
   vals=[float(r.get('t',r.get('gamma',r.get('root','nan')))) for r in refs];vals=[v for v in vals if v==v];near=min(vals,key=lambda v:abs(x-v)) if vals else None
   rootrows.append(dict(world=d['world'],m=d['m'],theta_index=item['theta_index'],root=x,nearest_zeta_xi_prime_zero=near,distance=None if near is None else abs(x-near),reference_scope='zeta reference only; DH comparison is not its own completed derivative',root_scope='sign-change scan; not certified complete'))
write('selected_gauges.csv',selected);write('real_W_roots.csv',rootrows)
print('cells',len(scalar),'selected',len(selected),'roots',len(rootrows))
