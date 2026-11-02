import diagnostics as d
from functools import lru_cache
d.targets=lru_cache(None)(d.targets)
for m in [20,40,60,80,120,160,200,240]:
 for world in ['zeta','dh']:d.run(world,m,xmax=20,suffix='_fixed20')
import csv,json
rows=[]
for p in sorted(d.P.glob('diagnostic_*_fixed20.json')):rows+=json.loads(p.read_text())['selected']
with (d.P/'selected_gauges_fixed20.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
