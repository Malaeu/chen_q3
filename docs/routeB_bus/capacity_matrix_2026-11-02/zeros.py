"""Positive zeta ordinates through400 and first beyond, 180 decimal precision."""
from pathlib import Path
import csv,json,hashlib,time
import mpmath as mp
P=Path(__file__).resolve().parent;src=P.parent/'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local/zeros.csv'
mp.mp.dps=180;rows=[dict(k=int(r['k']),gamma=r['gamma']) for r in csv.DictReader(src.open())];start=time.monotonic()
while mp.mpf(rows[-1]['gamma'])<=400:
 k=rows[-1]['k']+1;z=mp.zetazero(k);rows.append(dict(k=k,gamma=mp.nstr(mp.im(z),180)));print(k,mp.nstr(mp.im(z),15),flush=True)
 with (P/'zeros.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=['k','gamma']);w.writeheader();w.writerows(rows)
meta=dict(dps=180,count=len(rows),count_le_400=sum(mp.mpf(r['gamma'])<=400 for r in rows),last_gamma=rows[-1]['gamma'],inherited_count=138,inherited_source=str(src.relative_to(P.parent)),inherited_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,scope='mpmath numerical ordinates, no interval certification')
(P/'zeros_metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
