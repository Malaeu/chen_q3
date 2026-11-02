"""Aggregate EDGE_LAW diagnostics; source-implied tails are not independent sums."""
from pathlib import Path
import csv,json,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent
mp.mp.dps=100
fmt=lambda x:mp.nstr(x,70)
zrows={(int(r['m']),int(r['q'])):r for r in csv.DictReader((P/'zero_side/zero_sums.csv').open()) if r['world']=='zeta'}
drows={(int(r['m']),r['mode']):r for r in csv.DictReader((P/'zero_side/dh_extended.csv').open())}
rows=[];checks=[]
for world in ('zeta','dh'):
    paths=sorted((P/world).glob('cell_m*_dps120_gl192.json'))
    for path in paths:
        d=json.loads(path.read_text());m=d['m'];mode=d.get('mode','native');q=d['q']
        f=list(map(mp.mpf,d['complement_f'] if world=='zeta' else d['physical_modal_coefficients']))
        norm=mp.fsum(x*x for x in f)
        endpoint=mp.fsum((1 if n==0 else mp.sqrt(2))*x for n,x in enumerate(f))/mp.sqrt(mp.log(m))
        lam=mp.mpf(d['complement_minimum']);T=mp.mpf(d['T']);scale=endpoint**2*mp.log(T)/(mp.pi*T);R=lam/scale
        old_R=mp.mpf(d['R'] if world=='zeta' else d['R_edge'])
        norm_error=abs(norm-1);ratio_error=abs(R-old_R)/max(abs(R),mp.mpf('1e-100'))
        assert norm_error<mp.mpf('1e-90') and ratio_error<mp.mpf('1e-70')
        z=zrows[m,q] if world=='zeta' else drows[m,mode]
        head=mp.mpf(z['Weil_below_T']);prefix=mp.mpf(z['Weil_T_to_X'] if world=='zeta' else z['Weil_T_to_310'])
        tail_balance=lam-head;remaining=tail_balance-prefix
        row=dict(world=world,m=m,mode=mode,q=q,T=fmt(T),lambda_min=fmt(lam),endpoint_f_b=fmt(endpoint),R=fmt(R),
                 known_zero_head=fmt(head),tail_by_source_balance=fmt(tail_balance),known_tail_prefix=fmt(prefix),
                 prefix_height=400 if world=='zeta' else 310,uncomputed_source_minus_prefix=fmt(remaining),
                 head_fraction=fmt(head/lam),tail_balance_fraction=fmt(tail_balance/lam),
                 R_head=fmt(head/scale),R_tail_balance=fmt(tail_balance/scale),
                 tail_status='source balance, NOT independently evaluated or certified infinite zero tail')
        rows.append(row);checks.append(dict(path=str(path.relative_to(P)),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),norm_error=fmt(norm_error),R_relative_error=fmt(ratio_error)))
assert len(rows)==9
with (P/'summary.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
(P/'AGGREGATE_VALIDATION.json').write_text(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','checks':checks},indent=2)+'\n')
for r in rows:print(r['world'],r['m'],r['mode'],'lambda',mp.nstr(mp.mpf(r['lambda_min']),12),'edge',mp.nstr(mp.mpf(r['endpoint_f_b']),12),'R',mp.nstr(mp.mpf(r['R']),12),'head_fraction',mp.nstr(mp.mpf(r['head_fraction']),9))
