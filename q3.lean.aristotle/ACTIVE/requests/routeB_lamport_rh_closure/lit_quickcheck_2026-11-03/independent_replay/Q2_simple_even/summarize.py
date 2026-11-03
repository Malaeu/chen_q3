from pathlib import Path
import csv,json,hashlib
import mpmath as mp
mp.mp.dps=100;P=Path(__file__).resolve().parent;rows=[]
for p in sorted(P.glob('m*_N*_q*_p*_dps*.json')):
 for r in json.loads(p.read_text())['rows']:
  guard=mp.power(10,-r['dps']+15)*max(1,abs(mp.mpf(r['even1'])),abs(mp.mpf(r['odd0'])))
  r['precision_guard']=mp.nstr(guard,20)
  r['parity_resolved']=abs(mp.mpf(r['odd_even_gap']))>guard
  r['simplicity_resolved']=abs(mp.mpf(r['even_gap']))>guard
  r['numerical_verdict']='INCONCLUSIVE_RESOLUTION' if not(r['parity_resolved'] and r['simplicity_resolved']) else ('CONSISTENT' if r['global_even'] else 'VIOLATED_AT m='+str(r['m']))
  r['input_result_file']=p.name;rows.append(r)
rows.sort(key=lambda r:(r['m'],r['N'],r['world']))
with (P/'spectra.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
paired=[]
for world in ['zeta','dh','plant']:
 for m in [3,5,7,10,15,20,30,40,47,55]:
  rr=sorted([r for r in rows if r['world']==world and r['m']==m],key=lambda r:r['N'])
  if len(rr)!=2:continue
  a,b=rr;paired.append(dict(world=world,m=m,N_low=a['N'],N_high=b['N'],low_verdict=a['numerical_verdict'],high_verdict=b['numerical_verdict'],even0_absolute_drift=mp.nstr(abs(mp.mpf(b['even0'])-mp.mpf(a['even0'])),40),odd0_absolute_drift=mp.nstr(abs(mp.mpf(b['odd0'])-mp.mpf(a['odd0'])),40),high_even0=b['even0'],high_odd0=b['odd0'],high_odd_even_gap=b['odd_even_gap'],high_even_gap=b['even_gap']))
with (P/'resolution_comparison.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(paired[0]));w.writeheader();w.writerows(paired)
summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',rows=len(rows),comparison_rows=len(paired),worlds={world:dict(resolved_odd_cases=[r['m'] for r in paired if r['world']==world and r['low_verdict'].startswith('VIOLATED') and r['high_verdict'].startswith('VIOLATED')],unresolved_cases=[r['m'] for r in paired if r['world']==world and 'INCONCLUSIVE_RESOLUTION' in [r['low_verdict'],r['high_verdict']]]) for world in ['zeta','dh','plant']},guard_scope='heuristic arithmetic precision guard only; no interval quadrature or continuum spectral bound',source_sha256=hashlib.sha256((P/'parity.py').read_bytes()).hexdigest(),external_readme=dict(url='https://github.com/AlexGenusCore/weil-ground-state-simple-even/blob/main/README.md',git_blob='f18fa5e422e0488e82ef636e88480edd339dd2a4',sha256=hashlib.sha256((P/'BOTHA_README.md').read_bytes()).hexdigest(),access_date='2026-11-03'))
(P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
