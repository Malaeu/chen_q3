"""Extract frozen MP zero-threshold counts; no eigensystem or input mutations.

Usage: python extract_counts.py --input /workspace/conditioning_input
Guards are numerical heuristics, not interval or quadrature enclosures.
"""
from pathlib import Path
import argparse,csv,hashlib,json
import mpmath as mp

def extract(root):
 mp.mp.dps=260
 P=root/'C_conditioning' if (root/'C_conditioning').is_dir() else root
 chosen={}
 for p in (P/'matrices/mp_escalation').rglob('*GL*.json'):
  try:a=json.loads(p.read_text())
  except (OSError,ValueError):continue
  if not a.get('eigenvalues'):continue
  key=(a.get('world','zeta'),a.get('m'));pri=(int(a.get('GL',0)),p.name.startswith('mp_cell'))
  if key not in chosen or pri>chosen[key][0]:chosen[key]=(pri,p,a)
 rows=[]
 for world in ['zeta','plant','dh']:
  for m in range(16,121):
   p=P/'matrices'/f'cell_{world}_m{m}.json';a=json.loads(p.read_text());kind='cached_mp_eigenvalues'
   if (world,m) in chosen:
    _,p,a=chosen[world,m];values=a['eigenvalues'];kind='preferred_GL_spectrum'
   else:values=a.get('mp_eigenvalues',[])
   if not values:raise ValueError(f'Missing MP spectrum: {world} m={m}')
   ev=sorted(mp.mpf(x) for x in values)
   if 'roundoff_heuristic' in a:
    guard=mp.mpf(a['roundoff_heuristic']);method='receipt_roundoff_heuristic'
   else:
    digits=min(len(str(x).lower().split('e')[0].replace('.','').replace('-','').lstrip('0')) for x in values if mp.mpf(x))
    guard=mp.power(10,-digits+20)*max(1,max(abs(x) for x in ev))
    method=f'fallback_printed_digits_minus20_heuristic_digits{digits}'
   negative=sum(x<0 for x in ev);lower=sum(x < -guard for x in ev);uncertain=sum(abs(x)<=guard for x in ev)
   rows.append(dict(world=world,m=m,dimension=len(ev),literal_negative_printed=negative,guarded_negative_lower=lower,guarded_negative_upper=lower+uncertain,unresolved_near_zero=uncertain,minimum_eigenvalue=mp.nstr(ev[0],150),roundoff_guard=mp.nstr(guard,50),guard_method=method,count_0_to_2_literal=sum(0<x<2 for x in ev),near_2_guard=sum(abs(x-2)<=guard for x in ev),spectrum_kind=kind,spectrum_file=str(p.relative_to(P)),spectrum_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_sha256=json.dumps(a.get('source_sha256',a.get('mp_eigenvalues_source_sha256')),sort_keys=True),status='NUMERICAL_HEURISTIC_NOT_INTERVAL'))
 return rows

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--input',type=Path,default=Path('/workspace/conditioning_input'))
 ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'counts.csv')
 args=ap.parse_args();rows=extract(args.input)
 with args.output.open('w') as f:
  writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
 print(f'Wrote {len(rows)} rows to {args.output}')
