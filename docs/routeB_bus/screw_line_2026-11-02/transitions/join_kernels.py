"""Join formal kernel outputs with local atom kicks and discrete increments.

All arithmetic is decimal multiprecision; no float underflow at large
complex physical evaluations. Undefined source/kernel states are retained.
"""
from pathlib import Path
import csv,json,hashlib,os
import mpmath as mp
P=Path(__file__).resolve().parent
ROOT=Path(os.environ.get('SCREW_ROOT',str(P.parent)))
mp.mp.dps=100
fmt=lambda x:mp.nstr(x,80)
def number(value):
 try:
  x=mp.mpf(value)
  return x if mp.isfinite(x) else None
 except (ValueError,TypeError):return None
def write(name,rows):
 if not rows:return
 with (P/name).open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
def main():
 atoms={int(r['m']):r for r in csv.DictReader((P/'all_atoms.csv').open())};cells={}
 for p in (ROOT/'kernels').glob('*_m*_bits*.json'):
  try:d=json.loads(p.read_text())
  except (json.JSONDecodeError,OSError):continue
  if 'world' not in d or 'm' not in d:continue
  key=(d['world'],int(d['m']));bits=int(d.get('arithmetic_bits',0))
  if key not in cells or bits>int(cells[key][1].get('arithmetic_bits',0)):cells[key]=(p,d)
 rows=[];index={};missing=[]
 for world in ['zeta','dh']:
  for m in range(20,241):
   if (world,m) not in cells:missing.append(dict(world=world,m=m,reason='kernel cell not yet available'));continue
   p,d=cells[world,m];atom=atoms[m];wn=mp.mpf(atom['zeta_b_over_sqrt_n'] if world=='zeta' else atom['DH_b_over_sqrt_n']);L=mp.log(m)
   for r in d.get('rows',[]):
    eta=mp.mpf(r['eta']);Kstr=r.get('K','');crossstr=r.get('endpoint_cross','');K=number(Kstr);cross=number(crossstr)
    valid=K is not None and cross is not None and mp.isfinite(K) and mp.isfinite(cross)
    jk=2*wn*L*abs(cross)**2 if valid else None
    jr=-jk/(eta*K*K) if valid and eta>0 and K else None
    row=dict(world=world,m=m,q=r.get('q',d.get('q','')),gauge=r.get('gauge',''),eta=r['eta'],
      prime_power=atom['prime_power'],prime=atom['prime'],exponent=atom['exponent'],arithmetic_weight_b_over_sqrt_n=fmt(wn),
      source_g_prime_jump=fmt(wn),source_g_continuity='continuous; derivative has hinge jump',
      source_tau_rankone_coefficient=fmt(-2*wn*L),source_L_rankone_coefficient=fmt(-2*wn),
      K=Kstr,K_sign=r.get('K_sign',''),endpoint_cross=crossstr,form_negative_count=d.get('inertia',{}).get('negative',''),
      local_dotK_tau_jump=fmt(jk) if jk is not None else 'undefined',local_dotK_L_jump=fmt(jk/L) if jk is not None else 'undefined',
      local_dotr_proxy_tau_jump=fmt(jr) if jr is not None else 'undefined',local_dotr_proxy_L_jump=fmt(jr/L) if jr is not None else 'undefined',
      local_proxy_slope_sign=(1 if jr>0 else -1 if jr<0 else 0) if jr is not None else 'undefined',
      r_proxy=r.get('r_proxy',''),kernel_status=r.get('kernel_status',d.get('status','')),actual_Weyl_status='NOT_IDENTIFIED_BY_THIS_CALCULATION',
      derivative_path='N fixed; L_tau=L exp(tau); active zero coordinates fixed; no cutoff crossing',
      kernel_file=p.name,kernel_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),arithmetic_bits=d.get('arithmetic_bits',''))
    rows.append(row);index[(world,m,row['gauge'],row['eta'])]=row
 write('local_atom_slopes.csv',rows)
 pp=[r for r in rows if atoms[r['m']]['prime_power']=='True' and r['gauge']!='endpoint'];write('prime_power_kernel_slopes.csv',pp)
 nonpp=[r for r in rows if r['world']=='dh' and atoms[r['m']]['prime_power']=='False' and mp.mpf(r['arithmetic_weight_b_over_sqrt_n']) and r['gauge']!='endpoint'];write('DH_non_prime_power_kernel_slopes.csv',nonpp)
 discrete=[]
 for r in rows:
  if r['gauge']=='endpoint':continue
  prev=index.get((r['world'],r['m']-1,r['gauge'],r['eta']));rv=r['r_proxy'];pv=prev['r_proxy'] if prev else ''
  good=bool(prev and number(rv) is not None and number(pv) is not None)
  dr=mp.mpf(rv)-mp.mpf(pv) if good else None
  local=r['local_dotr_proxy_tau_jump'];sgn=int(r['local_proxy_slope_sign']) if r['local_proxy_slope_sign']!='undefined' else None
  discrete.append(dict(world=r['world'],m=r['m'],gauge=r['gauge'],eta=r['eta'],prime_power=r['prime_power'],
    current_q=r['q'],previous_q=prev['q'] if prev else '',delta_q=int(r['q'])-int(prev['q']) if prev else '',delta_N=1 if prev else '',
    r_proxy=rv,previous_r_proxy=pv,discrete_delta_r_proxy=fmt(dr) if dr is not None else 'undefined',
    discrete_delta_sign=(1 if dr>0 else -1 if dr<0 else 0) if dr is not None else 'undefined',
    fixedN_local_tau_slope_kick=local,fixedN_local_slope_sign=sgn if sgn is not None else 'undefined',
    same_sign_as_fixedN_kick=bool((1 if dr>0 else -1 if dr<0 else 0)==sgn) if dr is not None and sgn is not None else 'undefined',
    interpretation='different objects: discrete N/head/L changes versus one-sided fixed-N derivative kick'))
 write('discrete_increments.csv',discrete)
 summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',kernel_cells_available=len(cells),expected_kernel_cells=442,missing_cells=missing,
   joined_rows=len(rows),prime_power_point_rows=len(pp),DH_non_prime_power_nonzero_point_rows=len(nonpp),
   actual_Weyl_radius_claim=False,source_g_gate='RESOLVED by source_audit/SOURCE_AUDIT.md: g=-q[chi]/2, hence jump g_prime=+b(n)/sqrt(n)',
   comparison={})
 for world in ['zeta','dh']:
  for gauge in ['physical','fourier']:
   rr=[r for r in discrete if r['world']==world and r['gauge']==gauge and r['prime_power']=='True' and r['discrete_delta_r_proxy']!='undefined']
   summary['comparison'][world+'_'+gauge]=dict(prime_power_discrete_observations=len(rr),matching_fixedN_kick_sign=sum(r['same_sign_as_fixedN_kick'] is True for r in rr),different_sign=sum(r['same_sign_as_fixedN_kick'] is False for r in rr))
 (P/'kernel_transition_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='missing_cells'},indent=2))
if __name__=='__main__':main()
