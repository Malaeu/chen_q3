"""Exact-source scalar flow/atom bookkeeping for g at every integer length.
This is NOT a passive-transfer or finite-impedance construction.
"""
from pathlib import Path
import mpmath as mp,csv,json
from curve import Source,labelled_coefficients
mp.mp.dps=85;P=Path(__file__).resolve().parent
rows=[]
for world in ['zeta','dh']:
 s=Source(world,300);s.b=labelled_coefficients(300,world);cum=mp.mpf(0);gvals={}
 for n in range(2,241):
  if n>=20:gvals[n]=-s.psi(mp.log(n))
 for n in range(2,241):
  before=cum;wn=s.b[n]/mp.sqrt(n);cum+=wn
  if n<20:continue
  L=mp.log(n);aa=mp.exp(-L/2);tail=mp.atanh(aa)+(mp.atan(aa) if world=='zeta' else -mp.atan(aa))
  smooth_derivative=-s.c/2-tail-(4*mp.sinh(L/2) if world=='zeta' else 0)
  row={'world':world,'m':n,'L':mp.nstr(L,80),'g_L':mp.nstr(gvals[n],80),'gprime_smooth':mp.nstr(smooth_derivative,80),'gprime_atoms_before_birth':mp.nstr(before,80),'gprime_atom_jump':mp.nstr(wn,80),'gprime_left':mp.nstr(smooth_derivative+before,80),'gprime_right':mp.nstr(smooth_derivative+cum,80),'value_jump_exact':0,'b_n':mp.nstr(s.b[n],80)}
  if n<240:
   deltaL=mp.log(n+1)-L;total=gvals[n+1]-gvals[n];arith=cum*deltaL
   row.update(delta_L=mp.nstr(deltaL,80),delta_g_total=mp.nstr(total,80),delta_g_atoms_all_n_le_m=mp.nstr(arith,80),delta_g_smooth=mp.nstr(total-arith,80),next_atom_value_at_endpoint_exact=0)
  else:row.update(delta_L='',delta_g_total='',delta_g_atoms_all_n_le_m='',delta_g_smooth='',next_atom_value_at_endpoint_exact=0)
  rows.append(row)
 print(world,'source sections done',flush=True)
with (P/'source_sections.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
(P/'SOURCE_SECTION_SCOPE.json').write_text(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','rows':442,'dps':85,'value_jumps':0,'formula':'gprime=-c/2-integral_L^infinity j + pole_gprime + sum_(n<=expL)b(n)/sqrt(n)','finite_impedance_identified':False,'section_passivity_proved':False},indent=2)+'\n')
