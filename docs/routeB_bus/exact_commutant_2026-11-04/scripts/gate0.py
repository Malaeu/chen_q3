#!/usr/bin/env python3
"""Gate0 only: unchanged pinned source, 80dps scalar audit, Suzuki(1.1)."""
from pathlib import Path
import importlib.util,os,json,hashlib,time,datetime
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
SOURCE=Path(os.environ.get('CCM_SOURCE_ROOT','/workspace/stiffness/repo/docs/routeB_bus/ground_state_zeros_2026-11-03/inputs'))
PINS={'analytic_source.py':'27bbaabbc5938b3157b5bc20f5e6db2f882122c0','source_50777d4.py':'f8b558f8fd7e2cda65158856ae6bfa9011f5cd0a'}
mp.mp.dps=80
DPS=80;BITS=320

def text(x):return mp.nstr(x,82)
def mangoldt(m):
 result={}
 for p in range(2,m+1):
  if any(p%d==0 for d in range(2,int(p**.5)+1)):continue
  n=p
  while n<=m:result[n]=mp.log(p);n*=p
 return result

def main():
 reg=json.loads((ROOT/'PREREGISTRATION.json').read_text());assert reg['commit']and reg['predictions_blob']
 start=time.monotonic();started=datetime.datetime.now(datetime.timezone.utc).isoformat();inputs=[]
 for name,blob in PINS.items():
  b=(SOURCE/name).read_bytes();actual=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert actual==blob,(name,actual)
  inputs.append(dict(file=name,git_blob=blob,sha256=hashlib.sha256(b).hexdigest()))
 spec=importlib.util.spec_from_file_location('pinned_analytic_source',SOURCE/'analytic_source.py');source=importlib.util.module_from_spec(spec);spec.loader.exec_module(source)
 rows=[];tol=mp.mpf('1e-40')
 for m in [16,80,300]:
  L=mp.log(m);co=mangoldt(m);c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2
  def integrand(u):return mp.mpf(1)/2 if not u else u*mp.exp(-u/2)/(-mp.expm1(-2*u))
  # Literal source constant-mode overlap: R00(u)=2(1-u/L), zero beyond L.
  H=c+2/L*mp.quad(integrand,[0,L/2,L])+2*(mp.atanh(mp.exp(-L/2))+mp.atan(mp.exp(-L/2)))
  pv=4*mp.sqrt(2)*L**mp.mpf('1.5')*mp.sinh(L/4)/L**2;P=pv**2
  B=mp.fsum(2*lam/mp.sqrt(n)*(1-mp.log(n)/L)for n,lam in co.items())
  phi_gamma=L/2*(mp.digamma(mp.mpf(1)/4)-mp.log(mp.pi))+(mp.pi**2+8*mp.catalan-mp.exp(-L/2)*mp.lerchphi(mp.exp(-2*L),2,mp.mpf(1)/4))/4
  phi_pole=4*(mp.exp(L/2)+mp.exp(-L/2)-2)
  phi_prime=-mp.fsum(lam/mp.sqrt(n)*(L-mp.log(n))for n,lam in co.items())
  psi=phi_gamma+phi_pole+phi_prime;target=2*psi/L;A=H+P-B
  # Reuse unchanged pinned matrix builder, not a replacement source.
  worlds,meta=source.build(m,BITS);A_builder=mp.mpf(str(worlds['zeta'][0][0,0]))
  expected_pole=8*(mp.exp(L/2)+mp.exp(-L/2)-2)/L
  deltas=dict(H00_minus_Suzuki_gamma=H-2*phi_gamma/L,P00_minus_Suzuki_pole=P-2*phi_pole/L,minus_B00_minus_Suzuki_prime=-B-2*phi_prime/L,P00_minus_required_expression=P-expected_pole,A00_minus_2Psi_over_L=A_builder-target,A00_builder_minus_scalar_source=A_builder-A)
  ok=all(abs(x)<=tol for x in deltas.values())
  rows.append(dict(m=m,L=text(L),H00=text(H),P00=text(P),B00=text(B),A00_scalar=text(A),A00_pinned_builder=text(A_builder),Suzuki_Psi=text(psi),two_Psi_over_L=text(target),Suzuki_gamma_scaled=text(2*phi_gamma/L),Suzuki_pole_scaled=text(2*phi_pole/L),Suzuki_prime_signed_scaled=text(2*phi_prime/L),required_P00=text(expected_pole),differences={k:text(v)for k,v in deltas.items()},max_abs_difference=text(max(abs(v)for v in deltas.values())),pass_gate=ok,builder_metadata=meta))
  print(m,'PASS'if ok else'FAIL','max abs difference',rows[-1]['max_abs_difference'],flush=True)
  if not ok:break
 result=dict(status='PASS'if len(rows)==3 and all(r['pass_gate']for r in rows)else'FAIL_STOP_SCAN',diagnostic='DIAGNOSTIC_NEVER_A_PROOF_POINT_MPMATH_NOT_INTERVAL',mpmath_dps=DPS,builder_bits=BITS,tolerance='1e-40',source_inputs=inputs,registration_commit=reg['commit'],started_UTC=started,seconds=time.monotonic()-start,rows=rows,scan_run=False)
 (ROOT/'GATE0.json').write_text(json.dumps(result,indent=2)+'\n')
 if result['status']!='PASS':raise SystemExit('GATE0 FAILED: STOP_SCAN')
if __name__=='__main__':main()
