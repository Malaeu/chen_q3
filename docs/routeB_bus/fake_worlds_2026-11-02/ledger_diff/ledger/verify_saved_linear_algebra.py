"""Recheck published native Q/U/witness data, no new source eigensystem."""
from pathlib import Path
import os,json,time
import mpmath as mp
import ledger
P=Path(__file__).resolve().parent
ROOT=Path(os.environ.get('MATCHED_ROOT',str(P.parent)))

def main():
 mp.mp.dps=120;rows=[]
 for m,q in [(55,50),(80,73),(120,108)]:
  p=ROOT/'matched_cells'/f'dh_m{m}_q{q}_native.json';d=json.loads(p.read_text())
  A=mp.matrix(d['A']);Q=mp.matrix(d['Q']);U=mp.matrix(d['U']);f=mp.matrix(d['complement_f']);y=mp.matrix(d['complement_y']);ev=mp.mpf(d['complement_minimum']);E=mp.matrix(d['E'])
  aq=A*Q;dg=(aq.T*aq);computed=mp.sqrt(max(mp.eigsy(dg,eigvals_only=True)));delta=mp.mpf(d['delta'])
  compres=mp.norm(U.T*A*f-ev*y);fullR=-mp.mpf(d['full_eigenvalues'][0])
  row=dict(m=m,q=q,R_full=fullR,delta_saved=delta,delta_recomputed=computed,delta_difference=computed-delta,E_Q_residual=mp.norm(E*Q),U_Q_residual=mp.norm(U.T*Q),Q_orthogonality=mp.norm(Q.T*Q-mp.eye(Q.cols)),U_orthogonality=mp.norm(U.T*U-mp.eye(U.cols)),lift_residual=mp.norm(f-U*y),compressed_eigen_residual=compres,Rayleigh_minus_compressed=(f.T*A*f)[0]-ev)
  rows.append(row);print(m,'delta',mp.nstr(computed,20),'difference',mp.nstr(computed-delta,8),flush=True)
 (P/'saved_linear_algebra_verification.json').write_text(json.dumps(ledger.fmt(dict(status='DIAGNOSTIC_NEVER_A_PROOF',source_commit='8acecc1574740c5163c2a4e8ef75049f6df84313',method='Re-evaluate saved physical matrices/bases/witnesses; eigsy only on the existing small AQ Gram to check its norm',rows=rows)),indent=2)+'\n')

if __name__=='__main__':main()
