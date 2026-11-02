"""DIAGNOSTIC_NEVER_A_PROOF: numerical (7.1), no interval norm claim."""
from pathlib import Path
import json,csv
import mpmath as mp
P=Path(__file__).resolve().parent
def main():
 mp.mp.dps=120
 inputs=json.loads((P/'ledger'/'envelope_inputs.json').read_text())
 c=mp.euler+mp.log(8*mp.pi/5)-mp.pi/2
 out=[]
 for row in inputs:
  R=mp.mpf(row['R']);d=mp.mpf(row['delta']);assert R>d>0
  loss=d*d/(R-d);envelope=-R+loss;cv=R-loss-c
  out.append({'m':row['m'],'q_native_kappa1p1':row['q'],'R_full':mp.nstr(R,105),'delta':mp.nstr(d,105),
   'projection_loss_delta2_over_R_minus_delta':mp.nstr(loss,105),'envelope_7_1':mp.nstr(envelope,105),
   'c_D_positive_floor_constant':mp.nstr(c,105),'C_viol':mp.nstr(cv,105),
   'R_gt_delta':True,'C2_not_tested':True,'status':'DIAGNOSTIC_NUMERICAL_ENVELOPE_NOT_INTERVAL_NORM_CERTIFICATE'})
 (P/'envelopes.json').write_text(json.dumps(out,indent=2)+'\n')
 with (P/'envelopes.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(out[0]));w.writeheader();w.writerows(out)
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
