"""Eight-significant-digit viewing digest; full precision/guards stay in raw CSV."""
from pathlib import Path
import csv
P=Path(__file__).resolve().parent
def main():
    out=[]
    for r in csv.DictReader((P/'C_conditioning/conditioning.csv').open()):
        d={k:r[k] for k in ['world','m','r','count_minus_r']}
        d['cut']={'c_quarter':'1/4','c_half':'1/2','kappa_one':'1'}[r['cut']]
        for k in ['delta','delta_numeric_radius','sigma_min','sigma_min_squared','lambda_r_preferred','twice_sigma_squared_over_lambda_r','min_included_normalized_gap','weak_pair_left','weak_pair_right','weak_pair_mass']:
            d[k]=format(float(r[k]),'.8g') if r.get(k) else ''
        d['two_sigma_squared']=format(2*float(r['sigma_min_squared']),'.8g')
        d['delta_floor']=int(float(r['delta'])<=float(r['delta_numeric_radius']))
        out.append(d)
    with (P/'CONDITIONING_DIGEST.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=out[0]);w.writeheader();w.writerows(out)
if __name__=='__main__':main()
