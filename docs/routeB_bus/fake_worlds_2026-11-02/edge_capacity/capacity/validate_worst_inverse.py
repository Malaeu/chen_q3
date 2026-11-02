"""Extra high-conditioning DH inverse-capacity check, no eigensolver.

The full minimum/slice are well separated negative values; the tiny positive
G eigenvalue chiefly threatens the inverse. Compare that sensitive quantity
at110dps against its complete80dps computation.
"""
from pathlib import Path
import argparse,json,os,time
import mpmath as mp

def main():
 p=argparse.ArgumentParser();p.add_argument('--input-root',type=Path,default=Path(os.environ.get('EDGE_CAPACITY_INPUT_ROOT',Path(__file__).resolve().parent/'inputs')));p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent);args=p.parse_args();start=time.monotonic();mp.mp.dps=110
 path=args.input_root/'dense/dh_m240_q216_rebuild.json';src=json.loads(path.read_text());A=mp.matrix(src['A']);U=mp.matrix(src['U']);G=U.T*A*U;G=(G+G.T)/2;m=src['m'];L=mp.log(m)
 db=mp.matrix([1/mp.sqrt(L)]+[mp.sqrt(2/L)]*m);t=U.T*db;x=mp.lu_solve(G,t);den=(t.T*x)[0];cap=1/den;scale=mp.pi*mp.mpf(src['T'])/mp.log(mp.mpf(src['T']))
 old=json.loads((args.output/'dh_m240_q216_rebuild_capacity_dps80.json').read_text());low=mp.mpf(old['capacity_algebraic']);rel=abs(cap-low)/abs(cap)
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',source=str(path),validation='extra worst-conditioned inverse only; no eigenproblem',low_dps=80,high_dps=110,low_cap=old['capacity_algebraic'],high_cap=mp.nstr(cap,100),high_scaled_cap=mp.nstr(cap*scale,100),relative_difference=mp.nstr(rel,80),acceptance_relative=1e-8,passes_relative_1e_8=bool(rel<mp.mpf('1e-8')),source80_min_absolute_G_eigenvalue=old['saved_spectrum_min_absolute'],inverse_solve_relative_residual=mp.nstr(mp.norm(G*x-t)/(mp.norm(G)*mp.norm(x)+mp.norm(t)),80),seconds=time.monotonic()-start)
 (args.output/'worst_inverse_validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
 if not result['passes_relative_1e_8']:raise SystemExit(1)
if __name__=='__main__':main()
