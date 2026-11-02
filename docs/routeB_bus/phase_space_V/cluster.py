"""V calibration on m24 near-null levels and independent matrix controls."""
from pathlib import Path
import sys,csv,json,hashlib
import mpmath as mp
from v_forms import build_forms,quantities
P=Path(__file__).resolve().parent;LOW=P.parent/'lowcluster_2026-11-02'
def run(dps=180,order=160,tag='main'):
    mp.mp.dps=dps
    form=build_forms(24,24,dps,order)
    src=LOW/'ladder_limit/identify/zero_height_local'/('core_m24_dps220_gl192.json' if dps>180 else 'core_m24_dps180_gl160.json')
    core=json.loads(src.read_text());Kold=mp.matrix(core['A']);U=mp.matrix(core['V']);rows=[]
    for i in range(8):
        f=U[:,i]/mp.norm(U[:,i]);q=quantities(form,f);lam=mp.mpf(core['lambda_'][i])
        prime=mp.fdot(f,form['prime']*f);pole=mp.fdot(f,form['pole'])**2
        balance=lam+form['cstar']+prime-pole+q['spatial']
        r=dict(m=24,N=24,i=i,lambda0_or_level=lam,**q,prime=prime,pole=pole,
               source_balance_error=abs(balance-q['V']),eigenpair_residual=mp.norm(form['K']*f-lam*f))
        rows.append({k:(mp.nstr(v,120) if isinstance(v,mp.mpf) else v) for k,v in r.items()})
    out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',dps=dps,order=order,
             source=str(src.relative_to(P.parent)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
             matrix_comparison_max=mp.nstr(max(abs(z) for z in form['K']-Kold),120),
             source_V_ground_reference='3.840240026438',levels=rows)
    (P/f'cluster_{tag}.json').write_text(json.dumps(out,indent=2)+'\n')
    with (P/f'cluster_{tag}.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 180,int(sys.argv[2]) if len(sys.argv)>2 else 160,sys.argv[3] if len(sys.argv)>3 else 'main')
