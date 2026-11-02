"""Fixed-window phase-space V resolution diagnostic for true even ground states.

L=log(window_m) is independent of modal N. All forms come from v_forms.py.
No N-convergence, interval certificate, or cofinal bound is claimed.
"""
from pathlib import Path
import json,csv,hashlib,time,argparse
import mpmath as mp
from v_forms import build_forms,quantities
OUT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write_csv(path,rows):
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

def run(validation=False):
    dps,order=(160,160) if validation else (140,128)
    cells={16:[64]} if validation else {8:[44,56,68],12:[44,48,52,56,60,64],16:[44,48,52,56,60,64]}
    rows=[];raw=[];start=time.monotonic();fmt=lambda x:mp.nstr(x,dps)
    source_hashes={'v_forms.py':sha(OUT/'v_forms.py'),'resolution.py':sha(OUT/'resolution.py')}
    for wm,Ns in cells.items():
        NN=max(Ns);forms=build_forms(wm,NN,dps,order)
        assert forms['K'].rows==NN+1
        print('BUILT',wm,NN,'elapsed',time.monotonic()-start,flush=True)
        for N in Ns:
            K=forms['K'][:N+1,:N+1];ev,vec=mp.eigsy(K);f=vec[:,0];f/=mp.norm(f)
            h=forms['h'][:N+1,:]
            if mp.fdot(f,h)<0:f=-f
            q=quantities(forms,f,K);res=mp.norm(K*f-ev[0]*f)
            row=dict(window_m=wm,N=N,L=fmt(forms['L']),dps=dps,quadrature_order=order,
                     lambda0=fmt(ev[0]),gap=fmt(ev[1]-ev[0]),Apositive=fmt(q['arch']),spatial_log1p_x2=fmt(q['spatial']),
                     V=fmt(q['V']),w0=fmt(q['w0']),eigenpair_residual=fmt(res),
                     Rayleigh_minus_lambda0=fmt(q['Rayleigh']-ev[0]),norm_squared=fmt(mp.fdot(f,f)))
            rows.append(row)
            raw.append(dict(**row,ground_even_coefficients=[fmt(x) for x in f],eigenvalues=[fmt(x) for x in ev],
                            projected_h_coefficients=[fmt(x) for x in h],source_hashes=source_hashes,
                            active_atoms=[dict(k=k,log_k=fmt(a),weight=fmt(w)) for k,a,w in forms['atoms'] if a<forms['L']],
                            definition='V=Apositive+int log(1+x^2)|f(x)|^2 dx, full j(s)=exp(-s/2)/(1-exp(-2s)); physical x',
                            scope='Fixed-window finite-resolution diagnostic; no convergence certificate'))
            tag='validation' if validation else 'main'
            (OUT/f'resolution_{tag}.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',results=raw,elapsed=time.monotonic()-start),indent=2)+'\n')
            write_csv(OUT/f'resolution_{tag}.csv',rows)
            print('CELL',wm,N,'lambda',mp.nstr(ev[0],12),'V',mp.nstr(q['V'],18),'w0',mp.nstr(q['w0'],15),'elapsed',round(time.monotonic()-start,1),flush=True)
    print('DONE',time.monotonic()-start,flush=True)

def finalize():
    mp.mp.dps=180;fmt=lambda x:mp.nstr(x,100)
    a=json.loads((OUT/'resolution_main.json').read_text())['results'];v=json.loads((OUT/'resolution_validation.json').read_text())['results'][0]
    r=next(x for x in a if x['window_m']==16 and x['N']==64)
    checks=dict(window_m=16,N=64,main_dps=140,validation_dps=160,main_order=128,validation_order=160)
    for key in('lambda0','Apositive','spatial_log1p_x2','V','w0'):
        x=mp.mpf(r[key]);y=mp.mpf(v[key]);checks[key+'_absolute_difference']=fmt(abs(x-y));checks[key+'_relative_difference']=fmt(abs(x/y-1))
    f=mp.matrix(r['ground_even_coefficients']);g=mp.matrix(v['ground_even_coefficients']);checks['ground_vector_L2_difference']=fmt(mp.norm(f-g));checks['interval_certificate']=False
    (OUT/'resolution_validation_comparison.json').write_text(json.dumps(checks,indent=2)+'\n')
    ratios=[]
    for wm in(8,12,16):
        rr=sorted([x for x in a if x['window_m']==wm],key=lambda x:x['N'])
        for x,y in zip(rr,rr[1:]):
            ratios.append(dict(window_m=wm,N_left=x['N'],N_right=y['N'],lambda_ratio=fmt(mp.mpf(x['lambda0'])/mp.mpf(y['lambda0'])),V_ratio=fmt(mp.mpf(x['V'])/mp.mpf(y['V'])),V_change=fmt(mp.mpf(y['V'])-mp.mpf(x['V'])),Apositive_change=fmt(mp.mpf(y['Apositive'])-mp.mpf(x['Apositive'])),spatial_change=fmt(mp.mpf(y['spatial_log1p_x2'])-mp.mpf(x['spatial_log1p_x2'])),w0_change=fmt(mp.mpf(y['w0'])-mp.mpf(x['w0']))))
    write_csv(OUT/'resolution_ratios.csv',ratios)
    lines=['# Fixed-window V resolution diagnostic','',
           'All vectors are freshly computed L2-normalized even ground eigenvectors of the literal CCM matrix. L=log(window_m) stays fixed while N varies; the prime-power cutoff follows L, not N.','',
           'V=Apositive+integral log(1+x^2)|f(x)|^2 dx. Apositive uses the full jump kernel j(s)=exp(-s/2)/(1-exp(-2s)); spatial x is unscaled.','',
           '|window m|N|lambda0|Apositive|spatial term|V|w0|','|---:|---:|---:|---:|---:|---:|---:|']
    for r in a:lines.append(f"|{r['window_m']}|{r['N']}|{float(r['lambda0']):.8g}|{float(r['Apositive']):.12g}|{float(r['spatial_log1p_x2']):.12g}|{float(r['V']):.12g}|{float(r['w0']):.12g}|")
    lines+=['','Successive lambda and V ratios, changes in both V components, and w0 changes are in resolution_ratios.csv. Stability of V or overlap is not asserted to certify convergence of the bottom eigenvalue. No N is labeled converged.','',
            'Primary runs use140dps and eight-panel GL128. The log16,N64 cell is independently recomputed at160dps and GL160. Detailed discrepancies are in resolution_validation_comparison.json. This is a floating diagnostic, not an interval enclosure.','',
            'Ground coefficients, all eigenvalues, projected theta coefficients, source-code hashes and active atoms are preserved in resolution_main.json and resolution_validation.json. The source profile has H=hat h=4xi(1/2-it).','',
            'Replay:','```bash','uv run --with mpmath resolution.py','uv run --with mpmath resolution.py --validation','uv run --with mpmath resolution.py --finalize','```']
    (OUT/'RESULT_resolution.md').write_text('\n'.join(lines)+'\n');print(json.dumps(checks,indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--validation',action='store_true');p.add_argument('--finalize',action='store_true');args=p.parse_args()
    if args.finalize:finalize()
    else:run(args.validation)
