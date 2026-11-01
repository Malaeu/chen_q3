"""Numerical100-dps finite-profile peak and full-theta zero comparisons.

No symbolic identity for a peak is claimed. Theta zeros are found with
exponentially scaled sums, so vanishingly small tails never masquerade as zeros.
"""
from pathlib import Path
import json,csv
import mpmath as mp

OUT=Path(__file__).resolve().parent

def scaled_theta(x):
    """h^(r)=exp(x/2-pi*exp(2x))*S_r for x>=0,r=0,1,2."""
    x=mp.mpf(x);y1=mp.pi*mp.exp(2*x)
    sums=[mp.mpf(0)]*3;n=1;cutoff=mp.mpf('2.5')*mp.mp.prec
    while True:
        delta=(n*n-1)*y1
        if n>1 and delta>cutoff:break
        y=n*n*y1;ee=mp.exp(-delta)
        polys=(16*y*y-24*y,-60*y+120*y*y-32*y**3,
               -150*y+690*y*y-464*y**3+64*y**4)
        for r in range(3):sums[r]+=ee*polys[r]
        n+=1
    if x==0:sums[1]=mp.mpf(0) # exact parity, not a numerical tail cutoff
    return sums

def theta_equation(name,x):
    h,hp,hpp=scaled_theta(x)
    if name=='h_prime':return hp
    if name=='D_h':return -x*hp-h/2
    if name=='h_second':return hpp
    raise ValueError(name)

def theta_roots(step='0.001',end='3'):
    step=mp.mpf(step);end=mp.mpf(end)
    results=[]
    for name in('h_prime','D_h','h_second'):
        fun=lambda x:theta_equation(name,x)
        roots=[];brackets=[];prevx=mp.mpf(0);prev=fun(prevx)
        if prev==0:roots.append(mp.mpf(0));brackets.append([mp.mpf(0),mp.mpf(0)])
        min_nonzero=None
        for j in range(1,int(end/step)+1):
            x=step*j;fx=fun(x)
            if fx==0:
                roots.append(x);brackets.append([x,x])
            elif prev!=0 and fx*prev<0:
                root=mp.findroot(fun,(prevx,x),solver='anderson',tol=mp.mpf('1e-95'),verify=True)
                roots.append(root);brackets.append([prevx,x])
            if fx:
                av=abs(fx);min_nonzero=av if min_nonzero is None else min(min_nonzero,av)
            prevx=x;prev=fx
        for i,(root,bracket) in enumerate(zip(roots,brackets)):
            results.append(dict(function=name,root_index=i,x=root,bracket_left=bracket[0],bracket_right=bracket[1],scaled_residual=fun(root),scan_step=step,scan_end=end,minimum_nonzero_scaled_grid_value=min_nonzero))
    return results

def polynomial_stationary(a,L):
    """Independent check: f'=-omega*sin(theta)*sum n*a_n*U_(n-1)(cos theta)."""
    m=len(a)-1;pol=[mp.mpf(0)]*m
    us=[[mp.mpf(1)],[mp.mpf(0),mp.mpf(2)]]
    for n in range(2,m):
        u=[mp.mpf(0)]*(n+1)
        for j,v in enumerate(us[-1]):u[j+1]+=2*v
        for j,v in enumerate(us[-2]):u[j]-=v
        us.append(u)
    for n in range(1,m+1):
        for j,v in enumerate(us[n-1]):pol[j]+=n*a[n]*v
    rr=mp.polyroots(list(reversed(pol)),maxsteps=500,extraprec=200)
    interior=[r.real for r in rr if abs(r.imag)<mp.mpf('1e-80') and -1<r.real<1]
    xr=sorted(L*mp.acos(r)/(2*mp.pi) for r in interior)
    residual=max(abs(mp.polyval(list(reversed(pol)),r))/mp.fsum(abs(v)*abs(r)**j for j,v in enumerate(pol)) for r in rr)
    return xr,dict(stationary_polynomial_degree=m-1,stationary_polynomial_roots_returned=len(rr),stationary_polynomial_real_interior_roots=len(interior),stationary_polynomial_max_scaled_residual=residual)


def finite_shape(row):
    m=int(row['summary']['m']);L=mp.log(m);b=L/2
    coeff=[mp.mpf(x) for x in row['physical_modal_coefficients']]
    a=[(1 if n==0 else mp.sqrt(2))*(-1)**n*c/mp.sqrt(L) for n,c in enumerate(coeff)]
    om=2*mp.pi/L
    def f(x):return mp.fsum(v*mp.cos(n*om*x) for n,v in enumerate(a))
    def df(x):
        if x==0 or x==b:return mp.mpf(0)
        return -om*mp.fsum(n*v*mp.sin(n*om*x) for n,v in enumerate(a))
    # Dense stationary-point bracketing, with exact endpoint stationary values.
    samples=8192;roots=[];brackets=[];px=mp.mpf(0);pf=df(px)
    for j in range(1,samples):
        x=b*j/samples;fx=df(x)
        if fx and pf and fx*pf<0:
            r=mp.findroot(df,(px,x),solver='anderson',tol=mp.mpf('1e-95'),verify=True)
            if not roots or abs(r-roots[-1])>mp.mpf('1e-70'):
                roots.append(r);brackets.append((px,x))
        px=x;pf=fx
    polyroots,validation=polynomial_stationary(a,L)
    validation['stationary_polynomial_grid_match_error']=max(abs(x-y) for x,y in zip(roots,polyroots)) if len(roots)==len(polyroots) else mp.inf
    if len(roots)!=len(polyroots):raise ArithmeticError('Stationary polynomial and dense scan counts disagree')
    candidates=[mp.mpf(0),b]+roots
    peak=max(candidates,key=lambda x:abs(f(x)))
    bracket=next((br for r,br in zip(roots,brackets) if r==peak),(peak,peak))
    return dict(m=m,L=L,b=b,x_peak=peak,two_x_peak=2*peak,peak_value=f(peak),peak_density=f(peak)**2,
                derivative_residual=df(peak),peak_bracket_left=bracket[0],peak_bracket_right=bracket[1],
                stationary_roots=roots,stationary_density=[f(r)**2 for r in roots],
                peak_search_grid_points=samples+1,**validation,peak_search='global density maximum among endpoints and stationary roots, independently matched to all roots of derivative Chebyshev polynomial; floating diagnostic')

def write_csv(path,rows):
    with path.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)

def main():
    mp.mp.dps=100
    fmt=lambda x:mp.nstr(x,100)
    data=json.loads((OUT.parent/'shape_results.json').read_text())
    peaks=[finite_shape(r) for r in data if int(r['summary']['m']) in(20,24)]
    zeros=theta_roots()
    peakrows=[];logs=[];comparisons=[];raw=[]
    for p in peaks:
        pr={k:(fmt(v) if isinstance(v,mp.mpf) else v) for k,v in p.items() if k not in('stationary_roots','stationary_density')}
        distances=[(n,p['two_x_peak']-mp.log(n)) for n in range(2,13)]
        nearest=min(distances,key=lambda t:abs(t[1]));pr['nearest_log_n']=nearest[0];pr['two_x_minus_nearest_log_n']=fmt(nearest[1])
        peakrows.append(pr)
        raw.append(dict(**pr,stationary_roots=[fmt(x) for x in p['stationary_roots']],stationary_densities=[fmt(x) for x in p['stationary_density']]))
        for n,d in distances:logs.append(dict(m=p['m'],n=n,log_n=fmt(mp.log(n)),two_x_peak=fmt(p['two_x_peak']),signed_difference=fmt(d),absolute_difference=fmt(abs(d))))
        for z in zeros:
            comparisons.append(dict(m=p['m'],theta_function=z['function'],root_index=z['root_index'],theta_root=fmt(z['x']),x_peak=fmt(p['x_peak']),x_minus_root=fmt(p['x_peak']-z['x']),two_x_minus_root=fmt(p['two_x_peak']-z['x'])))
    zrows=[{k:(fmt(v) if isinstance(v,mp.mpf) else v) for k,v in r.items()} for r in zeros]
    write_csv(OUT/'peak_summary.csv',peakrows);write_csv(OUT/'peak_log_comparison.csv',logs);write_csv(OUT/'peak_theta_roots.csv',zrows);write_csv(OUT/'peak_theta_comparison.csv',comparisons)
    report=dict(dps=100,source_shape='../shape_results.json from pinned d6e7647 inputs',peaks=raw,theta_roots=zrows,
        theta_zero_scope='Numerical sign-change scan[0,3] step.001. Analytic termwise signs exclude roots x>=.5. No interval certificate of root count in(0,.5).',
        theta_tail_guard='Scaled sums always retain n=1; no zeros from underflow or absolute exponential cutoff.',
        symmetry='h_prime is odd and h_prime(0)=0; D_h and h_second are even. Positive roots reflect to negative roots.',
        no_symbolic_peak_identity=True,no_RH_claim=True)
    (OUT/'peak_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(peaks=peakrows,theta_roots=zrows),indent=2))

if __name__=='__main__':main()
