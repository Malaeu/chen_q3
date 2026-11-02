"""Independent220-dps sinc-kernel local-max validation of selected zero cells.

No main scanner kernel is imported. Denser grids plus independently refined
stationary roots are diagnostics, not interval certificates of exhaustive maxima.
"""
from pathlib import Path
import csv,json,time,hashlib
from functools import lru_cache
import mpmath as mp
OUT=Path(__file__).resolve().parent

def sinc_pair(z):
    if z==0:return mp.mpf(1),mp.mpf(0)
    if abs(z)<mp.mpf('.25'):
        sn=mp.sinc(z);term=-z/3;der=term;k=1
        while True:
            term*=-z*z/(2*k*(2*k+3));der+=term;k+=1
            if abs(term)<mp.eps*max(abs(der),mp.mpf('1e-1000')):break
        return sn,der
    sn=mp.sin(z);return sn/z,(z*mp.cos(z)-sn)/(z*z)

def basis(m,L,t):
    b=L/2;out=[];der=[]
    for n in range(m+1):
        om=2*mp.pi*n/L;factor=(1 if n==0 else mp.sqrt(2))*(-1)**n/mp.sqrt(L)
        a,da=sinc_pair((t-om)*b);c,dc=sinc_pair((t+om)*b)
        out.append(factor*b*(a+c));der.append(factor*b*b*(da+dc))
    return out,der

def write_csv(name,rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

def main():
    mp.mp.dps=220;start=time.monotonic();fmt=lambda x:mp.nstr(x,210)
    zrows={int(r['k']):r for r in csv.DictReader((OUT/'zeros.csv').open())}
    @lru_cache(None)
    def ordinate(k):
        if k in zrows:
            initial=mp.mpf(zrows[k]['gamma'])
            root=mp.findroot(mp.siegelz,initial,solver='newton',tol=mp.mpf('1e-205'),maxsteps=8,verify=True)
        else:root=mp.im(mp.zetazero(k))
        return root
    allmain={};selected={};sources={}
    for m in(16,20,24):
        data=list(csv.DictReader((OUT/f'samples_m{m}.csv').open()))
        byprofile={}
        for r in data:
            i=int(r['i']);k=int(r['k']);allmain[m,i,k]=r;byprofile.setdefault(i,[]).append(r)
        for i,rows in byprofile.items():
            rows.sort(key=lambda r:int(r['k']));kk={int(r['k']) for r in rows};reasons={}
            def add(k,why):
                if k in kk:reasons.setdefault(k,set()).add(why)
            add(1,'first zero');add(max(kk),'last zero')
            for threshold in('1e-6','1e-2'):
                crossing=next((int(r['k']) for r in rows if mp.mpf(r['rho'])>=mp.mpf(threshold)),None)
                if crossing:
                    for k in(crossing-1,crossing,crossing+1):add(k,'first '+threshold+' crossing and neighbor')
            highest=max(rows,key=lambda r:mp.mpf(r['rho']));add(int(highest['k']),'largest rho in profile')
            for k,why in reasons.items():selected[m,i,k]='; '.join(sorted(why))
        path=OUT/f'core_m{m}_dps220_gl192.json';d=json.loads(path.read_text());V=mp.matrix([[mp.mpf(x) for x in row] for row in d['V']]);sources[m]=(mp.log(m),V,hashlib.sha256(path.read_bytes()).hexdigest())
    selection=[dict(m=m,i=i,k=k,reasons=why) for (m,i,k),why in sorted(selected.items())];write_csv('validation_selected.csv',selection)
    groups={}
    for m,i,k in selected:groups.setdefault((m,k),[]).append(i)
    results=[]
    for count,((m,k),indices) in enumerate(sorted(groups.items()),1):
        L,V,source_sha=sources[m];g=ordinate(k);gn=ordinate(k+1);gapn=gn-g;gapp=g-ordinate(k-1) if k>1 else gapn;delta=min(gapp,gapn)/2
        left=g-delta;right=g+delta
        intervals=256 if any(mp.mpf(allmain[m,i,k]['rho'])>mp.mpf('.95') for i in indices) else 128
        grid=[left+(right-left)*j/intervals for j in range(intervals+1)]
        bb=[basis(m,L,t) for t in grid]
        for i in sorted(indices):
            coeff=[V[n,i] for n in range(m+1)]
            values=[mp.fsum(c*v for c,v in zip(coeff,b[0])) for b in bb]
            derivatives=[mp.fsum(c*v for c,v in zip(coeff,b[1])) for b in bb]
            scale=max(abs(x) for x in derivatives)
            def phi(t):return mp.fsum(c*v for c,v in zip(coeff,basis(m,L,t)[0]))
            def dphi(t):return mp.fsum(c*v for c,v in zip(coeff,basis(m,L,t)[1]))/scale
            candidates=[(abs(v),t) for v,t in zip(values,grid)];roots=[]
            if scale:
                for j in range(intervals):
                    if derivatives[j]==0:roots.append(grid[j])
                    elif derivatives[j]*derivatives[j+1]<0:
                        root=mp.findroot(dphi,(grid[j],grid[j+1]),solver='ridder',tol=mp.mpf('1e-190'),maxsteps=100,verify=True)
                        if left<=root<=right:roots.append(root)
            for root in roots:candidates.append((abs(phi(root)),root))
            numerator=abs(phi(g));candidates.append((numerator,g));denominator,argmax=max(candidates,key=lambda x:x[0]);rho=numerator/denominator
            original=allmain[m,i,k];oldrho=mp.mpf(original['rho']);old_den=mp.mpf(original['denominator']);old_num=mp.mpf(original['numerator'])
            row=dict(m=m,i=i,k=k,reasons=selected[m,i,k],dps=220,grid_subintervals=intervals,gamma=fmt(g),delta=fmt(delta),numerator=fmt(numerator),denominator=fmt(denominator),rho=fmt(rho),argmax=fmt(argmax),stationary_count=len(roots),main_rho=original['rho'],rho_absolute_difference=fmt(abs(rho-oldrho)),rho_relative_difference=fmt(abs(rho-oldrho)/max(abs(rho),mp.mpf('1e-210'))),denominator_relative_difference=fmt(abs(denominator-old_den)/denominator),numerator_relative_difference=fmt(abs(numerator-old_num)/max(numerator,mp.mpf('1e-210'))),threshold_1e6_class_agrees=bool((rho>=mp.mpf('1e-6'))==(oldrho>=mp.mpf('1e-6'))),threshold_1e2_class_agrees=bool((rho>=mp.mpf('1e-2'))==(oldrho>=mp.mpf('1e-2'))),source220_sha256=source_sha)
            results.append(row)
        (OUT/'validation_results.json').write_text(json.dumps(results,indent=2)+'\n')
        print('GROUP',count,'/',len(groups),'m',m,'k',k,'cases',len(results),'elapsed',round(time.monotonic()-start,1),flush=True)
    write_csv('validation_results.csv',results)
    maximum=lambda key:max(mp.mpf(r[key]) for r in results)
    summary=dict(status='INDEPENDENT_SINC_DIAGNOSTIC_VALIDATION',cases=len(results),groups=len(groups),dps=220,source_order=192,grid_subintervals=[128,256],max_rho_absolute_difference=fmt(maximum('rho_absolute_difference')),max_rho_relative_difference=fmt(maximum('rho_relative_difference')),max_denominator_relative_difference=fmt(maximum('denominator_relative_difference')),max_numerator_relative_difference=fmt(maximum('numerator_relative_difference')),threshold_classification_mismatches=sum(not(r['threshold_1e6_class_agrees'] and r['threshold_1e2_class_agrees']) for r in results),interval_certificate=False,scope='Separate sinc kernel, source220, refined zero ordinates and denser grid; no rigorous exhaustive-maximum certificate',elapsed=time.monotonic()-start)
    (OUT/'validation_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    used=sorted(set([k for m,i,k in selected]+[k+1 for m,i,k in selected]+[k-1 for m,i,k in selected if k>1]))
    (OUT/'validation_zero_ordinates.json').write_text(json.dumps({str(k):fmt(ordinate(k)) for k in used},indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':main()
