"""Finite optimized step residuals. DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
import sys,csv,json
import mpmath as mp
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parents[2]/'suzuki_W_2026-11-02'/'prediction'))
from scan import g_function,arithmetic

def write(name,rows):
    with (ROOT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def st(x):return mp.nstr(x,65)
def levinson(r,targets):
    a=[];v=r[0];neg=int(v<0);out={}
    if 1 in targets:out[1]=(v,[mp.mpf(1)],0,neg)
    for p in range(1,len(r)):
        if abs(v)<mp.mpf('1e-70'):raise ArithmeticError('unresolved pivot')
        refl=(r[p]-mp.fsum(a[j-1]*r[p-j] for j in range(1,p)))/v
        a=[a[j-1]-refl*a[p-j-1] for j in range(1,p)]+[refl]
        oldneg=neg;v*=1-refl**2;neg+=v<0
        if p+1 in targets:out[p+1]=(v,[-x for x in reversed(a)]+[mp.mpf(1)],oldneg,neg)
    return out
def autocorr(w):return [mp.fsum(w[i]*w[i+k] for i in range(len(w)-k)) for k in range(len(w))]+[mp.mpf(0)]
def Q(C,h,s):
    a=s/h;k=int(mp.floor(a));u=a-k
    return 0 if k>=len(C)-1 else 2*h*((1-u)*C[k]+u*C[k+1])
def r_from(gs):return [-2*gs[1]]+[2*gs[k]-gs[k-1]-gs[k+1] for k in range(1,len(gs)-1)]
def quadratic(r,C):return r[0]*C[0]+2*mp.fsum(r[k]*C[k] for k in range(1,len(r)))

def main():
    mp.mp.dps=90;budgets=[];cors=[];profiles=[];grad=[]
    for mesh in (32,64):
      h=mp.mpf(1)/mesh;N=6*mesh;times=range(N+1)
      for world in ('zeta','dh','plant'):
        g,atoms=g_function(world,mp.mpf(6));gs=[g(k*h) for k in times];r=r_from(gs)
        states=levinson(r,{mesh*t for t in range(1,7)})
        alpha=mp.mpf('1.5') if world=='dh' else mp.mpf('.5')
        c=mp.log(5/mp.pi)+mp.digamma(mp.mpf('.75')) if world=='dh' else -mp.euler-mp.log(8*mp.pi)-mp.pi/2
        for n,(v,w,oldneg,neg) in states.items():
          t=n*h;C=autocorr(w);norm=h*C[0]
          ap=mp.fsum(w[i]*2*(mp.exp((i+1)*h/2)-mp.exp(i*h/2)) for i in range(n))
          am=mp.fsum(w[i]*2*(mp.exp(-i*h/2)-mp.exp(-(i+1)*h/2)) for i in range(n))
          pole=0 if world=='dh' else 2*ap*am
          arith=-mp.fsum(weight*Q(C,h,s) for s,weight,integer in atoms if s<t)
          wp=2*mp.pi/mp.log(2)+mp.j/4
          gp=[4*mp.re((mp.cos(wp*k*h)-1)/wp**2) for k in range(n+1)] if world=='plant' else [mp.mpf(0)]*(n+1)
          plant=quadratic(r_from(gp),C)
          # Independent arch component obtained by removing source parts in g.
          ga=[gs[k]+c*k*h/2-mp.fsum(weight*(k*h-s) for s,weight,integer in atoms if s<k*h)+(16*mp.sinh(k*h/4)**2 if world!='dh' else 0)-gp[k] for k in range(n+1)]
          arch=quadratic(r_from(ga),C);direct=quadratic(r[:n],C)
          prime_atoms=arithmetic('zeta',t)
          qp=[(integer,Q(C,h,s),weight) for s,weight,integer in prime_atoms if s<t]
          budgets.append(dict(world=world,mesh=mesh,t=st(t),sigma2=st(v),past_negative_index=oldneg,full_negative_index=neg,minimizer=oldneg==0,norm2=st(norm),arch=st(arch),constant=st(c*norm),pole=st(pole),arithmetic=st(arith),plant=st(plant),source_sum=st(arch+c*norm+pole+arith+plant),source_error=st(abs(arch+c*norm+pole+arith+plant-v)),direct_error=st(abs(direct-v)),positive_prime_correlations=sum(q>mp.mpf('1e-40') for _,q,_ in qp),negative_prime_correlations=sum(q<-mp.mpf('1e-40') for _,q,_ in qp),total_prime_correlations=len(qp),max_Q=st(max([q for _,q,_ in qp],default=0))))
          for integer,q,weight in qp:cors.append(dict(world=world,mesh=mesh,t=st(t),past_negative_index=oldneg,n=integer,Q=st(q),zeta_reference_weight=st(weight),zeta_reference_weighted_Q=st(q*weight)))
          for i,x in enumerate(w):profiles.append(dict(world=world,mesh=mesh,t=st(t),bin=i,x_left=st(i*h),x_right=st((i+1)*h),f=st(x),past_negative_index=oldneg))
        # Genuine reoptimized coefficient derivative on a positive past.
        n=mesh;C=autocorr(states[n][1]);target=-Q(C,h,mp.log(2));errors=[]
        for eps in (mp.mpf('1e-10'),mp.mpf('5e-11')):
          vals=[]
          for sign in (-1,1):
            gg=[gs[k]+sign*eps*max(0,k*h-mp.log(2)) for k in range(n+1)]
            vals.append(levinson(r_from(gg),{n})[n][0])
          fd=(vals[1]-vals[0])/(2*eps)
          grad.append(dict(world=world,mesh=mesh,t=1,n=2,epsilon=st(eps),minus_Q=st(target),reoptimized_fd=st(fd),absolute_error=st(abs(fd-target))))
        print('DONE',world,mesh,flush=True)
    write('budgets.csv',budgets);write('prime_correlations.csv',cors);write('profiles.csv',profiles);write('gradient.csv',grad)
    (ROOT/'summary.json').write_text(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','dps':90,'max_source_error':max(budgets,key=lambda x:mp.mpf(x['source_error']))['source_error'],'max_direct_error':max(budgets,key=lambda x:mp.mpf(x['direct_error']))['direct_error'],'zeta_cone_violations':[r for r in budgets if r['world']=='zeta' and r['positive_prime_correlations']>0]},indent=2)+'\n')
if __name__=='__main__':main()
