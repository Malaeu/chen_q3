"""Task B: literal-source window return; numerical values are DIAG, not enclosures."""
from pathlib import Path
import sys,json,importlib.util,warnings,time
import numpy as np
import mpmath as mp
from scipy.integrate import quad,IntegrationWarning
from scipy.special import roots_legendre
OUT=Path(__file__).resolve().parents[1]
REPO=OUT.parents[2]
BUILDER=OUT.parent/'corner_vs_matrix_detection_2026-11-04/builder'
sys.path.insert(0,str(BUILDER))
import source_float
from task_a import F

def g(x): return (16*x**4-49*x*x+12.5)*np.exp(-x*x)/np.sqrt(np.pi)
def chi(y):
    v=4*np.abs(y)-3
    out=np.ones_like(v);out[v>=1]=0;mid=(v>0)&(v<1)
    z=v[mid];a=np.exp(-1/z);b=np.exp(-1/(1-z));out[mid]=b/(a+b)
    return out

def coefficients(m,N):
    L=np.log(m);x=-L/2+L*np.arange(N)/N
    u=chi(2*x/L)*(g(x-L/4)+g(x+L/4))
    d=np.full(m+1,np.sqrt(2.));d[0]=1
    return np.fft.rfft(u).real[:m+1]/N*np.sqrt(L)*d

def pole(m):
    L=np.log(m);j=np.arange(m+1);d=np.full(m+1,np.sqrt(2.));d[0]=1
    return np.sqrt(2/L)*d*np.sinh(L/4)/((2*np.pi*j/L)**2+.25)

def poly_form(m,c):
    """Function-level W via exact finite-cosine overlap R(s), no W matrix."""
    L=np.log(m);j=np.arange(m+1);k=2*np.pi*j/L;d=np.full(m+1,np.sqrt(2));d[0]=1
    b=d*c/np.sqrt(L);kk=k[1:];bb=b[1:];r=np.empty(m)
    # R(s)=(L-s)(b0²+sum b_j² cos(k_js)/2)+sum r_j sin(k_js).
    # This overlap identity integrates the literal zero-extended polynomial.
    for n in range(1,m+1):
        den=k[n]**2-kk**2;den[n-1]=np.inf
        r[n-1]=-b[n]**2/(2*k[n])-2*b[0]*b[n]/k[n]-2*k[n]*b[n]*np.sum(bb/den)
    norm=float(c@c)
    def corr(s):return (L-s)*(b[0]**2+np.dot(bb*bb/2,np.cos(kk*s)))+np.dot(r,np.sin(kk*s))
    def integ(s):
        if not s:return 0.
        delta=s*(b[0]**2+np.dot(bb*bb/2,np.cos(kk*s)))+L*np.dot(bb*bb,np.sin(kk*s/2)**2)-np.dot(r,np.sin(kk*s))
        return 2*np.exp(-s/2)/(-np.expm1(-2*s))*delta
    with warnings.catch_warnings(record=True) as ws:
        warnings.simplefilter('always',IntegrationWarning)
        arch,qe=quad(integ,0,L,epsabs=2e-10,epsrel=2e-11,limit=1200)
    z=np.exp(-L/2);arch+=2*norm*(np.arctanh(z)+np.arctan(z))
    arch-=(np.euler_gamma+np.log(8*np.pi)+np.pi/2)*norm
    atoms,weights=source_float.prime_power_atoms(m)
    prime=float(2*np.dot(weights,np.array([corr(s) for s in np.log(atoms)])))
    po=float((pole(m)@c)**2)
    return float(arch-prime+po),dict(arch=float(arch),prime=prime,pole=po,quad_error_estimate=float(qe),integration_warnings=[str(w.message) for w in ws])

def cut_form(m,nodes=768):
    L=np.log(m);gx,gw=roots_legendre(nodes)
    def u(x):return chi(2*x/L)*(g(x-L/4)+g(x+L/4))
    def integrate(fun,a,b):
        x=(a+b)/2+(b-a)*gx/2
        return (b-a)/2*np.dot(gw,fun(x))
    norm=integrate(lambda x:u(x)**2,-L/2,L/2)
    def corr(s):return integrate(lambda x:u(x)*u(x+s),-L/2,L/2-s)
    def integrand(s):
        if not s:return 0.
        return 2*np.exp(-s/2)/(-np.expm1(-2*s))*(norm-corr(s))
    with warnings.catch_warnings(record=True) as ws:
        warnings.simplefilter('always',IntegrationWarning)
        ar,qe=quad(integrand,0,L,epsabs=5e-10,epsrel=5e-11,limit=500)
    z=np.exp(-L/2);ar+=2*norm*(np.arctanh(z)+np.arctan(z))
    ar-=(np.euler_gamma+np.log(8*np.pi)+np.pi/2)*norm
    atoms,weights=source_float.prime_power_atoms(m)
    prime=2*np.dot(weights,np.array([corr(s) for s in np.log(atoms)]))
    moment=integrate(lambda x:np.sqrt(2)*np.cosh(x/2)*u(x),-L/2,L/2)
    pu=integrate(lambda x:np.real(np.exp((1/3+7j)*x))*u(x),-L/2,L/2)+1j*integrate(lambda x:np.imag(np.exp((1/3+7j)*x))*u(x),-L/2,L/2)
    return float(ar-prime+moment**2),float(4*np.real(pu**2)),float(qe)

def plant_form(m,c):
    L=np.log(m);u=1/3+7j;j=np.arange(m+1);k=2*np.pi*j/L;d=np.full(m+1,np.sqrt(2));d[0]=1
    # Literal builder uses z=gamma+i*a. This is the even Laplace moment at conjugate u.
    z=7+1j/3
    ev=2*d*z*np.sin(z*L/2)/(np.sqrt(L)*(z*z-k*k))
    return float(4*np.real(np.dot(c,ev)**2))

def ref(m,plant=False):
    with mp.workdps(65):
        t=mp.log(m)/2;z=[];n=1
        while True:
            u=mp.zetazero(n)-mp.mpf('.5')
            if u.imag>60:break
            z.append(u);n+=1
        val=4*mp.re(mp.fsum(F(u)**2*(1+mp.exp(u*t)) for u in z))
        if plant:
            u=mp.mpf(1)/3+7j
            val+=8*mp.re(F(u)**2*(1+mp.cosh(u*t)))
        return str(val)

def error_bound(L,plant=False):
    with mp.workdps(60):
        L=mp.mpf(L)
        E=mp.mpf('1e27')*(1+L)*mp.exp(3*L/4-L*L/256)+mp.mpf('1e27')*(1+L)**4*mp.exp(-5*L/4)
        return (32 if plant else 27)*E*(mp.mpf('4e5')*mp.exp(L/4)+E)

def main():
    start=time.time();rows=[];cross=[]
    with mp.workdps(65):
        crossings={world:str(mp.findroot(lambda L:mp.log(error_bound(L,world=='plant'))+30*mp.log(10),(360,370))) for world in ['zeta','plant']}
    global_bound=dict(domain='L>=1',E='1e27*(1+L)*exp(3*L/4-L^2/256)+1e27*(1+L)^4*exp(-5*L/4)',B_zeta='27*E*(4e5*exp(L/4)+E)',B_plant='32*E*(4e5*exp(L/4)+E)',real_L_infimum_for_strict_bound_below_1e_minus_30=crossings,first_integer_L_below_1e_minus_30=364,kind='explicit conservative paper continuity bound; not empirical fit, not a machine interval certificate',proof='task_b_notes.md')
    for m in [16,64,300,1000,3000]:
        v=coefficients(m,65536);vlow=coefficients(m,32768);p=pole(m)
        vt=v.copy();vt[0]=0;alpha=float(p@vt/p[1]);w=vt.copy();w[1]-=alpha
        vals=[];metas=[]
        for c in [v,vt,w]:
            q,meta=poly_form(m,c);vals.append(q);metas.append(meta)
        matrix_values=None
        if m<=300:
            import gmpy2 as gg
            path=OUT.parent/'ground_state_zeros_2026-11-03/inputs/analytic_source.py'
            spec=importlib.util.spec_from_file_location('pinned_b_source',path);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
            out,smeta=mod.build(m,256);E=out['zeta'][0]
            matrix_values=[]
            for c in [v,vt,w]:
                cv=[gg.mpfr(float(x)) for x in c]
                matrix_values.append(float(sum(cv[i]*sum(E[i,j]*cv[j] for j in range(m+1)) for i in range(m+1))))
            cross.append(dict(m=m,function_values=vals,matrix_values=matrix_values,max_abs_difference=max(abs(a-b) for a,b in zip(vals,matrix_values)),source_bits=256))
            vals=matrix_values
        qcut,qcutplant,qerr=cut_form(m)
        qcut2,qp2,_=cut_form(m,1024)
        for plant in [False,True]:
            stages=np.array(vals)+([plant_form(m,c) for c in [v,vt,w]] if plant else 0)
            qc=qcut+(qcutplant if plant else 0)
            target=ref(m,plant)
            row=dict(m=m,L=str(np.log(m)),world='plant' if plant else 'zeta',q=float(stages[2]),target=target,return_error=float(stages[2])-float(target),chi_component=qc-float(target),cosine_projection_component=float(stages[0]-qc),e0_component=float(stages[1]-stages[0]),e1_component=float(stages[2]-stages[1]),cutoff_form=qc,v0=float(v[0]),e1_correction=alpha,pole_residual=float(p@w),fft_coefficient_repeat_max=float(np.max(np.abs(v-vlow))),cutoff_quadrature_repeat_difference=float(qcut-qcut2+(qcutplant-qp2 if plant else 0)),cutoff_quad_error_estimate=qerr,form_quad_error_estimates=[x['quad_error_estimate'] for x in metas],integration_warnings=[x['integration_warnings'] for x in metas],global_return_bound=str(error_bound(np.log(m),plant)),bound_applies_to='same world, including finite-rank quartet when plant',interval_certificate=False)
            rows.append(row)
        print(json.dumps(dict(m=m,q=rows[-2]['q'],target=rows[-2]['target'],crosscheck=cross[-1] if m<=300 else None)),flush=True)
        (OUT/'task_b.json').write_text(json.dumps(dict(rows=rows,crosschecks=cross,seconds=time.time()-start,global_bound=global_bound),indent=2)+'\n')
if __name__=='__main__':main()
