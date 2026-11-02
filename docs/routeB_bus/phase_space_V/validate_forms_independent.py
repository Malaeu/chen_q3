"""Independent physical-integral checks for v_forms; no interval certificate.

Runs sampled entries only. Does not reuse q_even or the arch moment formulas
for its reference values; does not write files or change imported sources.
"""
import json
from pathlib import Path
import sys
import mpmath as mp

sys.path.insert(0,str(Path(__file__).resolve().parent))
from v_forms import build_forms

def main():
    f=build_forms(8,8,dps=90,order=48)
    L=f['L']
    ds=lambda n:mp.sqrt(2) if n else mp.mpf(1)
    def phi(x,n):
        return ds(n)*(-1)**n*mp.cos(2*mp.pi*n*x/L)/mp.sqrt(L)
    def corr(s,i,k):
        if s>=L:return mp.mpf(0)
        return mp.quad(lambda x:phi(x,i)*phi(x+s,k)+phi(x,k)*phi(x+s,i),[-L/2,L/2-s])
    # Reference closed correlation obtained by integrating the physical basis,
    # with the alternative difference/sum-frequency antiderivative.
    def physical_q(s,i,k):
        if s>=L:return mp.mpf(0)
        r=s/L
        def H(z):
            return (1-r) if not z else -mp.sin(2*mp.pi*z*r)/(2*mp.pi*z)
        # Integrals cos(2π i y) cos(2π k(y+r)) symmetrized.
        def C(a,b):
            def integ_cos(v,phase):
                if not v:return (1-r)*mp.cos(phase)
                return (mp.sin(2*mp.pi*v*(1-r)+phase)-mp.sin(phase))/(2*mp.pi*v)
            return (integ_cos(a-b,-2*mp.pi*b*r)+integ_cos(a+b,2*mp.pi*b*r))/2
        return ds(i)*ds(k)*(C(i,k)+C(k,i))
    rows=[]
    for i,k in [(0,0),(0,1),(1,1),(1,3),(3,3),(3,8),(8,8)]:
        # Stop quadrature from resolving meaningless sub-working-precision
        # cancellation in 2delta-Q near its removable endpoint.
        def integ(s):
            if abs(s)<mp.mpf('1e-50'):return ds(i)*ds(k)/L
            j=mp.exp(-s/2)/(-mp.expm1(-2*s))
            return j*((2 if i==k else 0)-physical_q(s,i,k))
        cuts=[L*j/8 for j in range(9)]
        a=mp.quad(integ,cuts)
        if i==k:a+=2*mp.quad(lambda s:mp.exp(-s/2)/(-mp.expm1(-2*s)),[L,L+1,L+4,L+12,mp.inf])
        x=mp.quad(lambda y:mp.log1p(y*y)*phi(y,i)*phi(y,k),[-L/2,0,L/2])
        p=mp.quad(lambda y:mp.sqrt(2)*mp.cosh(y/2)*phi(y,i),[-L/2,0,L/2])
        cq=max(abs(corr(L*r,i,k)-physical_q(L*r,i,k)) for r in [mp.mpf('.13'),mp.mpf('.37'),mp.mpf('.91')])
        rows.append({'i':i,'k':k,'arch_abs_error':mp.nstr(abs(a-f['arch'][i,k]),12),'spatial_abs_error':mp.nstr(abs(x-f['spatial'][i,k]),12),'pole_abs_error':mp.nstr(abs(p-f['pole'][i]),12),'correlation_abs_error':mp.nstr(cq,12)})
    print(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','m':8,'N':8,'dps':90,'GL_order_per_panel':48,'reference':'physical basis integration and alternative correlation antiderivative','rows':rows},indent=2))

if __name__=='__main__':main()
