"""Diagnostic checks only: mpmath is not interval arithmetic or a sign proof."""
from __future__ import annotations
import argparse, json, time
from pathlib import Path
import mpmath as mp

def source_atom(z: mp.mpc, n: int) -> mp.mpc:
    a = mp.pi*n*n
    return (4*a*a*mp.exp(mp.mpf(9)*z/2)-6*a*mp.exp(mp.mpf(5)*z/2))*mp.exp(-a*mp.exp(2*z))

def ray(n: int, p: mp.mpc, theta: mp.mpf) -> mp.mpc:
    a = mp.pi*n*n
    z = a*mp.exp(2j*theta)
    b = p/2 + mp.mpf(5)/4
    # Exact recurrence, with the principal logarithm in |arg z|<pi/2.
    return a**(-p/2-mp.mpf(1)/4)*((p-mp.mpf(1)/2)*mp.gammainc(b,z,mp.inf)+2*mp.exp(b*mp.log(z)-z))

def head(p: mp.mpc, theta: mp.mpf, N: int) -> mp.mpc:
    return mp.fsum(ray(n,p,theta)+ray(n,-p,-theta) for n in range(1,N+1))

def reference_xi(p: mp.mpc) -> mp.mpc:
    s = mp.mpf(1)/2+p
    return s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)/2

def check(T: int, dps: int) -> dict:
    mp.mp.dps=dps
    theta=mp.pi/4-1/mp.mpf(T+1)
    c=mp.cos(2*theta)
    M=int(mp.ceil(mp.sqrt(40/c)))
    N=M-1
    p=mp.mpf(1)/4+1j*T
    fac=mp.exp(theta*T)
    approx=[mp.diff(lambda x:head(x,theta,N),p,j) for j in range(3)]
    refs=[mp.diff(reference_xi,p,j) for j in range(3)]
    beta=mp.pi*c*M*M
    B=448*M**3/c*mp.exp(-beta)
    D=4/c**4
    err=16*mp.re(p)*D*B/mp.exp(2*theta*T)
    Hn=4*mp.re(approx[1]*mp.conj(approx[0]))
    H=4*mp.re(refs[1]*mp.conj(refs[0]))
    symmetry=head(-mp.conj(p),theta,N)-mp.conj(approx[0])
    values={"T":T,"dps":dps,"N":N,"M":M,"theta":theta,"c":c,"beta":beta,
     "scaled_error_F_derivatives":[fac*abs(approx[j]-refs[j]) for j in range(3)],
     "scaled_B":B,"scaled_D":D,"Hn":Hn,"H_reference":H,
     "H_error_bound":err,"observed_H_error":abs(H-Hn),
     "scaled_Hn_over_sigma":Hn*fac**2/mp.re(p),
     "scaled_remainder_over_sigma":16*D*B,
     "reflection_error":abs(symmetry),
     "derivative_errors_fit_envelope_diagnostic":all(fac*abs(approx[j]-refs[j])<=B for j in range(3)),
     "H_error_fits_envelope_diagnostic":abs(H-Hn)<=err,
     "claimed_sign_certificate":False}
    def serial(x):
        if isinstance(x,(bool,str,int)):return x
        if isinstance(x,list):return [serial(y) for y in x]
        return mp.nstr(x,32)
    return {k:serial(v) for k,v in values.items()}

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--T',type=int,required=True)
    ap.add_argument('--dps',type=int,default=50)
    args=ap.parse_args()
    start=time.time()
    ans=check(args.T,args.dps)
    ans['runtime_seconds']=time.time()-start
    out=Path(__file__).parent/f'check_T{args.T}_dps{args.dps}.json'
    out.write_text(json.dumps(ans,indent=2))
    print(json.dumps(ans,indent=2))
