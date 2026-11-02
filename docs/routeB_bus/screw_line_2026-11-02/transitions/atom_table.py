"""Exact finite log-Dirichlet coefficients and source threshold coefficients.

DIAGNOSTIC_NEVER_A_PROOF. This does not differentiate the discrete N=m series.
"""
from pathlib import Path
import json,csv,hashlib
from fractions import Fraction
import mpmath as mp
import sympy as sp
P=Path(__file__).resolve().parent

def main():
    mp.mp.dps=100;x=sp.Symbol('tau');M=sp.Poly(x**4+2*x**3-6*x**2-2*x+1,x)
    a={n:[sp.Integer(0),sp.Integer(1),x,-x,sp.Integer(-1)][n%5] for n in range(2,241)}
    powers={n:sp.Poly(a[n],x) for n in range(2,241)}
    B={n:sp.Poly(0,x) for n in range(2,241)}
    for k in range(1,8):
        for n in B:B[n]=(B[n]+powers.get(n,sp.Poly(0,x))*sp.Rational((-1)**(k+1),k)).rem(M)
        nxt={}
        for n in range(2,241):
            f=sp.Poly(0,x)
            for d in sp.divisors(n):
                if d>=2 and n//d>=2:f+=sp.Poly(a[d],x)*powers.get(n//d,sp.Poly(0,x))
            nxt[n]=f.rem(M)
        powers=nxt
    tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
    assert abs(tau**4+2*tau**3-6*tau**2-2*tau+1)<mp.mpf('1e-95')
    def polyval(poly):return mp.fsum(mp.mpf(str(c))*tau**i for (i,),c in poly.terms())
    coeff=[mp.mpf(0)]*241;aa=[mp.mpf(0),mp.mpf(1),tau,-tau,mp.mpf(-1)]
    for n in range(2,241):coeff[n]=aa[n%5]*mp.log(n)-mp.fsum(coeff[d]*aa[(n//d)%5] for d in sp.divisors(n) if 1<d<n)
    errors=[abs(coeff[n]-polyval(B[n])*mp.log(n)) for n in range(2,241)]
    assert max(errors)<mp.mpf('1e-90')
    assert B[3].as_expr()==-x and sp.expand(B[6].as_expr()-(1+x*x))==0
    assert all(B[n].is_zero for n in range(5,241,5))
    rows=[]
    for n in range(20,241):
        fac=sp.factorint(n);pp=len(fac)==1;p,k=next(iter(fac.items())) if pp else (None,None)
        wz=mp.log(int(p))/mp.sqrt(n) if pp else mp.mpf(0)
        cd=polyval(B[n]);wd=cd*mp.log(n)/mp.sqrt(n)
        sign=0 if B[n].is_zero else (1 if wd>0 else -1)
        rows.append(dict(m=n,log_m=mp.nstr(mp.log(n),70),prime_power=pp,prime=p,exponent=k,
          zeta_b_over_sqrt_n=mp.nstr(wz,70),zeta_atom_sign=int(pp),
          DH_exact_b_over_log_n=str(B[n].as_expr()),DH_b_over_sqrt_n=mp.nstr(wd,70),DH_atom_sign=sign,DH_exact_zero=B[n].is_zero,
          zeta_source_tau_rankone_coefficient=mp.nstr(-2*wz*mp.log(n),70),DH_source_tau_rankone_coefficient=mp.nstr(-2*wd*mp.log(n),70),
          zeta_source_L_rankone_coefficient=mp.nstr(-2*wz,70),DH_source_L_rankone_coefficient=mp.nstr(-2*wd,70)))
    for name,rr in [('all_atoms.csv',rows),('prime_powers.csv',[r for r in rows if r['prime_power']]),('DH_non_prime_powers.csv',[r for r in rows if not r['prime_power']])]:
        with (P/name).open('w') as f:
            w=csv.DictWriter(f,fieldnames=list(rr[0]));w.writeheader();w.writerows(rr)
    summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',range=[20,240],all_integer_count=len(rows),prime_power_count=sum(r['prime_power'] for r in rows),
      DH_non_prime_power_count=sum(not r['prime_power'] for r in rows),DH_non_prime_power_nonzero=sum(not r['prime_power'] and r['DH_atom_sign']!=0 for r in rows),
      zeta_atom_sign_counts={str(s):sum(r['zeta_atom_sign']==s for r in rows) for s in [-1,0,1]},
      DH_atom_sign_counts={str(s):sum(r['DH_atom_sign']==s for r in rows) for s in [-1,0,1]},
      DH_prime_power_sign_counts={str(s):sum(r['prime_power'] and r['DH_atom_sign']==s for r in rows) for s in [-1,0,1]},
      coefficient_recurrence_max_error=mp.nstr(max(errors),70),tau=mp.nstr(tau,70),exact_zero_test='polynomial remainder modulo tau^4+2tau^3-6tau^2-2tau+1',
      numerical_sign_evaluation='100 dps; exact-zero coefficients removed first',matrix_jump='dotA_plus-dotA_minus=-2*(b(n)/sqrt(n))*L*d_b*d_b^T, tau=dlogL',
      source_g_normalization='Suzuki g(t)=-q_source[1_[0,t]]/2; arithmetic hinge +(b(n)/sqrt(n))*(t-log(n))_+',
      source_g_audit='source_audit/SOURCE_AUDIT.md; Suzuki arXiv:2206.03682v4 (1.1),(1.8), arXiv:2209.04658v3 (1.1)',
      derivative_variable_guard='g is continuous; jump g_prime=+b(n)/sqrt(n). Matrix dot=d/dtau=L*d/dL. Do not call these discrete N=m increments.')
    (P/'atom_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
