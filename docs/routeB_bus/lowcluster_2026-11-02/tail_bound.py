"""Explicit F-vector tail bounds beyond R; no interval arithmetic certificate.

Source row envelope: source_F_ONLY.md (3.4).
Sharper H envelope (t>=1):
  |H(t)| <= C*t^(13/4)*exp(-pi*t/4),
  C=(5/2)*Gamma(1/4)*exp(1/2)*2^(-1/4)*(1+sqrt(5)).
Proof: for s=1/2+it, |zeta(s)|<=1+2*sqrt(t²+1/4).
Rotate Gamma's defining integral by theta=pi/2-1/t:
 |Gamma(1/4+it/2)|<=Gamma(1/4)*(sin(1/t))^(-1/4)
                              *exp(-pi*t/4+1/2).
Use sin(1/t)>=2/(pi*t), t²+1/4<=5t²/4, and
1+2sqrt(t²+1/4)<=(1+sqrt(5))*t.  H=4xi gives C above.

After the row bound and n-m>=n/2, n>R>=2m, sum polynomial-times-
exponential tails by a geometric ratio.  Each individual eigen-coordinate
has error at most this Euclidean F-vector tail bound.
"""
import json,csv
from pathlib import Path
import mpmath as mp


def mangoldt(n):
    for p in range(2,n+1):
        if n%p==0:
            a=n
            while a%p==0:a//=p
            return mp.log(p) if a==1 else mp.mpf(0)
    return mp.mpf(0)


def row_constants(m):
    L=mp.log(m)
    S=mp.fsum(mangoldt(n)/mp.sqrt(n) for n in range(2,m+1))
    PL=mp.sqrt(L+2*mp.sinh(L/2))
    A=L**mp.mpf('1.5')*mp.sinh(L/4)*PL/(2*mp.pi**2)
    B=mp.sqrt(2*(2*m+1))*(1+mp.pi/4+S)/mp.pi
    return L,A,B


def explicit_tail(m,R=192):
    L,A,B=row_constants(m)
    if R<2*m:raise ValueError('Requires R>=2m')
    n0=mp.mpf(R+1)
    aa=mp.pi**2/(2*L)
    C=mp.mpf('2.5')*mp.gamma(mp.mpf('.25'))*mp.exp(mp.mpf('.5'))*2**(-mp.mpf('.25'))*(1+mp.sqrt(5))
    def geometric(q):
        rho=mp.exp(-aa)*(1+1/n0)**q
        if rho>=1:raise ValueError('Geometric ratio is not below one')
        return n0**q*mp.exp(-aa*n0)/(1-rho),rho
    S1,rho1=geometric(mp.mpf(5)/4)
    S2,rho2=geometric(mp.mpf(9)/4)
    bound=mp.sqrt(2/L)*C*(2*mp.pi/L)**(mp.mpf(13)/4)*(A*S1+2*B*S2)
    return dict(m=m,R=R,bound=bound,L=L,row_A=A,row_B=B,H_constant=C,
                exponential_rate=aa,geometric_ratio_5over4=rho1,
                geometric_ratio_9over4=rho2,
                rounded_up_power_of_ten=mp.power(10,mp.ceil(mp.log10(bound))))


def source_hp_bound_scan(m,R=192,maxp=300):
    """Evaluate the coarse fully explicit source(3.6)-(3.7); select best p."""
    L,A,B=row_constants(m)
    poly=[mp.mpf(0),mp.mpf(-24),mp.mpf(16)]
    pref=mp.pi**(-mp.mpf('.25'))*mp.exp(-mp.pi/2)/(1-mp.exp(-3*mp.pi/2))
    best=None
    for p in range(1,maxp+1):
        nxt=[mp.mpf(0)]*(len(poly)+1)
        for k,v in enumerate(poly):
            nxt[k]+=(mp.mpf('.5')+2*k)*v
            nxt[k+1]-=2*v
        poly=nxt
        Hp=pref*mp.fsum(abs(v)*2**(k+mp.mpf('.25'))*mp.gamma(k+mp.mpf('.25')) for k,v in enumerate(poly))
        bound=mp.sqrt(2/L)*Hp*(L/(2*mp.pi))**p*(A/((p+1)*mp.mpf(R)**(p+1))+2*B/(p*mp.mpf(R)**p))
        if best is None or bound<best[1]:best=(p,bound)
    return best


def main():
    mp.mp.dps=100
    out=Path(__file__).resolve().parent
    rows=[]
    for m in(12,16,20,24):
        r=explicit_tail(m)
        p,coarse=source_hp_bound_scan(m)
        r.update(coarse_source_best_p=p,coarse_source_bound=coarse,coarse_search_max_p=300)
        rows.append({k:(mp.nstr(v,80) if isinstance(v,mp.mpf) else v) for k,v in r.items()})
    (out/'tail_bound_results.json').write_text(json.dumps(rows,indent=2)+'\n')
    with (out/'tail_bound_results.csv').open('w') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    print(json.dumps(rows,indent=2))

if __name__=='__main__':main()
