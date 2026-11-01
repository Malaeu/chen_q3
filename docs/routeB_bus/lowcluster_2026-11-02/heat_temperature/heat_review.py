"""Independent normalization/large-s checks for full-line heat then projection.
No fitting is performed and no files are mutated.
"""
import json
from pathlib import Path
import mpmath as mp


def H(t):
    z=mp.mpf('.5')+mp.j*t
    return mp.re(2*z*(z-1)*mp.pi**(-z/2)*mp.gamma(z/2)*mp.zeta(z))


def heat_moments():
    mass=H(mp.mpf(0));second=-mp.diff(H,mp.mpf(0),2)
    return mass,second,second/mass


def basis_fourier(n,L,t):
    b=L/2;om=2*mp.pi*n/L;dn=1 if n==0 else mp.sqrt(2)
    return dn*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-om)*b)+mp.sinc((t+om)*b))


def large_s_overlap_bound(v0,L,S,variance):
    """Upper bound for all s>=S; inputs describe a normalized target vector.

    h>0. eta bounds ||P g_s-g_s(0)*sqrt(L)*e0||/(g_s(0)*sqrt(L)).
    The normalized direction therefore has sine angle<=eta from e0.
    """
    S=mp.mpf(S);variance=mp.mpf(variance);b=L/2
    if 4*S<=variance:return dict(eta=mp.inf,overlap_squared_upper=mp.mpf(1))
    eta=b*b/(mp.sqrt(5)*(4*S-variance))
    a=min(mp.mpf(1),abs(v0));c=mp.sqrt(max(mp.mpf(0),1-a*a))
    if eta>=1 or eta>=c:upper=mp.mpf(1)
    else:upper=(a*mp.sqrt(1-eta*eta)+c*eta)**2
    return dict(eta=eta,overlap_squared_upper=upper)


def review_data(data,variance,S_values=('1','2','5','10')):
    m=int(data['m']);L=mp.log(m)
    V=mp.matrix([[mp.mpf(v) for v in row] for row in data['V']]);f=V[:,0];f/=mp.norm(f)
    h=mp.matrix([mp.mpf(v) for v in data['h']])
    hn=(h.T*h)[0];fh=(f.T*h)[0];W0=fh*fh/hn
    if 'ladder' in data:
        A=mp.matrix([[mp.mpf(v) for v in row] for row in data['ladder']['projected_profile_coefficients']])
        q=A[:,1] # P h'', full-line heat derivative at s=0+
        Wprime=2*fh*(f.T*q)[0]/hn-2*W0*(h.T*q)[0]/hn
    else:Wprime=None
    bounds={S:large_s_overlap_bound(f[0],L,S,variance) for S in S_values}
    return dict(m=m,constant_mode_overlap_squared=f[0]**2,W0=W0,Wprime0=Wprime,bounds=bounds)


def main():
    mp.mp.dps=100
    mass,second,var=heat_moments()
    print('M0',mp.nstr(mass,80));print('M2',mp.nstr(second,80));print('M2/M0',mp.nstr(var,80))
    for m in(8,12,16,20,24):
        directory=Path(__file__).resolve().parent if m==8 else Path(__file__).resolve().parent.parent
        data=json.loads((directory/f'core_m{m}_dps100_gl128.json').read_text())
        r=review_data(data,var,('1','2','5','10','100'))
        print('m',m,'W0',mp.nstr(r['W0'],18),'Wprime0',mp.nstr(r['Wprime0'],18),'W_infinity',mp.nstr(r['constant_mode_overlap_squared'],18))
        for S,z in r['bounds'].items():print(' S',S,'eta',mp.nstr(z['eta'],12),'bound',mp.nstr(z['overlap_squared_upper'],18))

if __name__=='__main__':main()
