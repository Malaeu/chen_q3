"""Independent physical arch quadrature on saved step profiles, including tail."""
from residual import *
mp.mp.dps=80
profiles=list(csv.DictReader((ROOT/'profiles.csv').open()))
budgets=list(csv.DictReader((ROOT/'budgets.csv').open()));out=[]
for world in ('zeta','dh','plant'):
    h=mp.mpf(1)/32;t=mp.mpf(1)
    w=[mp.mpf(r['f']) for r in profiles if r['world']==world and r['mesh']=='32' and r['t']=='1.0']
    C=autocorr(w);alpha=mp.mpf('1.5') if world=='dh' else mp.mpf('.5')
    def piece(k):
        def integrand(u):
            if not u:return C[0]-C[1]
            diff=2*h*(C[0]-C[k])+2*(u-k*h)*(C[k]-C[k+1])
            return mp.exp(-alpha*u)*diff/(-mp.expm1(-2*u))
        return mp.quad(integrand,[k*h,(k+1)*h])
    interior=mp.fsum(piece(k) for k in range(32));x=mp.exp(-t/2)
    tail=2*h*C[0]*(mp.atanh(x)+(-1 if world=='dh' else 1)*mp.atan(x))
    saved=next(mp.mpf(r['arch']) for r in budgets if r['world']==world and r['mesh']=='32' and r['t']=='1.0')
    error=abs(interior+tail-saved)
    assert error<mp.mpf('1e-60')
    out.append(dict(world=world,interior=st(interior),infinite_tail=st(tail),sum=st(interior+tail),saved_arch=st(saved),absolute_error=st(error)))
write('arch_validation.csv',out)
