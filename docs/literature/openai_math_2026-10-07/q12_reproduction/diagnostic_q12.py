from pathlib import Path
import mpmath as mp
import json,hashlib
mp.mp.dps=40
m=64; L=mp.log(m); T=L/2; w=2*mp.pi/L
cA=mp.euler+mp.log(8*mp.pi)+mp.pi/2
E0=-mp.mpf(3)/4;E1=1+4*w*w;E2=-(mp.mpf(1)/4+4*w*w)
O1=mp.mpf(1)/4+w*w;O2=-(mp.mpf(1)/4+4*w*w)/2
norm=mp.sqrt(L*(E0**2+(E1**2+E2**2+O1**2+O2**2)/2))
def psi(r):
    if r < -T or r > T:return mp.mpc(0)
    t=r+T
    return (E0+E1*mp.cos(w*t)+E2*mp.cos(2*w*t)+1j*(O1*mp.sin(w*t)+O2*mp.sin(2*w*t)))/norm

def dpsi(r):
    t=r+T
    return (-E1*w*mp.sin(w*t)-2*E2*w*mp.sin(2*w*t)+1j*(O1*w*mp.cos(w*t)+2*O2*w*mp.cos(2*w*t)))/norm

def mangoldt(n):
    for p in range(2,n+1):
        if any(p%d==0 for d in range(2,int(p**.5)+1)):continue
        v=n
        while v%p==0:v//=p
        if v==1:return mp.log(p)
    return mp.mpf(0)

atoms=[(mp.log(n),mangoldt(n)/mp.sqrt(n)) for n in range(2,9) if mangoldt(n)]
def a(s):return mp.exp(-s/2)/(-mp.expm1(-2*s))
def tail(s):
    u=mp.exp(-s/2)
    return mp.atanh(u)+mp.atan(u)
def arch(s):return cA/2-tail(s)
def pole(s):return -4*mp.sinh(s/2)

results=[]
for ratio in [mp.mpf(-3)/4,mp.mpf(-1)/2,mp.mpf(-1)/4,mp.mpf(1)/4,mp.mpf(1)/2,mp.mpf(3)/4]:
    r=ratio*T;sg=mp.sign(r);A=T-abs(r)
    pole_direct=-mp.quad(lambda s:pole(s)*dpsi(r+sg*s),[0,A])
    pole_conv=mp.quad(lambda u:mp.exp(-(r-u)/2)*psi(u),[-T,r])-mp.quad(lambda u:mp.exp(-(u-r)/2)*psi(u),[r,T])
    arch_direct=-mp.quad(lambda s:arch(s)*dpsi(r+sg*s),[0,A/2,A])
    def diff(s):
        if s==0:return sg*dpsi(r)/2
        return a(s)*(psi(r+sg*s)-psi(r))
    arch_repaired=sg*(cA*psi(r)/2+mp.quad(diff,[0,A/2,A])-psi(r)*tail(A))
    prime_repaired=sg*sum(v*psi(r+sg*ell) for ell,v in atoms if ell<=A)
    hinges=sorted([mp.mpf(0)]+[ell for ell,v in atoms if ell<A]+[A])
    def gp(s):return pole(s)+arch(s)+sum(v for ell,v in atoms if ell<=s)
    full_direct=-sum(mp.quad(lambda s:gp(s)*dpsi(r+sg*s),[left,right]) for left,right in zip(hinges,hinges[1:]))
    repaired=pole_conv+arch_repaired+prime_repaired
    residuals=[abs(pole_direct-pole_conv),abs(arch_direct-arch_repaired),abs(full_direct-repaired)]
    if max(residuals)>mp.mpf('1e-32'):raise AssertionError((ratio,residuals))
    results.append({'r_over_T':str(ratio),'pole_residual':mp.nstr(residuals[0],8),'arch_residual':mp.nstr(residuals[1],8),'full_residual':mp.nstr(residuals[2],8)})

# Verify both original exponential contacts for this complex mode combination.
contacts=[abs(mp.quad(lambda r:mp.exp(s*r/2)*psi(r),[-T,0,T])) for s in [-1,1]]
if max(contacts)>mp.mpf('1e-32'):raise AssertionError(contacts)
base=Path(__file__).resolve().parent
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','dps':mp.mp.dps,
     'm':m,'M':2,'schedule_scope':'local finite-band identity test, not the asymptotic production M=floor(m^epsilon)',
     'results':results,'contacts':[mp.nstr(x,8) for x in contacts],
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(base/'diagnostic_results.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
