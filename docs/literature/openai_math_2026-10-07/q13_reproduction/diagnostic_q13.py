"""Small actual-source Fourier diagnostics. Not interval certificates."""
import mpmath as mp
from pathlib import Path
import json,hashlib
mp.mp.dps=40
m=16;L=mp.log(m);T=L/2; w=2*mp.pi/L; rt=mp.sqrt(2*mp.pi)
cA=mp.euler+mp.log(8*mp.pi)+mp.pi/2
# The packet's exact even original-P vector, centered on [-T,T], unnormalized.
a0=-mp.mpf(3)/4
modes=[(w,-(1+4*w*w)),(2*w,-(mp.mpf(1)/4+4*w*w))]
def ps(t):return a0+sum(a*mp.cos(k*t) for k,a in modes)
def dp(t):return -sum(a*k*mp.sin(k*t) for k,a in modes)
def gp(s):
    e=mp.exp(-s/2)
    return -4*mp.sinh(s/2)+cA/2-mp.atanh(e)-mp.atan(e)+sum(a for ell,a in atoms if ell<=s)
atoms=[(mp.log(2),mp.log(2)/mp.sqrt(2)),(mp.log(3),mp.log(3)/mp.sqrt(3)),(mp.log(4),mp.log(2)/2)]
knots=[mp.mpf(0),mp.log(2),mp.log(3),T]
def integ(fun):return sum(mp.quad(fun,[lo,(lo+hi)/2,hi]) for lo,hi in zip(knots,knots[1:]))
j=-2*integ(lambda s:gp(s)*dp(s))
if not mp.mpf('.23225')<j<mp.mpf('.23226'):raise AssertionError(j)
# Independently check the contacts; numerical verification is not the proof.
contacts=[mp.quad(lambda t:mp.exp(s*t/2)*ps(t),[-T,0,T]) for s in [-1,1]]
if max(map(abs,contacts))>mp.mpf('1e-30'):raise AssertionError(contacts)

def sint(k,A,p):
    if abs(k)<mp.mpf('1e-35'):return A*mp.cos(p)
    return (mp.sin(k*A+p)-mp.sin(p))/k

def scos(k):
    if abs(k)<mp.mpf('1e-35'):return T
    return mp.sin(k*T)/k

def Fpsi(x):
    return 2/rt*(a0*scos(x)+sum(a*(scos(k-x)+scos(k+x))/2 for k,a in modes))

def FG(x):
    def fun(s):
        A=T-s
        return gp(s)*sum(a*k*(sint(k-x,A,k*s)-sint(k+x,A,k*s))/2 for k,a in modes)
    return -2j/rt*integ(fun)

def FV(x):
    # psi'(T)=0 for this even probe, so the differentiated Volterra endpoint is zero.
    def fun(s):
        A=T-s
        return gp(s)*sum(a*k*k*(sint(k-x,A,k*s)+sint(k+x,A,k*s))/2 for k,a in modes)
    return 2/rt*integ(fun)

def X(x):
    s=mp.mpf('.5')-1j*x
    return s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)/2
odd_modes=[(w,-(mp.mpf(1)/4+w*w)),(2*w,-(mp.mpf(1)/4+4*w*w)/2)]
endpoint_prime=sum(a*k*mp.cos(k*T) for k,a in odd_modes)
def oddFG(x):
    def fun(s):
        A=T-s
        return gp(s)*sum(a*k*(sint(k-x,A,k*s)+sint(k+x,A,k*s))/2 for k,a in odd_modes)
    return -2/rt*integ(fun)
def oddFV(x,include_endpoint=True):
    def fun(s):
        A=T-s
        v=sum(a*k*k*(sint(k-x,A,k*s)-sint(k+x,A,k*s))/2 for k,a in odd_modes)
        if include_endpoint:v+=endpoint_prime*mp.sin(x*(T-s))
        return gp(s)*v
    return -2j/rt*integ(fun)
def oddFpsi(x):
    return -1j/rt*sum(a*(scos(k-x)-scos(k+x)) for k,a in odd_modes)
rows=[]
for x in [mp.mpf(1)/3,mp.mpf(3)/2,mp.mpf(4)]:
    ef=Fpsi(x);eg=FG(x);ev=FV(x)
    of=oddFpsi(x);og=oddFG(x);ov=oddFV(x)
    wrongov=oddFV(x,False)
    wrong_endpoint_res=abs(1j*x*og-wrongov)
    if wrong_endpoint_res<mp.mpf('1e-6'):raise AssertionError('planted missing endpoint not detected')
    if abs(1j*x*og-ov)>mp.mpf('1e-28'):raise AssertionError('odd endpoint return')
    xx=mp.re(X(x));dx=mp.re(mp.diff(X,x));den=xx-1j*dx
    al=dx/den;be=xx/den;om=abs(be)**2;eta=mp.re(al*mp.conj(be))
    for label,ff,gg,vv in [('even',ef,eg,ev),('even_plus_i_odd',ef+1j*of,eg+1j*og,ev+1j*ov)]:
      ph=1j*x*ff
      derivative_res=abs(1j*x*gg-vv-j/rt)
      U=al*ff-1j*be*gg
      for ratio in [mp.mpf(1)/2,mp.mpf(1)/4]:
        h=ratio*T; z=mp.sin(h*x)/(h*x);hh=(1-z)/(1j*rt*x)
        greg=(vv+j*z/rt)/(1j*x)
        ureg=al*ff-1j*be*greg;ee=-1j*be*j*hh
        reconstruction=abs(U-ureg-ee)
        lhs=2*(abs(U)**2-abs(ureg)**2)
        rhs=j*j/mp.pi*om*(1-z*z)/(x*x)+4*mp.re(j*(1-z)/(rt*x*x)*(om*vv+1j*eta*ph))
        residual=abs(lhs-rhs)
        if max(derivative_res,reconstruction,residual)>mp.mpf('1e-28'):
            raise AssertionError((x,label,ratio,derivative_res,reconstruction,residual))
        rows.append({'profile':label,'x':str(x),'h_over_T':str(ratio),'actual_xi_beta_abs2':mp.nstr(om,16),
                     'distribution_derivative_residual':mp.nstr(derivative_res,8),
                     'full_seam_reconstruction_residual':mp.nstr(reconstruction,8),
                     'complete_mixed_correction_residual':mp.nstr(residual,8),
                     'planted_missing_odd_endpoint_residual':mp.nstr(wrong_endpoint_res,8)})
origin=X(mp.mpf(0)); origin_deriv=mp.diff(X,mp.mpf(0))
if abs(origin)==0 or abs(origin_deriv)>mp.mpf('1e-30'):raise AssertionError('origin')
base=Path(__file__).resolve().parent
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','dps':mp.mp.dps,'m':m,'M':2,
     'scope':'fixed original-P probe; not an asymptotic production schedule or CCM spectral bound',
     'full_jump_noninterval':mp.nstr(j,38),'contacts':[mp.nstr(abs(x),8) for x in contacts],
     'rows':rows,'actual_xi_beta_at_origin':'1 by evenness and X(0) != 0; numerical check only here',
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(base/'diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
