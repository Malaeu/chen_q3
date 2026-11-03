"""Numerical DH zero census; acb point evaluations, not interval contour proof."""
from pathlib import Path
import os,sys,json,time,math,cmath,hashlib
sys.path.insert(0,os.environ.get('FLINT_DEPS','/workspace/python_deps'))
from flint import acb,arb,ctx
import mpmath as mp
P=Path(__file__).resolve().parent
INPUT=Path(os.environ.get('DH_ZERO_INPUT','/workspace/zero_extension/dh_census/dh_zeros_600_200dps.json'))
ctx.dps=45;mp.mp.dps=40

def coeff():return ((10-2*arb(5).sqrt()).sqrt()-2)/(arb(5).sqrt()-1)
def Dball(s):
 c=coeff();return (-s*arb(5).log()).exp()*(s.zeta(acb(arb(1)/5))+c*s.zeta(acb(arb(2)/5))-c*s.zeta(acb(arb(3)/5))-s.zeta(acb(arb(4)/5)))
def cv(v):
 m,e=v.mid().man_exp();return mp.ldexp(mp.mpf(int(m)),int(e))
def D(s):
 ctx.dps=mp.mp.dps+12;v=Dball(acb(str(mp.re(s)),str(mp.im(s))));return mp.mpc(cv(v.real),cv(v.imag))
def Z(t):
 ctx.dps=mp.mp.dps+12;s=acb('.5',str(t));phase=((s+1)/2).lgamma().imag+arb(str(t))*((arb(5)/arb.pi()).log()/2);return cv((acb(0,phase).exp()*Dball(s)).real)
def fast(t):
 ctx.dps=35;s=acb('.5',str(t));phase=((s+1)/2).lgamma().imag+arb(str(t))*((arb(5)/arb.pi()).log()/2);return float((acb(0,phase).exp()*Dball(s)).real.mid())
def boundary(z):
 ctx.dps=40;s=acb(str(z.real),str(z.imag));s=1-s if z.real<.5 else s
 v=(s*((arb(5)/arb.pi()).log()/2)+((s+1)/2).lgamma()+arb(str(abs(z.imag)))*arb.pi()/4).exp()*Dball(s)
 return complex(float(v.real.mid()),float(v.imag.mid()))
def winding(lo,hi,step=.125,left=-1,right=2):
 vs=[complex(left,lo),complex(right,lo),complex(right,hi),complex(left,hi)];pts=[]
 for a,b in zip(vs,vs[1:]+vs[:1]):
  n=math.ceil(abs(b-a)/step);pts.extend(a+(b-a)*j/n for j in range(n))
 vals=[boundary(z) for z in pts];inc=[cmath.phase(b/a) for a,b in zip(vals,vals[1:]+vals[:1])];w=sum(inc)/(2*math.pi)
 return dict(low=lo,high=hi,left=left,right=right,step=step,samples=len(pts),winding=w,count=round(w),max_phase_increment=max(map(abs,inc)),min_boundary_modulus=min(map(abs,vals)))
def fmt(x):return mp.nstr(x,85)
def save(d): (P/'dh_zeros_900_200dps.json').write_text(json.dumps(d,indent=2)+'\n')
