from core import *

def bounded(seed,lo,hi):
 z=seed;h=mp.mpf('1e-8')
 for k in range(35):
  v=D(z)
  if abs(v)<mp.mpf('1e-25'):return z
  der=(D(z+h)-D(z-h))/(2*h)
  if abs(der)<mp.mpf('1e-18'):return None
  step=v/der
  if abs(step)>1:step/=abs(step)
  z-=step
  if not .2<float(mp.re(z))<1.99 or not lo-1<float(mp.im(z))<hi+1:return None
 return None

