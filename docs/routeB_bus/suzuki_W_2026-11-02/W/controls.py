import mpmath as mp,json
from pathlib import Path
mp.mp.dps=60;rows=[]
for m in [20,80,240]:
 a=mp.log(m)/2
 for j in [0,3,8]:
  th=2*mp.pi*j/16
  for z in [mp.mpc('.3','.2'),mp.mpc('2','.05'),mp.mpc('13','.5')]:
   fp=2*mp.sinh((1+1j*z)*a)/(1+1j*z);fm=2*mp.sinh((-1+1j*z)*a)/(-1+1j*z)
   direct=(z-1j)*fp+mp.exp(1j*th)*(z+1j)*fm
   exact=-1j*((mp.exp(a)+mp.exp(1j*th-a))*mp.exp(1j*a*z)-(mp.exp(-a)+mp.exp(1j*th+a))*mp.exp(-1j*a*z))
   rows.append({'m':m,'theta_index':j,'z':str(z),'absolute_error':str(abs(direct-exact))})
Path(__file__).with_name('flat_metric_control.json').write_text(json.dumps({'dps':60,'max_error':str(max(mp.mpf(r['absolute_error']) for r in rows)),'identity':'T=I, v+=exp(x), v-=exp(-x); theta0 roots 2pi*k/L, theta pi half integers; no zeta arithmetic','rows':rows},indent=2))
