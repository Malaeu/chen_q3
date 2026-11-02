"""Independent prolate modal/shift-jump controls; no eigenproblem."""
from pathlib import Path
import mpmath as mp
import json
mp.mp.dps=80;m=4;L=mp.log(m);b=L/2
v=mp.matrix([mp.mpf(2)/3,-mp.mpf(1)/5,mp.mpf(1)/7,0,mp.mpf(1)/11]);v/=mp.norm(v)
def mode(n,x,q=0):
 d=1 if n==0 else mp.sqrt(2);w=2*mp.pi*n/L
 return d*(-1)**n/mp.sqrt(L)*(mp.cos(w*x) if q==0 else (-w*mp.sin(w*x) if q==1 else -w*w*mp.cos(w*x)))
def f(x,q=0):return mp.fsum(v[n]*mode(n,x,q) for n in range(m+1))
def pp(x):return b*b-x*x
def Wf(x):return -pp(x)*f(x,2)+2*x*f(x,1)
def I2(k):return 2*b**3/3 if k==0 else 4*b*(-1)**k/(2*mp.pi*k/L)**2
def I0(k):return L if k==0 else mp.mpf(0)
W=mp.zeros(m+1)
for i in range(m+1):
 for j in range(m+1):
  di=1 if i==0 else mp.sqrt(2);dj=1 if j==0 else mp.sqrt(2)
  W[i,j]=di*dj*(-1)**(i+j)*(2*mp.pi*i/L)*(2*mp.pi*j/L)/(2*L)*(b*b*I0(i-j)-I2(i-j)-b*b*I0(i+j)+I2(i+j))
projection=max(abs(mp.quad(lambda x:mode(n,x)*Wf(x),[-b,0,b])-(W*v)[n]) for n in range(m+1))
s=L/3;a=b-s;w=mp.mpf('1.3')
plus=mp.quad(lambda x:f(x)*((-2*x*s-s*s)*f(x+s,2)-2*s*f(x+s,1)),[-b,-s/2,b-s])
minus=mp.quad(lambda x:f(x)*((2*x*s-s*s)*f(x-s,2)+2*s*f(x-s,1)),[-b+s,s/2,b])
regular=w*(plus+minus);expected=2*w*f(b)*pp(a)*f(a,1);jump=-expected
flux=[]
for alpha in [mp.mpf('.5'),mp.mpf('1.5')]:
 def j(z):return mp.exp(-alpha*z)/(-mp.expm1(-2*z))
 for h in [mp.mpf('1e-4'),mp.mpf('1e-8'),mp.mpf('1e-12')]:
  x=b-h;value=pp(x)*f(b)*(j(h)-j(2*b-h));target=b*f(b)
  flux.append({'alpha':str(alpha),'h':str(h),'relative_kernel_flux_error':mp.nstr(abs(value-target)/abs(target),30)})
A=mp.matrix([[mp.mpf(i+j+1)/(1+(i-j)**2) for j in range(m+1)] for i in range(m+1)])
comm=mp.fdot(v,A*(W*v)-W*(A*v))
assert projection<mp.mpf('1e-70') and abs(regular-expected)<mp.mpf('1e-70') and abs(comm)<mp.mpf('1e-70')
assert max(mp.mpf(d['relative_kernel_flux_error']) for d in flux if d['h']=='0.000000000001')<mp.mpf('1e-10')
print(json.dumps({'status':'PASS','dps':80,'scope':'Independent small-carrier projection and shifted-atom control; endpoint kernel limit control, not a new CCM scan',
 'prolate_projection_error':mp.nstr(projection,30),'W_symmetry_error':mp.nstr(mp.norm(W-W.T),30),
 'generic_real_symmetric_matrix_commutator':mp.nstr(comm,30),'prime_regular_volume':mp.nstr(regular,30),
 'prime_shifted_jump':mp.nstr(jump,30),'regular_formula_error':mp.nstr(abs(regular-expected),30),
 'total_shifted_atom':mp.nstr(regular+jump,30),'arch_endpoint_kernel_flux_controls':flux,'new_CCM_eigenproblems':0},indent=2))
