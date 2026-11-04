"""Independent formula replay: analytic Hurwitz derivatives and own-source log derivatives.
Point mpmath arithmetic; no matrices, eigensystems or truncated Euler products.
"""
from pathlib import Path
import argparse,json,time,datetime
import mpmath as mp
P=Path(__file__).resolve().parent
TARGETS=['85.6993484854','114.1633427308','240.4046723514','166.4793059132']

def render(x):return mp.nstr(x,mp.mp.dps-5)
def cplx(z):return dict(real=render(mp.re(z)),imag=render(mp.im(z)))
def calc(dps,census):
 mp.mp.dps=dps;I=mp.j;tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);co=[1,tau,-tau,-1];qs=[mp.mpf(k)/5 for k in range(1,5)];log5=mp.log(5);lg=mp.log(5/mp.pi)/2
 def H(s):return mp.fsum(a*mp.zeta(s,q)for a,q in zip(co,qs))
 def Hp(s):return mp.fsum(a*mp.zeta(s,q,derivative=1)for a,q in zip(co,qs))
 def D(s):return mp.exp(-s*log5)*H(s)
 def F(s):return mp.exp(s*lg+mp.loggamma((s+1)/2)-s*log5)*H(s)
 def MD(z):
  s=mp.mpf(1)/2-I*z
  return I*(lg+mp.digamma((s+1)/2)/2+Hp(s)/H(s)-log5)
 def MX(z):
  s=mp.mpf(1)/2-I*z
  return I*(1/s+1/(s-1)-mp.log(mp.pi)/2+mp.digamma(s/2)/2+mp.zeta(s,derivative=1)/mp.zeta(s))
 def ME(z):return mp.log(3)*mp.tan(mp.log(3)*z)
 def evaluate(func,z):
  M=func(z);S=(M-I)/(M+I);direct=abs(S)**2-1;rhs=-4*mp.im(M)/abs(M+I)**2
  return dict(z=cplx(z),M=cplx(M),S=cplx(S),defect=render(direct),identity_rhs=render(rhs),identity_error=render(abs(direct-rhs)),ratio_to_4eps=None)
 tol=mp.mpf('1e-30')if dps==45 else mp.mpf('1e-50');rows=[];failures=[]
 def check(name,ok,point,lhs,rhs):
  if not ok:failures.append(dict(marker='DIAG_FORMULA_OR_NORMALIZATION_FAILURE',gate=name,dps=dps,point=point,lhs=render(lhs),rhs=rhs))
 for target in TARGETS:
  seed=min(census['off_line_pairs'],key=lambda r:abs(mp.mpf(r['gamma'])-mp.mpf(target)))
  assert abs(mp.mpf(seed['gamma'])-mp.mpf(target))<mp.mpf('1e-8')
  # Independent Newton refinement of the Hurwitz combination H, with analytic derivative.
  rho=mp.mpc(seed['sigma_right'],seed['gamma']);iters=0
  for k in range(20):
   step=H(rho)/Hp(rho);rho-=step;iters=k+1
   if abs(step)<mp.power(10,-dps+5):break
  w=mp.mpc(mp.im(rho),mp.re(rho)-mp.mpf(1)/2)
  test=rho+mp.mpf('0.03');fa,fb=F(test),F(1-test);fe=abs(fa-fb)/max(abs(fa),abs(fb));real=evaluate(MD,mp.re(w));realZ=evaluate(MX,mp.re(w))
  row=dict(kind='DH',dps=dps,address_label=target,beta=render(mp.re(rho)),gamma=render(mp.im(rho)),w=cplx(w),seed_status=census['status'],refinement='analytic-Hurwitz-derivative Newton on H(s)',newton_iterations=iters,root_residual=render(abs(D(rho))),functional_equation_relative_error=render(fe),real_axis_DH=real,real_axis_zeta=realZ,samples=[])
  check('functional_equation',fe<tol,target,fe,str(tol));check('real_axis_unitarity',abs(mp.mpf(real['defect']))<tol,target,abs(mp.mpf(real['defect'])),str(tol))
  errors=[]
  for es in ['0.001','0.0001']:
   eps=mp.mpf(es);z=w-I*eps;dh=evaluate(MD,z);zz=evaluate(MX,z);curve=evaluate(ME,z);dd=mp.mpf(dh['defect']);dh['ratio_to_4eps']=render(dd/(4*eps));errors.append(abs(dd/(4*eps)-1))
   check('positive_size_lower',dd>2*eps,target+'/'+es,dd,render(2*eps));check('positive_size_upper',dd<6*eps,target+'/'+es,dd,render(6*eps))
   for name,r in [('DH',dh),('zeta',zz),('curve',curve)]:check('identity_7_7_'+name,mp.mpf(r['identity_error'])<tol,target+'/'+es,mp.mpf(r['identity_error']),str(tol))
   for name,r in [('zeta',zz),('curve',curve)]:check('nonpositive_'+name,mp.mpf(r['defect'])<=tol,target+'/'+es,mp.mpf(r['defect']),str(tol))
   row['samples'].append(dict(epsilon=es,DH=dh,zeta_control=zz,curve_control=curve))
  check('ratio_toward_one',errors[1]<errors[0],target,errors[1],render(errors[0]));row['ratio_error_decreases']=bool(errors[1]<errors[0]);rows.append(row)
  print('independent',dps,target,'done',flush=True)
 w=mp.mpc(7,mp.mpf(1)/3);poles=[w,-w,mp.conj(w),-mp.conj(w)]
 def MP(z):return MX(z)-mp.fsum(1/(z-v)for v in poles)
 row=dict(kind='PLANTED',dps=dps,address_label='7+i/3',w=cplx(w),real_axis=evaluate(MP,mp.mpf(7)),samples=[]);errors=[]
 check('plant_real_axis_unitarity',abs(mp.mpf(row['real_axis']['defect']))<tol,'plant',abs(mp.mpf(row['real_axis']['defect'])),str(tol))
 for es in ['0.001','0.0001']:
  eps=mp.mpf(es);z=w-I*eps;plant=evaluate(MP,z);zz=evaluate(MX,z);curve=evaluate(ME,z);dd=mp.mpf(plant['defect']);plant['ratio_to_4eps']=render(dd/(4*eps));errors.append(abs(dd/(4*eps)-1))
  check('plant_positive_size_lower',dd>2*eps,'plant/'+es,dd,render(2*eps));check('plant_positive_size_upper',dd<6*eps,'plant/'+es,dd,render(6*eps))
  for name,r in [('plant',plant),('zeta_at_plant',zz),('curve_at_plant',curve)]:check('identity_7_7_'+name,mp.mpf(r['identity_error'])<tol,'plant/'+es,mp.mpf(r['identity_error']),str(tol))
  for name,r in [('zeta',zz),('curve',curve)]:check('plant_nonpositive_'+name,mp.mpf(r['defect'])<=tol,'plant/'+es,mp.mpf(r['defect']),str(tol))
  row['samples'].append(dict(epsilon=es,plant=plant,zeta_control=zz,curve_control=curve))
 check('plant_ratio_toward_one',errors[1]<errors[0],'plant',errors[1],render(errors[0]));row['ratio_error_decreases']=bool(errors[1]<errors[0]);rows.append(row)
 return rows,failures

def main():
 start=time.monotonic();started=datetime.datetime.now(datetime.timezone.utc).isoformat();census=json.loads((P.parent/'INPUT_census.txt').read_text());rows=[];failures=[]
 for dps in [45,70]:
  r,f=calc(dps,census);rows+=r;failures+=f
 result=dict(status='PASS_DIAG_NOT_INTERVAL'if not failures else'DIAG_FORMULA_OR_NORMALIZATION_FAILURE',backend='mpmath',version=mp.__version__,started_UTC=started,elapsed_seconds=time.monotonic()-start,independent_derivative='Hp/H-log5 using analytic Hurwitz-zeta derivatives; no mp.diff(dh)',uses_full_mpmath_zeta=True,no_matrices_or_eigensystems=True,records=rows,failures=failures)
 (P/'INDEPENDENT_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],result['elapsed_seconds'],flush=True)
 if failures:raise SystemExit(1)
if __name__=='__main__':main()
