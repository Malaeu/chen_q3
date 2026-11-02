"""Standard conductor5 Davenport-Heilbronn zeros; numerical, not interval certified."""
from pathlib import Path
import json,time,sys,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;OUT=P/'dh_zeros.json'
def coefficient():return (mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
def D(s):
 c=coefficient();return mp.dirichlet(s,[0,1,c,-c,-1])
def Z(t):
 s=mp.mpf('.5')+mp.j*t;phase=mp.im(mp.loggamma((s+1)/2))+t*mp.log(5/mp.pi)/2
 return mp.re(mp.exp(mp.j*phase)*D(s))
def completed(s):return mp.exp(s*mp.log(5/mp.pi)/2+mp.loggamma((s+1)/2))*D(s)
def save(d):OUT.write_text(json.dumps(d,indent=2)+'\n')
def roots():
 start=time.monotonic();mp.mp.dps=25;step=mp.mpf('.125');grid=[mp.mpf('.001')+j*step for j in range(1841)];values=[Z(t) for t in grid];brackets=[(a,b) for a,b,x,y in zip(grid,grid[1:],values,values[1:]) if x*y<0];print('BRACKETS',len(brackets),flush=True)
 mp.mp.dps=80;fmt=lambda x:mp.nstr(x,80)
 d=dict(status='NUMERICAL_NOT_CERTIFIED',height_bound=230,dps=80,coefficient=fmt(coefficient()),convention='D(s)=5^(-s)[zeta(s,1/5)+c*zeta(s,2/5)-c*zeta(s,3/5)-zeta(s,4/5)], c=(sqrt(10-2sqrt5)-2)/(sqrt5-1)',completion='F(s)=(5/pi)^(s/2)*Gamma((s+1)/2)*D(s); F(s)=F(1-s)',critical_line_zeros=[],off_line_pairs=[],upper_half_plane_zeros=[],references=[dict(authors='E. P. Balanzario and J. Sánchez-Ortiz',title='Zeros of the Davenport-Heilbronn counterexample',year=2007,url='https://www.ams.org/mcom/2007-76-260/S0025-5718-07-01999-0/S0025-5718-07-01999-0.pdf'),dict(authors='E. Bombieri and A. Ghosh',title='Around the Davenport-Heilbronn function',year=2011,doi='10.1070/RM2011v066n02ABEH004740')],scan=dict(dps=25,step='.125',sign_change_brackets=len(brackets),interval=['.001','230.001']))
 for a,b in brackets:
  t=mp.findroot(Z,(a,b),tol=mp.mpf('1e-72'),maxsteps=30)
  if not(a-mp.mpf('.01')<t<b+mp.mpf('.01')):raise ValueError('root left bracket')
  if t>230:continue
  row=dict(index=len(d['critical_line_zeros'])+1,sigma='0.5',gamma=fmt(t),residual=fmt(abs(D(mp.mpf('.5')+mp.j*t))))
  d['critical_line_zeros'].append(row);d['upper_half_plane_zeros'].append(dict(sigma='0.5',gamma=fmt(t),kind='critical_line'));save(d)
  if row['index']%20==0:print('LINE',row['index'],fmt(t)[:15],flush=True)
 for re,im in [('.808517','85.699348'),('.650830','114.163343'),('.574356','166.479306'),('.724258','176.702461')]:
  z=mp.findroot(D,mp.mpc(re,im),tol=mp.mpf('1e-72'));mirror=1-mp.conj(z)
  row=dict(sigma_right=fmt(mp.re(z)),sigma_left=fmt(mp.re(mirror)),gamma=fmt(mp.im(z)),right_residual=fmt(abs(D(z))),left_residual=fmt(abs(D(mirror))))
  d['off_line_pairs'].append(row)
  for sigma in [mp.re(z),mp.re(mirror)]:d['upper_half_plane_zeros'].append(dict(sigma=fmt(sigma),gamma=fmt(mp.im(z)),kind='off_line'))
 d['upper_half_plane_zeros'].sort(key=lambda x:(mp.mpf(x['gamma']),mp.mpf(x['sigma'])));d['count_upper_half_plane']=len(d['upper_half_plane_zeros']);d['seconds']=time.monotonic()-start;save(d);print('ROOTS_DONE',len(d['critical_line_zeros']),len(d['off_line_pairs']),flush=True)

def argument_count():
 d=json.loads(OUT.read_text());mp.mp.dps=30;records=[]
 # Winding of entire D on a rectangle excluding trivial real-axis zeros.
 for h in [mp.mpf('.25'),mp.mpf('.125')]:
  vertices=[mp.mpc('-0.5','.001'),mp.mpc('1.5','.001'),mp.mpc('1.5','230'),mp.mpc('-0.5','230')];points=[]
  for a,b in zip(vertices,vertices[1:]+vertices[:1]):
   n=int(mp.ceil(abs(b-a)/h));points += [a+(b-a)*j/n for j in range(n)]
  def boundary(z):
   if mp.re(z)<mp.mpf('.5'):
    return mp.exp((mp.mpf('.5')-z)*mp.log(5/mp.pi)+mp.loggamma((2-z)/2)-mp.loggamma((1+z)/2))*D(1-z)
   return D(z)
  vals=[boundary(z) for z in points];increments=[mp.arg(b/a) for a,b in zip(vals,vals[1:]+vals[:1])];w=mp.fsum(increments)/(2*mp.pi)
  records.append(dict(step=str(h),samples=len(points),winding=mp.nstr(w,25),nearest_integer=int(mp.nint(w)),max_phase_increment=mp.nstr(max(abs(v) for v in increments),25),minimum_boundary_modulus=mp.nstr(min(abs(v) for v in vals),25)))
  d=json.loads(OUT.read_text())
  d['argument_count']=dict(rectangle_real=['-0.5','1.5'],rectangle_imag=['.001','230'],runs=records,accounted_root_count=d.get('count_upper_half_plane'),scope='Discrete winding cross-checked under step halving; no interval enclosure or rigorous boundary-zero exclusion');save(d);print('WINDING',records[-1],flush=True)
def wide_count():
 mp.mp.dps=30;records=[]
 for low,high,h in [(mp.mpf('.001'),mp.mpf(230),mp.mpf('.25')),(mp.mpf('-.001'),mp.mpf('.001'),mp.mpf('.025'))]:
  vertices=[mp.mpc(-1,low),mp.mpc(2,low),mp.mpc(2,high),mp.mpc(-1,high)];points=[]
  for a,b in zip(vertices,vertices[1:]+vertices[:1]):
   n=int(mp.ceil(abs(b-a)/h));points += [a+(b-a)*j/n for j in range(n)]
  def value(z):return completed(1-z) if mp.re(z)<mp.mpf('.5') else completed(z)
  vals=[value(z) for z in points];increments=[mp.arg(b/a) for a,b in zip(vals,vals[1:]+vals[:1])];w=mp.fsum(increments)/(2*mp.pi)
  records.append(dict(rectangle_real=['-1','2'],rectangle_imag=[str(low),str(high)],step=str(h),samples=len(points),winding=mp.nstr(w,25),nearest_integer=int(mp.nint(w)),max_phase_increment=mp.nstr(max(abs(v) for v in increments),25)))
  print('WIDE',records[-1],flush=True)
 d=json.loads(OUT.read_text());d['wide_argument_count']=dict(function='completed F, left side evaluated by functional reflection',runs=records,zero_free_exterior_reason='For Re(s)>=2, |D(s)-1|<=zeta(2)-1<1; functional reflection excludes completed zeros at Re(s)<=-1.',scope='Discrete winding only; no interval certification. Low-height rectangle separately checked.');save(d)

def checks():
 mp.mp.dps=80;d=json.loads(OUT.read_text());rows=[]
 for re,im in [('.7','10'),('.8','85.7'),('1.1','176.7')]:
  s=mp.mpc(re,im);a=completed(s);b=completed(1-s);rows.append(dict(sigma=re,gamma=im,relative_functional_equation_residual=mp.nstr(abs(a-b)/max(abs(a),abs(b)),60)))
 d['generator_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 d['functional_equation_checks']=rows
 d['max_refined_D_residual']=mp.nstr(max([mp.mpf(r['residual']) for r in d['critical_line_zeros']]+[mp.mpf(r[k]) for r in d['off_line_pairs'] for k in ['right_residual','left_residual']]),60)
 d['completeness_status']='NUMERICAL_COUNT_MATCH_NOT_INTERVAL_CERTIFIED' if d.get('argument_count') and all(r['nearest_integer']==d['count_upper_half_plane'] for r in d['argument_count']['runs']) else 'NOT_CHECKED'
 save(d)
if __name__=='__main__':
 if len(sys.argv)>1 and sys.argv[1]=='count':argument_count()
 elif len(sys.argv)>1 and sys.argv[1]=='checks':checks()
 elif len(sys.argv)>1 and sys.argv[1]=='wide':wide_count()
 else:roots()
