"""Incremental600..900 DH census, discrete counts only; preserve old coordinates."""
from core import *
from bounded import bounded
import copy,csv

def main():
 start=time.monotonic();old=json.loads(INPUT.read_text());checkpoint=P/'dh_zeros_900_200dps.json';d=json.loads(checkpoint.read_text()) if checkpoint.exists() else copy.deepcopy(old);d.update(height_bound=900,dps=200,status='NUMERICAL_NOT_CERTIFIED');d['extension_bands']=[];d['extension_input_sha256']=hashlib.sha256(INPUT.read_bytes()).hexdigest();step=.0625;last=float(d['critical_line_zeros'][-1]['gamma']);start_j=max(0,math.ceil((last-600)/step));a=600+start_j*step;pa=fast(a);br=[];print('RESUME_CRITICAL',len(d['critical_line_zeros'])-len(old['critical_line_zeros']),a,flush=True)
 for j in range(start_j+1,4801):
  b=600+j*step;pb=fast(b)
  if pa*pb<0:br.append((a,b))
  a,pa=b,pb
 print('NEW_LINE_BRACKETS',len(br),flush=True);mp.mp.dps=200;f=lambda x:mp.nstr(x,200)
 for i,(a,b) in enumerate(br):
  t=mp.findroot(Z,(mp.mpf(str(a)),mp.mpf(str(b))),tol=mp.mpf('1e-190'),maxsteps=40)
  if not a-.001<float(t)<b+.001:raise RuntimeError('root left bracket')
  d['critical_line_zeros'].append(dict(index=len(d['critical_line_zeros'])+1,sigma='0.5',gamma=f(t),residual=f(abs(D(mp.mpf('.5')+mp.j*t))),multiplicity=1))
  if i%50==0:print('LINE200',i,f(t)[:20],flush=True);save(d)
 for low in range(600,900,20):
  r=winding(low,low+20,.125);r['boundary_function']='completed F multiplied by positive exp(pi*abs(t)/4)';r['line_count']=sum(low<float(x['gamma'])<low+20 for x in d['critical_line_zeros']);r['off_line_upper_count_needed']=r['count']-r['line_count'];d['extension_bands'].append(r);print('BAND',r,flush=True);save(d)
 # Finer line scan of every deficit band, independent of root search.
 for r in d['extension_bands']:
  if not r['off_line_upper_count_needed']:continue
  a=r['low'];pa=fast(a);count=0
  for j in range(1,2001):
   b=r['low']+.01*j;pb=fast(b);count+=int(pa*pb<0);pa=pb
  r['fine_line_step']='.01';r['fine_line_brackets']=count
  if count!=r['line_count']:raise RuntimeError('fine critical scan differs; refine missing line roots')
 print('FINE_LINE_CHECKS_OK',flush=True);d['off_line_pairs']=copy.deepcopy(old['off_line_pairs']);pairs=[];mp.mp.dps=40
 for r in d['extension_bands']:
  target=r['off_line_upper_count_needed']//2
  if r['off_line_upper_count_needed']%2:raise RuntimeError('odd off-line deficit')
  if target==0:continue
  local=lambda:[z for z in pairs if r['low']<float(mp.im(z))<r['high']]
  gam=[r['low']]+[float(x['gamma']) for x in d['critical_line_zeros'] if r['low']<float(x['gamma'])<r['high']]+[r['high']]
  gaps=sorted(zip(gam,gam[1:]),key=lambda ab:ab[1]-ab[0],reverse=True);times=[(a+b)/2 for a,b in gaps]+[r['low']+(j+.5)/4 for j in range(80)]
  for t in times:
   for sig in ['.65','.85','1.15','1.65']:
    z=bounded(mp.mpc(sig,t),r['low'],r['high'])
    if z is None:continue
    if mp.re(z)<.5:z=1-mp.conj(z)
    if .500001<float(mp.re(z))<2 and r['low']<float(mp.im(z))<r['high'] and all(abs(z-p)>mp.mpf('1e-12') for p in pairs):pairs.append(z);print('NEW_PAIR',fmt(mp.re(z)),fmt(mp.im(z)),flush=True)
   if len(local())>=target:break
  if len(local())!=target:raise RuntimeError('unfilled off-line band '+str(r))
 mp.mp.dps=200;min_der=mp.inf;h=mp.mpf('1e-60')
 for seed in sorted(pairs,key=lambda z:float(mp.im(z))):
  z=mp.findroot(D,(seed,seed+mp.mpf('1e-25')),tol=mp.mpf('1e-190'),maxsteps=40);mirror=1-mp.conj(z);dv=abs((D(z+h)-D(z-h))/(2*h));min_der=min(min_der,dv)
  d['off_line_pairs'].append(dict(sigma_right=f(mp.re(z)),sigma_left=f(mp.re(mirror)),gamma=f(mp.im(z)),right_residual=f(abs(D(z))),left_residual=f(abs(D(mirror))),listed_multiplicity=1))
 d['upper_half_plane_zeros']=[dict(sigma='0.5',gamma=r['gamma'],kind='critical_line',multiplicity=1) for r in d['critical_line_zeros']]
 for r in d['off_line_pairs']:
  for k in ['sigma_left','sigma_right']:d['upper_half_plane_zeros'].append(dict(sigma=r[k],gamma=r['gamma'],kind='off_line',multiplicity=1))
 d['upper_half_plane_zeros'].sort(key=lambda r:(mp.mpf(r['gamma']),mp.mpf(r['sigma'])));d['count_upper_half_plane']=len(d['upper_half_plane_zeros']);save(d);d['extension_argument_count']=[]
 for step in [.25,.125,.0625]:
  r=winding(600,900,step);r['boundary_function']='completed F times positive exp(pi*abs(t)/4)';d['extension_argument_count'].append(r);print('EXT_WINDING',r,flush=True);save(d)
 for r in d['extension_bands']:
  r['accounted_count']=sum(r['low']<float(z['gamma'])<r['high'] for z in d['upper_half_plane_zeros']);r['matched']=r['count']==r['accounted_count']
 oldprefix=[r for r in d['upper_half_plane_zeros'] if mp.mpf(r['gamma'])<600];unchanged=oldprefix==old['upper_half_plane_zeros'] and d['critical_line_zeros'][:len(old['critical_line_zeros'])]==old['critical_line_zeros'] and d['off_line_pairs'][:len(old['off_line_pairs'])]==old['off_line_pairs'];newcount=d['count_upper_half_plane']-old['count_upper_half_plane'];okay=unchanged and all(r['matched'] for r in d['extension_bands']) and all(r['count']==newcount for r in d['extension_argument_count']);d['completeness_status']='NUMERICAL_COUNT_MATCH_NOT_INTERVAL_CERTIFIED' if okay else 'GAP';d['extension_checks']=dict(old600_coordinates_and_rows_unchanged=unchanged,new_upper_count=newcount,new_quartet_count=len(pairs),new_critical_count=len(d['critical_line_zeros'])-len(old['critical_line_zeros']),new_offline_min_abs_derivative=f(min_der),seconds=time.monotonic()-start,scope='Incremental strip counts added to inherited old600 numerical count; no interval-certified contour or simplicity proof.');save(d);print('DONE',d['count_upper_half_plane'],d['extension_checks'],flush=True)
if __name__=='__main__':main()
