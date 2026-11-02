"""Numerical DH zero extension; discrete winding is NOT interval certification."""
from pathlib import Path
import sys,json,time,datetime
import mpmath as mp
P=Path(__file__).resolve().parent;FAKE=P.parents[1]
sys.path.insert(0,str(FAKE))
from dh_zeros import D,Z,completed

def register(name,prediction,kill):
 with (P/'PREDICTIONS.md').open('a') as f:f.write(f'\n## {datetime.datetime.now(datetime.timezone.utc).isoformat()} — {name}\n\nPrediction: {prediction}\n\nKill condition: {kill}\n')
def line():
 register('DH critical-line extension230..310','Sign-change scan at step0.125, followed by80dps refinement, yields candidate line zeros. No absence of off-line pairs inferred.','Failed bracket refinement or roots leaving interval block merging. All roots remain numerical.')
 mp.mp.dps=25;lo=mp.mpf(230);hi=mp.mpf(310);step=mp.mpf('.125');ts=[lo+i*step for i in range(641)];vs=[]
 for i,t in enumerate(ts):
  vs.append(Z(t))
  if i%80==0:print('LINEGRID',i,str(t),flush=True)
 brackets=[(ts[i],ts[i+1]) for i in range(len(ts)-1) if vs[i]*vs[i+1]<0];extrema=[ts[i] for i in range(1,len(ts)-1) if (vs[i]-vs[i-1])*(vs[i+1]-vs[i])<0]
 mp.mp.dps=80;roots=[]
 for a,b in brackets:
  g=mp.findroot(Z,(a,b),tol=mp.mpf('1e-70'),maxsteps=40);assert a<=g<=b
  roots.append({'sigma':'0.5','gamma':mp.nstr(g,80),'residual':mp.nstr(abs(D(mp.mpf('.5')+mp.j*g)),80)})
 (P/'extension_line.json').write_text(json.dumps({'status':'NUMERICAL_NOT_CERTIFIED','critical_line_zeros':roots,'extremum_seed_heights':[str(t) for t in extrema],'step':'0.125','interval':[230,310]},indent=2)+'\n');print('LINE DONE',len(roots),len(extrema),flush=True)
def off():
 register('DH off-line search230..310','Complex Newton seeds at line-scan extrema with realparts0.7/1.1 search right-side off-line zeros. Every candidate is refined and reflected.','Any mismatch with the independent winding count leaves the census incomplete; no unlocated pairs are assumed absent.')
 data=json.loads((P/'extension_line.json').read_text());mp.mp.dps=30;seeds=list(map(mp.mpf,data['extremum_seed_heights']));seeds.sort(key=lambda t:abs(Z(t)));found=[]
 counts=json.loads((P/'extension_count.json').read_text())['runs'];expected=counts[0]['nearest_integer'];assert len(counts)==2 and all(r['nearest_integer']==expected for r in counts)
 deficit=expected-len(data['critical_line_zeros']);assert deficit>=0 and deficit%2==0;target=deficit//2;print('OFF TARGET',target,flush=True)
 for i,t in enumerate(seeds):
  if len(found)>=target:break
  for re in (mp.mpf('.7'),mp.mpf('1.1')):
   try:
    z=mp.findroot(D,mp.mpc(re,t),tol=mp.mpf('1e-22'),maxsteps=25)
    if mp.re(z)<mp.mpf('.5'):z=1-mp.conj(z)
    if not (mp.re(z)>mp.mpf('.50000001') and mp.re(z)<2 and 230<mp.im(z)<310 and abs(D(z))<mp.mpf('1e-18')):continue
    if all(abs(z-w)>mp.mpf('1e-8') for w in found):found.append(z);print('OFF CANDIDATE',str(z),flush=True)
   except (ValueError,ZeroDivisionError):pass
  if i%10==0:print('OFF SEARCH',i,len(seeds),flush=True)
 mp.mp.dps=80;out=[]
 for z in found:
  z=mp.findroot(D,z,tol=mp.mpf('1e-70'),maxsteps=40);out.append({'sigma_right':mp.nstr(mp.re(z),80),'sigma_left':mp.nstr(1-mp.re(z),80),'gamma':mp.nstr(mp.im(z),80),'right_residual':mp.nstr(abs(D(z)),80),'left_residual':mp.nstr(abs(D(1-mp.conj(z))),80)})
 out.sort(key=lambda r:mp.mpf(r['gamma']));(P/'extension_off.json').write_text(json.dumps({'status':'NUMERICAL_SEARCH_NOT_CERTIFIED','off_line_pairs':out,'candidate_seed_count':2*len(seeds),'off_pairs_required_by_discrete_count':target,'early_stop_scope':'stop once refined candidates account for the two discrete winding counts; not an interval completeness theorem'},indent=2)+'\n');print('OFF DONE',len(out),flush=True)
def count():
 register('DH winding extension230..310','Two discrete winding runs at steps0.25/0.125 should agree and match line roots plus twice the off-line pair count.','Disagreement, large phase increments or an unexplained count deficit marks census incomplete. No rigorous boundary exclusion claimed.')
 mp.mp.dps=30;out=[]
 for step in (mp.mpf('.25'),mp.mpf('.125')):
  vertices=[mp.mpc(-1,230),mp.mpc(2,230),mp.mpc(2,310),mp.mpc(-1,310)];points=[]
  for a,b in zip(vertices,vertices[1:]+vertices[:1]):
   n=int(mp.ceil(abs(b-a)/step));points.extend(a+(b-a)*j/n for j in range(n))
  vals=[]
  for i,z in enumerate(points):
   vals.append(completed(1-z) if mp.re(z)<mp.mpf('.5') else completed(z))
   if i%200==0:print('WINDING',str(step),i,len(points),flush=True)
  increments=[mp.arg(b/a) for a,b in zip(vals,vals[1:]+vals[:1])];w=mp.fsum(increments)/(2*mp.pi)
  out.append({'step':str(step),'winding':mp.nstr(w,28),'nearest_integer':int(mp.nint(w)),'max_phase_increment':mp.nstr(max(abs(v) for v in increments),28),'samples':len(points)})
  (P/'extension_count.json').write_text(json.dumps({'status':'DISCRETE_WINDING_NOT_CERTIFIED','rectangle_real':[-1,2],'rectangle_imag':[230,310],'runs':out},indent=2)+'\n');print('COUNT',out[-1],flush=True)
def merge():
 old=json.loads((FAKE/'dh_zeros.json').read_text());line=json.loads((P/'extension_line.json').read_text());off=json.loads((P/'extension_off.json').read_text());count=json.loads((P/'extension_count.json').read_text());accounted=len(line['critical_line_zeros'])+2*len(off['off_line_pairs']);matched=all(r['nearest_integer']==accounted for r in count['runs']) and len(count['runs'])==2
 old['critical_line_zeros']+=line['critical_line_zeros'];old['off_line_pairs']+=off['off_line_pairs']
 for i,row in enumerate(old['critical_line_zeros']):row['index']=i+1
 upper=[{'sigma':'0.5','gamma':r['gamma'],'kind':'critical_line'} for r in old['critical_line_zeros']]
 for r in old['off_line_pairs']:
  upper.extend({'sigma':r[key],'gamma':r['gamma'],'kind':'off_line'} for key in ('sigma_left','sigma_right'))
 upper.sort(key=lambda r:(mp.mpf(r['gamma']),mp.mpf(r['sigma'])));old['upper_half_plane_zeros']=upper;old['count_upper_half_plane']=len(upper);old['height_bound']=310;old['extension_argument_count']=count;old['extension_accounted_count']=accounted;old['completeness_status']='NUMERICAL_COUNT_MATCH_NOT_INTERVAL_CERTIFIED' if matched else 'INCOMPLETE_EXTENSION_COUNT_MISMATCH';old['status']='NUMERICAL_NOT_CERTIFIED'
 (P/'dh_zeros_extended.json').write_text(json.dumps(old,indent=2)+'\n');print('MERGED',old['completeness_status'],accounted,flush=True)
if __name__=='__main__':globals()[sys.argv[1]]()
