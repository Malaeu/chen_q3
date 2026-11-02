"""DIAGNOSTIC_NEVER_A_PROOF: positive fixed-weight SHAKE, both edge conventions."""
from pathlib import Path
import sys,json,csv,time
import mpmath as mp
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(OUT))

def qfull(L,s,n,j):
 if n==j:return 2*(L-s)/L*mp.cos(2*mp.pi*n*s/L)
 return (mp.sin(2*mp.pi*j*s/L)-mp.sin(2*mp.pi*n*s/L))/(mp.pi*(n-j))
def qeven(L,s,N,clip=False):
 if clip and s>L:return mp.zeros(N+1)
 Q=mp.zeros(N+1)
 for n in range(N+1):
  for j in range(n,N+1):
   ns=[(0,mp.mpf(1))] if n==0 else [(n,1/mp.sqrt(2)),(-n,1/mp.sqrt(2))]
   js=[(0,mp.mpf(1))] if j==0 else [(j,1/mp.sqrt(2)),(-j,1/mp.sqrt(2))]
   Q[n,j]=Q[j,n]=mp.fsum(a*b*qfull(L,s,k,l) for k,a in ns for l,b in js)
 return Q

def run(m,dps=180,order=160,epses=('1e-26','1e-20','1e-12','1e-6')):
 from v_forms import build_forms
 start=time.monotonic();mp.mp.dps=dps
 data=build_forms(m,m,dps,order);K=data['K'];arch=data['arch'];spatial=data['spatial'];h=data['h'];L=mp.log(m)
 ev,U=mp.eigsy(K);f=U[:,0]
 if mp.fdot(f,h)<0:f=-f
 Hnorm=mp.fdot(h,h);Vmat=arch+spatial
 fmt=lambda x:mp.nstr(x,dps)
 def metrics(A,base=False):
  if base:e,g=ev,f
  else:e,W=mp.eigsy(A);g=W[:,0]
  return {'lambda0':fmt(e[0]),'lambda0_sign':int(mp.sign(e[0])),'V':fmt(mp.fdot(g,Vmat*g)),'arch':fmt(mp.fdot(g,arch*g)),'spatial':fmt(mp.fdot(g,spatial*g)),'w0':fmt(abs(mp.fdot(g,h))**2/Hnorm),'overlap_true_ground':fmt(abs(mp.fdot(g,f))**2),'eigen_residual':fmt(mp.norm(A*g-e[0]*g))}
 baseline=metrics(K,True);rows=[]
 for eps_string in epses:
  eps=mp.mpf(eps_string)
  for convention in ('analytic_continuation','physical_clipped'):
   delta=mp.zeros(m+1);atoms=[];j=1
   while 2**j<=m:
    n=2**j;s=mp.log(n);shift=j*eps;weight=mp.log(2)/mp.sqrt(n)
    delta-=weight*(qeven(L,s+shift,m,convention=='physical_clipped')-qeven(L,s,m,False))
    atoms.append({'n':n,'j':j,'weight':fmt(weight),'old_location':fmt(s),'new_location':fmt(s+shift),'beyond_window':s+shift>L});j+=1
   row={'m':m,'dps':dps,'order':order,'epsilon':eps_string,'convention':convention,**metrics(K+delta),'delta_matrix_norm':fmt(mp.norm(delta))}
   for key in ('lambda0','V','arch','spatial','w0'):row['change_'+key]=fmt(mp.mpf(row[key])-mp.mpf(baseline[key]))
   row['shifted_atoms']=atoms;rows.append(row)
   print(m,dps,eps_string,convention,row['lambda0_sign'],flush=True)
 out={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':m,'dps':dps,'order':order,'baseline':baseline,'rows':rows,'all_other_prime_powers_unchanged':True,'V_forms_unchanged':True,'elapsed':time.monotonic()-start}
 (OUT/f'shake_m{m}_dps{dps}_gl{order}.json').write_text(json.dumps(out,indent=2)+'\n')
 return out
if __name__=='__main__':
 m,dps,order=map(int,sys.argv[1:4]);run(m,dps,order,sys.argv[4:] or ('1e-26','1e-20','1e-12','1e-6'))

def summarize():
 import hashlib
 files=[OUT/f'shake_m{m}_dps180_gl160.json' for m in (8,12,16,20,24)]
 sets=[json.loads(p.read_text()) for p in files];rows=[]
 for d in sets:
  for r in d['rows']:rows.append({k:v for k,v in r.items() if k!='shifted_atoms'})
 with (OUT/'shake_summary.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 mp.mp.dps=240
 lo=sets[-1];hi=json.loads((OUT/'shake_m24_dps220_gl192.json').read_text());checks=[]
 for r in hi['rows']:
  a=next(x for x in lo['rows'] if x['epsilon']==r['epsilon'] and x['convention']==r['convention'])
  check={'epsilon':r['epsilon'],'convention':r['convention']}
  for key in ('lambda0','V','arch','spatial','w0','overlap_true_ground'):
   u,v=mp.mpf(a[key]),mp.mpf(r[key]);check[key]={'absolute_difference':mp.nstr(abs(u-v),80),'relative_difference':mp.nstr(abs(u-v)/abs(v),80) if v else None}
  checks.append(check)
 provenance={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [OUT/'shake.py',OUT/'v_forms.py',OUT/'source/break_sign_keep_shape.py',OUT/'source/shake_probe.py']}
 (OUT/'shake_validation.json').write_text(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','source_sha256':provenance,'m24_180_vs_220':checks},indent=2)+'\n')
 lines=['# Positive fixed-weight SHAKE','', '**DIAGNOSTIC_NEVER_A_PROOF.**','', 'Each atom 2^j ≤ m moves from log(2^j) to log(2^j)+jε, preserving its original log(2)/sqrt(2^j) weight. All other prime powers remain unchanged. The primary convention analytically continues q beyond L; the secondary convention sets q=0 beyond L. The archimedean and spatial matrices in V are unchanged; their expectations change because the ground vector changes.','', 'Primary analytic-continuation results (180 dps, GL160):','', '|m|positive ε|λ₀|V|w₀(theta)|overlap² with true ground|','|---:|---:|---:|---:|---:|---:|']
 s=lambda x:mp.nstr(mp.mpf(x),10)
 for d in sets:
  b=d['baseline'];lines.append(f"|{d['m']}|0|{s(b['lambda0'])}|{s(b['V'])}|{s(b['w0'])}|1|")
  for r in d['rows']:
   if r['convention']=='analytic_continuation':lines.append(f"|{d['m']}|{r['epsilon']}|{s(r['lambda0'])}|{s(r['V'])}|{s(r['w0'])}|{s(r['overlap_true_ground'])}|")
 lines+=['','Physical clipping changes only the endpoint atoms for m=8 and m=16 on this ε grid. Both conventions and all differences from baseline are recorded in shake_summary.csv and individual JSON files.','', '|m|ε|clipped λ₀|clipped V|clipped w₀|','|---:|---:|---:|---:|---:|']
 for d in sets:
  if d['m'] in (8,16):
   for r in d['rows']:
    if r['convention']=='physical_clipped':lines.append(f"|{d['m']}|{r['epsilon']}|{s(r['lambda0'])}|{s(r['V'])}|{s(r['w0'])}|")
 vv=[mp.mpf(r['V']) for r in rows];lines+=['',f"Across these finite perturbations, V ranges from {mp.nstr(min(vv),12)} to {mp.nstr(max(vv),12)}. The table reports growth with m directly; no cofinal bound or asymptotic law is inferred.",'','m24 at ε=10⁻²⁶ and 10⁻⁶ was rebuilt at 220 dps with GL192. Componentwise changes are in shake_validation.json. This is numerical validation, not an interval certificate.']
 lines+=['', 'For fixed ε=10⁻²⁰ and 10⁻¹², the sampled V increases with m. At ε=10⁻²⁶ it first decreases slightly from m8 to m12, then rises; at ε=10⁻⁶ it falls slightly from m20 to m24 after earlier growth. These five cells therefore do not support universal monotonicity. Positive shifts were used throughout; the negative ε examples in the reference script were not substituted.', '', 'Replay each cell with `uv run --with mpmath python3 shake.py m 180 160`; validation uses `shake.py 24 220 192 1e-26 1e-6`. Rebuild summary by importing shake and calling shake.summarize().']
 (OUT/'RESULT_shake.md').write_text('\n'.join(lines)+'\n')
