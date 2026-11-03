"""Complete scheduled tall-DH half-cutoff σ grid; fixed80digit zero inputs.
Example: python3 tall_sweep.py --m80.. expanded shell list --tag even --cpu600.
Only assigned distinct m cells are mutated; E/J/Schur and A remain unchanged.
"""
from core import *
import resource,signal,argparse
OUT=P/'tall_sweep';OUT.mkdir(exist_ok=True)
a=argparse.ArgumentParser();a.add_argument('--m',nargs='+',type=int,required=True);a.add_argument('--tag',required=True);a.add_argument('--cpu',type=int,default=600);args=a.parse_args();start=time.process_time();completed=[];current=None

def atomic(path,data):
 tmp=path.with_suffix('.json.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(path)

def summary(status):
 atomic(OUT/f'{args.tag}_DONE.json',dict(status=status,scope='DIAGNOSTIC_NEVER_A_PROOF',requested=args.m,completed=completed,missing=[m for m in args.m if m not in completed],cpu_seconds=time.process_time()-start,cpu_cap=args.cpu))

def timeout(sig,frame):
 summary('UNRESOLVED_CPU_CAP');raise SystemExit(0)
signal.signal(signal.SIGXCPU,timeout);resource.setrlimit(resource.RLIMIT_CPU,(args.cpu,args.cpu+1))

for m in args.m:
 current=m;receipt=OUT/f'dh_m{m}_half.json'
 if receipt.exists():
  old=json.loads(receipt.read_text())
  if old.get('outcome')=='RESOLVED_FIXED_DECIMAL_MATRIX':completed.append(m);continue
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world='dh',m=m,cut='c_half',J_dimension=0,input_scope='SAME frozen≈80digit DH zero table at both arithmetic precisions; no root enclosure or root-uncertainty propagation.',attempts=[])
 try:
  estimates=[]
  for precision in [200,240]:
   mp.mp.dps=precision;T=cutoff(m,'.5');E,labels,heights,metric=rows_for('dh',m,T);s=sigma_min(E,maxiter=35);estimates.append(s['sigma']);mass={}
   for label,value in zip(labels,s['left']):mass.setdefault(label['gamma'],mp.mpf(0));mass[label['gamma']]+=abs(value)**2
   hs=sorted(mass,key=lambda x:mp.mpf(x));pair=max(range(len(hs)-1),key=lambda i:mass[hs[i]]+mass[hs[i+1]])
   result['attempts'].append(dict(weak_left=[dict(label=label,coordinate=mp.nstr(value,120),mass=mp.nstr(abs(value)**2,120)) for label,value in zip(labels,s['left'])],weak_pair_localization='localized' if mass[hs[pair]]+mass[hs[pair+1]]>=mp.mpf('.5') else 'diffuse',weak_pair_left=hs[pair],weak_pair_right=hs[pair+1],weak_pair_mass=mp.nstr(mass[hs[pair]]+mass[hs[pair+1]],100),dps=precision,q=E.rows,dimension=E.cols,sigma=mp.nstr(s['sigma'],160),sigma_squared=mp.nstr(s['squared'],160),iterations=s['iterations'],relative_residual=mp.nstr(s['relative_residual'],40),relative_change=mp.nstr(s['relative_change'],40),cpu_seconds=time.process_time()-start));atomic(receipt,result)
  agreement=abs(estimates[1]/estimates[0]-1)
  if agreement>=mp.mpf('1e-20'):raise ArithmeticError(f'cross-precision agreement gate failed: {agreement}')
  result.update(outcome='RESOLVED_FIXED_DECIMAL_MATRIX',relative_200_240=mp.nstr(agreement,60),agreement_gate='relative_200_240 <1e-20');atomic(receipt,result)
  cp=P/'cells'/f'dh_m{m}.json';cell=json.loads(cp.read_text());s=result['attempts'][-1]
  for r in cell['rows']:
   if r['cut']=='c_half' and r['variant']=='base':
    r.update(sigma_min=s['sigma'],sigma_min_squared=s['sigma_squared'],sigma_dps=s['dps'],sigma_iterations=s['iterations'],sigma_relative_residual=s['relative_residual'],sigma_relative_change=s['relative_change'],sigma_status='MP200_240_TALL_SWEEP',sigma_sweep_source=str(receipt.relative_to(P)),weak_pair_left=s['weak_pair_left'],weak_pair_right=s['weak_pair_right'],weak_pair_mass=s['weak_pair_mass'])
    lr=r['lambda_r_preferred'];r['twice_sigma_squared_over_lambda_r']=mp.nstr(2*mp.mpf(s['sigma_squared'])/mp.mpf(lr),100) if lr is not None and mp.mpf(lr) else None
  atomic(cp,cell);completed.append(m);summary('RUNNING');print('TALL',m,s['sigma'],'CPU',time.process_time()-start,flush=True)
 except Exception as error:
  result.update(outcome='UNRESOLVED_EXCEPTION',exception=repr(error));atomic(receipt,result);print('ERROR',m,repr(error),flush=True)
summary('COMPLETE' if len(completed)==len(args.m) else 'PARTIAL')
