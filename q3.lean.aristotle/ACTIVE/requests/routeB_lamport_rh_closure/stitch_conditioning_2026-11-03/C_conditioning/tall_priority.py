"""One prespecified tall DH priority, hard90CPU-s cap; no quiet sector exists."""
from core import *
import resource,signal
OUT=P/'tall_DH120_half_priority.json';start=time.process_time()
result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world='dh',m=120,cut='c_half',J_dimension=0,cpu_budget_seconds=90,prediction_probability_resolution=.8,input_scope='Fixed decimal numerical DH zero census; higher arithmetic dps is not a tighter root enclosure.',attempts=[])
def save():OUT.write_text(json.dumps(result,indent=2)+'\n')
def timeout(sig,frame):
 result.update(outcome='UNRESOLVED_CPU_BUDGET',cpu_seconds=time.process_time()-start);save();raise SystemExit(0)
signal.signal(signal.SIGXCPU,timeout);resource.setrlimit(resource.RLIMIT_CPU,(90,91))
try:
 estimates=[]
 for precision in [200,240]:
  mp.mp.dps=precision;T=cutoff(120,'.5');E,labels,heights,metric=rows_for('dh',120,T);s=sigma_min(E,maxiter=35);estimates.append(s['sigma']);mass={}
  for label,value in zip(labels,s['left']):mass.setdefault(label['gamma'],mp.mpf(0));mass[label['gamma']]+=abs(value)**2
  hs=sorted(mass,key=lambda x:mp.mpf(x));pair=max(range(len(hs)-1),key=lambda i:mass[hs[i]]+mass[hs[i+1]])
  result['attempts'].append(dict(weak_pair_left=hs[pair],weak_pair_right=hs[pair+1],weak_pair_mass=mp.nstr(mass[hs[pair]]+mass[hs[pair+1]],100),dps=precision,q=E.rows,dimension=E.cols,sigma=mp.nstr(s['sigma'],160),sigma_squared=mp.nstr(s['squared'],160),iterations=s['iterations'],relative_residual=mp.nstr(s['relative_residual'],40),relative_change=mp.nstr(s['relative_change'],40),cpu_seconds=time.process_time()-start));save()
 result.update(outcome='RESOLVED_FIXED_DECIMAL_MATRIX',relative_200_240=mp.nstr(abs(estimates[1]/estimates[0]-1),60),cpu_seconds=time.process_time()-start);save()
except Exception as error:
 result.update(outcome='UNRESOLVED_EXCEPTION',exception=repr(error),cpu_seconds=time.process_time()-start);save()
print(json.dumps(result,indent=2))
