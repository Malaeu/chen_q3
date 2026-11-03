"""All old history through exact arithmetic endpoints. Finite diagnostic only."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,csv,time
import numpy as np
import scipy.linalg as la
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'uniform'))
from margins import float_source,CORE

def gram(g,left,right,fl,fr):
    left=np.asarray(left)[:,None];right=np.asarray(right)[:,None]
    fl=np.asarray(fl)[None,:];fr=np.asarray(fr)[None,:]
    return g(right-fr)-g(right-fl)-g(left-fr)+g(left-fl)

class World:
    def __init__(self,world,mesh):
        self.world=world;self.mesh=mesh;self.h=1/mesh
        saved=json.loads((CORE/f'{world}_mesh{mesh}_dps100.json').read_text())
        self.first=saved['first_negative_prefix']
        self.rr=np.array(saved['r_values'],float)
        maximum=int(np.floor(np.log(240)*mesh))
        if self.first is not None:maximum=min(maximum,self.first-1)
        self.L=la.cholesky(la.toeplitz(self.rr[:maximum]),lower=True,check_finite=False)
        self.g=float_source(world,end=6.3)
    def evaluate(self,n,q):
        a=np.log(n);delta=np.log1p(1/n);p=int(np.floor(a*self.mesh));t=p*self.h
        base=dict(world=self.world,mesh=self.mesh,n=n,a=a,delta=delta,q=q,old_uniform_count=p,old_partial_length=a-t,outside_proved_short_coercivity=n<16)
        empty=dict(mu='',partial_old_pivot='',fresh_min_chol='',status='',coupling_top='',precision='float64 source with MP100 old Toeplitz data')
        if self.first is not None and p>=self.first:return dict(**base,**(empty|{'status':'INVALID_OLD_UNIFORM_PREFIX'}))
        oldleft=np.arange(p)*self.h;oldright=(np.arange(p)+1)*self.h
        fl=a+np.arange(q)*delta/q;fr=a+np.arange(1,q+1)*delta/q
        left=np.r_[t,fl];right=np.r_[a,fr]
        B=gram(self.g,oldleft,oldright,left,right)
        Y=la.solve_triangular(self.L[:p,:p],B,lower=True,check_finite=False)
        fresh=gram(self.g,left,right,left,right);fresh=(fresh+fresh.T)/2
        pivot=fresh[0,0]-Y[:,0]@Y[:,0]
        if pivot<=1e-11:
            return dict(**base,**(empty|{'status':'INVALID_PARTIAL_OLD' if pivot<-1e-11 else 'UNRESOLVED_PARTIAL_OLD','partial_old_pivot':float(pivot)}))
        F=fresh[1:,1:]
        try:LF=la.cholesky(F,lower=True,check_finite=False)
        except la.LinAlgError:return dict(**base,**(empty|{'status':'FRESH_NOT_POSITIVE_OR_UNRESOLVED','partial_old_pivot':float(pivot)}))
        v=fresh[0,1:]-Y[:,0]@Y[:,1:]
        G=Y[:,1:].T@Y[:,1:]+np.outer(v,v)/pivot
        W=la.solve_triangular(LF,G,lower=True,check_finite=False)
        W=la.solve_triangular(LF,W.T,lower=True,check_finite=False).T;W=(W+W.T)/2
        top=la.eigvalsh(W,subset_by_index=[q-1,q-1],check_finite=False)[0]
        return dict(**base,mu=float(1-top),partial_old_pivot=float(pivot),fresh_min_chol=float(np.min(np.diag(LF))),status='FINITE_SAMPLED',coupling_top=float(top),precision=empty['precision'])

def write(name,rows):
    with (ROOT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)

def main():
    start=time.monotonic();single=[];refined=[];summary=[]
    for mesh in (32,64,128,256):
        for world in ('zeta','dh','plant'):
            ctx=World(world,mesh)
            block=[ctx.evaluate(n,1) for n in range(2,241)]
            valid=[x for x in block if x['status']=='FINITE_SAMPLED']
            best=min(valid,key=lambda x:x['mu']) if valid else None
            reps=sorted(set([16,32,64,120,240]+([best['n']] if best else [])))
            checks=[ctx.evaluate(n,q) for n in reps for q in (1,4,8,16,32)]
            for n in reps:
                vv=[x for x in checks if x['n']==n and x['status']=='FINITE_SAMPLED']
                if len(vv)>1 and any(y['mu']>x['mu']+1e-7 for x,y in zip(vv,vv[1:])):raise ArithmeticError(f'Nonmonotone future refinement: {world},{mesh},{n}')
            single.extend(block);refined.extend(checks)
            sr=dict(world=world,mesh=mesh,q1_valid_sections=len(valid),q1_argmin_n=best['n'] if best else None,q1_min_mu=best['mu'] if best else None,refined_min_mu=min([x['mu'] for x in checks if x['status']=='FINITE_SAMPLED'],default=None),first_invalid_section=next((x['n'] for x in block if x['status']!='FINITE_SAMPLED'),None))
            summary.append(sr);print(json.dumps(sr),flush=True)
    write('all_sections_q1.csv',single);write('representative_q_refinement.csv',refined);write('summary.csv',summary)
    (ROOT/'summary.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',seconds=time.monotonic()-start,summary=summary,single_count=len(single),refined_count=len(refined)),indent=2)+'\n')
if __name__=='__main__':main()
