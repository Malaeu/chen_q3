"""Bounded all-section zeta q4/q8 profile; no proof."""
from pathlib import Path
import time,csv,json
from sections import World,write,ROOT

def main():
    start=time.monotonic();rows=[];stopped=False
    old=list(csv.DictReader((ROOT/'all_sections_q1.csv').open()))
    q1={(int(x['mesh']),int(x['n'])):float(x['mu']) for x in old if x['world']=='zeta' and x['status']=='FINITE_SAMPLED'}
    for mesh in (32,64,128,256):
        ctx=World('zeta',mesh)
        for n in range(2,241):
            previous=q1[mesh,n]
            for q in (4,8):
                if time.monotonic()-start>120:stopped=True;break
                row=ctx.evaluate(n,q);rows.append(row)
                if row['status']=='FINITE_SAMPLED':
                    if row['mu']>previous+1e-7:raise ArithmeticError('Nested monotonicity failed')
                    previous=row['mu']
            if stopped:break
        print('mesh',mesh,'rows',len(rows),'seconds',time.monotonic()-start,flush=True)
        if stopped:break
    write('zeta_all_sections_q4_q8.csv',rows)
    valid=[x for x in rows if x['status']=='FINITE_SAMPLED']
    summary=[]
    for mesh in (32,64,128,256):
        for q in (4,8):
            block=[x for x in valid if x['mesh']==mesh and x['q']==q]
            best=min(block,key=lambda x:x['mu']) if block else None
            summary.append(dict(mesh=mesh,q=q,count=len(block),argmin_n=best['n'] if best else None,min_mu=best['mu'] if best else None,positive_count=sum(x['mu']>0 for x in block)))
    write('zeta_block_profile_summary.csv',summary)
    result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',complete=len(rows)==1912,stopped_at_budget=stopped,expected_rows=1912,rows=len(rows),seconds=time.monotonic()-start,all_valid=len(valid)==len(rows),all_positive=all(x['mu']>0 for x in valid),nested_monotonicity_checked=True,summary=summary)
    (ROOT/'zeta_block_profile_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
if __name__=='__main__':main()
