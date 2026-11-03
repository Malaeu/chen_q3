"""Independent source regressions; numerical diagnostics, not interval bounds."""
from pathlib import Path
import sys,importlib.util,argparse,json,time,hashlib
sys.path.insert(0,'/workspace/conditioning_deps')
import gmpy2 as g
import mpmath as mp
import analytic_source as analytic
P=Path(__file__).resolve().parent;BUS=P.parents[1]
def module(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def main():
    a=argparse.ArgumentParser();a.add_argument('--mode',choices=['q2','mpfr'],required=True);a.add_argument('--m',type=int,required=True);z=a.parse_args();started=time.monotonic();rows=[]
    if z.mode=='q2':
        ref=module('reference_q2',BUS/'lit_quickcheck_2026-11-03/Q2_simple_even/check.py')
        mp.mp.dps=120;ref.nodes.cache_clear();A,meta=analytic.build(z.m,448)
        for world in ['zeta','dh']:
            E,O=ref.build(z.m,z.m,world,160)
            for parity,F,R in [('even',A[world][0],E),('odd',A[world][1],O)]:
                err=max(abs(mp.mpf(str(F[i,j]))-R[i,j]) for i in range(R.rows) for j in range(R.cols))
                assert err<mp.mpf('1e-110'),(world,parity,err)
                rows.append(dict(world=world,parity=parity,max_entry_difference=mp.nstr(err,35),reference_dps=120,reference_order=160))
        PE,PO=ref.plant(*ref.build(z.m,z.m,'zeta',160),mp.log(z.m))
        for parity,F,R in [('even',A['plant'][0],PE),('odd',A['plant'][1],PO)]:
            err=max(abs(mp.mpf(str(F[i,j]))-R[i,j]) for i in range(R.rows) for j in range(R.cols));assert err<mp.mpf('1e-110')
            rows.append(dict(world='plant',parity=parity,max_entry_difference=mp.nstr(err,35),reference_dps=120,reference_order=160))
    else:
        ref=module('reference_mpfr',P/'source_50777d4.py');A,meta=analytic.build(z.m,448);g.get_context().precision=400
        R=ref.build(z.m,256)
        for world in ['zeta','dh','plant']:
            err=max(abs(x-y) for x,y in zip(A[world][0].flat,R[world].flat));assert err<g.mpfr('1e-110'),(world,err)
            rows.append(dict(world=world,parity='even',max_entry_difference=str(err),reference_bits=400,reference_order=256))
    result=dict(status='ANALYTIC_SOURCE_NUMERIC_REGRESSION_PASS',m=z.m,mode=z.mode,rows=rows,analytic_metadata=meta,seconds=time.monotonic()-started,source_sha256=hashlib.sha256((P/'analytic_source.py').read_bytes()).hexdigest(),interval_bound=False)
    (P/f'validation_{z.mode}_m{z.m}.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
