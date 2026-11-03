#!/usr/bin/env python3
"""Arb outward finite screw-Gram certificates, independent of zero tables.

DIAGNOSTIC_NEVER_A_PROOF. The certified statement is finite matrix PD.
Run with python-flint: python certify.py --mesh32 --bits512
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
import argparse,csv,json,time,hashlib,math,os
try:
    import flint
    from flint import arb,acb,ctx
    BACKEND='python-flint/Arb '+flint.__version__
except ModuleNotFoundError:
    from interval_backend import arb,acb,ctx
    BACKEND='mpmath.iv directed intervals + bounded Li2 series'

P=Path(__file__).resolve().parent

def source(mesh,window):
    pi=arb.pi();constant=arb.const_euler()+(8*pi).log()+pi/2
    # psi_1(1/4)/4 = (pi^2+8 Catalan)/4.
    trig=(pi*pi+8*arb.const_catalan())/4
    atoms=[]
    for n in range(2,window+1):
        prime=None
        for p in range(2,n+1):
            if n%p==0:
                k=n
                while k%p==0:k//=p
                if k==1:prime=p
                break
        if prime:atoms.append((n,arb(n).log(),arb(prime).log()/arb(n).sqrt()))
    comparisons={'strict':0,'exact_hinge':0}
    @lru_cache(None)
    def g(dk,ratio):
        if dk==0 and ratio==1:return arb(0)
        t=arb(dk)/mesh+arb(ratio.numerator).log()-arb(ratio.denominator).log()
        if t.upper()<0:return g(-dk,1/ratio)
        if not t.lower()>0:raise ArithmeticError('unresolved source argument sign')
        x=(-t/2).exp()
        if not x.upper()<1:raise ArithmeticError('dilog argument unresolved at1')
        z1=acb(x).polylog(2);z2=acb(-x).polylog(2)
        assert z1.imag.contains(0) and z2.imag.contains(0)
        tail=z1.real-z2.real+2*acb(0,x).polylog(2).imag
        value=constant*t/2-trig+tail-16*(t/4).sinh()**2
        for n,logn,weight in atoms:
            if dk==0 and ratio==n:
                comparisons['exact_hinge']+=1
                continue
            diff=t-logn
            if diff.lower()>0:value+=weight*diff
            elif diff.upper()<0:pass
            else:raise ArithmeticError(f'unresolved arithmetic hinge n={n}, dk={dk}, ratio={ratio}')
            comparisons['strict']+=1
        if not value.is_finite():raise ArithmeticError('nonfinite source enclosure')
        return value
    return g,comparisons

def nodes(mesh,window):
    L=arb(window).log();items=[]
    for r in range(1,window+1):
        k=0
        while True:
            if r==window and k==0:items.append((k,r));break
            x=arb(k)/mesh+arb(r).log()
            if (L-x).lower()>0:items.append((k,r));k+=1
            elif (x-L).lower()>0:break
            else:raise ArithmeticError('unresolved node/window ordering')
    # Python sorting uses approximate midpoints only for convenience; every
    # adjacent relation is then verified by a strict Arb difference below.
    items=sorted(set(items),key=lambda z:z[0]/mesh+math.log(z[1]))
    assert items[0]==(0,1)
    for (k,r),(j,s) in zip(items,items[1:]):
        assert (arb(j-k)/mesh+arb(s).log()-arb(r).log()).lower()>0
    return items[1:]

def show(x):return x.str(90)

def certify(window,mesh,bits=512,timeout=180):
    ctx.prec=bits;start=time.monotonic();labels=nodes(mesh,window);n=len(labels)
    g,comparisons=source(mesh,window);values=[g(k,Fraction(r)) for k,r in labels]
    A=[[None]*n for _ in range(n)]
    for i,(k,r) in enumerate(labels):
        if time.monotonic()-start>timeout:raise TimeoutError(f'cell budget during source row{i}')
        for j in range(i+1):
            l,s=labels[j];v=g(k-l,Fraction(r,s))-values[i]-values[j]
            A[i][j]=v;A[j][i]=v
    LL=[[arb(int(i==j)) if i>=j else arb(0) for j in range(n)] for i in range(n)];D=[]
    for j in range(n):
        if time.monotonic()-start>timeout:raise TimeoutError(f'cell budget beforepivot{j}')
        d=A[j][j]-sum((LL[j][k]**2)*D[k] for k in range(j))
        if not d.lower()>0:
            result=dict(status='PIVOT_NOT_CERTIFIED',window=window,mesh=mesh,bits=bits,dimension=n,pivot_index=j,pivot=show(d),seconds=time.monotonic()-start)
            (P/f'W{window}_M{mesh}_b{bits}_failure.json').write_text(json.dumps(result,indent=2)+'\n')
            return result
        D.append(d)
        for i in range(j+1,n):LL[i][j]=(A[i][j]-sum(LL[i][k]*D[k]*LL[j][k] for k in range(j)))/d
    # Rigorous lower eigenvalue from A=L D L^T and induced-norm bounds.
    inv=[[arb(int(i==j)) for j in range(n)] for i in range(n)]
    for i in range(n):
        if time.monotonic()-start>timeout:raise TimeoutError(f'cell budget during inverse-L row{i}')
        for j in range(i):inv[i][j]=-sum(LL[i][k]*inv[k][j] for k in range(j,i))
    norm1=max(sum(abs(inv[i][j]) for i in range(n)).upper() for j in range(n))
    norminf=max(sum(abs(inv[i][j]) for j in range(n)).upper() for i in range(n))
    dmin=min(d.lower() for d in D);eiglower=arb(dmin)/(arb(norm1)*arb(norminf))
    assert eiglower.lower()>0
    stem=f'W{window}_M{mesh}_b{bits}'
    with (P/(stem+'_nodes.csv')).open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=['index','k','r','expression','point_interval']);wr.writeheader()
        for i,(k,r) in enumerate(labels):wr.writerow(dict(index=i,k=k,r=r,expression=f'{k}/{mesh}+log({r})',point_interval=show(arb(k)/mesh+arb(r).log())))
    with (P/(stem+'_pivots.csv')).open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=['index','pivot_interval','positive_lower_endpoint']);wr.writeheader()
        for i,d in enumerate(D):wr.writerow(dict(index=i,pivot_interval=show(d),positive_lower_endpoint=show(d.lower())))
    result=dict(status='FINITE_SCREW_GRAM_POSITIVE_DEFINITE',diagnostic_label='DIAGNOSTIC_NEVER_A_PROOF / CHALLENGER / NOT_RH',window_integer=window,window_length=show(arb(window).log()),mesh_denominator=mesh,precision_bits=bits,dimension=n,arithmetic_backend=BACKEND,minimum_ldl_pivot_lower=show(dmin),inverse_L_norm1_upper=show(norm1),inverse_L_norminf_upper=show(norminf),eigenvalue_lower_interval=show(eiglower),eigenvalue_strict_lower_endpoint=show(eiglower.lower()),source_comparisons=comparisons,source_unique_evaluations=g.cache_info().currsize,seconds=time.monotonic()-start,verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source='Full arithmetic screw source; all prime powers within support; both poles; complete archimedean closed form',scope='Only the listed finite exact nodes. Structural zero removed. Does not certify arbitrary additional points, arbitrary cardinality, all continuous windows, or RH.')
    result['series_tail_target']=os.environ.get('LADDER_LI2_TAIL_TARGET','1e-50') if BACKEND.startswith('mpmath.iv') else None
    result['interval_backend_sha256']=hashlib.sha256((P/'interval_backend.py').read_bytes()).hexdigest() if BACKEND.startswith('mpmath.iv') else None
    (P/(stem+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['window_integer','mesh_denominator','dimension','minimum_ldl_pivot_lower','eigenvalue_strict_lower_endpoint','seconds']}),flush=True)
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--mesh',type=int,default=32);ap.add_argument('--bits',type=int,default=512);ap.add_argument('--window',type=int,nargs='+',default=[3,5,7]);args=ap.parse_args()
    for w in args.window:
        started=time.monotonic()
        try:certify(w,args.mesh,args.bits)
        except TimeoutError as exc:
            result=dict(status='BUDGET_EXHAUSTED_NOT_CERTIFIED',window_integer=w,mesh_denominator=args.mesh,precision_bits=args.bits,arithmetic_backend=BACKEND,reason=str(exc),seconds=time.monotonic()-started,verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
            (P/f'W{w}_M{args.mesh}_b{args.bits}_failure.json').write_text(json.dumps(result,indent=2)+'\n')
            print(json.dumps(result),flush=True)
