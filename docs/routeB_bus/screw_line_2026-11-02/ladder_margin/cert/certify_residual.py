#!/usr/bin/env python3
"""Verified exact-dyadic Cholesky residual certificate; finite scope only."""
from pathlib import Path
from fractions import Fraction
import argparse,json,time,hashlib
from certify import arb,ctx,nodes,source,BACKEND,show
P=Path(__file__).resolve().parent

def dyadic(matrix):
    ratios=[[float(x).as_integer_ratio() for x in row] for row in matrix]
    bits=max(d.bit_length()-1 for row in ratios for n,d in row)
    return [[n << (bits-(d.bit_length()-1)) for n,d in row] for row in ratios],bits

def build_source(W,M,bits):
    ctx.prec=bits;labels=nodes(M,W);g,controls=source(M,W);v=[g(k,Fraction(r)) for k,r in labels];n=len(labels)
    A=[[arb(0)]*n for _ in range(n)]
    for i,(k,r) in enumerate(labels):
        for j in range(i+1):
            l,s=labels[j];a=g(k-l,Fraction(r,s))-v[i]-v[j];A[i][j]=a;A[j][i]=a
    return labels,A,controls

def midpoint(x):
    # Witness construction only; this is not used in interval verification.
    if hasattr(x,'mid'):return float(x.mid())
    return float(x.v.a)

def run(W,M,bits=512,replay=False):
    start=time.monotonic();labels,A,controls=build_source(W,M,bits);n=len(labels)
    stem=f'W{W}_M{M}_residual_b{bits}';wp=P/(stem+'_witness.json')
    if replay:
        witness=json.loads(wp.read_text());assert witness['W']==W and witness['M']==M and witness['dimension']==n
        Li=witness['L_numerators'];Bi=witness['B_numerators'];dl=witness['L_denominator_bits'];db=witness['B_denominator_bits']
    else:
        import numpy as np
        from scipy.linalg import cholesky,solve_triangular
        approx=np.array([[midpoint(x) for x in row] for row in A]);L=cholesky(approx,lower=True,check_finite=False);B=solve_triangular(L,np.eye(n),lower=True,check_finite=False)
        Li,dl=dyadic(L);Bi,db=dyadic(B)
        witness=dict(W=W,M=M,dimension=n,L_denominator_bits=dl,B_denominator_bits=db,L_numerators=Li,B_numerators=Bi,interpretation='Exact dyadic matrices. Approximate construction is untrusted; verification uses exact integers and directed source intervals.')
        wp.write_text(json.dumps(witness,separators=(',',':'))+'\n')
    assert all(len(r)==n for r in Li+Bi)
    assert all(Li[i][i]>0 for i in range(n))
    assert all(Li[i][j]==Bi[i][j]==0 for i in range(n) for j in range(i+1,n))
    # BL-I exact dyadic product; no floating arithmetic in this verification.
    scale=1<<(dl+db);rowerr=[0]*n;colerr=[0]*n
    for i in range(n):
        for j in range(i+1):
            value=sum(Bi[i][k]*Li[k][j] for k in range(j,i+1))-(scale if i==j else 0)
            rowerr[i]+=abs(value);colerr[j]+=abs(value)
    epsinfnum=max(rowerr);eps1num=max(colerr)
    assert epsinfnum<scale and eps1num<scale
    bninf=max(sum(abs(x) for x in row) for row in Bi)
    bn1=max(sum(abs(Bi[i][j]) for i in range(n)) for j in range(n))
    bscale=1<<db
    gamma=(1-arb(eps1num)/scale)*(1-arb(epsinfnum)/scale)/((arb(bn1)/bscale)*(arb(bninf)/bscale))
    # Source residual A-LL^T: LL^T products are exact integer sums.
    lscale=1<<(2*dl);errs=[arb(0)]*n;max_entry=arb(0)
    for i in range(n):
        for j in range(i+1):
            a0=sum(Li[i][k]*Li[j][k] for k in range(j+1))
            bound=abs(A[i][j]-arb(a0)/lscale).upper()
            errs[i]+=bound
            if i!=j:errs[j]+=bound
            if bound>max_entry:max_entry=bound
    enorm=max(x.upper() for x in errs);lower=gamma-enorm
    assert lower.lower()>0
    result=dict(status='FINITE_SCREW_GRAM_POSITIVE_DEFINITE_BY_DYADIC_RESIDUAL',diagnostic='DIAGNOSTIC_NEVER_A_PROOF / CHALLENGER / NOT_RH',window_integer=W,mesh_denominator=M,dimension=n,precision_bits=bits,arithmetic_backend=BACKEND,epsilon1=show(arb(eps1num)/scale),epsilon_infinity=show(arb(epsinfnum)/scale),B_norm1=show(arb(bn1)/bscale),B_norm_infinity=show(arb(bninf)/bscale),approximate_factor_eigenvalue_lower=show(gamma),source_residual_norm_upper=show(enorm),maximum_entry_residual_upper=show(max_entry),eigenvalue_strict_lower_endpoint=show(lower.lower()),eigenvalue_lower_interval=show(lower),source_comparisons=controls,witness_sha256=hashlib.sha256(wp.read_bytes()).hexdigest(),verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_verifier_sha256=hashlib.sha256((P/'certify.py').read_bytes()).hexdigest(),interval_backend_sha256=hashlib.sha256((P/'interval_backend.py').read_bytes()).hexdigest(),seconds=time.monotonic()-start,replay_only=replay,scope='Finite listed exact nodes only. Not arbitrary between-node points, cardinality or RH.')
    outfile=P/(stem+('_replay' if replay else '')+'.json');outfile.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['window_integer','mesh_denominator','dimension','eigenvalue_strict_lower_endpoint','source_residual_norm_upper','seconds','replay_only']}),flush=True)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--mesh',type=int,default=64);parser.add_argument('--bits',type=int,default=512);parser.add_argument('--window',type=int,nargs='+',default=[3,5,7]);parser.add_argument('--replay',action='store_true');a=parser.parse_args()
    for W in a.window:run(W,a.mesh,a.bits,a.replay)
