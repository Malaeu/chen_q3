"""Outward evaluation of the reviewer's analytic continuity budget.

This bounds a fixed-cardinality Gram perturbation. It is not an all-node
positivity certificate. A negative lower budget is an unpaid bound.
"""
from pathlib import Path
import csv,json,re
from certify import arb,ctx,nodes,BACKEND,show
P=Path(__file__).resolve().parent
ctx.prec=512

def omega(e,T,W):
    x=(-e/2).exp()
    arch=e*(e*arb('1.5')).exp()/2+e*(x.atanh()+x.atan())
    c=arb.const_euler()+(8*arb.pi()).log()+arb.pi()/2
    weights=arb(0)
    for n in range(2,W+1):
        for p in range(2,n+1):
            if n%p==0:
                k=n
                while k%p==0:k//=p
                if k==1:weights+=arb(p).log()/arb(n).sqrt()
                break
    return arch+e*(c/2+4*(T/2).sinh()+weights)

def entry_budget(e,T,W):return omega(2*e,T,W)+2*omega(e,T,W)

rows=[];candidates={}
for f in sorted(P.glob('W*_M*_b512.json')):
    cert=json.loads(f.read_text())
    if not cert.get('status','').startswith('FINITE_SCREW_GRAM_POSITIVE_DEFINITE'):continue
    key=cert['window_integer'],cert['mesh_denominator']
    if key not in candidates or arb(cert['eigenvalue_strict_lower_endpoint']).lower()>arb(candidates[key][1]['eigenvalue_strict_lower_endpoint']).lower():candidates[key]=(f,cert)
for key,(f,cert) in sorted(candidates.items()):
    W=cert['window_integer'];M=cert['mesh_denominator'];N=cert['dimension'];T=arb(W).log()
    # Parse the recorded lower interval conservatively. Native Arb ball text
    # is accepted by arb; iv endpoint-pair text is parsed by its own context.
    lower=arb(cert['eigenvalue_strict_lower_endpoint'])
    e=arb(1)/(2*M);entry=entry_budget(e,T,W);operator=N*entry
    tiny=None
    for k in range(2,25):
        eps=arb(1)/(10**k);loss=N*entry_budget(eps,T,W)
        if loss.upper()<lower.lower()/2:
            tiny=dict(epsilon=f'1e-{k}',entry_error_interval=show(entry_budget(eps,T,W)),matrix_error_upper=show(loss.upper()),perturbed_eigenvalue_lower=show((lower-loss).lower()))
            break
    rows.append(dict(window_integer=W,mesh_denominator=M,dimension=N,base_certificate=f.name,nearest_grid_error=show(e),entry_error=show(entry),matrix_norm_error_bound=show(operator),base_eigenvalue_lower=show(lower),interstitial_lower_budget=show(lower-operator),interstitial_certificate=False,arithmetic_backend=BACKEND,small_fixed_configuration_neighborhood=tiny))
(P/'INTERSTITIAL_BUDGET.json').write_text(json.dumps(dict(status='EXPLICIT_INTERSTITIAL_BOUND_INSUFFICIENT_FOR_ALL_NODES',diagnostic='DIAGNOSTIC_NEVER_A_PROOF',scope='The small-neighborhood result is only for configurations of the SAME finite cardinality, each corresponding coordinate within the stated epsilon and all coordinates remaining inside [0,logW]. It does not cover every possible new point or arbitrary cardinality.',rows=rows),indent=2)+'\n')
print(json.dumps([dict(W=r['window_integer'],M=r['mesh_denominator'],N=r['dimension'],small_epsilon=r['small_fixed_configuration_neighborhood']['epsilon'] if r['small_fixed_configuration_neighborhood'] else None) for r in rows]))
