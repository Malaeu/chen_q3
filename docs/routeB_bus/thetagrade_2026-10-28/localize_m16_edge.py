#!/usr/bin/env python3
"""Finite full-source absolute edge bound; not a cofinal NOESCAPE proof."""
from pathlib import Path
import hashlib
import json
from flint import arb, ctx

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'noescape_m16_ground_eigenpair.json'
OUTPUT = HERE / 'localize_m16_edge.json'


def main():
    ctx.dps = 100
    data = json.loads(SOURCE.read_text())
    block = data['ground_eigenvector']
    assert block['selected_index_zero_based'] == 0
    v = [arb(a['ball']) for a in block['interval_normalized']['even_basis_coordinates']]
    assert len(v) == 17
    norm2 = sum((x*x for x in v), arb(0))
    assert 1 in norm2
    m, w = 16, 4
    L = arb(m).log()
    omega = 2*arb.pi()*m/L
    delta = sum((x*x for x in v[m-w+1:]), arb(0)).sqrt()
    derivative2 = sum(((2*arb.pi()*i/L)**2*v[i]**2 for i in range(1,m+1)), arb(0))
    trace = (v[0]+arb(2).sqrt()*sum(v[1:],arb(0)))/L.sqrt()
    endpoint_sum = 2*abs(trace)
    d = arb.const_euler()+(8*arb.pi()).log()+arb.pi()/2+(2+4*L)*arb(m).sqrt()
    bf = (10*derivative2+10*endpoint_sum**2+20+d).sqrt()
    br = delta*(10*(64+2*omega)**2+40*(2*m+1)/L+20+d).sqrt()
    bound = bf*br
    assert bound.upper() < arb('0.00001185')
    result = {
        'status':'FINITE_SOURCE_MAJORANT_NOT_COFINAL_PROOF',
        'm':m,'N':m,'w':w,'edge_even_indices':list(range(13,17)),
        'input_index':0,'input_normalization':'interval-normalized ground block',
        'cutoff':'even C-infinity, plateau |x|<=1/4, support |x|<=1/2; u=4|x|-1, chi=theta(1-u)/(theta(1-u)+theta(u)), theta(t)=exp(-1/t)',
        'kappa':'chi squared','kappa_derivative_upper_bound':64,
        'edge_norm':str(delta),'interior_derivative_norm_squared':str(derivative2),
        'endpoint_sum':str(endpoint_sum),'input_norm_squared':str(norm2),
        'full_form_majorant_f':str(bf),'full_form_majorant_return_upper':str(br),
        'absolute_E_bound_ball':str(bound),
        'certified_symmetric_E_enclosure':'[-0.00001185, 0.00001185]',
        'derivation':'LOCALIZE L2: ||r||<=delta; ||r_prime||<= (64+2 Omega)delta; J(r)<=2 sqrt((2m+1)/L)delta; E=k(f,r)',
        'full_source_terms':'arch tail, all supported prime powers, both pole operator costs, scalar and endpoint jumps',
        'not_used':'bottom stationarity, local energy identity, numerical quadrature',
        'limitations':['Does not determine the sign of E.','Does not bound the off-edge term or F_far.','Input eigenpair provenance inherited; residual containment alone is not an eigenpair existence proof.','No cofinal statement or RH claim.'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
    print(result['certified_symmetric_E_enclosure'])

if __name__ == '__main__':
    main()
