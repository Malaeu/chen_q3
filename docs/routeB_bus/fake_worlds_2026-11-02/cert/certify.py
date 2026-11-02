#!/usr/bin/env python3
"""Fixed finite DH Rayleigh enclosure. DIAGNOSTIC_NEVER_A_PROOF; NOT_RH.

Replay: uv run --with python-flint python certify.py 51
        uv run --with python-flint python certify.py 55
No approximate matrix or eigensolver is used in verification.
"""
from pathlib import Path
import argparse, hashlib, json, time
import flint
from flint import arb, acb, ctx

OUT = Path(__file__).resolve().parent

def certify(m, bits=512):
    ctx.prec = bits
    path = OUT / f'witness_m{m}.json'
    witness = json.loads(path.read_text())
    assert witness['m'] == m and len(witness['coefficients']) == m + 1
    denominator = 2 ** witness['denominator_bits']
    c = [arb(int(k)) / denominator for k in witness['coefficients']]
    norm = sum(x*x for x in c)
    assert norm.lower() > 0
    L, pi = arb(m).log(), arb.pi()
    ds = [arb(1)] + [arb(2).sqrt()] * m
    B = [arb(0) for _ in c]
    for n in range(1, m+1):
        B[n] = -c[n]*c[n]/(pi*n)
    for i in range(m+1):
        for j in range(i+1, m+1):
            z = 2*c[i]*c[j]*ds[i]*ds[j]/(pi*(i*i-j*j))
            B[j] += z*j
            B[i] -= z*i
    omega = [2*pi*n/L for n in range(m+1)]

    def Q(s):
        return sum(2*c[n]*c[n]*(1-s/L)*(omega[n]*s).cos()
                   + B[n]*(omega[n]*s).sin() for n in range(m+1))

    def integrand(s, analytic):
        # Entire numerator quotient (2||f||^2-Q(s))/s, including s=0.
        z = acb(0)
        for n in range(m+1):
            x = omega[n]*s
            half = x/2
            z += (2*c[n]*c[n]*(omega[n]*half.sin()*half.sinc()+x.cos()/L)
                  - B[n]*omega[n]*x.sinc())
        # s*j_D(s)=exp(-s/2)/(2*sinh(s)/s). sinc(i*s)=sinh(s)/s.
        # The callback is meromorphic; a denominator containing a pole
        # gives a nonfinite ball. No branch-cut function is used here.
        return (-s/2).exp()*z/(2*(acb(0,1)*s).sinc())

    start = time.monotonic()
    pieces = []
    for i in range(16):
        value = acb.integral(integrand, L*i/16, L*(i+1)/16,
                             abs_tol=arb('1e-58'), rel_tol=arb('1e-58'),
                             eval_limit=100000, deg_limit=200)
        assert value.is_finite() and value.imag.contains(0)
        pieces.append(value)
    a = (-L/2).exp()
    tail = 2*norm*(a.atanh()-a.atan())
    arch = sum(pieces).real + tail
    theta = ((10-2*arb(5).sqrt()).sqrt()-2)/(arb(5).sqrt()-1)
    periodic = [arb(0), arb(1), theta, -theta, arb(-1)]
    b = [arb(0)] * (m+1)
    for n in range(2, m+1):
        b[n] = periodic[n%5]*arb(n).log() - sum(
            b[d]*periodic[(n//d)%5] for d in range(2,n) if n%d == 0)
    arithmetic = sum(b[n]/arb(n).sqrt()*Q(arb(n).log()) for n in range(2,m))
    c_D = arb.const_euler() + (8*pi/5).log() - pi/2
    rayleigh = (arch-c_D*norm-arithmetic)/norm
    assert rayleigh.is_finite() and rayleigh.upper() < 0
    if m == 51:
        assert 2*rayleigh.rad() < arb('1e-49')
    show = lambda x: x.str(90)
    result = {
        'status': 'FINITE_DH_RAYLEIGH_UPPER_NEGATIVE',
        'route_label': 'DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER / NOT_RH',
        'm': m, 'N': m, 'precision_bits': bits,
        'python_flint_version': flint.__version__,
        'witness_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'norm_squared': show(norm), 'arch_interior': show(sum(pieces).real),
        'arch_tail': show(tail), 'arch_total': show(arch),
        'arithmetic_all_integers': show(arithmetic), 'c_D_positive': show(c_D),
        'pole': '0', 'rayleigh_interval': show(rayleigh),
        'rayleigh_lower': show(rayleigh.lower()), 'rayleigh_upper': show(rayleigh.upper()),
        'rayleigh_ball_radius': show(rayleigh.rad()), 'upper_strictly_negative': True,
        'panels': [str(x) for x in pieces], 'seconds': time.monotonic()-start,
        'scope': 'One exact dyadic vector in the finite literal carrier. Does not certify the first negative m, full minimum value, zero census, quiet space, envelope delta, or any cofinal assertion.'
    }
    (OUT/f'rayleigh_m{m}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('m','rayleigh_interval','upper_strictly_negative','seconds')}))
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('m',type=int,choices=(51,55))
    parser.add_argument('--bits',type=int,default=512)
    args = parser.parse_args()
    certify(args.m,args.bits)
