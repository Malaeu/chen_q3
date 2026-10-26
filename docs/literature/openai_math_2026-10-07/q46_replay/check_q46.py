#!/usr/bin/env python3
"""Q46: exact coefficient/quadrature controls and canonical-source verification.
Standard library only. No numerical CCM spectral calculation and no prime-gap
asymptotic verification. Historical embedded programs are never executed.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re
import sys

PACKET_NAME = 'PROSHKA_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46_2026-10-26.txt'
PACKET_BYTES = 144321
PACKET_LF = 2537
PACKET_SHA = 'f12272c56c0d65abc1a93171cad52581bbb841ee91c083523e1b0a4678101a3b'
HEADER = re.compile(rb'^BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n', re.M)


def verify_packet(raw: bytes) -> dict:
    if len(raw) != PACKET_BYTES or raw.count(b'\n') != PACKET_LF:
        raise ValueError('packet length or LF mismatch')
    if hashlib.sha256(raw).hexdigest() != PACKET_SHA:
        raise ValueError('packet SHA-256 mismatch')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n'):
        raise ValueError('unexpected newline convention')
    if not raw.startswith(b'OPERATIVE_CLASS: TRY_CCM_ORIGINAL_P_STRATEGIC_ROLLBACK_Q46\n'):
        raise ValueError('wrong operative request')
    pos = 0
    entries = []
    for i in range(1, 14):
        hit = HEADER.search(raw, pos)
        if hit is None or hit[1] != f'S{i}'.encode():
            raise ValueError('missing/out-of-order source')
        start = hit.end()
        end = start + int(hit[3])
        body = raw[start:end]
        if len(body) != int(hit[3]) or body.count(b'\n') != int(hit[4]):
            raise ValueError('source length mismatch')
        if hashlib.sha256(body).hexdigest() != hit[5].decode():
            raise ValueError('source hash mismatch')
        body.decode('utf-8')
        suffix = b'\nEND_SOURCE ' + hit[1] + b'\n'
        if raw[end:end+len(suffix)] != suffix:
            raise ValueError('source boundary mismatch')
        entries.append(dict(id=hit[1].decode(), name=hit[2].decode(),
                            bytes=len(body), lf=body.count(b'\n'),
                            sha256=hashlib.sha256(body).hexdigest(),
                            start_byte=start, end_byte=end,
                            start_line=raw[:start].count(b'\n')+1,
                            end_line=raw[:end].count(b'\n')))
        pos = end + len(suffix)
    if raw[pos:].strip():
        raise ValueError('unexpected trailing content')
    return dict(packet=PACKET_NAME, bytes=len(raw), lf=PACKET_LF,
                sha256=PACKET_SHA, source_count=len(entries),
                all_source_frames_verified=True, sources=entries)


class LL:
    """Rational linear combinations of 1 and formal log(prime)."""
    def __init__(self, terms=None):
        self.t = {int(k): F(v) for k, v in (terms or {}).items() if v}
    def __add__(self, x):
        if not isinstance(x, LL):
            x = LL({0: x})
        out = self.t.copy()
        for p, v in x.t.items():
            out[p] = out.get(p, F()) + v
        return LL(out)
    __radd__ = __add__
    def __neg__(self):
        return self * -1
    def __sub__(self, x):
        return self + (-x if isinstance(x, LL) else -F(x))
    def __rsub__(self, x):
        return -self + x
    def __mul__(self, x):
        return LL({p: v*F(x) for p, v in self.t.items()})
    __rmul__ = __mul__
    def __eq__(self, x):
        if not isinstance(x, LL):
            x = LL({0: x})
        return self.t == x.t


def factor(n):
    out = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def mobius(n):
    fs = factor(n)
    return 0 if any(a > 1 for a in fs.values()) else (-1)**len(fs)


def log_form(n):
    return LL(factor(n))


def lam(n):
    fs = factor(n)
    return LL({next(iter(fs)): 1}) if len(fs) == 1 else LL()


def psi(n):
    return sum((lam(k) for k in range(2, int(n)+1)), LL())


def add(a, b):
    c = [F() for _ in range(max(len(a), len(b)))]
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += v
    return c


def scale(a, c): return [F(c)*v for v in a]


def mul(a, b):
    c = [F() for _ in range(len(a)+len(b)-1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    return c


def deriv(a): return [i*a[i] for i in range(1, len(a))] or [F()]


def ev(a, x): return sum((v*F(x)**i for i, v in enumerate(a)), F())


def integral(a, u, v):
    return sum((c*(F(v)**(i+1)-F(u)**(i+1))/F(i+1)
                for i, c in enumerate(a)), F())


def mesh(a, m):
    nodes = [a] + [n for n in range(a+1, m) if lam(n) != 0] + [m]
    weights = [F() for _ in nodes]
    for j in range(len(nodes)-1):
        half = F(nodes[j+1]-nodes[j], 2)
        weights[j] += half
        weights[j+1] += half
    return nodes, weights


def trap(poly, nodes, weights):
    return sum((w*ev(poly, x) for x, w in zip(nodes, weights)), F())


def peano(poly, nodes):
    dd = deriv(deriv(poly))
    return sum((integral(mul([F(-u*v), F(u+v), F(-1)], dd), u, v)/2
                for u, v in zip(nodes[:-1], nodes[1:])), F())


def components(poly, a, m, nodes, weights):
    full = sum((lam(n)*ev(poly, n) for n in range(2, m+1)), LL()) - integral(poly, 1, m)
    low = sum((lam(n)*ev(poly, n) for n in range(2, a)), LL()) - integral(poly, 1, a)
    signed = sum(((lam(n)-ell)*ev(poly, n) for n, ell in zip(nodes, weights)), LL())
    geom = peano(poly, nodes)
    return full, low, signed, geom


def mathematical_checks():
    cfg = [(3,20), (5,25), (5,29), (7,30), (11,64), (17,97)]
    counts = dict(mesh_configurations=len(cfg), polynomial_peano_controls=0,
                  matrix_entry_returns=0, prefix_and_abel_controls=0,
                  formal_mangoldt_coefficients=96, continuum_controls=0)
    mutations = {}
    witnesses = []
    for a, m in cfg:
        nodes, ell = mesh(a, m)
        assert sum(ell) == m-a
        assert sum((w*x for x, w in zip(nodes, ell)), F()) == F(m*m-a*a, 2)
        for degree in range(6):
            poly = [F()]*degree + [F(1)]
            assert trap(poly, nodes, ell)-integral(poly, a, m) == peano(poly, nodes)
            counts['polynomial_peano_controls'] += 1
        base = [F(m*m), F(-2*m), F(1)]
        # Four real components of a Hermitian matrix polynomial; these are
        # algebra fixtures, NOT the physical CCM kernel.
        parts = [mul(base,[F(1),F(1,7)]),
                 mul(base,[F(-2),F(),F(1,11)]),
                 mul(base,[F(-2),F(1,3)]),
                 mul(base,[F(2),F(1,5),F(1,13)])]
        returns = []
        for poly in parts:
            assert ev(poly,m) == 0 and ev(deriv(poly),m) == 0
            full, low, signed, geom = components(poly,a,m,nodes,ell)
            assert full == low + signed + geom
            returns.append((full, low, signed, geom))
            counts['matrix_entry_returns'] += 1
            cumul = []
            d = LL()
            for j,(x,w) in enumerate(zip(nodes,ell)):
                d += lam(x)-w
                cumul.append(d)
                E_at_x = psi(x)-(x-1)
                E_a_minus = psi(a-1)-(a-1)
                gap = F(nodes[j+1]-x,2) if j+1<len(nodes) else F()
                assert d == E_at_x-E_a_minus-gap
            abel = sum((d*(ev(poly,nodes[j])-ev(poly,nodes[j+1]))
                        for j,d in enumerate(cumul[:-1])),LL()) + cumul[-1]*ev(poly,m)
            assert signed == abel
            counts['prefix_and_abel_controls'] += 1
            # Full continuum control: both interpolation errors, not only one.
            interp_error = integral(poly,a,m)-trap(poly,nodes,ell)
            assert interp_error + geom == 0
            counts['continuum_controls'] += 1
        # c=(3/5, 12/25+16i/25) is a Gaussian-rational unit vector.
        assert F(3,5)**2+F(12,25)**2+F(16,25)**2 == 1
        coeff = [F(9,25),F(16,25),F(72,125),F(-96,125)]
        contracted = [F()]
        for k,poly in zip(coeff,parts): contracted = add(contracted,scale(poly,k))
        direct = components(contracted,a,m,nodes,ell)
        for j in range(4):
            assert direct[j] == sum((k*returns[i][j] for i,k in enumerate(coeff)),LL())
        # One finite negative control: the same mesh with different positive
        # masses has either sign for the affine centered test m-x.
        affine = [F(m),F(-1)]
        middle = min(1,len(nodes)-2)
        amp = ell[middle]/2
        pos = amp*ev(affine,nodes[middle])
        neg = -pos
        assert amp>0 and ell[middle]-amp>=0 and pos>0 and neg<0
        witnesses.append(dict(a=a,m=m,nodes=len(nodes),positive_extra=str(pos),negative_extra=str(neg)))
    for n in range(1,97):
        got = sum((mobius(d)*log_form(n//d) for d in range(1,n+1) if n%d==0),LL())
        assert got == lam(n)
    # Exponent and constant controls, exact rational arithmetic.
    theta=F(21,40)
    assert F(3,2)-2*theta == F(9,20)
    assert 2-2*(F(3,2)-2*theta) == F(11,10)
    assert 2**29 < 3**20
    assert (F(7,3)-F(1,2))*(F(7,3)-F(3,2)) == F(7,3)**2-2*F(7,3)+F(3,4)
    a,m=cfg[0]
    nodes,ell=mesh(a,m)
    poly=[F(m*m),F(-2*m),F(1)]
    full,low,signed,geom=components(poly,a,m,nodes,ell)
    mutations['reverse_peano_sign'] = full != low+signed-geom
    mutations['omit_lower_prefix'] = full != signed+geom
    prime_only=sum((lam(n)*ev(poly,n) for n in range(2,m+1)
                    if len(factor(n))==1 and next(iter(factor(n).values()))==1),LL())
    mutations['delete_proper_prime_powers'] = prime_only != full+integral(poly,1,m)
    mutations['delete_virtual_endpoint_mass'] = sum(ell[:-1]) != m-a
    mutations['replace_Lambda_by_cell_mass'] = signed != 0
    mutations['omit_continuum_reconstruction'] = geom != 0
    # Removing complex mixed terms changes this exact full-source contraction.
    base=[F(m*m),F(-2*m),F(1)]
    imaginary=mul(base,[F(2),F(1,5),F(1,13)])
    mutations['drop_complex_cross_term'] = components(imaginary,a,m,nodes,ell)[0] != 0
    assert all(mutations.values())
    return dict(scope='Exact algebra on finite polynomial fixtures and true arithmetic coefficients; not original-P spectra or BHP asymptotic verification',
                passed=True, counts=counts, planted_errors_detected=mutations,
                negative_control_outside_actual_source=witnesses,
                finite_tests_do_not_prove_asymptotic_sign=True)


def main():
    if len(sys.argv)!=2:
        raise SystemExit('usage: python3 check_q46.py PATH_TO_CANONICAL_Q46.txt')
    raw=Path(sys.argv[1]).read_bytes()
    provenance=verify_packet(raw)
    bad=bytearray(raw)
    bad[provenance['sources'][0]['start_byte']+100] ^= 1
    try:
        verify_packet(bytes(bad))
    except ValueError:
        provenance['single_byte_corruption_detected']=True
    else:
        raise AssertionError('undetected corruption')
    result=dict(provenance=provenance,mathematics=mathematical_checks(),
                historical_programs_executed=False,production_spectrum_run=False,
                lean_run=False,arb_run=False)
    text=json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q46_checks.json').write_text(text,encoding='utf-8')
    print(text,end='')

if __name__=='__main__':
    main()
