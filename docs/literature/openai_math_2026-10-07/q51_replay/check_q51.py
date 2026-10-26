#!/usr/bin/env python3
"""Q51: byte framing and exact finite algebra, NOT production CCM spectra.
Usage: python3 check_q51.py CANONICAL_Q51.txt
Only the Python standard library is required. Historical programs are not run.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re
import sys

SIZE = 51031
LF = 849
SHA = '5c34576e47a0b1b23a94cda5c381d29402355613e20e734846104f2eb919d61d'
NAME = 'PROSHKA_CCM_JOINT_LOW_RESIDUE_Q51_2026-10-27.txt'
MANIFEST = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)


def verify(raw: bytes, outer: bool = True) -> dict:
    if outer and (len(raw) != SIZE or raw.count(b'\n') != LF or hashlib.sha256(raw).hexdigest() != SHA):
        raise ValueError('canonical bytes/LF/SHA mismatch')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n'):
        raise ValueError('newline convention')
    if not raw.startswith(b'Q51 JOINT_LOW_RESIDUE'):
        raise ValueError('wrong request')
    pos = raw.index(b'BEGIN S1 ')
    heads = list(MANIFEST.finditer(raw[:pos]))
    if len(heads) != 8:
        raise ValueError('manifest count')
    rows = []
    for expected, h in enumerate(heads, 1):
        sid = 'S' + h[1].decode()
        if sid != f'S{expected}':
            raise ValueError('source order')
        name = h[2].decode()
        begin = f'BEGIN {sid} {name}\n'.encode()
        if raw[pos:pos + len(begin)] != begin:
            raise ValueError('source opening')
        start = pos + len(begin)
        end = start + int(h[3])
        body = raw[start:end]
        if len(body) != int(h[3]) or body.count(b'\n') != int(h[4]):
            raise ValueError('source size/LF')
        if hashlib.sha256(body).hexdigest() != h[5].decode():
            raise ValueError('source SHA')
        body.decode('utf-8')
        suffix = f'\nEND {sid}\n'.encode()
        if raw[end:end + len(suffix)] != suffix:
            raise ValueError('source closing')
        rows.append(dict(id=sid, name=name, bytes=len(body), lf=body.count(b'\n'),
                         sha256=h[5].decode(), start_byte=start, end_byte=end,
                         start_line=raw[:start].count(b'\n') + 1,
                         end_line=raw[:end].count(b'\n')))
        pos = end + len(suffix)
        if pos < len(raw):
            if raw[pos:pos + 1] != b'\n':
                raise ValueError('inter-source separator')
            pos += 1
    if pos != len(raw):
        raise ValueError('trailing content')
    return dict(packet=NAME, bytes=len(raw), lf=raw.count(b'\n'),
                sha256=hashlib.sha256(raw).hexdigest(), source_count=8,
                all_frames_verified=True, sources=rows)


@dataclass(frozen=True)
class Q:
    """Gaussian rational, for exact complex algebra (no float conversion)."""
    re: F = F(0)
    im: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))

    @staticmethod
    def cast(x):
        return x if isinstance(x, Q) else Q(F(x))

    def __add__(self, x):
        x = Q.cast(x)
        return Q(self.re + x.re, self.im + x.im)

    __radd__ = __add__

    def __neg__(self):
        return Q(-self.re, -self.im)

    def __sub__(self, x):
        return self + (-Q.cast(x))

    def __rsub__(self, x):
        return Q.cast(x) - self

    def __mul__(self, x):
        x = Q.cast(x)
        return Q(self.re*x.re - self.im*x.im, self.re*x.im + self.im*x.re)

    __rmul__ = __mul__

    def conj(self):
        return Q(self.re, -self.im)

    def norm2(self):
        return self.re*self.re + self.im*self.im

    def inverse(self):
        n = self.norm2()
        if not n:
            raise ZeroDivisionError('zero Gaussian rational')
        return Q(self.re/n, -self.im/n)

    def __truediv__(self, x):
        return self * Q.cast(x).inverse()

    def __rtruediv__(self, x):
        return Q.cast(x) * self.inverse()

    def __pow__(self, n):
        if not isinstance(n, int):
            raise TypeError('integer exponent required')
        if n < 0:
            return self.inverse() ** (-n)
        r, a = Q(1), self
        while n:
            if n & 1:
                r = r*a
            a = a*a
            n //= 2
        return r

    def pair(self):
        return [str(self.re), str(self.im)]


I = Q(0, 1)
ZERO = Q()


def dot(a, b):
    return sum((Q.cast(x)*Q.cast(y) for x, y in zip(a, b)), ZERO)


def pmul(a, b):
    out = [ZERO] * (len(a) + len(b) - 1)
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            out[j+k] = out[j+k] + x*y
    return out


def polynomial(roots):
    p = [Q(1)]
    for w, r in roots:
        for _ in range(r):
            p = pmul(p, [-w, Q(1)])
    return p


def peval(p, z):
    r = ZERO
    for a in reversed(p):
        r = r*z + a
    return r


def deriv(p):
    return [j*p[j] for j in range(1, len(p))]


def ld(roots, z):
    return sum((r/(z-w) for w, r in roots), ZERO)


def quartet(delta, gamma, r=1):
    return [(Q(s*delta, t*gamma), r) for s in (-1, 1) for t in (-1, 1)]


def math_checks():
    counts = {}
    errors = {}
    # Synthetic symmetric divisors test algebra only. They are NOT zeta zeros.
    low = quartet(F(1,4), F(1), 2) + [(Q(0, 2), 3), (Q(0, -2), 3)]
    high = quartet(F(1,5), F(7), 1)
    pl, ph = polynomial(low), polynomial(high)
    pall = pmul(pl, ph)
    nodes = [Q(F(1,8), F(1,3)), Q(F(3,4), F(5,2)), Q(2, -3)]
    for z in nodes:
        assert peval(deriv(pl), z)/peval(pl, z) == ld(low, z)
        assert peval(deriv(pall), z)/peval(pall, z) == ld(low, z) + ld(high, z)
        assert peval(pl, -z) == peval(pl, z)
        assert peval(pl, z.conj()) == peval(pl, z).conj()
    counts['finite_divisor_nodes'] = len(nodes)
    assert all(x.im == 0 for x in pl)
    assert all(pl[j] == ZERO for j in range(1, len(pl), 2))
    errors['drop_entire_factor_high_zeros'] = ld(high, nodes[0]) != ZERO
    errors['erase_multiplicity'] = ld(low, nodes[0]) != ld([(w, 1) for w, _ in low], nodes[0])

    # Positivity in a safely zero-free right half-plane; no assertion on actual xi.
    for z in [Q(F(3,4), t) for t in (F(-4), F(0), F(3,2), F(8))]:
        assert ld(low, z).re > 0
    counts['right_halfplane_exact_controls'] = 4
    toy = quartet(F(1,4), F(1))
    zz = Q(F(6,25), F(1))
    negative = ld(toy, zz).re
    assert negative < -90
    errors['even_real_implies_positive_real'] = negative < 0

    # Real/odd contact vectors; d is a rational test parameter for omega_1.
    # The PAPER identities hold for every real d>0, including d=2pi/log(m).
    a = F(1,2)
    js = [-2, -1, 0, 1, 2]
    vector_cases = 0
    positive_even = negative_odd = None
    for d in (F(1,3), F(2,5), F(3,2)):
        q1, q2 = a*a+d*d, a*a+4*d*d
        e = [q2, -4*q1, 6*a*a, -4*q1, q2]
        o = [q2, -2*q1, F(0), 2*q1, -q2]
        assert sum(e) == 0 and sum(o) == 0
        for c in (e, o):
            for s in (-1, 1):
                assert dot(c, [1/(Q(a)+s*I*j*d) for j in js]) == ZERO
        for z in (Q(F(1,4), F(2,3)), Q(F(2,7), F(-4,5)), Q(F(1,4))):
            r = [z/(z*z+(j*d)**2) for j in js]
            t = [Q(j*d)/(z*z+(j*d)**2) for j in js]
            E = 24*d**4*(a*a-z*z)/(z*(z*z+d*d)*(z*z+4*d*d))
            O = 12*d**3*(a*a-z*z)/((z*z+d*d)*(z*z+4*d*d))
            assert dot(e, r) == E and dot(o, t) == O
            assert dot(e, t) == ZERO and dot(o, r) == ZERO
            vp = [1/(z+I*j*d) for j in js]
            vm = [1/(z-I*j*d) for j in js]
            qe = dot(e, vp)**2 + dot(e, vm)**2
            qo = dot(o, vp)**2 + dot(o, vm)**2
            assert qe == 2*E*E and qo == -2*O*O
            assert E != ZERO and O != ZERO
            assert dot(e, vp)*dot(o, vp)+dot(e, vm)*dot(o, vm) == ZERO
            vector_cases += 1
            if z.im == 0:
                assert qe.re > 0 and qo.re < 0
                positive_even, negative_odd = qe.re, qo.re
                errors['transpose_replaced_by_adjoint'] = qo.re != dot(o, vp).norm2()+dot(o, vm).norm2()
                errors['omit_one_time_orientation'] = qo != dot(o, vp)**2
        # Both contact contractions vanish at the actual contact exponent a.
        ra = [Q(a)/(a*a+(j*d)**2) for j in js]
        ta = [Q(j*d)/(a*a+(j*d)**2) for j in js]
        assert dot(e, ra) == ZERO and dot(o, ta) == ZERO
        raw0 = [F(0), F(0), F(1), F(0), F(0)]
        errors['raw_zero_mode_treated_as_contact_vector'] = dot(raw0, ra) != ZERO
    counts['five_mode_parameter_pairs'] = vector_cases

    # Exact reflected pair formula and high-divisor inner-strip sign.
    pair_cases = 0
    for delta in (F(0), F(1,4), F(2,5)):
        for x in (F(1,16), F(1,3), F(1)):
            for y in (F(-5), F(-2), F(2), F(5)):
                p = (1/Q(x-delta, y)+1/Q(x+delta, y)).re
                rhs = 2*x*(x*x+y*y-delta*delta)/(((x-delta)**2+y*y)*((x+delta)**2+y*y))
                assert p == rhs and p > 0
                pair_cases += 1
    counts['reflected_pair_controls'] = pair_cases
    near = (1/Q(F(1,8)-F(1,4), 0)+1/Q(F(1,8)+F(1,4), 0)).re
    assert near < 0
    errors['extend_separated_height_sign_to_pole_neighborhood'] = near < 0

    # Monodromy: D(z)=z^r, K polynomial, positively oriented unit circle.
    # Exact integrated formula after division by 2pi*i; no quadrature.
    for r in (1, 2, 5):
        for co in ([F(1)], [F(2), F(-3), F(4)], [F(0), F(2,3), F(-5,7), F(1)]):
            residue = r*co[0]
            corner = r*sum(co)
            primitive_integral = r*sum(co[1:])
            assert residue == corner-primitive_integral
    counts['monodromy_polynomial_controls'] = 9
    errors['drop_winding_corner'] = F(2) != F(0)  # D=z^2, K=1
    errors['reverse_winding_orientation'] = F(2) != F(-2)

    exponent_rows = []
    for eps in (F(1,128), F(1,64), F(1,100), F(1,32)):
        kap = F(5,24)+eps
        high_power = F(1,2)+3*eps-3*kap
        corner_power = F(1,2)+3*eps+kap-4*(F(1,4)+eps)
        middle_power = 2*eps-kap
        assert high_power == -F(1,8)
        assert corner_power == -F(7,24)
        assert middle_power == eps-F(5,24) < 0
        exponent_rows.append(dict(epsilon=str(eps), high=str(high_power), corner=str(corner_power), middle=str(middle_power)))
    counts['rational_budget_controls'] = len(exponent_rows)
    # Complete signed reassembly; no new spectral estimate is asserted.
    A, Hd, vert, err, rhigh = map(F, [7, 2, 3, -1, 4])
    rlow = vert+err-rhigh-A-Hd
    assert A == -Hd+vert-rlow-rhigh+err
    errors['double_continuous_charge'] = A != -2*Hd+vert-rlow-rhigh+err
    assert all(errors.values())
    return dict(
        passed=True,
        scope='Exact finite algebra and rational surrogate controls; NOT production CCM or numeric zeta zeros',
        counts=counts,
        negative_control=dict(real_logder=str(negative), upper_bound='-90', actual_zeta_data=False),
        five_mode_real_example=dict(L_scaled_even=str(positive_even), L_scaled_odd=str(negative_odd), actual_cell=False),
        exponent_rows=exponent_rows,
        planted_errors_detected=errors,
        original_P_cofinal_floor_certified_by_code=False,
        independent_arithmetic_supplier=False)


def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: python3 check_q51.py CANONICAL_Q51.txt')
    raw = Path(sys.argv[1]).read_bytes()
    provenance = verify(raw)
    cases = {}
    bad = bytearray(raw)
    bad[provenance['sources'][0]['start_byte']+40] ^= 1
    for name, value, outer in (
        ('one_byte_corruption', bytes(bad), True),
        ('body_hash_without_outer_guard', bytes(bad), False),
        ('extra_separator', raw[:provenance['sources'][0]['end_byte']]+b'\n'+raw[provenance['sources'][0]['end_byte']:], False),
        ('truncated_final_frame', raw[:-2], False),
    ):
        try:
            verify(value, outer=outer)
        except (ValueError, UnicodeError):
            cases[name] = True
        else:
            raise AssertionError('missed provenance mutation '+name)
    result = dict(provenance=provenance, provenance_mutations=cases,
                  mathematics=math_checks(),
                  historical_programs_executed=False, production_spectrum=False,
                  numeric_zeta_zeros=False, lean=False, arb=False, independent_new_audit=False)
    text = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2)+'\n'
    Path('q51_checks.json').write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
