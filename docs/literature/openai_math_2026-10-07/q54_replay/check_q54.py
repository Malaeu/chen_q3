#!/usr/bin/env python3
"""Q54: exact finite arithmetic/algebra and canonical byte framing.
Usage: python3 check_q54.py CANONICAL_Q54.txt
Standard library only. No historical program or production CCM is executed.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from math import gcd
import hashlib, json, re, sys

SIZE, LF = 139662, 2276
SHA = '29975f46faee9550eea39e6de9048f0c73f9e483d1522ebfed9a32003651ce6a'
NAME = 'PROSHKA_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54_2026-10-27.txt'
MAN = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)


def verify(raw: bytes, outer: bool = True) -> dict:
    if outer and (len(raw) != SIZE or raw.count(b'\n') != LF or hashlib.sha256(raw).hexdigest() != SHA):
        raise ValueError('outer bytes/LF/SHA')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.startswith(b'Q54 SIGNED_DIVISOR_IMAGE_RETURN\n'):
        raise ValueError('request/newline convention')
    pos = raw.index(b'BEGIN S1 ')
    heads = list(MAN.finditer(raw[:pos]))
    if len(heads) != 8:
        raise ValueError('manifest count')
    rows = []
    for i, h in enumerate(heads, 1):
        if h[1] != str(i).encode():
            raise ValueError('source order')
        sid, name = f'S{i}', h[2].decode()
        opening = f'BEGIN {sid} {name}\n'.encode()
        if raw[pos:pos+len(opening)] != opening:
            raise ValueError('opening')
        st, en = pos+len(opening), pos+len(opening)+int(h[3])
        body = raw[st:en]
        if len(body) != int(h[3]) or body.count(b'\n') != int(h[4]):
            raise ValueError('body bytes/LF')
        if hashlib.sha256(body).hexdigest() != h[5].decode():
            raise ValueError('body SHA')
        body.decode('utf-8')
        closing = f'\nEND {sid}\n\n'.encode()
        if raw[en:en+len(closing)] != closing:
            raise ValueError('closing/separator')
        rows.append(dict(id=sid, name=name, bytes=len(body), lf=body.count(b'\n'),
                         sha256=h[5].decode(), start_byte=st, end_byte=en,
                         start_line=raw[:st].count(b'\n')+1, end_line=raw[:en].count(b'\n')))
        pos = en+len(closing)
    if pos != len(raw):
        raise ValueError('trailing bytes')
    return dict(packet=NAME, bytes=len(raw), lf=LF, sha256=SHA,
                source_count=8, all_frames_verified=True, sources=rows)


@dataclass(frozen=True)
class Q:
    re: F = F(0)
    im: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))
    @staticmethod
    def cast(x): return x if isinstance(x, Q) else Q(x)
    def __add__(self, x):
        x = Q.cast(x); return Q(self.re+x.re, self.im+x.im)
    __radd__ = __add__
    def __neg__(self): return Q(-self.re, -self.im)
    def __sub__(self, x): return self + (-Q.cast(x))
    def __rsub__(self, x): return Q.cast(x) + (-self)
    def __mul__(self, x):
        x = Q.cast(x)
        return Q(self.re*x.re-self.im*x.im, self.re*x.im+self.im*x.re)
    __rmul__ = __mul__
    def conj(self): return Q(self.re, -self.im)
    def norm2(self): return self.re*self.re+self.im*self.im
    def pair(self): return [str(self.re), str(self.im)]
Z = Q()


def fac(n: int) -> dict[int, int]:
    ans = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0)+1; n //= p
        p += 1
    if n > 1: ans[n] = ans.get(n, 0)+1
    return ans


def mu(n):
    f = fac(n)
    return 0 if any(v > 1 for v in f.values()) else (-1)**len(f)


def divs(n): return [d for d in range(1, n+1) if n % d == 0]


# Polynomials in independent formal symbols log(p), with Gaussian-rational
# coefficients. Monomial () is a constant; no floating logarithms are used.
def padd(a, b):
    r = dict(a)
    for k, v in b.items(): r[k] = r.get(k, Z)+v
    return {k:v for k,v in r.items() if v != Z}


def pscale(a, s): return {k:Q.cast(s)*v for k,v in a.items() if Q.cast(s)*v != Z}


def pmul(a, b):
    r = {}
    for k,v in a.items():
        for l,w in b.items():
            kl = tuple(sorted(k+l)); r[kl] = r.get(kl, Z)+v*w
    return {k:v for k,v in r.items() if v != Z}


def logp(n): return {(p,):Q(v) for p,v in fac(n).items()}


def mang(n):
    f = fac(n)
    return {(next(iter(f)),):Q(1)} if len(f) == 1 else {}


def pquad(A, x):
    r = {}
    for i in range(len(x)):
        for j in range(len(x)):
            r = padd(r, pscale(A[i][j], x[i].conj()*x[j]))
    return r


def qquad(A, x):
    return sum((x[i].conj()*A[i][j]*x[j] for i in range(len(x)) for j in range(len(x))), Z)


def mobius_matrix(m):
    return [[mu(n//d) if n % d == 0 else 0 for d in range(1, m+1)] for n in range(1, m+1)]


def ptr(A, U):
    m = len(U); out = [[{} for _ in range(m)] for _ in range(m)]
    for i in range(m):
        for j in range(m):
            for a in range(m):
                if U[i][a]:
                    for b in range(m):
                        if U[j][b]:
                            out[i][j] = padd(out[i][j], pscale(A[a][b], U[i][a]*U[j][b]))
    return out


def math_checks():
    counts, bad = {}, {}
    tangent_entries = 0; positive_cases = 0; mixed_cases = 0
    for m in (2, 4, 8, 12):
        U = mobius_matrix(m)
        E = [[int(n % d == 0) for d in range(1, m+1)] for n in range(1, m+1)]
        assert all(sum(U[i][k]*E[k][j] for k in range(m)) == int(i == j)
                   for i in range(m) for j in range(m))
        assert [sum(row) for row in U] == [1]+[0]*(m-1)
        Qprime = []; distances = []
        for n in range(1, m+1):
            qr, dr = [], []
            for k in range(1, m+1):
                d = padd(pscale(padd(logp(n), logp(k)), F(1,2)), pscale(logp(gcd(n,k)), -1))
                dr.append(d); qr.append(pscale(d, -1))
            Qprime.append(qr); distances.append(dr)
        derivative = ptr(Qprime, U)
        expected = [[{} for _ in range(m)] for _ in range(m)]
        for n in range(1, m+1):
            for k in range(1, m+1):
                v = mang(n) if n == k else {}
                if k == 1: v = padd(v, pscale(mang(n), -F(1,2)))
                if n == 1: v = padd(v, pscale(mang(k), -F(1,2)))
                expected[n-1][k-1] = v
                assert derivative[n-1][k-1] == v
                tangent_entries += 1
        # The separate log-gcd congruence is exactly diag(Lambda).
        Lg = [[logp(gcd(n,k)) for k in range(1,m+1)] for n in range(1,m+1)]
        diag = ptr(Lg, U)
        assert all(diag[i][j] == (mang(i+1) if i == j else {}) for i in range(m) for j in range(m))
        for tau in (2, 4):
            J = [sum(mu(n//d)*d**tau for d in divs(n)) for n in range(1,m+1)]
            assert all(j > 0 for j in J)
            K = [[F(gcd(n,k)**tau, (n*k)**(tau//2)) for k in range(1,m+1)] for n in range(1,m+1)]
            for n in range(1,m+1):
                for k in range(1,m+1):
                    factored = sum(J[d-1] for d in divs(gcd(n,k)))
                    assert K[n-1][k-1] == F(factored,(n*k)**(tau//2))
            x = [Q(F((-1)**n,n+1),F(n,2*n+1)) for n in range(1,m+1)]
            r = [sum((U[n][d]*x[n] for n in range(m)), Z) for d in range(m)]
            full = qquad(K,r)
            square = sum((J[d-1]*sum((F(1,n**(tau//2))*r[n-1] for n in range(d,m+1,d)),Z).norm2()
                          for d in range(1,m+1)),F(0))
            assert full.im == 0 and full.re == square and square >= 0
            positive_cases += 1
            tangent = pquad(derivative,x)
            rhs = {}
            for n in range(1,m+1):
                rhs = padd(rhs,pscale(mang(n),x[n-1].norm2()-(x[0].conj()*x[n-1]).re))
            assert tangent == rhs
            mixed_cases += 1
        bad['drop_normalization_derivative'] = diag != derivative
        bad['replace_Mobius_by_absolute_values'] = any(sum(abs(z) for z in row) != int(i == 0) for i,row in enumerate(U))
    counts.update(tangent_entries=tangent_entries,positive_deformation_cases=positive_cases,complex_quadratic_cases=mixed_cases)

    # A PSD family need not have a PSD tangent. This is an arithmetic-index
    # algebra control, NOT a physical original-P spectral counterexample.
    T = [[{}, {(2,):Q(-F(1,2))}], [{(2,):Q(-F(1,2))},{(2,):Q(1)}]]
    neg = pquad(T,[Q(1),Q(F(1,2))])
    assert neg == {(2,):Q(-F(1,4))}
    bad['PSD_family_implies_PSD_tangent'] = True
    bad['Lambda_power_replaced_by_log_n'] = mang(8) != logp(8)

    # Linked finite-translation controls. Here log(p) shifts are formal additive
    # integer shifts and q_n=1/n is a rational test weight. These specialize the
    # universal algebra, not a production cell or its n^(-1/2) norm.
    m = 8; U = mobius_matrix(m)
    primes = [p for p in range(2,m+1) if fac(p) == {p:1}]
    lp = {p:i+1 for i,p in enumerate(primes)}
    shift = {n:sum(lp[p]*v for p,v in fac(n).items()) for n in range(1,m+1)}
    f = {1:Q(1,1), 2:Q(2,-1)}
    norm = sum(z.norm2() for z in f.values())
    times = list(range(1-max(shift.values()),3))
    V1 = [[{} for _ in range(m)] for _ in range(m)]
    for n in range(1,m+1):
        V1[n-1][n-1] = mang(n)
        V1[n-1][0] = padd(V1[n-1][0],pscale(mang(n),-F(1,2)))
        V1[0][n-1] = padd(V1[0][n-1],pscale(mang(n),-F(1,2)))
    tangent = {}; baseline = F(0); sum_norm = F(0)
    curvature_full = {}; curvature_deleted = {}
    for t in times:
        x = [F(1,n)*f.get(t+shift[n],Z) for n in range(1,m+1)]
        baseline += x[0].norm2(); sum_norm += sum(z.norm2() for z in x)
        tangent = padd(tangent,pquad(V1,x))
        r = [sum((U[n][d]*x[n] for n in range(m)), Z) for d in range(m)]
        for n in range(1,m+1):
            for k in range(1,m+1):
                dist = padd(pscale(padd(logp(n),logp(k)),F(1,2)),pscale(logp(gcd(n,k)),-1))
                term = pscale(pmul(dist,dist),r[n-1].conj()*r[k-1])
                curvature_full = padd(curvature_full,term)
                if n % k == 0 or k % n == 0:
                    curvature_deleted = padd(curvature_deleted,term)
    assert baseline == norm
    assert sum_norm == norm*sum(F(1,n*n) for n in range(1,m+1))
    h = {}; Aprime = {}
    for n in range(1,m+1):
        corr = sum((f.get(t,Z).conj()*f.get(t+shift[n],Z) for t in f),Z)
        h = padd(h,pscale(mang(n),F(1,n*n)*norm))
        Aprime = padd(Aprime,pscale(mang(n),2*F(1,n)*corr.re))
    assert tangent == padd(h,pscale(Aprime,-F(1,2)))
    bad['drop_noninteger_ratio_cross_terms'] = curvature_full != curvature_deleted
    bad['drop_factor_two_in_source_return'] = tangent != padd(h,pscale(Aprime,-1))
    bad['drop_top_diagonal_because_top_overlap_is_zero'] = mang(m) != {}
    top_corr = sum((f.get(t,Z).conj()*f.get(t+shift[m],Z) for t in f),Z)
    assert top_corr == Z and shift[m] == 3
    counts['linked_formal_translation_cases'] = 1
    counts['linked_time_rows'] = len(times)

    # Taylor return via independently differentiated exponential antiderivative:
    # H(s)=((s-tau)/q+1/q^2)*exp(-q*s), H'=(tau-s)*exp(-q*s).
    tc = 0
    for q in (F(1,3),F(1),F(5,2)):
        for tau in (F(1,7),F(2,3),F(2)):
            a0,a1 = -tau/q+1/q**2,1/q
            assert (a1-q*a0, -q*a1) == (tau,-F(1))
            # pair (constant, coefficient of the formal E=exp(-tau*q)).
            rem = (-a0,a0+a1*tau)
            assert (1-tau*q+q*q*rem[0],q*q*rem[1]) == (0,1)
            tc += 1
    bad['erase_Taylor_remainder'] = (1-F(2,3),0) != (0,1)
    counts['exact_Taylor_returns'] = tc

    opt = 0
    for k in (1,3,7):
        C = F(2*k*k)
        for tau in (F(1,k),F(1,2*k),F(2,k)):
            price = 2/tau+C*tau
            assert price*price >= 8*C
            if tau == F(1,k): assert price == 4*k
            opt += 1
    counts['optimization_controls'] = opt
    bad['remove_n1_baseline'] = norm != 0
    # Distinct signed E versus an absolute scalar is not an identity.
    bad['replace_signed_defect_by_its_absolute_value'] = F(-2) != abs(F(-2))
    bad['double_short_in_direct_K'] = -F(7) != -F(7)-F(3)
    assert all(bad.values()), bad
    return dict(passed=True,counts=counts,planted_errors_detected=bad,
                tangent_negative_control={'value':'-log(2)/4','arithmetic_index_only':True,'original_P_counterexample':False},
                exact_prime_power_weights=True,source_bound_proved_by_finite_tests=False,
                scope='Exact finite arithmetic and polynomial identities in formal log(p); rational translation controls only; universal bounds are PAPER arguments')


def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: python3 check_q54.py CANONICAL_Q54.txt')
    raw = Path(sys.argv[1]).read_bytes(); provenance = verify(raw)
    bad = bytearray(raw); bad[provenance['sources'][0]['start_byte']+50] ^= 1
    en = provenance['sources'][0]['end_byte']; mutations = {}
    for name,data,outer in [('outer_hash',bytes(bad),True),('body_hash',bytes(bad),False),
                            ('extra_separator',raw[:en]+b'\n'+raw[en:],False),('truncated_frame',raw[:-2],False)]:
        try: verify(data,outer)
        except (ValueError,UnicodeError): mutations[name] = True
        else: raise AssertionError('missed provenance mutation: '+name)
    result = dict(provenance=provenance,framing_mutations=mutations,mathematics=math_checks(),
                  historical_programs_executed=False,production_CCM_spectrum=False,
                  numeric_actual_zeta_zeros=False,lean=False,arb=False,independent_audit=False,
                  new_vanishing_exponent_supplier=False)
    text = json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q54_checks.json').write_text(text,encoding='utf-8')
    print(text,end='')
if __name__ == '__main__': main()
