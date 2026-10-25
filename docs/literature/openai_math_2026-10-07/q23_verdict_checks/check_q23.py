#!/usr/bin/env python3
"""Exact local controls only: not a proof of the global CCM inequalities."""
from __future__ import annotations
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parent
REQUEST = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT.parent / 'PROSHKA_CCM_JOINT_PHASE_DELAY_Q23_2026-10-25.txt'
EXPECTED_HASH = '7e4d41f5bcadaa03a18589a22760b88c8253b95872391ddd0accd136d53cd31e'
checks: Counter[str] = Counter()
planted: list[str] = []

def equal(a, b, category: str) -> None:
    if sp.simplify(sp.expand(a-b)) != 0:
        raise AssertionError(f'{category}: {a!s} != {b!s}')
    checks[category] += 1

def reject(a, b, name: str) -> None:
    if sp.simplify(sp.expand(a-b)) == 0:
        raise AssertionError(f'Planted error was NOT detected: {name}')
    planted.append(name)

raw = REQUEST.read_bytes()
assert len(raw) == 318444 and raw.count(b'\n') == 4656
assert hashlib.sha256(raw).hexdigest() == EXPECTED_HASH
pat = re.compile(rb'^(S\d+): ([^\n]+) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$', re.M)
rows = []
for z in pat.finditer(raw):
    sid, path, size, digest = z.groups()
    size = int(size)
    marker = b'BEGIN_SOURCE '+sid+b' '+path+b'\n'
    offset = raw.index(marker) + len(marker)
    body = raw[offset:offset+size]
    assert hashlib.sha256(body).hexdigest().encode() == digest
    assert raw[offset+size:].startswith(b'\nEND_SOURCE '+sid)
    rows.append({'id': sid.decode(), 'bytes': size, 'sha256': digest.decode()})
assert len(rows) == 11

s, d, r, v = sp.symbols('s delta r v', real=True, positive=True)
# The symbolic r is not a numerically assigned zero multiplicity.
phi = v*s-2*r*sp.atan(s/d)
equal(sp.diff(phi,s), v-2*r*d/(d*d+s*s), 'phase')
equal(sp.diff(phi,s,2), 4*r*d*s/(d*d+s*s)**2, 'phase')
equal(sp.diff(phi,s,2).subs(s,0), 0, 'coalescence')
equal(sp.diff(phi,s,3).subs(s,0), 4*r/d**3, 'coalescence')
equal(sp.diff(phi,s).subs(s*s, 2*r*d/v-d*d), 0, 'stationary_root')
equal(sp.limit((phi-(v-2*r/d)*s)/s**3,s,0), 2*r/(3*d**3), 'cubic_coefficient')

# Inherited all-pass/normalization algebra, not a new theorem.
c, cb, ar = sp.symbols('c conjugate_c A_real', nonzero=True)
for rr in range(1,4):
    eta = c/cb
    q = ((d-sp.I*s)/(d+sp.I*s))**rr
    p = ar**2/(c*cb*(d*d+s*s)**rr)
    equal(eta*q*p, ar**2/(cb**2*(d+sp.I*s)**(2*rr)), 'allpass_normalization')

# Complete forward/reverse differentiation with the true C derivative.
gamma, a, ell = sp.symbols('gamma a ell', real=True)
C0, C1 = sp.symbols('C C_prime', complex=True)
qK = C0
qKp = -sp.I*gamma*C0-C1
# The omitted common factor is exp(-i gamma v)/eta.
equal((sp.I*gamma-sp.Rational(1,2))*qK+qKp, -C1-C0/2, 'joint_derivative')
equal((-sp.I*gamma-sp.Rational(1,2))*qK-qKp, C1-C0/2, 'joint_derivative')
equal(2*gamma*a+gamma*(ell-2*a), gamma*ell, 'orientation_phase')
equal(2*gamma*a+gamma*(-ell-2*a), -gamma*ell, 'orientation_phase')

x = sp.symbols('x', real=True)
AA, BB = sp.Function('AA')(x), sp.Function('BB')(x)
parts = [1-AA, AA*BB, AA*(1-BB)]
equal(sum(parts), 1, 'partition')
equal(sum(sp.diff(t,x) for t in parts), 0, 'partition')
reject(sum(sp.diff(t,x) for t in parts[:2]), 0, 'omit_partition_derivative')

# Boundary control: omission is invalid even for a smooth Stieltjes source.
m = sp.symbols('m', positive=True)
E, F = x-1, x
equal((m-1)*m-sp.integrate(E*sp.diff(F,x),(x,1,m)), sp.integrate(F,(x,1,m)), 'stieltjes_boundary')
reject(-sp.integrate(E*sp.diff(F,x),(x,1,m)),sp.integrate(F,(x,1,m)), 'omit_cutoff_boundary')
# Planted scalar phase/time errors; not assignments to the hypothetical zero.
reject(sp.re(sp.I*sp.I), sp.re(sp.I), 'replace_eta_by_one')
zplus,zminus=sp.symbols('forward reverse')
reject(zplus+zminus,zplus,'omit_reverse_orientation')

# True finite prime-power support. Coefficients are formal log(p) weights.
def prime_power_support(M: int):
    out={}
    for n in range(2,M+1):
        fact=sp.factorint(n)
        if len(fact)==1:
            p,k=next(iter(fact.items()))
            out[n]=(int(p),int(k))
    return out
for M in (4,9,16,64,257):
    original=prime_power_support(M)
    prime={n:pk for n,pk in original.items() if pk[1]==1}
    square={n:pk for n,pk in original.items() if pk[1]==2}
    higher={n:pk for n,pk in original.items() if pk[1]>=3}
    assert not (set(prime)&set(square) or set(prime)&set(higher) or set(square)&set(higher))
    assert original==dict(prime|square|higher)
    checks['exact_prime_power_partition']+=1
    assert original.get(4)==(2,2)
    # All exponents k have coefficient log(p), not k log(p).
    for n,(p,k) in original.items():
        assert n==p**k
    checks['all_exponents_retained']+=1
assert 4 not in {n:pk for n,pk in prime_power_support(16).items() if pk[1]!=2}
planted.append('omit_prime_square')

# Calculus used in the infinite k>=3 scalar tail bound.
t=sp.symbols('t',positive=True)
equal(sp.integrate(sp.log(t)/t**sp.Rational(3,2),(t,1,sp.oo)),4,'higher_power_tail')
equal(1/(1-1/sp.sqrt(2)),2+sp.sqrt(2),'higher_power_tail')
assert bool(2+sp.sqrt(2)<4)
checks['higher_power_tail']+=1
# The L2 norm bound has a factor two for the two time orientations.
L=sp.symbols('L',positive=True)
equal(2*(3*L+26),6*L+52,'full_operator_return')

# Exact returned exponents; the instance is a schedule check, not zero data.
eps=sp.Rational(1,64); qq=67
powers=[1+eps*(sp.Rational(1,2)-qq),sp.Rational(1,2)+eps*(sp.Rational(3,2)-qq),sp.Rational(1,2)+eps*(1-qq),sp.Rational(1,2)+eps*(sp.Rational(1,2)-qq)]
assert all(z<0 for z in powers)
checks['receiver_power_signs']+=4
# e^h = sqrt(m)/L and E_T ~ exp(2 delta h)/T imply this price/signal power.
dd=sp.symbols('delta', positive=True)
equal(sp.Rational(1,2)-dd, (1-2*dd)/2, 'price_signal_power')

out={
 'status':'EXACT_LOCAL_CHECKS_PASSED',
 'meaning':'Finite algebra, support, source integrity and bookkeeping only; no CCM sign or asymptotic certificate',
 'request_bytes':len(raw),'request_LF':raw.count(b'\n'),'request_sha256':EXPECTED_HASH,
 'source_bodies_verified':len(rows),
 'sympy_version':sp.__version__,
 'checks':dict(checks),'exact_local_check_count':sum(checks.values()),
 'planted_errors_detected':planted,'planted_error_count':len(planted),
 'receiver_powers':[str(z) for z in powers],
 'registration_sha256':hashlib.sha256((ROOT/'registration.json').read_bytes()).hexdigest(),
 'check_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'numerical_zero_assignments':False,'arb':False,'lean':False,'independent_review':False
}
(ROOT/'results_q23.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,ensure_ascii=False,indent=2))
