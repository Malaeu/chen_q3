"""Exact Q03 controls. No CCM spectral computation and no zero-location certificate."""
from fractions import Fraction as F
from collections import Counter
from pathlib import Path
import hashlib, json


def mu(n: int) -> int:
    out, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            out = -out
            if n % p == 0:
                return 0
        p += 1
    return -out if n > 1 else out


def flog(n: int) -> dict[int, int]:
    c: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            c[p] = c.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        c[n] = c.get(n, 0) + 1
    return c


def coeff(n: int, lo: int, hi: int) -> dict[int, int]:
    out: dict[int, int] = {}
    for d in range(lo, min(hi, n)+1):
        if n % d == 0:
            for p, a in flog(n//d).items():
                out[p] = out.get(p, 0) + mu(d)*a
    return {p:a for p,a in out.items() if a}


def plus(a, b):
    z = dict(a)
    for p, t in b.items():
        z[p] = z.get(p, 0) + t
    return {p:t for p,t in z.items() if t}

# Exact Gaussian rationals (real,imaginary).
def z(x=0,y=0): return (F(x),F(y))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def neg(a): return (-a[0],-a[1])
def sub(a,b): return add(a,neg(b))
def conj(a): return (a[0],-a[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def norm2(a): return a[0]**2+a[1]**2
def div(a,b):
    q=norm2(b)
    if not q: raise ZeroDivisionError
    c=mul(a,conj(b))
    return (c[0]/q,c[1]/q)

stats = Counter()
for n in range(1,193):
    fs=flog(n)
    target={next(iter(fs)):1} if len(fs)==1 else {}
    assert coeff(n,1,n)==target
    stats['full_mu_log_to_mangoldt']+=1
    for R in (2,3,5,8,16):
        assert plus(coeff(n,1,R),coeff(n,R+1,n))==target
        stats['short_long_all_atom_returns']+=1
assert coeff(27,3,27)=={3:-2}
assert coeff(12,4,12)=={2:1}
stats['proper_power_and_cutoff_controls']+=2

values=[z(F(k,3),F(j,5)) for k in range(-2,3) for j in (-1,0,2)]
phases=[z(1),z(-1),z(0,1),z(0,-1),z(F(3,5),F(4,5))]
for a in values:
    for b in values:
        for phase in phases:
            ap=mul(phase,a)
            paired=2*mul(ap,conj(b))[0]
            assert paired+norm2(a)+norm2(b)==norm2(add(ap,b))
            assert paired>=-norm2(a)-norm2(b)
            stats['reflected_pair_lower_bound_and_return']+=1
        assert 2*mul(a,conj(a))[0]==2*norm2(a)
        stats['critical_pair_sign_controls']+=1

# Deliberate invalid replacement of the reflected bilinear term by a modulus.
a,b=z(1),z(-1)
assert 2*mul(a,conj(b))[0]==-2
assert 2*norm2(a)==2
stats['false_modulus_square_rejected']+=1

for a0 in (F(1,2),F(1,3),F(2,3)):
    for re in (F(1,10),F(1,4),F(3,8)):
        for im in (F(0),F(1),F(7,3)):
            w=z(re,im)
            wd=neg(conj(w))
            def bf(v): return div(sub(v,z(a0)),add(v,z(a0)))
            assert mul(bf(w),conj(bf(wd)))==z(1)
            assert norm2(bf(w))<1
            assert norm2(bf(wd))>1
            stats['allpass_pair_invariance']+=1

# Exponent bookkeeping only, not a test of any asymptotic arithmetic premise.
for eps in (F(1,10000),F(1,1000),F(1,100),F(1,33)):
    assert F(3,2)*eps<F(3,8)
    assert eps<F(3,8)
    assert F(1,8)<F(3,8)
    stats['returned_exponent_comparisons']+=1

out={'status':'PASS','counts':dict(stats),'total_checks':sum(stats.values()),
     'scope':'finite exact coefficient and signed-pair algebra; no CCM sign certificate',
     'ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
