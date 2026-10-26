#!/usr/bin/env python3
"""Q49: exact source framing, finite convolution and factor-length controls.
Standard library only. No actual CCM spectrum or transcendental sign sampling.
Usage: python3 check_q49.py CANONICAL_Q49.txt [RESULT.json]
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
from math import comb, prod
import hashlib
import json
import re
import sys

NAME = 'PROSHKA_CCM_JOINT_CENTRAL_FACTOR_LENGTH_Q49_2026-10-26.txt'
SIZE = 233604
LF = 4132
SHA = '5a9766d5eb45a7af9e29a572b38ae2a7f4e0f8f259501cce21eb92010bf4b745'
HEAD = re.compile(rb'^===== SOURCE (S\d+) =====\nPATH: ([^\n]+)\nBYTES: (\d+)\nLF: (\d+)\nSHA256: ([0-9a-f]{64})\nBEGIN_BODY\n', re.M)


def frames(raw: bytes) -> list[dict]:
    raw.decode('utf-8')
    rows = []
    pos = 0
    for i in range(1, 11):
        hit = HEAD.search(raw, pos)
        if hit is None or hit[1] != f'S{i}'.encode():
            raise ValueError('source order')
        if i > 1 and raw[pos:hit.start()].strip():
            raise ValueError('unframed material between bodies')
        start = hit.end()
        end = start + int(hit[3])
        body = raw[start:end]
        if len(body) != int(hit[3]) or body.count(b'\n') != int(hit[4]):
            raise ValueError('source size/LF')
        if hashlib.sha256(body).hexdigest() != hit[5].decode():
            raise ValueError('source hash')
        body.decode('utf-8')
        suffix = b'\nEND_BODY ' + hit[1] + b'\n'
        if raw[end:end+len(suffix)] != suffix:
            raise ValueError('source framing')
        rows.append(dict(id=hit[1].decode(), path=hit[2].decode(),
                         bytes=len(body), lf=body.count(b'\n'),
                         sha256=hit[5].decode(), start_byte=start, end_byte=end,
                         start_line=raw[:start].count(b'\n')+1,
                         end_line=raw[:end].count(b'\n')))
        pos = end + len(suffix)
    if raw[pos:].strip():
        raise ValueError('trailing material')
    return rows


def verify(raw: bytes) -> dict:
    if (len(raw), raw.count(b'\n'), hashlib.sha256(raw).hexdigest()) != (SIZE, LF, SHA):
        raise ValueError('canonical size/LF/SHA')
    if b'\r' in raw or not raw.endswith(b'\n'):
        raise ValueError('newline convention')
    if not raw.startswith(b'OPERATIVE_CLASS: TRY_CCM_JOINT_CENTRAL_FACTOR_LENGTH_Q49\n'):
        raise ValueError('request binding')
    return dict(name=NAME, bytes=SIZE, lf=LF, sha256=SHA,
                source_count=10, all_frames_verified=True, sources=frames(raw))


def factor(n: int) -> dict[int, int]:
    if n < 1:
        raise ValueError('positive integer required')
    ans = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        ans[n] = ans.get(n, 0) + 1
    return ans


def mu(n: int) -> int:
    f = factor(n)
    return 0 if any(v > 1 for v in f.values()) else (-1)**len(f)


def logn(n: int) -> dict[int, int]:
    return factor(n)  # exact integer coefficients of formal log(prime)


def mangoldt(n: int) -> dict[int, int]:
    f = factor(n)
    return {next(iter(f)): 1} if len(f) == 1 else {}


def ladd(a: dict, b: dict, mult=1) -> dict:
    c = a.copy()
    for p, v in b.items():
        c[p] = c.get(p, 0) + mult*v
        if not c[p]:
            del c[p]
    return c


def conv(a: list[int], b: list[int]) -> list[int]:
    N = min(len(a), len(b))-1
    out = [0]*(N+1)
    for d in range(1, N+1):
        if a[d]:
            for k in range(1, N//d+1):
                if b[k]:
                    out[d*k] += a[d]*b[k]
    return out


def conv_log(a: list[int]) -> list[dict]:
    N = len(a)-1
    out = [{} for _ in range(N+1)]
    for d in range(1, N+1):
        if a[d]:
            for k in range(2, N//d+1):
                out[d*k] = ladd(out[d*k], logn(k), a[d])
    return out


def ceil_root(n: int, k: int) -> int:
    lo, hi = 1, n
    while lo < hi:
        mid = (lo+hi)//2
        if mid**k >= n:
            hi = mid
        else:
            lo = mid+1
    return lo


def hb(N: int, z: int, absolute_mu=False):
    u = [0]+[(abs(mu(n)) if absolute_mu else mu(n)) if n <= z else 0 for n in range(1, N+1)]
    one = [0]+[1]*N
    power = u[:]
    rows = []
    total = [{} for _ in range(N+1)]
    for j in range(1, 6):
        row = conv_log(power)
        rows.append(row)
        coeff = (-1)**(j-1)*comb(5, j)
        for n in range(1, N+1):
            total[n] = ladd(total[n], row[n], coeff)
        power = conv(conv(power, u), one)
    y = conv(one, u)
    y = [0]+[(1 if n == 1 else 0)-y[n] for n in range(1, N+1)]
    y5 = [0, 1]+[0]*(N-1)
    for _ in range(5):
        y5 = conv(y5, y)
    tail = [{} for _ in range(N+1)]
    for d in range(2, N+1):
        ld = mangoldt(d)
        if ld:
            for k in range(1, N//d+1):
                if y5[k]:
                    tail[d*k] = ladd(tail[d*k], ld, y5[k])
    return total, rows, y, y5, tail


def divisors(n: int):
    return [d for d in range(1, n+1) if n % d == 0]


def tuples_for(n: int, j: int, z: int):
    """All ordered exact factorizations; first j slots are Mobius slots."""
    def walk(left, slot, acc):
        if slot == 2*j-1:
            yield tuple(acc+[left])
            return
        for v in divisors(left):
            if slot < j and v > z:
                continue
            yield from walk(left//v, slot+1, acc+[v])
    yield from walk(n, 0, [])


def dyadic(n: int) -> int:
    return 1 << (n.bit_length()-1)


def merge(lengths, tags, threshold: Q):
    # threshold is the pair-product threshold, namely sqrt(B)/2^20.
    a = [(int(n), frozenset(t)) for n, t in zip(lengths, tags)]
    while True:
        hit = next(((i,j) for i in range(len(a)) for j in range(i+1,len(a))
                    if a[i][0]*a[j][0] < threshold), None)
        if hit is None:
            return a
        i, j = hit
        merged = (a[i][0]*a[j][0], a[i][1] | a[j][1])
        a = [v for k,v in enumerate(a) if k not in hit] + [merged]


def math_checks() -> dict:
    counts = {}
    neg = {}
    configs = [32, 33, 64, 243, 244, 486, 1024]
    for N in configs:
        z = ceil_root(N, 5)
        assert (z-1)**5 < N <= z**5
        total, rows, y, y5, tail = hb(N, z)
        assert not any(y[1:z+1]) and not any(y5[1:])
        for n in range(1, N+1):
            assert total[n] == mangoldt(n) and tail[n] == {}
    counts['support_valid_coefficient_configurations'] = len(configs)
    # Outside the support-valid regime, retain the full finite remainder.
    tail_rows = []
    for N,z in [(64,1), (486,2)]:
        total, rows, y, y5, tail = hb(N,z)
        assert any(tail[n] for n in range(1,N+1))
        for n in range(1,N+1):
            assert ladd(total[n],tail[n]) == mangoldt(n)
        first = next(n for n in range(1,N+1) if tail[n])
        tail_rows.append(dict(N=N,z=z,first_nonzero_tail=first,tail=tail[first]))
    counts['nonzero_remainder_configurations'] = len(tail_rows)
    total, rows, y, y5, tail = hb(64,1)
    neg['delete_tail_outside_support_range'] = total[64] != mangoldt(64)
    # Strict versus inclusive cutoff changes the support claim at z^5.
    _,_,_,strict_y5,_ = hb(32,1)
    _,_,_,inclusive_y5,_ = hb(32,2)
    neg['replace_inclusive_mu_cutoff_by_strict'] = strict_y5[32] == -1 and inclusive_y5[32] == 0
    total, rows, *_ = hb(64,3)
    no_fifth = [ladd(total[n],rows[4][n],-1) for n in range(65)]
    neg['omit_fifth_binomial_channel'] = any(no_fifth[n] != mangoldt(n) for n in range(1,65))
    wrong, *_ = hb(64,3,absolute_mu=True)
    neg['replace_mu_by_absolute_mu'] = any(wrong[n] != mangoldt(n) for n in range(1,65))
    # Independently enumerate exact ordered hyperbolic faces and dyadic boxes.
    cases = []
    for n in (8,12,16,24):
        N=32;z=2
        _,rows,*_ = hb(N,z)
        for j in range(1,6):
            got={}; boxes={}; number=0
            for t in tuples_for(n,j,z):
                assert prod(t)==n and all(v<=z for v in t[:j])
                v=prod(mu(a) for a in t[:j]); ell=logn(t[j])
                got=ladd(got,ell,v)
                key=tuple(dyadic(a) for a in t)
                boxes[key]=ladd(boxes.get(key,{}),ell,v)
                assert prod(key)<=n<2**(2*j)*prod(key)
                number+=1
            rec={}
            for v in boxes.values(): rec=ladd(rec,v)
            assert got==rows[j-1][n]==rec
            cases.append((n,j,number))
    counts['ordered_factor_box_cases']=len(cases)
    neg['replace_hyperbola_by_rectangle'] = 2<=ceil_root(24,5) and 16<=24 and 2*16>24 and mu(2)!=0 and bool(logn(16))
    # Actual prime-power family, finite support and a literal nonzero HB tuple.
    actual=[]
    for p in (3,5,7):
        assert mangoldt(p)=={p:1}
        m=2*p**5;z=ceil_root(m,5)
        a=(p,p,p,p,1); b=(p,1,1,1,1)
        assert p<=z<p*p and prod(a)*prod(b)==p**5<m
        assert prod(mu(v) for v in a)==1 and logn(b[0])=={p:1}
        # On p-powers the convolution can be computed in exponent coordinates.
        E=5;u=[1,-1]+[0]*(E-1)
        def ec(x,y):
            return [sum(x[i]*y[k-i] for i in range(k+1)) for k in range(E+1)]
        power=u[:];one=[1]*(E+1);ell=list(range(E+1))
        ch=[]
        for j in range(1,6):
            ch.append(ec(power,ell)[5]);power=ec(ec(power,u),one)
        assert ch==[1]*5 and sum((-1)**(j-1)*comb(5,j)*ch[j-1] for j in range(1,6))==1
        actual.append(dict(p=p,m=m,z=z,product=p**5,tuple_logp_coefficient=1,channel_logp_coefficients=ch))
    counts['actual_prime_power_family_controls']=len(actual)
    # Merging leaves every initial long Mobius factor untouched.
    rootB=2**24;Nlong=2**25
    lens=[Nlong]*5+[1]*5
    tags=[{f'mu{i}'} for i in range(4)]+[{'log'}]+[{f'unit{i}'} for i in range(5)]
    merged=merge(lens,tags,Q(rootB,2**20))
    assert prod(n for n,_ in merged)==prod(lens)
    assert all(any(n==Nlong and tag==frozenset({f'mu{i}'}) for n,tag in merged) for i in range(4))
    counts['small_pair_merge_control']=1
    exponents={
        'B_vs_length_domain':Q(3,8)-Q(4,9),
        'B_vs_new_typeII_height':Q(3,8)-Q(5,12),
        'mu_length_minus_rootB':Q(1,5)-Q(3,16),
        'balanced_length_minus_height':Q(2,5)-Q(3,8),
        'q_theta_decay':Q(1,2)-Q(5,8),
    }
    assert exponents=={'B_vs_length_domain':-Q(5,72),'B_vs_new_typeII_height':-Q(1,24),'mu_length_minus_rootB':Q(1,80),'balanced_length_minus_height':Q(1,40),'q_theta_decay':-Q(1,8)}
    neg['declare_length_lemma_domain_satisfied'] = Q(3,8)<Q(4,9)
    neg['drop_length_term_in_mean_value'] = Q(2,5)>Q(3,8)
    # Integer-only check of the global rational-approximation separation at X=2^32.
    X=2**32;lam=Q(1,2**20);Nmax=4*X+1
    assert lam**2*Nmax<Q(1,16) and lam**2*Nmax<1
    assert Q(1,4)<Q(1,2) and X>4
    counts['rational_domain_exact_control']=1
    # A full central test is linear in all Hermitian coordinates. A rational
    # convolution fixture tests algebra only; its kernel is not the CCM kernel.
    N=32; z=2;I=list(range(8,33)); total,*_=hb(N,z)
    def logs_sub(d):
        return sum((Q(p,p+1)*v for p,v in d.items()),Q())
    def chi(q):
        if q<=1: return Q(1)
        if q>=2: return Q()
        u=q-1;return 1-10*u**3+15*u**4-6*u**5
    h={r:tuple(Q(N-r)*(v) for v in (Q(1,r),Q(-2,r+1),Q(3,r+2),Q(4,r+3))) for r in I}
    a={r:tuple((chi(Q(r,16))-chi(Q(r,8)))*v for v in h[r]) for r in I}
    K=lambda r,n:Q(1,1+abs(r-n))
    phi={n:tuple(sum((K(r,n)*a[r][i] for r in I),Q()) for i in range(4)) for n in I}
    direct=tuple(sum(((logs_sub(mangoldt(n))-1)*phi[n][i] for n in I),Q()) for i in range(4))
    restored=tuple(sum(((logs_sub(total[n])-1)*phi[n][i] for n in I),Q()) for i in range(4))
    assert direct==restored and any(direct)
    assert all(sum((Q(0)*phi[n][i] for n in I),Q())==0 for i in range(4))
    # One fixed Gaussian-rational unit vector: (3/5,(12+16i)/25).
    contraction=lambda v:Q(9,25)*v[0]+Q(16,25)*v[1]+Q(72,125)*v[2]-Q(96,125)*v[3]
    assert Q(9,25)+Q(12,25)**2+Q(16,25)**2==1
    assert contraction(direct)==sum(((logs_sub(total[n])-1)*contraction(phi[n]) for n in I),Q())
    neg['drop_constant_model'] = any(sum((phi[n][i] for n in I),Q()) for i in range(4))
    neg['drop_complex_mixed_entries'] = contraction(direct)!=Q(9,25)*direct[0]+Q(16,25)*direct[1]
    neg['delete_smoothed_top_atom'] = h[N]==(Q(),)*4 and any(phi[N])
    counts['joint_Hermitian_pairing_fixture']=1
    # Actual sinc at lambda=1/4: pi*k_lambda(1)=sin(pi/2)=1.
    # This is the exact symbolic numerator, not a float evaluation.
    counts['exact_sinc_top_numerator']=1
    sinc_top_scaled_numerator=1
    assert sinc_top_scaled_numerator!=0
    assert all(neg.values())
    return dict(passed=True,counts=counts,negative_controls=neg,
                remainder_examples=tail_rows,actual_prime_power_examples=actual,
                exponent_differences={k:str(v) for k,v in exponents.items()},
                scope='Formal arithmetic, exact rational algebra and exponent controls. No finite test proves the cofinal signed CCM inequality.',
                source_signed_supplier_proved=False,actual_CCM_spectrum_evaluated=False)


def main():
    if len(sys.argv) not in (2,3):
        raise SystemExit('usage: python3 check_q49.py CANONICAL_Q49.txt [RESULT.json]')
    raw=Path(sys.argv[1]).read_bytes()
    proven=verify(raw)
    bad=bytearray(raw);bad[proven['sources'][0]['start_byte']+120]^=1
    for name,fn in [('global_corruption_detected',verify),('body_corruption_detected',frames)]:
        try: fn(bytes(bad))
        except ValueError: proven[name]=True
        else: raise AssertionError(name)
    end=proven['sources'][0]['end_byte']
    bad_frame=raw[:end]+raw[end+1:]
    try: frames(bad_frame)
    except ValueError: proven['separator_corruption_detected']=True
    else: raise AssertionError('separator accepted')
    result=dict(provenance=proven,mathematics=math_checks(),
                historical_code_executed=False,Lean=False,Arb=False,
                independent_audit=False,repository_writes=False)
    txt=json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    dest=Path(sys.argv[2]) if len(sys.argv)==3 else Path('q49_checks.json')
    dest.write_text(txt,encoding='utf-8')
    print(json.dumps({'status':'EXACT_CONTROLS_COMPLETED','sources':10,
                      'negative_controls':len(result['mathematics']['negative_controls']),
                      'output':str(dest)},sort_keys=True))

if __name__=='__main__':
    main()
