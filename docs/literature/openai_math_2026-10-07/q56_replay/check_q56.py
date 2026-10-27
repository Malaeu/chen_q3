#!/usr/bin/env python3
"""Q56: new exact finite controls; Python 3.9+, standard library only.
Usage: python3 check_q56.py PACKET.txt [RESULT.json]
No historical code is executed. Formal rational controls are not production
CCM spectra, interval certificates, or an independent PAPER audit.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
from math import factorial, isqrt
import hashlib
import json
import re
import sys

SHA = 'b3a5f4823019bd3e9464973b3457e7d3e9497241be81e49b0cccbc08099b270a'


def require(ok: bool, text: str) -> None:
    if not ok:
        raise ValueError(text)


def verify_packet(raw: bytes) -> dict:
    require(hashlib.sha256(raw).hexdigest() == SHA, 'packet SHA256')
    require(len(raw) == 160453 and raw.count(b'\n') == 2597, 'packet bytes/LF')
    raw.decode('utf-8')
    head = raw[:raw.index(b'BEGIN S1 ')]
    rx = rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$'
    rows = []
    for i, h in enumerate(re.finditer(rx, head, re.M), 1):
        sid, name, size, lf, sha = h.groups()
        require(int(sid) == i, 'source order')
        op = b'BEGIN S'+sid+b' '+name+b'\n'
        start = raw.index(op)+len(op)
        end = start+int(size)
        body = raw[start:end]
        require(len(body) == int(size) and body.count(b'\n') == int(lf), 'source size/LF')
        require(hashlib.sha256(body).hexdigest().encode() == sha, 'source SHA256')
        require(raw[end:].startswith(b'\nEND S'+sid+b'\n'), 'source closing frame')
        rows.append(dict(id='S'+sid.decode(), name=name.decode(), bytes=len(body),
                         lf=int(lf), sha256=sha.decode()))
    require(len(rows) == 14, 'source count')
    return dict(bytes=len(raw), lf=raw.count(b'\n'), sha256=SHA, sources=rows)


def factor(n: int) -> dict[int, int]:
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out


def mu(n: int) -> int:
    a = factor(n)
    return 0 if any(k >= 2 for k in a.values()) else (-1)**len(a)


def primes(n: int) -> list[int]:
    return [p for p in range(2, n+1) if factor(p) == {p: 1}]


def addlog(a: dict, b: dict, weight=F(1)) -> dict:
    c = dict(a)
    for p, x in b.items():
        c[p] = c.get(p, F(0))+weight*x
    return {p: x for p, x in c.items() if x}


def arithmetic_controls() -> dict:
    coeff_count = 0
    for n in range(1, 129):
        got = {}
        for d in range(1, n+1):
            if n % d == 0:
                got = addlog(got, factor(n//d), F(mu(d)))
        fn = factor(n)
        want = {next(iter(fn)): F(1)} if len(fn) == 1 else {}
        require(got == want, 'all-power Lambda convolution')
        coeff_count += 1
    local_count = 0
    for p in primes(31):
        for r in range(1, 129):
            require(mu(p*r) == -mu(r)+int(r % p == 0)*mu(r), 'prime-square correction')
            local_count += 1
    amp_count = 0
    detectors = dict(omit_square_correction=False, reverse_main_sign=False,
                     replace_mu_by_absolute=False, square_before_prime_sum=False)
    for N in (8, 17, 32, 65):
        plist = primes(N)
        for mode in (0, 1, 2):
            selected = plist[:min(len(plist), (2, 4, 7)[mode])]
            weights = {p: F((p % 5)+1, p+mode+1) for p in selected}
            H = sum((a/F(p) for p, a in weights.items()), F(0))
            b = {n: F(((-1)**n)*(n*n+3*n+1), n+2) for n in range(1, N+1)}
            omega = {n: sum((a for p, a in weights.items() if n % p == 0), F(0))
                     for n in range(1, N+1)}
            rmax = N//min(selected)
            G = {r: sum((a*b[p*r] for p, a in weights.items() if p*r <= N), F(0))
                 for r in range(1, rmax+1)}
            S = sum((F(mu(n))*b[n] for n in b), F(0))
            main = -sum((F(mu(r))*G[r] for r in G), F(0))
            E = sum((a*mu(r)*b[p*r] for p, a in weights.items()
                     for r in range(1, N//p+1) if r % p == 0), F(0))
            R = sum((mu(n)*(H-omega[n])*b[n] for n in b), F(0))
            require(H*S == main+E+R, 'full amplifier return')
            Q = sum(mu(r)**2 for r in G)
            GG = sum((g*g for g in G.values()), F(0))
            require(main*main <= Q*GG, 'exact Cauchy inequality')
            Ea = sum((a*abs(mu(r)*b[p*r]) for p, a in weights.items()
                      for r in range(1, N//p+1) if r % p == 0), F(0))
            Ra = sum((abs(mu(n)*(H-omega[n])*b[n]) for n in b), F(0))
            deficit = H*S-Ea-Ra
            require(deficit <= 0 or deficit*deficit <= Q*GG, 'one-sided certificate')
            detectors['omit_square_correction'] |= H*S != main+R
            detectors['reverse_main_sign'] |= H*S != -main+E+R
            detectors['replace_mu_by_absolute'] |= S != sum(abs(mu(n))*b[n] for n in b)
            wrongG = sum((a*a*b[p*r]**2 for r in G for p, a in weights.items()
                          if p*r <= N), F(0))
            detectors['square_before_prime_sum'] |= GG != wrongG
            amp_count += 1
    require(all(detectors.values()), 'missed amplifier mutation')
    require(factor(8) != {2: 1}, 'prime-power negative control')
    return dict(lambda_formal_log_cases=coeff_count, prime_square_cases=local_count,
                full_amplifier_cases=amp_count, cauchy_inequalities=amp_count,
                detected=detectors, proper_power_control=True,
                scope='actual mu and formal log(p); arbitrary rational full observables, not physical CCM cells')


def gaussian_add(x, y):
    return (x[0]+y[0], x[1]+y[1])


def contact_controls() -> dict:
    rows = []
    missing = dict(endpoint=False, exponential=False)
    for a in (F(1, 2), F(1, 4), F(1, 8), F(1, 16), F(1, 32)):
        A0 = -F(3, 32)
        A1 = (a*a+F(1, 4))/2
        A2 = -(4*a*a+F(1, 4))/8
        coeff = {0: A0, 1: A1/2, -1: A1/2, 2: A2/2, -2: A2/2}
        require(sum(coeff.values()) == 0, 'endpoint contact')
        for sigma in (F(1, 2), -F(1, 2)):
            z = (F(0), F(0))
            for j, c in coeff.items():
                den = sigma*sigma+j*j*a*a
                z = gaussian_add(z, (c*sigma/den, -c*j*a/den))
            require(z == (0, 0), 'exponential contact rational function')
        norm = A0*A0+(A1*A1+A2*A2)/2
        require(norm > 0, 'positive normalization')
        bad = dict(coeff)
        bad[0] += F(1, 7)
        missing['endpoint'] |= sum(bad.values()) != 0
        sigma = F(1, 2)
        badmoment = sum((c*sigma/(sigma*sigma+j*j*a*a) for j,c in bad.items()), F(0))
        missing['exponential'] |= badmoment != 0
        rows.append(dict(formal_angular_step=str(a), norm_square_divided_by_L=str(norm)))
    require(all(missing.values()), 'missed contact mutation')
    # Exact convolution of the endpoint polynomial q(t)=12*t^2-t^4/4.
    q = {2: F(12), 4: -F(1, 4)}
    J = {}
    for i, a in q.items():
        for j, b in q.items():
            deg = i+j+1
            J[deg] = J.get(deg, F(0))+a*b*F(factorial(i)*factorial(j), factorial(deg))
    require(J == {5: F(24, 5), 7: -F(2, 35), 9: F(1, 10080)}, 'endpoint polynomial')
    require(F(9,1024)+(F(1,64)+F(1,1024))/2 == F(35,2048), 'limiting norm')
    return dict(formal_frequency_cases=rows, endpoint_polynomial={str(k):str(v) for k,v in J.items()},
                limiting_norm_square_divided_by_L='35/2048', mutations_detected=missing,
                scope='formal rational frequencies only; no m=e^(2*pi/a) is asserted to be an integer production cell')


def interval_controls() -> dict:
    count = 0
    for m in (112, 113, 224, 997):
        for r in range((m+7)//8, m//7+1):
            require(F(m,4) <= 2*r <= F(2*m,7), 'two-dilation interval')
            require(F(3*m,8) <= 3*r <= F(3*m,7), 'three-dilation interval')
            require(5*r > F(m,2), 'all higher prime channels vanish')
            require(4*r <= F(4*m,7), 'positive k=2 witness interval')
            count += 1
        for N in (m//4, m//2):
            sqfree = sum(mu(n)**2 for n in range(1,N+1))
            require(4*sqfree >= N, 'squarefree lower control')
    return dict(integer_interval_points=count, squarefree_count_cases=8,
                scope='integer endpoint arithmetic only, not a sparse-band production test')


def main() -> None:
    if len(sys.argv) not in (2, 3):
        raise SystemExit('usage: python3 check_q56.py PACKET.txt [RESULT.json]')
    raw = Path(sys.argv[1]).read_bytes()
    ans = dict(packet=verify_packet(raw), arithmetic=arithmetic_controls(),
               contacts=contact_controls(), endpoints=interval_controls(),
               historical_programs_executed=False, floating_point_mathematics=False,
               lean=False, arb=False, independent_audit=False, production_spectrum=False,
               cofinal_claim_certified_by_computation=False)
    text = json.dumps(ans, ensure_ascii=False, sort_keys=True, indent=2)+'\n'
    out = Path(sys.argv[2] if len(sys.argv) == 3 else 'q56_checks.json')
    out.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
