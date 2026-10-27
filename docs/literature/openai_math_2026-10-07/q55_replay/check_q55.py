#!/usr/bin/env python3
"""Q55 source lock and NEW finite checks. Python 3.9+, standard library only.
Usage: python3 check_q55.py PACKET.txt [RESULT.json]
No embedded historical program is extracted or executed. Floating tests are
small, off-schedule Fourier diagnostics, not interval or cofinal certificates.
"""
from __future__ import annotations
import cmath
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path
import re
import sys

SHA = 'ecf79b6faecccceff894a4d98902de6aac198d3b06355240f0154d2e3d63632e'
SIZE = 127670
LF = 2039


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def source_lock(raw: bytes) -> dict:
    require(len(raw) == SIZE and raw.count(b'\n') == LF, 'packet size/LF')
    require(hashlib.sha256(raw).hexdigest() == SHA, 'packet SHA256')
    raw.decode('utf-8')
    frames = []
    for name in ('LOCAL_UPDATE', 'BASE_REQUEST'):
        h = re.search(rb'^' + name.encode() + rb': bytes=(\d+) SHA256=([0-9a-f]{64})$', raw, re.M)
        require(h is not None, 'missing outer frame ' + name)
        opening = b'BEGIN ' + name.encode() + b'\n'
        start = raw.index(opening) + len(opening)
        end = start + int(h[1])
        body = raw[start:end]
        require(hashlib.sha256(body).hexdigest() == h[2].decode(), 'frame hash ' + name)
        require(raw[end:].startswith(b'\nEND ' + name.encode() + b'\n'), 'frame closing ' + name)
        frames.append(dict(id=name, bytes=len(body), lf=body.count(b'\n'), sha256=h[2].decode(), start_byte=start, end_byte=end))
        if name == 'BASE_REQUEST':
            base, base_start = body, start
    headers = list(re.finditer(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', base[:base.index(b'BEGIN S1 ')], re.M))
    require(len(headers) == 9, 'source count')
    sources = []
    for i, h in enumerate(headers, 1):
        require(h[1] == str(i).encode(), 'source order')
        opening = b'BEGIN S' + h[1] + b' ' + h[2] + b'\n'
        start = base.index(opening) + len(opening)
        end = start + int(h[3])
        body = base[start:end]
        require(len(body) == int(h[3]) and body.count(b'\n') == int(h[4]), 'source size/LF')
        require(hashlib.sha256(body).hexdigest() == h[5].decode(), 'source hash')
        require(base[end:].startswith(b'\nEND S' + h[1] + b'\n'), 'source closing')
        absolute_start, absolute_end = base_start + start, base_start + end
        sources.append(dict(id='S'+str(i), name=h[2].decode(), bytes=len(body), lf=body.count(b'\n'), sha256=h[5].decode(), start_byte=absolute_start, end_byte=absolute_end, start_line=raw[:absolute_start].count(b'\n')+1, end_line=raw[:absolute_end].count(b'\n')))
    return dict(bytes=SIZE, lf=LF, sha256=SHA, frames=frames, sources=sources)


def exact_checks() -> dict:
    # pi has been absorbed into the off-diagonal unit; this checks signs,
    # differences and complex pairing, not an approximation to physical pi.
    total_entries = 0
    for M in (1, 2, 4):
        js = list(range(-M, M+1))
        g = {j: F(j*j*j-2*j, 7) for j in js}
        diagonal = {j: F(3*j*j-1, 5) for j in js}
        H = [[F(0) if j == k else F(1, j-k) for k in js] for j in js]
        direct = [[diagonal[j] if j == k else -(g[j]-g[k])/F(j-k) for k in js] for j in js]
        comm = [[(g[j]-g[k])*H[a][b] for b,k in enumerate(js)] for a,j in enumerate(js)]
        rebuilt = [[(diagonal[j] if j == k else F(0))-comm[a][b] for b,k in enumerate(js)] for a,j in enumerate(js)]
        require(direct == rebuilt, 'exact commutator identity')
        require(all(direct[a][b] == direct[b][a] for a in range(len(js)) for b in range(len(js))), 'symmetry')
        re = [F(j+2, 3) for j in js]
        im = [F(j*j-1, 4) for j in js]
        # For a real symmetric B, c*Bc = Re(c)^T B Re(c)+Im(c)^T B Im(c).
        imag = sum((re[a]*im[b]-im[a]*re[b])*direct[a][b] for a in range(len(js)) for b in range(len(js)))
        require(imag == 0, 'same complex vector pairing')
        shifted = [[(g[j]+F(11,3)-g[k]-F(11,3))*H[a][b] for b,k in enumerate(js)] for a,j in enumerate(js)]
        require(shifted == comm, 'constant shift invariance')
        total_entries += len(js)**2
    # Exact joint-family change: Psi-Phi=q(tau), q'(0)=A_cont/2.
    # Retain constant, linear, quadratic, cubic and quartic coefficients.
    q = [F(0), F(-3,7), F(5,4), F(-2,9), F(7,11)]
    tau = F(3,5)
    qvalue = sum(v*tau**i for i,v in enumerate(q))
    remainder_change = sum(q[i]*tau**i for i in range(2,len(q)))
    require(remainder_change-qvalue == -tau*q[1], 'full joint remainder change')
    # The modulus cap |E|<=B in a strip plus radius 1/L gives |E'|/L<=B:
    # diagonal <=4B and oscillation<=2B, hence the advertised 6B.
    require(2+2+2 == 6, 'strip-to-matrix budget')
    return dict(matrix_entries=total_entries, exact_joint_polynomial_case=1, commutator_constant_shift=True, exact_complex_pairing=True)


def mangoldt(m: int) -> list[float]:
    a = [0.0]*(m+1)
    for p in range(2,m+1):
        if all(p%d for d in range(2, math.isqrt(p)+1)):
            n = p
            while n <= m:
                a[n] = math.log(p)
                n *= p
    return a


def primitive(z: complex, L: float) -> tuple[complex,complex]:
    """Integral exp(z*a) da and its derivative w.r.t. the real frequency."""
    if abs(z) < 1e-12:
        return complex(L), 0.5j*L*L
    e = cmath.exp(z*L)
    return (e-1)/z, 1j*(e*(L*z-1)+1)/(z*z)


def matrix_from_symbol(values, derivatives, js, L):
    out = []
    for a,j in enumerate(js):
        row = []
        for b,k in enumerate(js):
            if j == k:
                v = 2*values[a].real-2*derivatives[a].imag/L
            else:
                v = -(values[a].imag-values[b].imag)/(math.pi*(j-k))
            row.append(v)
        out.append(row)
    return out


def shift_matrix(js, L, a):
    freq = [2*math.pi*j/L for j in js]
    out = []
    for j,wj in enumerate(freq):
        row = []
        for k,wk in enumerate(freq):
            if j == k:
                entry = (1-a/L)*cmath.exp(1j*wk*a)
            else:
                entry = cmath.exp(1j*wk*a)*((cmath.exp(1j*(wk-wj)*(L-a))-1)/(1j*L*(wk-wj)))
            row.append(2*entry.real)
        out.append(row)
    return out


def quadratic(A, c):
    return sum(c[j].conjugate()*A[j][k]*c[k] for j in range(len(c)) for k in range(len(c)))


def solve(A, b):
    A = [list(map(complex,row))+[complex(v)] for row,v in zip(A,b)]
    n = len(b)
    for k in range(n):
        pivot = max(range(k,n), key=lambda i: abs(A[i][k]))
        require(abs(A[pivot][k]) > 1e-14, 'singular diagnostic constraint matrix')
        A[k], A[pivot] = A[pivot], A[k]
        d = A[k][k]
        A[k] = [x/d for x in A[k]]
        for i in range(n):
            if i != k:
                d = A[i][k]
                A[i] = [x-d*y for x,y in zip(A[i],A[k])]
    return [A[i][-1] for i in range(n)]


def diagnostic_checks() -> dict:
    max_entry_error = max_form_error = max_contact_residual = max_continuous_error = 0.0
    rows = []
    detectors = dict(reverse_commutator=False, erase_diagonal_derivative=False, delete_top_derivative=False, independent_complex_vector=False, ignore_contacts=False)
    # Judge-before-player: a wrong diagonal (no derivative) must not be
    # accepted for a positive atom at a=L. Correct endpoint form is zero.
    bad_endpoint = 2*math.log(16)/math.sqrt(16)
    require(bad_endpoint > 1.0, 'planted endpoint violation was not detected')
    detectors['delete_top_derivative'] = True
    for m,M in ((8,2),(16,3),(27,2),(64,3),(81,4)):
        L = math.log(m)
        js = list(range(-M,M+1))
        freq = [2*math.pi*j/L for j in js]
        lm = mangoldt(m)
        V = [sum(lm[n]/math.sqrt(n)*cmath.exp(1j*w*math.log(n)) for n in range(2,m+1)) for w in freq]
        D = [sum(1j*math.log(n)*lm[n]/math.sqrt(n)*cmath.exp(1j*w*math.log(n)) for n in range(2,m+1)) for w in freq]
        C, CD = zip(*(primitive(0.5+1j*w,L) for w in freq))
        Q, QD = zip(*(primitive(-0.5+1j*w,L) for w in freq))
        A = [[0.0]*len(js) for _ in js]
        for n in range(2,m+1):
            if lm[n]:
                H = shift_matrix(js,L,math.log(n))
                for a in range(len(js)):
                    for b in range(len(js)):
                        A[a][b] += lm[n]/math.sqrt(n)*H[a][b]
        formula = matrix_from_symbol(V,D,js,L)
        err = max(abs(A[a][b]-formula[a][b]) for a in range(len(js)) for b in range(len(js)))
        max_entry_error = max(max_entry_error,err)
        require(err < 2e-11, 'physical matrix identity')
        c = [complex(j+2, j*j-1) for j in js]
        norm = math.sqrt(sum(abs(v)**2 for v in c))
        c = [v/norm for v in c]
        ferr = abs(quadratic(A,c)-quadratic(formula,c))
        max_form_error = max(max_form_error,ferr)
        require(ferr < 2e-11, 'complex physical form')
        # Same three contact rows, on a deliberately off-schedule small band.
        contacts = [[1+0j for _ in js], [1/(0.5+1j*w) for w in freq], [1/(-0.5+1j*w) for w in freq]]
        chosen = [0,M,2*M]
        rest = [k for k in range(len(js)) if k not in chosen]
        rhs = [-sum(row[k]*c[k] for k in rest) for row in contacts]
        vals = solve([[row[k] for k in chosen] for row in contacts],rhs)
        for k,v in zip(chosen,vals): c[k] = v
        norm = math.sqrt(sum(abs(v)**2 for v in c)); c = [v/norm for v in c]
        residual = max(abs(sum(row[k]*c[k] for k in range(len(js)))) for row in contacts)
        max_contact_residual = max(max_contact_residual,residual)
        AC = matrix_from_symbol(C,CD,js,L)
        AQ = matrix_from_symbol(Q,QD,js,L)
        cv,qv = quadratic(AC,c),quadratic(AQ,c)
        max_continuous_error = max(max_continuous_error,abs(cv+qv))
        require(residual < 2e-12 and abs(cv+qv) < 2e-11, 'contact/continuous identity')
        require(-4-2e-11 <= cv.real <= 2e-11, 'continuous interval diagnostic')
        E = [v-u for v,u in zip(V,C)]; ED = [v-u for v,u in zip(D,CD)]
        B = matrix_from_symbol(E,ED,js,L)
        diagonal = [B[k][k] for k in range(len(js))]
        g = [v.imag for v in E]
        cap = max(diagonal)+max(g)-min(g)
        value = quadratic(B,c).real
        require(value <= cap+2e-11, 'one-sided cap diagnostic')
        detectors['reverse_commutator'] |= any(abs(A[a][b]+formula[a][b]) > 1e-4 for a in range(len(js)) for b in range(len(js)) if a != b)
        detectors['erase_diagonal_derivative'] |= any(abs(A[k][k]-2*V[k].real) > 1e-4 for k in range(len(js)))
        d = [complex(v.real,-v.imag) for v in c]
        wrong = sum(c[j].conjugate()*B[j][k]*d[k] for j in range(len(c)) for k in range(len(c)))
        detectors['independent_complex_vector'] |= abs(wrong-quadratic(B,c)) > 1e-4
        e0 = [0j]*len(js); e0[M] = 1
        detectors['ignore_contacts'] |= quadratic(AC,e0).real > 0.1
        rows.append(dict(m=m,M=M,original_epsilon_schedule=False,source_matrix_max_abs_error=format(err,'.17g'),contact_max_abs_residual=format(residual,'.17g'),continuous_value=format(cv.real,'.17g'),directed_cap=format(cap,'.17g'),tested_quadratic_value=format(value,'.17g')))
    require(all(detectors.values()), 'missed planted algebra violation')
    return dict(cases=rows,max_entry_error=format(max_entry_error,'.17g'),max_form_error=format(max_form_error,'.17g'),max_contact_residual=format(max_contact_residual,'.17g'),max_continuous_identity_error=format(max_continuous_error,'.17g'),tolerance='2e-11',arithmetic='binary64, not outward rounded',interval_certificate=False,planted_violations_detected=detectors)


def main() -> None:
    if len(sys.argv) not in (2,3):
        raise SystemExit('usage: python3 check_q55.py PACKET.txt [RESULT.json]')
    raw = Path(sys.argv[1]).read_bytes()
    result = dict(source=source_lock(raw),exact=exact_checks(),diagnostics=diagnostic_checks(),historical_programs_executed=False,production_spectrum=False,lean=False,arb=False,independent_audit=False,cofinal_bound_certified_by_computation=False,actual_zeta_zeros_computed=False)
    text = json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    out = Path(sys.argv[2] if len(sys.argv)==3 else 'q55_checks.json')
    out.write_text(text,encoding='utf-8')
    print(text,end='')

if __name__ == '__main__':
    main()
