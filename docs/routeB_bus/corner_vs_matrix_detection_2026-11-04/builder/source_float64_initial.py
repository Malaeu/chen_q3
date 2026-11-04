"""Zeta EVEN diagnostic assembly, literal physical basis j=0,...,m.

Algebraically identical to the pinned analytic_source.build(m,bits)['zeta'][0].
No DH, legacy plant, zero Gram, clipping, or positivity assumption. Float64
rounding is not an enclosure. This diagnostic cannot establish RH.
"""
from __future__ import annotations
import hashlib
from pathlib import Path
import platform
import time
import numpy as np
import scipy
from scipy.special import digamma

SOURCE_PATH = Path(__file__).resolve().parents[2] / 'ground_state_zeros_2026-11-03/inputs/analytic_source.py'
SOURCE_SHA256 = '4e26ed90c8ef7305699802c02490bb0cea0da26be49891c98d387b5210eb8f63'
SOURCE_GIT_BLOB = '27bbaabbc5938b3157b5bc20f5e6db2f882122c0'


def verify_source():
    got = hashlib.sha256(SOURCE_PATH.read_bytes()).hexdigest()
    if got != SOURCE_SHA256:
        raise RuntimeError(f'PINNED_SOURCE_HASH_MISMATCH: {got}')
    return got


def trigamma(z):
    """Complex trigamma by recurrence to Re>=18 and Bernoulli asymptotic.

    B_2,...,B_20: psi_1(z)=1/z+1/(2z^2)+sum B_2k/z^(2k+1).
    Re>=18 keeps this ten-term expansion below float64 roundoff. Each
    recurrence uses psi_1(z)=psi_1(z+1)+1/z^2. Validated against fresh FLINT.
    """
    z = np.asarray(z, dtype=np.complex128)
    w = z.copy()
    acc = np.zeros_like(w)
    # All source arguments have Re=1/4; support arbitrary positive real parts.
    while np.any(w.real < 18):
        mask = w.real < 18
        acc[mask] += 1 / w[mask]**2
        w[mask] += 1
    inv = 1 / w
    v2 = inv * inv
    term = inv * v2
    ans = inv + .5*v2
    for b in [1/6, -1/30, 1/42, -1/30, 5/66, -691/2730,
              7/6, -3617/510, 43867/798, -174611/330]:
        ans += b*term
        term *= v2
    return ans + acc


def prime_power_atoms(m):
    """All Lambda(k)/sqrt(k), 2<=k<m; includes every prime power."""
    sieve = np.ones(m, dtype=bool)
    sieve[:2] = False
    atoms, values = [], []
    for p in range(2, m):
        if sieve[p]:
            sieve[p*p::p] = False
            k = p
            while k < m:
                atoms.append(k)
                values.append(np.log(float(p))/np.sqrt(float(k)))
                k *= p
    order = np.argsort(atoms)
    return np.asarray(atoms, dtype=np.int64)[order], np.asarray(values)[order]


def build(m: int, *, block: int = 128):
    """Return (A, meta), symmetric float64 (m+1)x(m+1), unplanted zeta EVEN.

    The tail is truncated at the pinned source's 256-bit cut 2^(-304),
    far below float64 accuracy; no analytic term is removed. Matrix entries
    include endpoint corrections, full prime powers, arch tail, and pole.
    O(m^2 + m*pi(m)) time, O(m^2 + block*pi(m)) memory.
    """
    if not isinstance(m, (int, np.integer)) or m < 2:
        raise ValueError('m must be an integer >=2')
    wall, cpu = time.perf_counter(), time.process_time()
    verify_source()
    L = np.log(float(m)); pi = np.pi
    n = np.arange(m+1, dtype=np.float64)
    omega = 2*pi*n/L
    w2 = omega**2
    zarg = .25 + .5j*omega
    psi = digamma(zarg)
    tri = trigamma(zarg).real
    diag = psi.real - digamma(.25) + tri/(2*L)
    diag[1:] += psi.imag[1:] / (L*omega[1:])
    moment = psi.imag/2
    # This is exactly the alpha=1/2 branch in the pinned source.
    a, e, tail_count = .5, np.exp(-L/2), 0
    step = np.exp(-2*L)
    cut = 2.0**-304
    while e > cut:
        den = a*a + w2
        moment -= omega*e/den
        diag -= e*(2*w2/(a*den) + 4*a*a/(L*den**2) + 2*a/den)
        # n=0 has its own direct pinned diagonal, not a continuation.
        diag[0] += 2*e/(L*a*a)
        a += 2
        e *= step
        tail_count += 1
    atoms, weights = prime_power_atoms(m)
    ratios = np.log(atoms.astype(np.float64))/L
    ps = np.empty(m+1); pd = np.empty(m+1)
    for lo in range(0, m+1, block):
        hi = min(m+1, lo+block)
        phase = (2*pi*n[lo:hi, None])*ratios[None, :]
        ss = np.sin(phase) @ weights
        cc = np.cos(phase) @ (2*(1-ratios)*weights)
        ps[lo:hi] = ss
        nz = n[lo:hi] > 0
        cc[nz] -= ss[nz]/(pi*n[lo:hi][nz])
        pd[lo:hi] = cc
    beta = moment + ps
    d = np.full(m+1, np.sqrt(2.)); d[0] = 1
    bn = n*beta
    nn = n*n
    A = bn[:, None]-bn[None, :]
    denominator = nn[:, None]-nn[None, :]
    np.fill_diagonal(denominator, 1.)
    A /= denominator
    A *= d[:, None]
    A *= d[None, :]/pi
    c = -np.euler_gamma-np.log(8*pi)-pi/2
    z = np.exp(-L/2)
    diagonal = c + diag + 2*(np.arctanh(z)+np.arctan(z))-pd
    np.fill_diagonal(A, diagonal)
    pole = 4*np.sqrt(2.)*d*L**1.5*np.sinh(L/4)/(L*L+16*pi*pi*n*n)
    A += np.outer(pole, pole)
    meta = dict(m=int(m), dimension=m+1, dtype=str(A.dtype),
                source_sha256=SOURCE_SHA256, source_git_blob=SOURCE_GIT_BLOB,
                builder_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                python=platform.python_version(), numpy=np.__version__, scipy=scipy.__version__,
                tail_terms=tail_count, tail_cut='2^-304', prime_power_count=len(atoms),
                wall_seconds=time.perf_counter()-wall, cpu_seconds=time.process_time()-cpu,
                basis='d_j*(-1)^j/sqrt(log(m))*cos(2*pi*j*x/log(m)); j=0..m',
                unplanted=True, interval_certificate=False,
                honesty='DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER_NOT_RH')
    return A, meta
