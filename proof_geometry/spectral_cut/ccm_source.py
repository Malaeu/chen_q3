#!/usr/bin/env python3
"""Exact numerical transcription of the Route-B finite CCM source layer.

Source locks (Lean, byte-pinned in the results manifest):
  - Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean   (entry formulas)
  - Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean     (finite wrapper, J-symmetry)
  - Q3/Proofs/RouteB/ProlateLayer.lean                  (prolateCombination)
  - Q3/Proofs/RouteB/D0KTrialStage1/2/3.lean            (V_n, E_star, kTrial, c_n)
Paper: Connes-Consani-Moscovici, arXiv:2511.22755v1.

Matrix entry (ccmWeilTauN1):  tau(n,m) = W02(n,m) - WR(n,m) - Prime(n,m)
with L = log(mProject), on modes -N..N.

Trial chain: h0=psi_0, h4=psi_4 of the prolate expression
PW_lambda = -d/dx((lambda^2-x^2)d/dx) + (2 pi lambda x)^2 on [-lambda,lambda],
lambda = sqrt(mProject); after t = x/lambda this is the standard PSWF problem
-((1-t^2)psi')' + c^2 t^2 psi = chi psi with c = 2 pi mProject.
hTrial = (I4 h0 - I0 h4)/sqrt(I0^2+I4^2);  E*(h)(u) = sqrt(u) sum_k h(k u);
g = E*(hTrial) on [lambda^-1, lambda];  c'_n = <V_n, g>;  kTrial row =
projection to |n|<=N, normalized to unit l2 norm (norm_kTrial_m_N).

Everything here is numerics for a read-only preflight: no proof claim.
"""

from __future__ import annotations

import mpmath as mp

# ── Legendre / PSWF layer ────────────────────────────────────────────────────


def legendre_tridiag(K):
    """alpha_k = (k+1)/sqrt((2k+1)(2k+3)); t Pb_k = a_{k-1}Pb_{k-1}+a_k Pb_{k+1}."""
    return [ (k + 1) / mp.sqrt(mp.mpf((2 * k + 1) * (2 * k + 3))) for k in range(K) ]


def pswf_even_pair(c, K_full):
    """Even PSWF eigenpairs (psi_0, psi_4) as normalized-Legendre coefficients.

    Builds M = diag(k(k+1)) + c^2 T^2 restricted to even k, diagonalizes, and
    returns coefficient vectors for the 1st and 3rd even eigenfunctions
    (global PSWF indices 0 and 4) with sum d_k^2 = 1 (L2[-1,1] normalized).
    """
    alpha = legendre_tridiag(K_full)
    K_even = K_full // 2
    # (T^2)[j,k] over even indices j=2a, k=2b
    M = mp.zeros(K_even)
    for a in range(K_even):
        k = 2 * a
        diag = mp.mpf(k * (k + 1))
        t2_diag = (alpha[k - 1] ** 2 if k >= 1 else mp.mpf(0)) + alpha[k] ** 2
        M[a, a] = diag + c ** 2 * t2_diag
        if a + 1 < K_even:
            M[a, a + 1] = M[a + 1, a] = c ** 2 * alpha[k] * alpha[k + 1]
    E, Q = mp.eigsy(M)
    order = sorted(range(K_even), key=lambda i: E[i])
    out = []
    for pos in (0, 2):  # even eigenfunctions #1 and #3 = psi_0 and psi_4
        idx = order[pos]
        d = {2 * a: Q[a, idx] for a in range(K_even)}
        norm = mp.sqrt(mp.fsum(v ** 2 for v in d.values()))
        d = {k: v / norm for k, v in d.items()}
        out.append((mp.mpf(E[idx]), d))
    return out  # [(chi0, d0), (chi4, d4)]


def legendre_norm_eval(coeffs, t):
    """Evaluate sum_k coeffs[k] * Pbar_k(t), Pbar_k = sqrt(k+1/2) P_k."""
    kmax = max(coeffs)
    p_prev = mp.mpf(1)          # P_0
    p_curr = t                  # P_1
    total = coeffs.get(0, mp.mpf(0)) * mp.sqrt(mp.mpf(1) / 2)
    if kmax >= 1 and 1 in coeffs:
        total += coeffs[1] * mp.sqrt(mp.mpf(3) / 2) * p_curr
    for k in range(2, kmax + 1):
        p_next = ((2 * k - 1) * t * p_curr - (k - 1) * p_prev) / k
        p_prev, p_curr = p_curr, p_next
        if k in coeffs:
            total += coeffs[k] * mp.sqrt(k + mp.mpf(1) / 2) * p_curr
    return total


def pswf_ode_residual(chi, coeffs, c, samples=7):
    """Max residual of -((1-t^2)psi')' + c^2 t^2 psi - chi psi at sample points,
    via high-order central differences, relative to chi*|psi| scale."""
    h = mp.mpf(10) ** (-int(mp.mp.dps // 3))
    worst = mp.mpf(0)
    for s in range(1, samples + 1):
        t = mp.mpf(2 * s - samples - 1) / (samples + 2)  # interior points
        f = lambda x: legendre_norm_eval(coeffs, x)
        d1 = (f(t + h) - f(t - h)) / (2 * h)
        d2 = (f(t + h) - 2 * f(t) + f(t - h)) / h ** 2
        lhs = -((1 - t ** 2) * d2 - 2 * t * d1) + c ** 2 * t ** 2 * f(t)
        scale = abs(chi * f(t)) + abs(chi)
        worst = max(worst, abs(lhs - chi * f(t)) / scale)
    return worst


# ── Trial chain ──────────────────────────────────────────────────────────────


class SourceTrial:
    """hTrial coefficients and the normalized kTrial coefficient row."""

    def __init__(self, m_project, K_full=300):
        self.m = m_project
        self.lam = mp.sqrt(mp.mpf(m_project))
        self.L = mp.log(mp.mpf(m_project))
        self.c = 2 * mp.pi * m_project
        (self.chi0, d0), (self.chi4, d4) = pswf_even_pair(self.c, K_full)
        self.d0, self.d4 = d0, d4
        # I_n = integral of h_n over R = sqrt(2*lambda) * d_0 (only Pbar_0 has
        # nonzero integral: int Pbar_0 = sqrt(2)); h(x) = psi(x/lam)/sqrt(lam).
        self.I0 = mp.sqrt(2 * self.lam) * d0[0]
        self.I4 = mp.sqrt(2 * self.lam) * d4[0]
        den = mp.sqrt(self.I0 ** 2 + self.I4 ** 2)
        # hTrial(x) = sum_k e_k Pbar_k(x/lam), e = (I4 d0 - I0 d4)/(den sqrt(lam))
        self.e = {
            k: (self.I4 * d0.get(k, mp.mpf(0)) - self.I0 * d4.get(k, mp.mpf(0)))
            / (den * mp.sqrt(self.lam))
            for k in set(d0) | set(d4)
        }

    def h_trial(self, x):
        if abs(x) >= self.lam:
            return mp.mpf(0)
        return legendre_norm_eval(self.e, x / self.lam)

    def e_star(self, u):
        """E*(hTrial)(u) = sqrt(u) sum_{k>=1} hTrial(k u); finite sum."""
        kmax = int(mp.floor(self.lam / u))
        if kmax < 1:
            return mp.mpf(0)
        return mp.sqrt(u) * mp.fsum(self.h_trial(k * u) for k in range(1, kmax + 1))

    def coefficient_row(self, N, panels_scale=4, gauss_order=12):
        """c'_n = sqrt(L) * int_0^1 exp(-2 pi i n v) G(v) dv, G(v)=E*(lam^-1 e^{Lv}),
        split at the comb breakpoints v_k = 1 - log(k)/L, then normalized."""
        L, lam = self.L, self.lam
        brk = sorted(set(
            [mp.mpf(0), mp.mpf(1)]
            + [1 - mp.log(k) / L for k in range(2, self.m + 1)]
        ))
        nodes_w = gauss_nodes(gauss_order)
        samples = []  # (v, weight*G(v))
        for a, b in zip(brk[:-1], brk[1:]):
            length = b - a
            npan = max(6, int(mp.ceil(panels_scale * N * length)))
            for p in range(npan):
                lo = a + length * p / npan
                hi = a + length * (p + 1) / npan
                half = (hi - lo) / 2
                mid = (hi + lo) / 2
                for t, w in nodes_w:
                    v = mid + half * t
                    u = mp.exp(L * v) / lam
                    samples.append((v, w * half * self.e_star(u)))
        row = {}
        for n in range(0, N + 1):
            acc = mp.fsum(gw * mp.exp(-2j * mp.pi * n * v) for v, gw in samples)
            row[n] = mp.sqrt(L) * acc
            if n:
                row[-n] = mp.conj(row[n])
        raw_norm = mp.sqrt(mp.fsum(abs(z) ** 2 for z in row.values()))
        self.raw_norm = raw_norm
        return {n: z / raw_norm for n, z in row.items()}


_GAUSS_CACHE = {}


def gauss_nodes(order):
    key = (order, mp.mp.dps)
    if key in _GAUSS_CACHE:
        return _GAUSS_CACHE[key]
    # roots of P_order via mp.polyroots on monomial coefficients
    coeffs = legendre_poly_coeffs(order)
    roots = mp.polyroots([mp.mpf(c) for c in coeffs], maxsteps=200, extraprec=60)
    out = []
    for r in roots:
        t = mp.re(r)
        dp = legendre_deriv(order, t)
        w = 2 / ((1 - t ** 2) * dp ** 2)
        out.append((t, w))
    _GAUSS_CACHE[key] = out
    return out


def legendre_poly_coeffs(n):
    """Monomial coefficients of P_n, highest degree first (exact rationals)."""
    from fractions import Fraction
    p0 = [Fraction(1)]
    p1 = [Fraction(1), Fraction(0)]
    if n == 0:
        return p0
    for k in range(2, n + 1):
        a = [Fraction(2 * k - 1, k) * c for c in p1] + [Fraction(0)]
        b = [Fraction(0), Fraction(0)] + [Fraction(k - 1, k) * c for c in p0]
        p0, p1 = p1, [x - y for x, y in zip(a, b)]
    return p1


def legendre_deriv(n, t):
    pm, pc = mp.mpf(1), t
    for k in range(2, n + 1):
        pm, pc = pc, ((2 * k - 1) * t * pc - (k - 1) * pm) / k
    return n * (t * pc - pm) / (t ** 2 - 1)


# ── Matrix layer ─────────────────────────────────────────────────────────────

VON_MANGOLDT = {2: 2, 3: 3, 4: 2, 5: 5, 7: 7, 8: 2, 9: 3, 11: 11, 13: 13,
                16: 2, 25: 5, 27: 3, 32: 2, 49: 7, 64: 2, 81: 3, 121: 11,
                125: 5, 128: 2}  # k -> p for prime powers (Lambda(k)=log p)


def q_kernel(L, n, m, x):
    """ccmQKernel, literal."""
    if n == m:
        return 2 * (L - x) / L * mp.cos(2 * mp.pi * n * x / L)
    return (mp.sin(2 * mp.pi * m * x / L) - mp.sin(2 * mp.pi * n * x / L)) / \
        (mp.pi * (n - m))


def w02_entry(L, n, m):
    return 32 * L * mp.sinh(L / 4) ** 2 * \
        (L ** 2 - 16 * mp.pi ** 2 * m * n) / \
        ((L ** 2 + 16 * mp.pi ** 2 * m ** 2) * (L ** 2 + 16 * mp.pi ** 2 * n ** 2))


def prime_entry(m_project, L, n, m):
    return mp.fsum(
        mp.log(VON_MANGOLDT[k]) / mp.sqrt(k) * q_kernel(L, n, m, mp.log(k))
        for k in range(2, m_project + 1) if k in VON_MANGOLDT
    )


def wr_integrand_literal(L, n, m, x):
    return (mp.e ** (x / 2) * q_kernel(L, n, m, x) - q_kernel(L, n, m, 0)) / \
        (mp.e ** x - mp.e ** (-x))


def wr_entry_literal(L, n, m, m_project):
    """ccmWREntry by direct quadrature of the literal integrand."""
    const = q_kernel(L, n, m, 0) / 2 * (
        mp.euler + mp.log(4 * mp.pi * (m_project - 1) / mp.mpf(m_project + 1)))
    pts = [L * k / max(4, abs(n) + abs(m) + 2)
           for k in range(0, max(4, abs(n) + abs(m) + 2) + 1)]
    integ = mp.quad(lambda x: wr_integrand_literal(L, n, m, x), pts)
    return const + integ


class SourceMatrix:
    """Optimized exact construction of ccmWeilMatFinite(m, N) with the literal
    formula retained as an independent verification path."""

    def __init__(self, m_project, N):
        self.m, self.N = m_project, N
        self.L = mp.log(mp.mpf(m_project))
        self._I_sin = {}
        self._wr_diag = {}

    def I_sin(self, k):
        """int_0^L e^{x/2} sin(2 pi k x / L)/(e^x - e^-x) dx."""
        k = int(k)
        if k == 0:
            return mp.mpf(0)
        if k < 0:
            return -self.I_sin(-k)
        if k not in self._I_sin:
            L = self.L
            pts = [L * j / max(4, k) for j in range(0, max(4, k) + 1)]
            self._I_sin[k] = mp.quad(
                lambda x: mp.e ** (x / 2) * mp.sin(2 * mp.pi * k * x / L) /
                (mp.e ** x - mp.e ** (-x)), pts)
        return self._I_sin[k]

    def wr_diag(self, n):
        n = abs(int(n))
        if n not in self._wr_diag:
            L, m = self.L, self.m
            const = mp.euler + mp.log(4 * mp.pi * (m - 1) / mp.mpf(m + 1))
            pts = [L * j / max(4, n + 2) for j in range(0, max(4, n + 2) + 1)]
            integ = mp.quad(
                lambda x: (mp.e ** (x / 2) * 2 * (L - x) / L *
                           mp.cos(2 * mp.pi * n * x / L) - 2) /
                (mp.e ** x - mp.e ** (-x)), pts)
            self._wr_diag[n] = const + integ
        return self._wr_diag[n]

    def wr_entry(self, n, m):
        if n == m:
            return self.wr_diag(n)
        return (self.I_sin(m) - self.I_sin(n)) / (mp.pi * (n - m))

    def tau(self, n, m, prime_sign=-1):
        """ccmWeilTauN1 = W02 - WR - Prime  (prime_sign=-1 canonical; +1 only
        as the mandated mutation plant, which the source gate must reject)."""
        return w02_entry(self.L, n, m) - self.wr_entry(n, m) + \
            prime_sign * prime_entry(self.m, self.L, n, m)

    def full_matrix(self, prime_sign=-1):
        N = self.N
        modes = list(range(-N, N + 1))
        K = mp.zeros(2 * N + 1)
        for i, n in enumerate(modes):
            for j, m in enumerate(modes):
                if j < i:
                    continue
                v = self.tau(n, m, prime_sign)
                K[i, j] = v
                K[j, i] = v
        return modes, K

    def tau_literal(self, n, m):
        """Independent literal path (Lean formula verbatim) for spot checks."""
        return w02_entry(self.L, n, m) - wr_entry_literal(self.L, n, m, self.m) \
            - prime_entry(self.m, self.L, n, m)
