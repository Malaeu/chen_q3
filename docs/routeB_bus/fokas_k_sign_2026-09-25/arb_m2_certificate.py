#!/usr/bin/env python3
"""Strict finite-cell m=2 Arb certificate for the Goal058 scalar sign.

Scratch-only; no canonical source edits. All real and complex arithmetic uses
python-flint Arb balls. The finite R3 form is enclosed over the full rational
source-energy rectangle. The tail comparison uses the same universal norm
argument with a certified Frobenius bound for the literal K matrix; the
canonical coarse Gamma test is reported separately.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb
import json
from pathlib import Path
from flint import arb, acb, ctx, fmpq

OUT = Path(__file__).resolve().parent
M = 2
N = 6*M - 1
MODES = tuple(range(-M, M + 1))
ENERGY_RATIONALS = {
    0: (Fraction("11.799685000256793"), Fraction("11.799685000256800")),
    4: (Fraction("100.85413101702084"), Fraction("100.85413101722911")),
}


def qball(q: Fraction) -> arb:
    return arb(fmpq(q.numerator, q.denominator))


def source_G(m=M):
    return 4 * arb.pi()**2 * m**2


def ell(m, k):
    if k < 1:
        return arb(0)
    G = source_G(m)
    return -G * (2*k - 1) * (2*k) / ((4*k - 3) * (4*k - 1))


def diag(m, k):
    G = source_G(m)
    return 2*k*(2*k + 1) + G * (4*k*(2*k + 1) - 1) / ((4*k - 1)*(4*k + 3))


def up(m, k):
    G = source_G(m)
    return -G * (2*k + 1)*(2*k + 2) / ((4*k + 3)*(4*k + 5))


def source_energy_ball(i):
    lo, hi = ENERGY_RATIONALS[i]
    return qball(lo).union(qball(hi))


def sturm_count_below(m, t, x):
    """Certified LDL inertia count for symmetric J_m(t)-xI.

    The off-diagonal square at edge k is u_k*ell_(k+1); no square root is
    needed. The returned signs certify each nonzero interval pivot.
    """
    last = 6*m - 1
    pivot = diag(m, 0) - x
    signs = []
    def sign_of(p):
        if p > 0:
            return 1
        if p < 0:
            return -1
        raise ArithmeticError(f"LDL pivot interval contains zero: {p}")
    signs.append(sign_of(pivot))
    for k in range(1, last + 1):
        d = diag(m, k) - x
        if k == last:
            d += up(m, last) * t
        edge_sq = up(m, k - 1) * ell(m, k)
        pivot = d - edge_sq / pivot
        signs.append(sign_of(pivot))
    return sum(s < 0 for s in signs), signs


def certify_brackets():
    checks = []
    for i, p in ((0, 0), (4, 2)):
        lo, hi = ENERGY_RATIONALS[i]
        count_lo, signs_lo = sturm_count_below(M, arb("0.5"), qball(lo))
        count_hi, signs_hi = sturm_count_below(M, arb(0), qball(hi))
        if count_lo != p or count_hi != p + 1:
            raise ArithmeticError(f"Sturm count mismatch for i={i}: {count_lo}, {count_hi}")
        checks.append({
            "mode": i,
            "eigenvalue_index": p,
            "lower_t": "1/2",
            "lower_rational": str(lo),
            "negative_pivots_below_lower": count_lo,
            "lower_pivot_signs": signs_lo,
            "upper_t": "0",
            "upper_rational": str(hi),
            "negative_pivots_below_upper": count_hi,
            "upper_pivot_signs": signs_hi,
        })
    return checks


def energy_midpoint(i):
    lo, hi = ENERGY_RATIONALS[i]
    return qball((lo + hi) / 2)


def source_recurrence(e):
    """Arb recurrence P_k(e), indexed for k=0..N, over a point or interval."""
    P = [arb(1)]
    for k in range(N):
        prev = P[k - 1] if k else arb(0)
        P.append(((e - diag(M, k))*P[k] - ell(M, k)*prev) / up(M, k))
    return P


def monomial_kernel(n, degree):
    """Exact finite Mellin monomial sum, enclosed by Arb/Acb."""
    L = arb(M).log()
    pi = arb.pi()
    s = acb(arb("0.5"), -2*pi*n/L)
    total = acb(0)
    for r in range(1, M + 1):
        rr = arb(r)
        r_to_minus_s = (-s * rr.log()).exp()
        compact_power = arb(fmpq(r, M))**degree
        total += (arb(M).sqrt()*r_to_minus_s - compact_power) / (s + degree)
    return (-L/4).exp() * total / L.sqrt()


def legendre_column(n, k):
    """Mellin transform of P_(2k), using its exact finite monomial expansion."""
    deg = 2*k
    total = acb(0)
    for j in range(k + 1):
        power = deg - 2*j
        numerator = (-1 if j % 2 else 1) * comb(deg, j) * comb(2*deg - 2*j, deg)
        coefficient = arb(fmpq(numerator, 2**deg))
        total += coefficient * monomial_kernel(n, power)
    return total


def source_F():
    """Full F matrix, rows n=-m..m and columns source k=1..6m-1."""
    return [[legendre_column(n, k) for k in range(1, N + 1)] for n in MODES]


def frobenius_upper(matrix):
    total = arb(0)
    for row in matrix:
        for value in row:
            magnitude_upper = value.abs_upper()
            total += magnitude_upper**2
    return total.sqrt()


def z_from_energies(F, e0, e4):
    P0, P4 = source_recurrence(e0), source_recurrence(e4)
    z = []
    for row in F:
        z.append(sum((row[k - 1] * ((-1)**k) * (P0[k] - P4[k])
                      for k in range(1, N + 1)), acb(0)))
    return z


def r6_bounds(i):
    """Uniform R6 absolute majorants for P, P', P'' over the energy ball."""
    E = source_energy_ball(i)
    R0, R1, R2 = [arb(1)], [arb(0)], [arb(0)]
    for k in range(N):
        D = (E - diag(M, k)).abs_upper()
        ell_abs, up_abs = abs(ell(M, k)), abs(up(M, k))
        prev0 = R0[k - 1] if k else arb(0)
        prev1 = R1[k - 1] if k else arb(0)
        prev2 = R2[k - 1] if k else arb(0)
        R0.append((D*R0[k] + ell_abs*prev0) / up_abs)
        R1.append((R0[k] + D*R1[k] + ell_abs*prev1) / up_abs)
        R2.append((2*R1[k] + D*R2[k] + ell_abs*prev2) / up_abs)
    return (R0, R1, R2)


def l2_upper(values):
    return sum((v**2 for v in values), arb(0)).sqrt()


def interval_halfwidth(i):
    lo, hi = ENERGY_RATIONALS[i]
    return qball((hi - lo) / 2)


def q_kernel(x, n, j, L):
    x = acb(x)
    pi = arb.pi()
    if n == j:
        omega = 2*pi*n/L
        return 2*(L - x)/L * (omega*x).cos()
    wn, wj = 2*pi*n/L, 2*pi*j/L
    return ((wj*x).sin() - (wn*x).sin()) / (pi*(n-j))


def wr_integrand(x, n, j, L):
    """Entire/meromorphic analytic continuation of the literal WR integrand."""
    x = acb(x)
    pi = arb.pi()
    imaginary_unit = acb(0, 1)
    sinhc = (imaginary_unit*x).sinc()
    if n != j:
        wn, wj = 2*pi*n/L, 2*pi*j/L
        return (-((x/2).exp()) * (((wn + wj)*x/2).cos())
                * (((wj - wn)*x/2).sinc()) / (L*sinhc))
    omega = 2*pi*n/L
    numerator = (arb("0.5")*(x/4).exp()*(imaginary_unit*x/4).sinc()
                 - (x/2).exp()*omega**2*x/2*(omega*x/2).sinc()**2
                 - (x/2).exp()*(omega*x).cos()/L)
    return numerator/sinhc


def von_mangoldt(k):
    """Exact von Mangoldt value for the small finite m=2 prime block."""
    p = 2
    while p*p <= k:
        if k % p == 0:
            power = p
            while power < k:
                power *= p
            return arb(p).log() if power == k else arb(0)
        p += 1
    return arb(k).log()


def source_K():
    """Literal full K= W02 - WR - Prime on modes -2..2, with Arb integrals."""
    L = arb(M).log()
    pi = arb.pi()
    euler = arb.const_euler()
    K = [[arb(0) for _ in MODES] for _ in MODES]
    for row, n in enumerate(MODES):
        for col in range(row, len(MODES)):
            j = MODES[col]
            w02 = (32*L*((L/4).sinh())**2
                   *(L**2 - 16*pi**2*j*n)
                   / ((L**2 + 16*pi**2*j**2)*(L**2 + 16*pi**2*n**2)))
            wr_integral = acb.integral(
                lambda x, analytic: wr_integrand(x, n, j, L),
                arb(0), L, rel_tol=arb("1e-65"), abs_tol=arb("1e-65"))
            if not wr_integral.imag.contains(0):
                raise ArithmeticError(f"WR integral not real for {(n,j)}: {wr_integral}")
            q0 = arb(2 if n == j else 0)
            wr_constant = (q0/2) * (euler + (4*pi*((L/2).tanh())).log())
            wr = wr_constant + wr_integral.real
            prime = arb(0)
            for k in range(2, M + 1):
                prime += von_mangoldt(k) / arb(k).sqrt() * q_kernel(arb(k).log(), n, j, L).real
            value = w02 - wr - prime
            K[row][col] = value
            K[col][row] = value
    return K


def gaussian_H(x):
    pi = arb.pi()
    return (24*pi*x**2 - 16*pi**2*x**4) * (-pi*x**2).exp()


def gaussian_H_prime(x):
    pi = arb.pi()
    polynomial = 24*pi*x**2 - 16*pi**2*x**4
    derivative = 48*pi*x - 64*pi**2*x**3
    return (derivative - 2*pi*x*polynomial) * (-pi*x**2).exp()


def gaussian_G_truncated(t, cutoff):
    t = acb(t)
    scale = (t/2).exp()
    u = t.exp()
    return scale * sum((gaussian_H(r*u) for r in range(1, cutoff + 1)), acb(0))


def gaussian_G_prime_truncated(t, cutoff):
    """Derivative in t of e^(t/2) sum H(r e^t), finite r cutoff."""
    t = acb(t)
    scale = (t/2).exp()
    u = t.exp()
    terms = []
    for r in range(1, cutoff + 1):
        x = r*u
        terms.append(arb("0.5")*gaussian_H(x) + x*gaussian_H_prime(x))
    return scale * sum(terms, acb(0))


def gaussian_plane(cutoff=12):
    """Q5 two-plane with certified omitted Gaussian tails."""
    L = arb(M).log()
    b = L/2
    pi = arb.pi()
    exp_step = (-pi*(2*cutoff + 3)/2).exp()
    tail_series = (-pi*(cutoff + 1)**2/2).exp() / (1 - exp_step)
    tail_G = 304 * (b/2).exp() * tail_series
    tail_Gprime = 8952 * (b/2).exp() * tail_series
    basis0, basis1 = [], []
    for n in MODES:
        omega = 2*pi*n/L
        integral = acb.integral(
            lambda t, analytic: gaussian_G_truncated(t, cutoff)*(omega*t).cos(),
            arb(0), b, rel_tol=arb("1e-65"), abs_tol=arb("1e-65"))
        if not integral.imag.contains(0):
            raise ArithmeticError(f"Gaussian coefficient integral not real for n={n}: {integral}")
        sign = 1 if n % 2 == 0 else -1
        b_trunc = sign * 2/L.sqrt() * integral.real
        b_error = L.sqrt() * tail_G
        basis0.append(b_trunc + arb(0, b_error))

        gp = gaussian_G_prime_truncated(b, cutoff)
        if not gp.imag.contains(0):
            raise ArithmeticError(f"Gaussian endpoint derivative not real for n={n}: {gp}")
        d_trunc = -(omega**2)*b_trunc + 2*gp.real/L.sqrt()
        d_error = omega**2*b_error + 2*tail_Gprime/L.sqrt()
        basis1.append(d_trunc + arb(0, d_error))

    # Invert the 2x2 Gram matrix explicitly; determinant separation certifies
    # the same rank-two plane used by Q5.
    g00 = sum((x*x for x in basis0), arb(0))
    g01 = sum((basis0[i]*basis1[i] for i in range(len(MODES))), arb(0))
    g11 = sum((x*x for x in basis1), arb(0))
    determinant = g00*g11 - g01*g01
    if determinant.lower() <= 0:
        raise ArithmeticError(f"Gaussian Gram determinant not separated from zero: {determinant}")
    inv00, inv01, inv11 = g11/determinant, -g01/determinant, g00/determinant
    V = [[basis0[i], basis1[i]] for i in range(len(MODES))]
    Pi = []
    for i in range(len(MODES)):
        row = []
        for j in range(len(MODES)):
            row.append(V[i][0]*inv00*V[j][0]
                       + V[i][0]*inv01*V[j][1]
                       + V[i][1]*inv01*V[j][0]
                       + V[i][1]*inv11*V[j][1])
        Pi.append(row)
    meta = {
        "cutoff": cutoff,
        "tail_series_upper": tail_series,
        "tail_G_upper": tail_G,
        "tail_Gprime_upper": tail_Gprime,
        "b_fourier_tail_radius_upper": L.sqrt()*tail_G,
        "gram_determinant": determinant,
    }
    return Pi, basis0, basis1, meta


def matvec(A, v):
    return [sum((A[i][j]*v[j] for j in range(len(v))),
                arb(0) if v and isinstance(v[0], arb) else acb(0))
            for i in range(len(A))]


def inner(u, v):
    return sum((u[i].conjugate()*v[i] for i in range(len(u))), acb(0))


def trace_product(Pi, K):
    # tr(Pi K Pi) = sum_ijk Pi[i,j] K[j,k] Pi[k,i].
    value = arb(0)
    for i in range(len(MODES)):
        for j in range(len(MODES)):
            for k in range(len(MODES)):
                value += Pi[i][j]*K[j][k]*Pi[k][i]
    return value


def full_r3(Pi, K, F, e0, e4):
    z = z_from_energies(F, e0, e4)
    p = matvec(Pi, z)
    X2c, Y2c = inner(z, z), inner(z, p)
    qz, qp = inner(z, matvec(K, z)), inner(p, matvec(K, p))
    theta = trace_product(Pi, K)
    for label, value in (("X2", X2c), ("Y2", Y2c), ("zKz", qz), ("pKp", qp)):
        if not value.imag.contains(0):
            raise ArithmeticError(f"quadratic form {label} has nonzero imaginary part: {value}")
    X2, Y2 = X2c.real, Y2c.real
    return Y2*(qz.real - theta*X2) + X2*qp.real, {
        "z": z, "p": p, "X2": X2, "Y2": Y2,
        "theta": theta, "qz": qz.real, "qp": qp.real,
    }


def certify_remainder(Pi, K, F, K_gamma, F_gamma):
    """Enclose R3 on the whole energy rectangle and both tail budgets."""
    e0, e4 = source_energy_ball(0), source_energy_ball(4)
    P_rect, rect_data = full_r3(Pi, K, F, e0, e4)
    c0, c4 = energy_midpoint(0), energy_midpoint(4)
    P_center, center_data = full_r3(Pi, K, F, c0, c4)
    if not P_rect.upper() < 0:
        raise ArithmeticError(f"direct whole-rectangle R3 is not strictly negative: {P_rect}")

    majorants = {i: r6_bounds(i) for i in (0, 4)}
    a = {i: interval_halfwidth(i) for i in (0, 4)}
    V, J = {}, {}
    for i in (0, 4):
        V[i] = F_gamma * l2_upper(majorants[i][1][1:])
        J[i] = F_gamma * l2_upper(majorants[i][2][1:])
    sensitivity = sum((a[i]*V[i] for i in (0, 4)), arb(0))
    Rbound = rect_data["X2"].sqrt() + sensitivity
    y_lower = center_data["Y2"].sqrt() - sensitivity
    if not y_lower.lower() > 0:
        raise ArithmeticError(f"projected norm lower bound is not positive: {y_lower}")

    tail_index = 5*M - 1
    Pcenter = {i: source_recurrence(energy_midpoint(i)) for i in (0, 4)}
    eta_sum = arb(0)
    for i in (0, 4):
        P_tail_abs = Pcenter[i][tail_index].abs_upper()
        P_tail_abs += a[i]*majorants[i][1][tail_index]
        eta_sum += P_tail_abs
    eta = (arb(M)*(arb(M).sqrt() - 1/arb(M).sqrt())).sqrt() * arb(2)**(-M) * eta_sum
    if not y_lower.lower() > eta.upper():
        raise ArithmeticError(f"required y_lower > eta_upper failed: y={y_lower}, eta={eta}")

    # The same accepted universal-norm remainder argument with ||K|| <= ||K||_F.
    # K_gamma and F_gamma are Arb enclosures; their upper endpoints are used
    # automatically by outward interval evaluation below.
    Bhat_F = (2*K_gamma*eta*(2*Rbound + eta)
              + 4*K_gamma*Rbound**2*eta/y_lower)
    remainder_F = Rbound**2 * Bhat_F
    margin_F = -P_rect - remainder_F

    L = arb(M).log()
    gamma_canonical = (2*arb(M).sqrt() + 4*arb(M).sqrt()*L + 9
                       + (20*arb.pi()*M + 20*M + 10)/L)
    Bhat_canonical = (2*gamma_canonical*eta*(2*Rbound + eta)
                      + 4*gamma_canonical*Rbound**2*eta/y_lower)
    remainder_canonical = Rbound**2 * Bhat_canonical
    margin_canonical = -P_rect - remainder_canonical

    return {
        "P_rect": P_rect,
        "P_center": P_center,
        "center_data": center_data,
        "rect_data": rect_data,
        "majorants": majorants,
        "V": V,
        "J": J,
        "sensitivity": sensitivity,
        "Rbound": Rbound,
        "y_lower": y_lower,
        "eta": eta,
        "K_gamma": K_gamma,
        "F_gamma": F_gamma,
        "Bhat_F": Bhat_F,
        "remainder_F": remainder_F,
        "margin_F": margin_F,
        "gamma_canonical": gamma_canonical,
        "Bhat_canonical": Bhat_canonical,
        "remainder_canonical": remainder_canonical,
        "margin_canonical": margin_canonical,
        "tail_index": tail_index,
    }


def _str(x):
    return str(x)


def run_certificate():
    brackets = certify_brackets()
    F = source_F()
    K = source_K()
    Pi, basis0, basis1, plane_meta = gaussian_plane(cutoff=12)
    K_gamma = frobenius_upper(K).upper()
    F_gamma = frobenius_upper(F)
    data = certify_remainder(Pi, K, F, K_gamma, F_gamma)
    margin_F = data["margin_F"]
    margin_canonical = data["margin_canonical"]
    sharp_pass = margin_F.lower() > 0
    canonical_pass = margin_canonical.lower() > 0
    result = {
        "status": ("FINITE_CELL_ALGEBRA_CERTIFICATE_SHARPENED_REMAINDER"
                   if sharp_pass else "FINITE_CELL_CERTIFICATE_NOT_CLOSED"),
        "m": M,
        "N": N,
        "precision_dps": ctx.dps,
        "energy_brackets": brackets,
        "intervals_exact_rational": {i: [str(x) for x in ENERGY_RATIONALS[i]] for i in (0, 4)},
        "F_rows_modes_n_minus_m_to_m_cols_k_1_to_N": [len(F), len(F[0])],
        "F_frobenius_upper": _str(F_gamma),
        "K_frobenius_upper": _str(K_gamma),
        "K_matrix_rows_modes_n_minus_m_to_m": len(K),
        "gaussian_plane": {
            "cutoff": plane_meta["cutoff"],
            "gram_determinant_interval": _str(plane_meta["gram_determinant"]),
            "tail_series_upper": _str(plane_meta["tail_series_upper"]),
            "G_tail_upper": _str(plane_meta["tail_G_upper"]),
            "Gprime_tail_upper": _str(plane_meta["tail_Gprime_upper"]),
        },
        "R3_rectangle_interval": _str(data["P_rect"]),
        "R3_rectangle_upper_strictly_negative": bool(data["P_rect"].upper() < 0),
        "R3_center_interval": _str(data["P_center"]),
        "norm_z_center_squared": _str(data["center_data"]["X2"]),
        "norm_Pi_z_center_squared": _str(data["center_data"]["Y2"]),
        "theta_interval": _str(data["center_data"]["theta"]),
        "R6_frobenius_sensitivity": _str(data["sensitivity"]),
        "R6_V0": _str(data["V"][0]),
        "R6_V4": _str(data["V"][4]),
        "R6_J0": _str(data["J"][0]),
        "R6_J4": _str(data["J"][4]),
        "R_upper": _str(data["Rbound"]),
        "y_lower": _str(data["y_lower"]),
        "eta_upper": _str(data["eta"]),
        "y_lower_gt_eta_upper": bool(data["y_lower"].lower() > data["eta"].upper()),
        "Bhat_Frob": _str(data["Bhat_F"]),
        "R2_Bhat_Frob": _str(data["remainder_F"]),
        "Frob_sharp_margin_interval": _str(margin_F),
        "Frob_sharp_margin_lower_positive": bool(sharp_pass),
        "canonical_Gamma": _str(data["gamma_canonical"]),
        "canonical_R2_Bhat": _str(data["remainder_canonical"]),
        "canonical_Gamma_margin_interval": _str(margin_canonical),
        "canonical_Gamma_test_passes": bool(canonical_pass),
        "scope": {
            "cofinal_or_selected_schedule_membership": "not established; m=2 is below the verdict's M0>=64 threshold",
            "source_tau_sign": "conditional only on applying the accepted source/tail identities at this finite cell",
            "canonical_R8_TEST": "not claimed; m=2 canonical Gamma budget is checked separately",
            "numeric_or_interval": "all displayed enclosures are Arb balls; strict comparisons use positive lower endpoints",
        },
    }
    return result


def main():
    ctx.dps = 100
    result = run_certificate()
    out = OUT / "arb_m2_certificate.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print(f"WROTE {out}")


if __name__ == "__main__":
    main()
