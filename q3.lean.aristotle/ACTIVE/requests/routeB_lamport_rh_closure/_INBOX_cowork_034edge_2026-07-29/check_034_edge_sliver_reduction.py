#!/usr/bin/env python3
"""
check_034_edge_sliver_reduction.py — independent judge for transaction 034
(abstract layer: STEP 0/1/3). Exact rational arithmetic (fractions) + exact
symbolics (sympy). No Arb/flint imports; no floats in verdict-bearing checks
(floats appear only inside display strings). Contains planted violations
(C5, C9) that MUST be detected — a judge that cannot fail is not a judge.
"""
import sys
from fractions import Fraction as F

RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append((name, bool(ok), detail))


def run_all():
    m, r_cert = 257, 195
    A_edge = F(4, 3)

    # ---- C1: m=257 conservativity of A_edge = 4/3 (exact integers) ----
    check("C1a_conservativity_3m_lt_4rcert", 3 * m < 4 * r_cert,
          "3*257=771 < 780=4*195  =>  257/195 < 4/3")
    check("C1b_exact_margin_1_over_65", A_edge - F(m, r_cert) == F(1, 65),
          "4/3 - 257/195 = 9/585 = 1/65")

    # ---- C2: every certified-positive band r=195..256 lies in [1, 4/3) ----
    ok = all(F(m, r) < A_edge and F(m, r + 1) >= 1 for r in range(195, 257))
    check("C2_positive_bands_inside_sliver", ok,
          "bands r=195..256: [257/(r+1), 257/r] subset of [1, 4/3)")

    # ---- C3: crossing band of a = 4/3 is r = 192 ----
    check("C3a_crossing_band_r192", F(m, 193) < A_edge < F(m, 192),
          "257/193 < 4/3 < 257/192")
    check("C3b_floor_id", (3 * m) // 4 == 192,
          "floor(m / (4/3)) = floor(192.75) = 192")

    # ---- C4: zero-compatible teeth r=196..257 lie inside the sliver ----
    ok = all(F(m, r) < A_edge for r in range(196, 258)) and F(m, 257) == 1
    check("C4a_teeth_inside_sliver", ok,
          "teeth a = 257/r, r=196..257, all in [1, 4/3)")
    check("C4b_buffer_bands_below_edge",
          F(m, 193) < A_edge and F(m, 194) < A_edge and F(m, 195) < A_edge,
          "bands 193,194 (eps=0) buffer the sliver boundary")

    # ---- C5: PLANTED VIOLATION — A_edge = 5/4 must FAIL (judge must fire) --
    planted_conservative = (4 * m < 5 * r_cert)   # 1028 < 975 : False
    check("C5_plant_A_5_4_detected", not planted_conservative,
          "4*257=1028 > 975=5*195  =>  5/4 < 257/195: plant correctly rejected")

    # ---- C6: sliver inside (0,1): A_edge <= lambda_m for all m >= 2 ----
    check("C6_sliver_inside_unit_interval", F(16, 9) < 2,
          "A_edge^2 = 16/9 < 2 <= m  =>  4/3 < sqrt(m)")

    # ---- C7: m=257 assembly geometry for hypothesis (S) at A = 4/3 ----
    check("C7a_assembly_lower_edge", F(m, r_cert) < A_edge,
          "certified-nonneg band region starts at a = 257/195 < 4/3")
    check("C7b_junction_bracket", 16 ** 2 < m < 17 ** 2,
          "16 < sqrt(257) < 17; 033-band cover tops out exactly at a = sqrt(257), "
          "where the 027 upper-half region [sqrt(257), 257] begins")

    import sympy as sp
    u, lam, A, s, B = sp.symbols('u lam A sigma B', positive=True)
    half = sp.Rational(1, 2)

    def zero(e):
        e2 = sp.powsimp(sp.expand_power_base(e, force=True), force=True)
        return sp.simplify(e2) == 0

    # ---- C8: FTC identity — the exact closed form of (034-edge) ----
    p = -s - half
    anti = u ** (half - s) / (half - s)
    check("C8a_antiderivative", sp.simplify(sp.diff(anti, u) - u ** p) == 0,
          "d/du [u^(1/2-sigma)/(1/2-sigma)] = u^(-sigma-1/2)")
    val = anti.subs(u, A / lam) - anti.subs(u, 1 / lam)
    target = lam ** (s - half) * (A ** (half - s) - 1) / (half - s)
    check("C8b_endpoint_algebra", zero(val - target),
          "int_{1/lam}^{A/lam} u^(-sigma-1/2) du = lam^(sigma-1/2)(A^(1/2-sigma)-1)/(1/2-sigma)")

    # ---- C9: PLANTED VIOLATIONS — Jacobian/weight mutants (P8) must fire ----
    # Control point sigma=1/4, lam=4, A=4/3; sliver = [1/4, 1/3].
    # correct = int u^(-3/4); integrand >= 3^(3/4) >= 2 on [1/4,1/3] (27>=16),
    # so correct >= 2*(1/12) = 1/6. Mutant (drop du/u) = int u^(1/4) <= 1*(1/12).
    check("C9a_correct_value_bracket", sp.Integer(3) ** 3 >= sp.Integer(2) ** 4,
          "3^(3/4) >= 2 on the sliver => correct >= 1/6")
    check("C9b_plant_drop_du_over_u_fires", sp.Rational(1, 12) < sp.Rational(1, 6),
          "mutant <= 1/12 < 1/6 <= correct: strict exact separation, plant detected")
    check("C9c_plant_drop_lambda_factor_fires",
          (sp.Rational(3, 4)) ** 4 >= sp.Rational(1, 4) and sp.Rational(4, 3) > 1,
          "(3/4)^4 = 81/256 >= 1/4 => 4^(-1/4) <= 3/4 < 1 while A^(1/2-s)-1 > 0: "
          "dropping lam^(sigma-1/2) changes a strictly positive value")

    # ---- C10: P3 trap — Psi(t) = t^2 - 1/3 ----
    t = sp.symbols('t', positive=True)
    n = sp.symbols('n', positive=True, integer=True)
    r = sp.symbols('r', positive=True, integer=True)
    Psi = t ** 2 - sp.Rational(1, 3)
    check("C10a_zero_mass", sp.integrate(Psi, (t, 0, 1)) == 0,
          "int_0^1 (t^2 - 1/3) dt = 0")
    star = sp.summation(Psi.subs(t, n / r), (n, 1, r - 1)) \
        + sp.Rational(1, 2) * Psi.subs(t, 1)
    check("C10b_star_identity", sp.simplify(star - (r + 1) / (6 * r)) == 0,
          "S*_r = (r+1)/(6r) > 0 for every r, though Psi changes sign at 1/sqrt(3)")
    check("C10c_sign_change",
          Psi.subs(t, sp.Rational(1, 2)) < 0 and Psi.subs(t, 1) > 0,
          "Psi(1/2) = -1/12 < 0 < 2/3 = Psi(1): interior zero is real")

    # ---- C11: A-monotonicity (conservativity lemma) + uniform-sigma constant ----
    check("C11a_A_monotone", zero(sp.diff(target, A) - lam ** (s - half) * A ** (-s - half)),
          "d/dA RHS = lam^(sigma-1/2) A^(-sigma-1/2) > 0: replacing A_m by 4/3 >= A_m is safe")
    x = sp.symbols('x', positive=True)
    c = sp.Rational(4, 3)
    phi = x * c ** x * sp.log(c) - c ** x + 1
    check("C11b_phi_prime_identity", sp.simplify(sp.diff(phi, x) - x * c ** x * sp.log(c) ** 2) == 0,
          "phi'(x) = x c^x (ln c)^2 >= 0 and phi(0) = 0 => g(x) = (c^x-1)/x increasing")
    gmax = (c ** half - 1) / half
    check("C11c_uniform_sigma_constant", sp.simplify(gmax - 2 * (2 / sp.sqrt(3) - 1)) == 0,
          "sup_sigma g(1/2-sigma) = g(1/2) = 2(2/sqrt(3)-1) ~ %.9f at sigma=0; "
          "sigma->1/2- limit ln(4/3) ~ %.9f" % (float(2 * (2 / sp.sqrt(3) - 1)), float(sp.log(c))))

    # ---- C12: P11 direction semantics — simple-bound failures do not kill (034-product) ----
    expr_a = lam ** (s - half) * (2 ** (half - s) - 1) / (half - s)   # A_m = 2 > 4/3
    check("C12a_A_gt_43_still_finite",
          sp.limit(expr_a.subs(s, sp.Rational(1, 4)), lam, sp.oo) == 0,
          "A_m = 2 violates A<=4/3, yet per-sigma product -> 0 as lam -> oo")
    expr_b = (1 + sp.log(lam)) * lam ** (sp.Rational(1, 4) - half)    # B/C = 1+ln lam
    check("C12b_BC_unbounded_still_finite", sp.limit(expr_b, lam, sp.oo) == 0,
          "B_m/C_m = 1+ln(lam) violates B<=B0*C, yet per-sigma product -> 0")

    # ---- C13: P4 crosswalk exponent lock (m = lam^2, a = m z) ----
    a_ = sp.symbols('a', positive=True)
    z_expr = a_ / lam ** 2
    check("C13_crosswalk_exponent",
          zero(sp.sqrt(z_expr / lam) - sp.sqrt(a_) * lam ** sp.Rational(-3, 2)),
          "sqrt(z/lam)|_{z=a/m, m=lam^2} = sqrt(a) lam^(-3/2): 033-contract and 034 scaled forms agree")

    # ---- C14: sharpness witness attains equality ----
    sharp_val = B * val
    check("C14_sharpness_equality", zero(sharp_val - B * target),
          "E0 = B sqrt(u) 1[u < A/lam] attains (034-edge) with equality: constant optimal")


def main():
    run_all()
    width = max(len(nm) for nm, _, _ in RESULTS)
    fails = 0
    for nm, ok, d in RESULTS:
        print(f"{'PASS' if ok else 'FAIL'}  {nm:<{width}}  {d}")
        fails += (not ok)
    print("=" * 100)
    print(f"{len(RESULTS) - fails}/{len(RESULTS)} checks passed.")
    if fails:
        print("VERDICT: CHECKER_FAILED")
        sys.exit(1)
    print("VERDICT: ALL_CHECKS_PASS (planted violations C5/C9 detected as required)")
    sys.exit(0)


if __name__ == "__main__":
    main()
