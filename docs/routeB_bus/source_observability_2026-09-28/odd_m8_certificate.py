#!/usr/bin/env python3
"""Arb certificate that the prescribed even trial separation fails at m=8.

Prediction saved before this script's certificate run: on the exact full
CCM matrix with modes -8,...,8 and the two full-window source columns
c(G), c(G''), U is about 6.02217e-15; an exact-rational odd vector obtained
by rounding the lowest numerical odd eigenvector has full-K Rayleigh value
about 3.33898e-17, hence a strict separation defect about -5.98878e-15.
This is one finite-cell counterexample to separation. It says nothing about
any eventual tail.

The source K and Gaussian plane routines are imported unchanged from
fokas_k_sign_2026-09-25/arb_m2_certificate.py. Their global M and MODES are
set to 8 and -8,...,8 before calling them. The candidate vector is generated
with full_center_probe.matrix_K, then frozen as exact decimal rationals for
the proof arithmetic. All final bounds use Arb K entries, Arb source-column
intervals, and the complete theta-tail enclosures, never the floating
eigenvalue.
"""
from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
REFERENCE_DIR = ROOT / "docs/routeB_bus/fokas_k_sign_2026-09-25"
REFERENCE = REFERENCE_DIR / "arb_m2_certificate.py"
FULL_CENTER = REFERENCE_DIR / "full_center_probe.py"
M = 8
MODES = tuple(range(-M, M + 1))
CUTOFF = 12
PRECISION_DPS = 90


def load_reference():
    spec = importlib.util.spec_from_file_location("arb_m2_certificate_ref", REFERENCE)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load reference module: {REFERENCE}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.M = M
    module.MODES = MODES
    return module


def load_full_center_probe():
    sys.path.insert(0, str(REFERENCE_DIR))
    spec = importlib.util.spec_from_file_location("full_center_probe_ref", FULL_CENTER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load candidate module: {FULL_CENTER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rational_candidate(full_center_probe):
    """Use mpmath only to find a vector; return exact rational coordinates."""
    import mpmath as mp

    mp.mp.dps = PRECISION_DPS
    K = full_center_probe.matrix_K(M)
    odd_embedding = mp.zeros(2 * M + 1, M)
    for n in range(1, M + 1):
        odd_embedding[M + n, n - 1] = 1
        odd_embedding[M - n, n - 1] = -1
    compressed = odd_embedding.T * K * odd_embedding
    eigenvalues, eigenvectors = mp.eigsy(compressed)
    candidate = eigenvectors[:, 0]
    if candidate[0] < 0:
        candidate = -candidate

    # Decimal rounding produces simple, finite denominators. This list is the
    # only contribution from the approximate eigenvector to the certificate.
    odd_coordinates = [
        Fraction(Decimal(mp.nstr(candidate[i], 45, min_fixed=-100, max_fixed=100)))
        for i in range(M)
    ]
    full_coordinates = [Fraction(0) for _ in MODES]
    for n, value in enumerate(odd_coordinates, start=1):
        full_coordinates[M + n] = value
        full_coordinates[M - n] = -value

    # The columns of odd_embedding have norm sqrt(2), so divide the small
    # eigenvalue by 2 to report the normalized odd Rayleigh quotient.
    approximate_rayleigh = eigenvalues[0] / 2
    return odd_coordinates, full_coordinates, mp.nstr(approximate_rayleigh, 35)


def bilinear(left, matrix, right):
    return sum(
        (left[i] * matrix[i][j] * right[j]
         for i in range(len(left)) for j in range(len(right))),
        arb(0),
    )


def ball_record(value):
    return {
        "interval": str(value),
        "lower_endpoint_enclosure": str(value.lower()),
        "upper_endpoint_enclosure": str(value.upper()),
    }


def verify_tail_majorants(ref):
    """Check the existing constants 304 and 8952 by a universal inequality."""
    pi = arb.pi()
    # With y=pi*x^2/2, h*(x)=(48y-64y^2)e^(-2y), and
    # (1/2)h*(x)+x h*'(x)=(120y-480y^2+256y^3)e^(-2y).
    # Since e^y >= y^k/k!, y^k e^-y <= k! for y>=0. Factoring one
    # e^-y out gives exact integer multipliers 48+64*2=176 and
    # 120+480*2+256*6=2616. Check these against the source constants.
    g_multiplier = 48 * 1 + 64 * 2
    derivative_multiplier = 120 * 1 + 480 * 2 + 256 * 6
    if not g_multiplier < 304:
        raise ArithmeticError(f"Gaussian G tail constant check failed: {g_multiplier}")
    if not derivative_multiplier < 8952:
        raise ArithmeticError(
            f"Gaussian G_t derivative tail constant check failed: {derivative_multiplier}"
        )

    # The source routine sums exp(-pi*r^2/2) for r>CUTOFF. Consecutive
    # ratios decrease, so the first ratio gives a geometric majorant.
    b = arb(M).log() / 2
    exp_step = (-pi * (2 * CUTOFF + 3) / 2).exp()
    tail_series = (-pi * (CUTOFF + 1) ** 2 / 2).exp() / (1 - exp_step)
    tail_G = 304 * (b / 2).exp() * tail_series
    tail_Gprime = 8952 * (b / 2).exp() * tail_series

    return {
        "variable": "y=pi*x^2/2 >= 0",
        "G_pointwise_majorant_derivation": "e^y>=y^k/k! gives |48y-64y^2|e^(-2y) <= (48*1!+64*2!)e^(-y)=176e^(-y) < 304e^(-y)",
        "G_t_derivative_pointwise_majorant_derivation": "e^y>=y^k/k! gives |120y-480y^2+256y^3|e^(-2y) <= (120*1!+480*2!+256*3!)e^(-y)=2616e^(-y) < 8952e^(-y)",
        "checked_integer_multipliers": {"G": g_multiplier, "G_t_derivative": derivative_multiplier},
        "valid_for_all_x_nonnegative": True,
        "window_b": ball_record(b),
        "theta_cutoff": CUTOFF,
        "first_geometric_ratio_upper": str(exp_step.upper()),
        "tail_series_upper": ball_record(tail_series),
        "G_tail_upper": ball_record(tail_G),
        "G_first_derivative_endpoint_theta_tail_upper": ball_record(tail_Gprime),
        "quadrature_requested_abs_tol": "1e-65",
        "quadrature_requested_rel_tol": "1e-65",
        "quadrature_method": "python-flint acb.integral (Arb ball enclosure)",
    }


def certify():
    ctx.dps = PRECISION_DPS
    ref = load_reference()
    full_center_probe = load_full_center_probe()
    odd_coordinates, witness, approximate_candidate_rayleigh = rational_candidate(full_center_probe)

    tail_data = verify_tail_majorants(ref)
    K = ref.source_K()
    Pi, basis0, basis1, plane_meta = ref.gaussian_plane(cutoff=CUTOFF)

    # The prescribed trial is range{c(G),c(G'')}. Compute its 2x2 generalized
    # Rayleigh data directly from the full-window columns and full K matrix.
    g00 = sum((x * x for x in basis0), arb(0))
    g01 = sum((basis0[i] * basis1[i] for i in range(len(MODES))), arb(0))
    g11 = sum((x * x for x in basis1), arb(0))
    gram_det = g00 * g11 - g01 * g01
    h00 = bilinear(basis0, K, basis0)
    h01 = bilinear(basis0, K, basis1)
    h11 = bilinear(basis1, K, basis1)
    h_det = h00 * h11 - h01 * h01
    trace_adjugate = h00 * g11 + h11 * g00 - 2 * h01 * g01
    discriminant = trace_adjugate**2 - 4 * gram_det * h_det

    if not gram_det.lower() > 0:
        raise ArithmeticError(f"source columns are not certified rank two: det={gram_det}")
    if not discriminant.lower() > 0:
        raise ArithmeticError(f"generalized eigenvalue discriminant not separated: {discriminant}")
    if not h_det.lower() > 0 or not trace_adjugate.lower() > 0:
        raise ArithmeticError(
            f"stable positive-root formula hypotheses fail: detH={h_det}, T={trace_adjugate}"
        )
    sqrt_discriminant = discriminant.sqrt()
    # Stable form of the smaller root of det(H-uG)=0. The ordinary
    # (T-sqrt(D))/(2 det(G)) expression would cancel two nearly equal balls.
    U = 2 * h_det / (trace_adjugate + sqrt_discriminant)

    witness_ball = [ref.qball(q) for q in witness]
    numerator = bilinear(witness_ball, K, witness_ball)
    denominator = sum((q * q for q in witness_ball), arb(0))
    if not denominator.lower() > 0:
        raise ArithmeticError("exact rational odd witness has zero norm")
    witness_rayleigh = numerator / denominator
    separation_margin = U.lower() - witness_rayleigh.upper()
    if not separation_margin.lower() > 0:
        raise ArithmeticError(
            "strict finite-cell separation defect not certified: "
            f"U={U}; witness={witness_rayleigh}; margin={separation_margin}"
        )

    source_files = [
        "q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean",
        "q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean",
    ]
    source_hashes = {
        path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for path in source_files
    }
    reference_hash = hashlib.sha256(REFERENCE.read_bytes()).hexdigest()
    evenness_reference = ROOT / "docs/routeB_bus/proshka/PROSHKA_GOAL058_FLOOR_KILL_INDEPENDENT_AUDIT_2026-09-25.md"

    result = {
        "status": "CERTIFIED_FINITE_M8_EVEN_TRIAL_SEPARATION_FAILURE",
        "scope": "single finite cell m=N=8; no eventual-tail conclusion",
        "repository_source_pin": "c256c6510e10a218dc65b68a7e373f246893ff55",
        "source_mode_order": list(MODES),
        "source_matrix_shape": [len(K), len(K[0])],
        "source_files_sha256": source_hashes,
        "arb_reference_file": str(REFERENCE.relative_to(ROOT)),
        "arb_reference_sha256": reference_hash,
        "precision_dps": ctx.dps,
        "gaussian_tail_validation": tail_data,
        "even_source_identity": {
            "status": "INHERITED_EXACT_SOURCE_IDENTITY",
            "identity": "Poisson summation and h*(0)=integral_R h*=0 give G(-t)=G(t); no finite partial theta sum is claimed even",
            "reference": "docs/routeB_bus/proshka/PROSHKA_GOAL058_FLOOR_KILL_INDEPENDENT_AUDIT_2026-09-25.md, lines 45-52",
            "reference_sha256": hashlib.sha256(evenness_reference.read_bytes()).hexdigest(),
        },
        "gaussian_plane": {
            "cutoff": CUTOFF,
            "gram_determinant": ball_record(gram_det),
            "source_r_G_column_norm_squared": ball_record(g00),
            "source_r_G_Gsecond_inner_product": ball_record(g01),
            "source_r_Gsecond_column_norm_squared": ball_record(g11),
            "existing_plane_gram_determinant": ball_record(plane_meta["gram_determinant"]),
            "certified_rank_two": True,
            "tail_series_upper": str(plane_meta["tail_series_upper"]),
            "G_tail_upper": str(plane_meta["tail_G_upper"]),
            "G_first_derivative_endpoint_theta_tail_upper": str(plane_meta["tail_Gprime_upper"]),
        },
        "generalized_even_trial": {
            "H00": ball_record(h00),
            "H01": ball_record(h01),
            "H11": ball_record(h11),
            "det_H": ball_record(h_det),
            "T=H00*G11+H11*G00-2*H01*G01": ball_record(trace_adjugate),
            "discriminant": ball_record(discriminant),
            "minimum_generalized_rayleigh_U": ball_record(U),
            "stable_formula": "2*det(H)/(T+sqrt(T^2-4*det(G)*det(H)))",
            "positive_rank_two_hypotheses_certified": True,
        },
        "odd_witness": {
            "construction": "odd_embedding x[-n]=-q_n, x[n]=q_n, x[0]=0; q is the 45-digit decimal rationalization of the lowest eigenvector of full_center_probe.matrix_K(8) restricted to the odd subspace",
            "candidate_floating_rayleigh_used_only_for_selection": approximate_candidate_rayleigh,
            "odd_coordinates_q_n_exact_rational": [str(q) for q in odd_coordinates],
            "full_vector_modes_minus8_to8_exact_rational": [str(q) for q in witness],
            "full_K_quadratic_numerator": ball_record(numerator),
            "exact_norm_squared": ball_record(denominator),
            "full_K_rayleigh": ball_record(witness_rayleigh),
        },
        "strict_comparison": {
            "U_lower_endpoint_enclosure": str(U.lower()),
            "witness_rayleigh_upper_endpoint_enclosure": str(witness_rayleigh.upper()),
            "positive_gap_lower_enclosure": ball_record(separation_margin),
            "certified": True,
        },
        "interpretation": "At this finite cell, an exact odd rational vector has full-source K Rayleigh quotient strictly below the minimum Rayleigh quotient on span{c(G),c(G'')}. This refutes separation by this chosen even trial at m=8 only; it does not refute any eventual-tail claim.",
    }
    return result


def main():
    result = certify()
    text = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    output = HERE / "odd_m8_certificate.json"
    output.write_text(text, encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "m": M,
        "U": result["generalized_even_trial"]["minimum_generalized_rayleigh_U"]["interval"],
        "odd_rayleigh": result["odd_witness"]["full_K_rayleigh"]["interval"],
        "positive_gap_lower": result["strict_comparison"]["positive_gap_lower_enclosure"]["interval"],
        "json": str(output.relative_to(ROOT)),
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
