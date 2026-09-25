#!/usr/bin/env python3
"""Arb certificate of one negative m=8 central-trial complement direction.

This is a finite pointwise certificate at two explicitly rational source
energies. It does not certify spectral-root membership, selected-tail
applicability, a family statement, or Goal058 tracking.
"""
from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path

from flint import acb, arb, ctx

PACKET = Path(__file__).resolve().parent
HELPER_PATH = PACKET / "arb_m2_certificate.py"
WITNESS_JSON = PACKET / "schur_probe_m8_dps140.json"
M = 8
N = 6*M - 1
MODES = tuple(range(-M, M + 1))

# 145-significant-digit rational decimal inputs: rounded midpoint of the
# numerical m=8 Jacobi brackets. These are fixed point inputs, not certified
# eigenvalues or claims that the bracket midpoint is an exact source root.
E0_DECIMAL = "49.51165583794277442001335055057766789377897572006239563282885756485940071854646980898054686747605331896719188279965416713151980971369805907819338"
E4_DECIMAL = "441.3634596445877046681289270141033676452071666239670224088369817582924661773825111488519989051554903786536291453619175883221276920219445773258134"


def load_arb_helper():
    spec = importlib.util.spec_from_file_location("m8_arb_helpers", HELPER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load interval helper at {HELPER_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    # Explicit parameterization of the read-only m=2 helper's module globals.
    module.M = M
    module.N = N
    module.MODES = MODES
    module.ENERGY_RATIONALS = {
        0: (Fraction(E0_DECIMAL), Fraction(E0_DECIMAL)),
        4: (Fraction(E4_DECIMAL), Fraction(E4_DECIMAL)),
    }
    return module


H = load_arb_helper()


def exact_decimal_ball(value: str) -> arb:
    return H.qball(Fraction(Decimal(value)))


def build_source_state(dps: int = 100):
    """Build and return the m=8 full Arb K, normalized Acb q, and real Arb a.

    Also returns source intermediates for the local finite-witness certificate.
    The parent task can reuse build_data(dps) to obtain exactly (K,q,a).
    """
    ctx.dps = dps
    H.ctx.dps = dps
    e0, e4 = exact_decimal_ball(E0_DECIMAL), exact_decimal_ball(E4_DECIMAL)
    F = H.source_F()
    z = H.z_from_energies(F, e0, e4)
    z_norm2 = H.inner(z, z)
    if not z_norm2.imag.contains(0) or z_norm2.real.lower() <= 0:
        raise ArithmeticError(f"source norm squared not certified positive real: {z_norm2}")
    qnorm = z_norm2.real.sqrt()
    q = [zi / qnorm for zi in z]
    K = H.source_K()
    Kq = H.matvec(K, q)
    a_complex = H.inner(q, Kq)
    if not a_complex.imag.contains(0):
        raise ArithmeticError(f"q*K*q not certified real: {a_complex}")
    a = a_complex.real
    return {
        "K": K,
        "q": q,
        "a": a,
        "z": z,
        "F": F,
        "e0": e0,
        "e4": e4,
        "z_norm2": z_norm2.real,
        "q_norm2": H.inner(q, q).real,
        "a_complex": a_complex,
    }


def build_data(dps: int = 100):
    """Reusable root interface: return full Arb K, normalized Acb q, and Arb a."""
    state = build_source_state(dps)
    return state["K"], state["q"], state["a"]


def acb_from_decimal_pair(pair):
    return acb(exact_decimal_ball(pair[0]), exact_decimal_ball(pair[1]))


def load_rationalized_witness():
    raw = json.loads(WITNESS_JSON.read_text())
    coords = raw["complement"]["minimum_eigenvector_qperp_witness_by_mode_real_imag"]
    if len(coords) != len(MODES):
        raise ValueError(f"witness length {len(coords)} != mode count {len(MODES)}")
    # The JSON decimal strings are converted to exact Fractions before Arb.
    return [acb_from_decimal_pair(pair) for pair in coords], coords


def midpoint_fmt(x, digits=80):
    return arb(x).str(digits=digits)


def run_certificate(dps: int = 100):
    state = build_source_state(dps)
    K, q, a = state["K"], state["q"], state["a"]
    w, witness_decimals = load_rationalized_witness()
    qstarw = H.inner(q, w)
    y = [w[i] - q[i]*qstarw for i in range(len(MODES))]
    qstary = H.inner(q, y)
    ynorm2 = H.inner(y, y)
    if not qstary.contains(0):
        raise ArithmeticError(f"projected witness orthogonality does not enclose zero: {qstary}")
    if not ynorm2.imag.contains(0) or ynorm2.real.lower() <= 0:
        raise ArithmeticError(f"projected witness norm squared not positive real: {ynorm2}")

    Ay = []
    for i in range(len(MODES)):
        row_value = sum((acb(K[i][j]) * y[j] for j in range(len(MODES))), acb(0))
        Ay.append(row_value - acb(a)*y[i])
    qform = H.inner(y, Ay)
    if not qform.imag.contains(0):
        raise ArithmeticError(f"Hermitian witness form not certified real: {qform}")
    rayleigh = qform.real / ynorm2.real
    margin = -qform.real
    rayleigh_margin = -rayleigh
    if not margin.lower() > 0 or not rayleigh_margin.lower() > 0:
        raise ArithmeticError(f"negative witness margin not certified: form={qform}, rayleigh={rayleigh}")

    K_strings = [[str(entry) for entry in row] for row in K]
    z_strings = [str(value) for value in state["z"]]
    q_strings = [str(value) for value in q]
    y_strings = [str(value) for value in y]
    witness_sha = hashlib.sha256(WITNESS_JSON.read_bytes()).hexdigest()
    helper_sha = hashlib.sha256(HELPER_PATH.read_bytes()).hexdigest()

    result = {
        "status": "CERTIFIED_FINITE_RATIONAL_CENTER_NEGATIVE_COMPLEMENT_WITNESS",
        "precision_decimal_digits": dps,
        "scope": {
            "operator": "literal full m=8 K=W02-WR-Prime on modes n=-8..8",
            "energy_inputs": "fixed exact rational decimals given below; numerical bracket-midpoint provenance only",
            "claim": "the projected nonzero y lies in q-perp and has y*(K-aI)y strictly negative at this rational center",
            "not_claimed": [
                "that either rational energy equals an exact Jacobi eigenvalue",
                "selected Ferrers schedule membership or m>=M0 source applicability",
                "any source-family or cofinal conclusion",
                "the Goal058 ground/tracking theorem",
            ],
        },
        "source_inputs": {
            "m": M,
            "N": N,
            "modes": list(MODES),
            "E0_exact_rational_decimal": E0_DECIMAL,
            "E4_exact_rational_decimal": E4_DECIMAL,
            "E0_arb": str(state["e0"]),
            "E4_arb": str(state["e4"]),
            "z_norm_squared_arb": str(state["z_norm2"]),
            "q_norm_squared_arb": str(state["q_norm2"]),
            "a_qKq_arb": str(a),
            "a_imaginary_part_arb": str(state["a_complex"].imag),
            "z_complex_entries_arb": z_strings,
            "q_complex_entries_arb": q_strings,
        },
        "witness": {
            "source_json": WITNESS_JSON.name,
            "source_json_sha256": witness_sha,
            "source_description": "lowest m=8 eigenvector of the numerical q-perpendicular compression, rounded componentwise to the exact decimal rationals shown",
            "rationalized_w_complex_decimal_components": witness_decimals,
            "qstarw_arb": str(qstarw),
            "y_definition": "y=w-q*(q*w)",
            "qstary_arb_contains_zero": qstary.contains(0),
            "qstary_arb": str(qstary),
            "y_norm_squared_arb": str(ynorm2.real),
            "y_norm_squared_lower_positive": bool(ynorm2.real.lower() > 0),
            "y_complex_entries_arb": y_strings,
        },
        "operator_and_form": {
            "K_arb_matrix": K_strings,
            "quadrature": "python-flint acb.integral with helper rel_tol=abs_tol=1e-65 for every WR entry; all K entries are Arb balls",
            "finite_prime_range": "k=2..8, exact von Mangoldt selection and Arb logarithms",
            "witness_form_y_star_K_minus_aI_y_arb": str(qform.real),
            "witness_form_upper_strictly_negative": bool(qform.real.upper() < 0),
            "strict_negative_margin_minus_form_arb": str(margin),
            "strict_negative_margin_lower_positive": bool(margin.lower() > 0),
            "normalized_witness_rayleigh_arb": str(rayleigh),
            "normalized_rayleigh_upper_strictly_negative": bool(rayleigh.upper() < 0),
            "normalized_negative_margin_minus_rayleigh_arb": str(rayleigh_margin),
            "normalized_negative_margin_lower_positive": bool(rayleigh_margin.lower() > 0),
        },
        "helper_sha256": helper_sha,
    }
    return result


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", type=int, default=100)
    args = parser.parse_args()
    result = run_certificate(args.dps)
    output = PACKET / f"m8_negative_certificate_dps{args.dps}.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print(f"WROTE {output}")


if __name__ == "__main__":
    main()
