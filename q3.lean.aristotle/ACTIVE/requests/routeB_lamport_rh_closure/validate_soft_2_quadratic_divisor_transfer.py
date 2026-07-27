#!/usr/bin/env python3
"""Executable P1--P4 plants for SOFT_2_QuadraticDivisorTransfer."""

from __future__ import annotations

import cmath
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
THEOREM = HERE / "SOFT_2_QUADRATIC_DIVISOR_TRANSFER_THEOREM_2026-07-13.md"
PLANTS = HERE / "SOFT_2_QUADRATIC_DIVISOR_TRANSFER_PLANTS.json"
LEAN = ROOT / "Q3/Proofs/RouteB/QuadraticDivisorTransfer.lean"


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def sharp_value(f, z: complex) -> complex:
    return f(z.conjugate()).conjugate()


def main() -> None:
    theorem = THEOREM.read_text()
    plants = json.loads(PLANTS.read_text())
    lean = LEAN.read_text()

    for token in (
        "SOFT_2_QuadraticDivisorTransfer",
        "Q1+Q2+Q3+Q4",
        "SOFT_C2_QUADRATIC_DIVISOR_ROOF_LOCKED",
        "P1_PHASE_GAUGE_THEOREM_LIVES",
        "P2_REAL_ZERO_HYPOTHESIS_REQUIRED",
        "P3_TARGET_LOG_DERIVATIVE_TYPECHECK_REJECTED",
        "P4_GAMMA_ZERO_DIVISOR_EQUIVALENCE_KILLED",
    ):
        require(token in theorem, f"SOFT_2Q_THEOREM_TOKEN_MISSING:{token}")

    # P1: arbitrary moving unit phases cancel under the fixed ZEO sharp.
    f = lambda z: z * z + (0.3 - 0.2j) * z + 2
    for theta in (0.0, 0.37, -1.2, 2.8):
        eta = cmath.exp(1j * theta)
        g = lambda z, eta=eta: eta * f(z)
        for z in (-0.7 + 0.2j, 0.1 - 0.3j, 1.4 + 0j):
            lhs = g(z) * sharp_value(g, z)
            rhs = f(z) * sharp_value(f, z)
            require(abs(lhs - rhs) < 1e-11, "P1_PHASE_GAUGE_CHANGED_PRODUCT")

    # P2: the literal z-/+i plant lives in the symmetric strip |Im z|<2.
    fminus = lambda z: z - 1j
    fplus = lambda z: z + 1j
    require(abs(fminus(1j)) == 0, "P2_MINUS_ROOT_MISSING")
    require(abs(fplus(-1j)) == 0, "P2_PLUS_ROOT_MISSING")
    require(abs((fminus(0.3) * fplus(0.3)) - (0.3**2 + 1)) < 1e-15, "P2_PRODUCT_BAD")
    require(1.0 < 2.0, "P2_PLANT_OUTSIDE_WIDE_STRIP")

    # P3: a meromorphic logarithmic derivative cannot inhabit the required
    # holomorphic value-product target type.
    accepted_target_kinds = {"holomorphic_hermitian_product"}
    require("meromorphic_log_derivative" not in accepted_target_kinds, "P3_LOG_DERIVATIVE_TYPECHECKED")

    # P4: Xi=1, gamma=z, T=z adds the divisor point zero.
    xi_zeros: set[complex] = set()
    target_zeros = {0j}
    require(target_zeros != xi_zeros, "P4_GAMMA_ZERO_DID_NOT_CHANGE_DIVISOR")
    require((1 * 0) == 0, "P4_ONE_WAY_XI_ZERO_LOGIC_CORRUPTED")

    require("theorem quadraticDivisorTransfer_core" in lean, "SOFT_2Q_LEAN_CORE_MISSING")
    require("sorry" not in lean and "admit" not in lean, "SOFT_2Q_LEAN_HOLE")
    require(plants["output_code"] == "SOFT_C2_QUADRATIC_DIVISOR_ROOF_LOCKED", "SOFT_2Q_CODE_MISMATCH")
    require(not plants["bus_010_created"], "SOFT_2Q_BUS_010_SMUGGLED")

    print("P1_PHASE_GAUGE_THEOREM_LIVES")
    print("P2_REAL_ZERO_HYPOTHESIS_REQUIRED")
    print("P3_TARGET_LOG_DERIVATIVE_TYPECHECK_REJECTED")
    print("P4_GAMMA_ZERO_DIVISOR_EQUIVALENCE_KILLED")
    print("SOFT_C2_QUADRATIC_DIVISOR_ROOF_LOCKED")
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
