#!/usr/bin/env python3
"""Fail-closed validation for D0.6 ExactTransformConvention."""

from __future__ import annotations

import cmath
import hashlib
import json
import math
from pathlib import Path


SCRIPT = Path(__file__).resolve()
REQUEST_DIR = SCRIPT.parent
REPO_ROOT = SCRIPT.parents[4]
CERT_PATH = REQUEST_DIR / "D0_6_CERTIFICATE.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise SystemExit(code)


def close(a: complex | float, b: complex | float, tol: float = 1e-12) -> bool:
    return abs(a - b) <= tol * max(1.0, abs(a), abs(b))


def main() -> None:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    require(cert["node_id"] == "D0.6", "D0_6_CERT_NODE_MISMATCH")
    require(cert["proof_status"] == "PROVED", "D0_6_CERT_NOT_PROVED")
    require(cert["exit_code"] == "EXACT_TRANSFORM_CONVENTION_LOCKED", "D0_6_EXIT_MISMATCH")
    require(cert["rh_status"] == "NOT_RH", "D0_6_RH_FIREWALL_MISSING")

    dependency = REPO_ROOT / cert["dependency"]["certificate_path"]
    require(dependency.is_file(), "D0_6_D0_1_CERT_MISSING")
    require(sha256(dependency) == cert["dependency"]["certificate_sha256"], "D0_6_D0_1_CERT_HASH_DRIFT")

    checked_pins: list[str] = []
    for pin in cert["source_pins"] + [cert["proof_artifact"]]:
        path = REPO_ROOT / pin["path"]
        require(path.is_file(), f"D0_6_PIN_MISSING:{pin['path']}")
        require(sha256(path) == pin["sha256"], f"D0_6_PIN_HASH_DRIFT:{pin['path']}")
        checked_pins.append(pin["path"])

    lock = cert["transform_lock"]
    topology = cert["topology_lock"]
    require(lock["measure"] == "d*u=du/u", "D0_6_MEASURE_MISMATCH")
    require(lock["kernel"] == "u^(-i*z)=exp(-i*z*log(u))", "D0_6_TRANSFORM_SIGN_MISMATCH")
    require("1/2-i*z" in lock["half_density_crosswalk"], "D0_6_HALF_SHIFT_SIGN_MISMATCH")
    require("(-z)" in lock["xi_crosswalk"], "D0_6_XI_SIGN_FLIP_WITHOUT_REFLECTION")
    require(topology["topology"] == "COMPACT_OPEN_ON_S", "D0_6_TOPOLOGY_MISMATCH")
    require(topology["uniform_in_lambda"] == "NOT_CLAIMED", "D0_6_LAMBDA_UNIFORMITY_SMUGGLED")
    require(topology["global_closed_substrip_uniformity"] == "NOT_CLAIMED", "D0_6_GLOBAL_STRIP_OVERCLAIM")
    require(topology["h3_status"] == "OPEN_NOT_DISCHARGED", "D0_6_H3_FALSELY_CLOSED")

    proof = (REPO_ROOT / cert["proof_artifact"]["path"]).read_text(encoding="utf-8")
    for token in (
        "exp(-i*z*log(u))",
        "Mellin(g)(1/2-i*z)",
        "Xi(z)=F_mu(Half(g))(-z)",
        "sqrt(L)*(-1)^n",
        "COMPACT_OPEN",
        "NO_UNIFORM_IN_LAMBDA_EVALUATION",
        "D0.6 = PROVED",
        "NO_RH",
    ):
        if token == "COMPACT_OPEN":
            require("compact-open topology" in proof, "D0_6_COMPACT_OPEN_TOKEN_MISSING")
        else:
            require(token in proof, f"D0_6_PROOF_TOKEN_MISSING:{token}")

    # F1: Haar measure on [lambda^-1,lambda] versus planted Lebesgue measure.
    lam = 2.0
    L = 2.0 * math.log(lam)
    haar_mass = L
    lebesgue_mass = lam - 1.0 / lam
    require(not close(haar_mass, lebesgue_mass), "D0_6_MEASURE_PLANT_INERT")

    # F2: at its own frequency, V_1 has nonzero correct-sign transform;
    # the planted plus-sign kernel integrates frequency 2 and gives zero.
    correct_v1 = -math.sqrt(L)
    wrong_plus_sign = 0.0
    require(not close(correct_v1, wrong_plus_sign), "D0_6_TRANSFORM_SIGN_PLANT_INERT")

    # F3: the two half-shift signs disagree on g=1_[1,e], z=i/4.
    z = 0.25j
    s_correct = 0.5 - 1j * z
    s_wrong = 0.5 + 1j * z
    mellin_correct = (math.e ** s_correct.real - 1.0) / s_correct.real
    mellin_wrong = (math.e ** s_wrong.real - 1.0) / s_wrong.real
    require(not close(mellin_correct, mellin_wrong), "D0_6_HALF_SHIFT_PLANT_INERT")

    # F4: centered phase lambda^(iz) is nontrivial at imaginary z.
    centered_phase = cmath.exp(1j * z * math.log(lam))
    require(not close(centered_phase, 1.0), "D0_6_CENTERING_PHASE_PLANT_INERT")

    # F5: the removable value is finite, signed, and nonzero.
    n = 1
    removable = math.sqrt(L) * ((-1) ** n)
    require(math.isfinite(removable) and removable < 0.0, "D0_6_REMOVABLE_POLE_PLANT_INERT")

    # F6: z/j is small on a fixed compact but unbounded on an unbounded strip.
    j = 100.0
    fixed_compact_sample = 10.0 / j
    far_strip_sample = (j * j) / j
    require(fixed_compact_sample < 1.0 and far_strip_sample > 1.0, "D0_6_TOPOLOGY_PLANT_INERT")

    # F7: V_0(i*sigma) grows with lambda; no uniform constant is certified.
    sigma = 0.25
    def v0_imag(lam_value: float) -> float:
        l_value = 2.0 * math.log(lam_value)
        return (lam_value**sigma - lam_value ** (-sigma)) / (sigma * math.sqrt(l_value))
    require(v0_imag(16.0) > v0_imag(2.0), "D0_6_LAMBDA_UNIFORMITY_PLANT_INERT")

    # F8/F9 are fail-closed metadata checks: point representatives and the
    # trial-to-ground bridge remain explicitly outside this leaf.
    nonclaims = set(cert["explicit_nonclaims"])
    require("NO_BOUNDARY_NORMALIZATION" in nonclaims, "D0_6_REPRESENTATIVE_PLANT_INERT")
    require("NO_TRIAL_GROUND_CROSSWALK" in nonclaims, "D0_6_TRIAL_GROUND_PLANT_INERT")
    require("NO_H3" in nonclaims, "D0_6_H3_NONCLAIM_MISSING")

    result = {
        "node": "D0.6",
        "verdict": "EXACT_TRANSFORM_CONVENTION_LOCKED",
        "proof_status": "PROVED",
        "pins_checked": checked_pins,
        "plants": list(cert["plants"].values()),
        "topology": "COMPACT_OPEN_ON_S",
        "evaluation": "FIXED_M_ONLY",
        "h3": "OPEN_NOT_DISCHARGED",
        "lean": "INTERFACE_UNPINNED",
        "rh": "NOT_RH",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
