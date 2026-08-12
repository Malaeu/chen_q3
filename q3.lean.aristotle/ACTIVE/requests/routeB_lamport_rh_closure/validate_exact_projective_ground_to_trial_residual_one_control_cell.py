#!/usr/bin/env python3
"""Independent fail-closed validation of the (13,120) projective measurement."""

from __future__ import annotations

import hashlib
import json
from decimal import Decimal, localcontext
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
SOURCE_DIR = HERE.parent / "routeB_twolevel_spectral_ladder" / "out"
TRIAL_SOURCE = SOURCE_DIR / "portable_k_coeffs_lambda_sq_13_N_120.json"
GROUND_SOURCE = SOURCE_DIR / "nconv_anchor_lambda_sq_13_N_120.json"
RESULT = HERE / "EXACT_PROJECTIVE_GROUND_TO_TRIAL_RESIDUAL_ONE_CONTROL_CELL.json"
EXPECTED_TRIAL_SHA = "0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88"
EXPECTED_GROUND_SHA = "cbc556ef7c73c9aefa9f177bb59aeca5867ed6628e3f1cca6edb270bfc13e7f0"
RESULT_TOLERANCE = Decimal("1e-75")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise SystemExit(f"VALIDATE_EXACT_PROJECTIVE_ONE_CONTROL_CELL: FAIL: {message}")


def rows_by_n(rows: list[dict[str, Any]]) -> dict[int, tuple[Decimal, Decimal]]:
    result: dict[int, tuple[Decimal, Decimal]] = {}
    for row in rows:
        n = int(row["n"])
        if n in result:
            fail(f"duplicate coordinate {n}")
        result[n] = Decimal(str(row["re"])), Decimal(str(row["im"]))
    return result


def close(label: str, actual: Decimal, recorded: str) -> None:
    target = Decimal(recorded)
    scale = max(Decimal(1), abs(actual), abs(target))
    if abs(actual - target) > RESULT_TOLERANCE * scale:
        fail(f"{label} mismatch: recomputed={actual} recorded={target}")


def main() -> int:
    if sha256(TRIAL_SOURCE) != EXPECTED_TRIAL_SHA:
        fail("trial SHA-256 drift")
    if sha256(GROUND_SOURCE) != EXPECTED_GROUND_SHA:
        fail("ground SHA-256 drift")

    trial_payload = json.loads(TRIAL_SOURCE.read_text(encoding="utf-8"))
    ground_payload = json.loads(GROUND_SOURCE.read_text(encoding="utf-8"))
    result = json.loads(RESULT.read_text(encoding="utf-8"))

    if result.get("evidence_class") != ["FINITE_CELL", "CONDITIONAL"]:
        fail("evidence class drift")
    if result.get("outcome") != "MEASURED_FINITE_CELL_CONDITIONAL_NOT_PROMOTING":
        fail("outcome drift")
    if result.get("cell") != {"lambda_sq": 13, "N": 120, "coordinate_count": 241}:
        fail("result cell drift")
    if result.get("knowledge_preflight", {}).get("outcome") != "NO_HITS":
        fail("knowledge preflight receipt missing")
    if result.get("source_lock") != {
        "trial": {
            "path": "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/portable_k_coeffs_lambda_sq_13_N_120.json",
            "expected_sha256": EXPECTED_TRIAL_SHA,
            "actual_sha256": EXPECTED_TRIAL_SHA,
            "sha256_match": True,
            "selector": "coefficients; logical_vector=k1",
        },
        "ground": {
            "path": "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/nconv_anchor_lambda_sq_13_N_120.json",
            "expected_sha256": EXPECTED_GROUND_SHA,
            "actual_sha256": EXPECTED_GROUND_SHA,
            "sha256_match": True,
            "selector": "xi_m_y_cache[0].xi_vector; name=xi1",
        },
    }:
        fail("recorded source lock drift")
    if result.get("spectral_residual_and_gap") != {
        "status": "NO_PERSISTED_MFIN_MATVEC",
        "matrix_residual": "NOT_MEASURED",
        "spectral_gap": "NOT_MEASURED",
        "reason": "the two source-locked packets do not persist a canonical Mfin matvec; eigenpair-cache metadata is not a replacement",
    }:
        fail("spectral non-measurement guard drift")
    if result.get("non_claims") != [
        "not a theorem",
        "not a cofinal estimate",
        "not a Route B closure",
        "not an RH claim",
    ]:
        fail("non-claim boundary drift")

    trial = rows_by_n(trial_payload["coefficients"])
    ground = rows_by_n(ground_payload["xi_m_y_cache"][0]["xi_vector"])
    expected = set(range(-120, 121))
    if set(trial) != expected or set(ground) != expected:
        fail("coordinate support drift")
    if trial_payload.get("logical_vector") != "k1":
        fail("trial selector drift")
    if ground_payload["xi_m_y_cache"][0].get("name") != "xi1":
        fail("ground selector drift")

    # This validation independently recomputes the Gram-determinant formula,
    # rather than importing the generator or its direct-residual routine.
    with localcontext() as context:
        context.prec = 170
        trial_norm_sq = sum(a * a + b * b for a, b in trial.values())
        ground_norm_sq = sum(a * a + b * b for a, b in ground.values())
        dot_re = sum(
            trial[n][0] * ground[n][0] + trial[n][1] * ground[n][1]
            for n in expected
        )
        dot_im = sum(
            trial[n][0] * ground[n][1] - trial[n][1] * ground[n][0]
            for n in expected
        )
        overlap_sq = (dot_re * dot_re + dot_im * dot_im) / (
            trial_norm_sq * ground_norm_sq
        )
        if not Decimal(0) <= overlap_sq <= Decimal(1):
            fail("recomputed overlap outside [0,1]")
        overlap_abs = overlap_sq.sqrt()
        defect = Decimal(1) - overlap_sq
        distance = defect.sqrt()
        phase_distance = (Decimal(2) - Decimal(2) * overlap_abs).sqrt()
        best_scalar_re = dot_re / trial_norm_sq
        best_scalar_im = dot_im / trial_norm_sq
        normalized_inner_scale = (trial_norm_sq * ground_norm_sq).sqrt()
        normalized_inner_re = dot_re / normalized_inner_scale
        normalized_inner_im = dot_im / normalized_inner_scale

        recorded = result["measurement"]
        close("trial norm", trial_norm_sq.sqrt(), recorded["trial_norm"])
        close("ground norm", ground_norm_sq.sqrt(), recorded["ground_norm"])
        close(
            "normalized inner re",
            normalized_inner_re,
            recorded["normalized_inner_product"]["re"],
        )
        close(
            "normalized inner im",
            normalized_inner_im,
            recorded["normalized_inner_product"]["im"],
        )
        close("overlap abs", overlap_abs, recorded["normalized_overlap_abs"])
        close("overlap abs squared", overlap_sq, recorded["normalized_overlap_abs_squared"])
        close("projective defect", defect, recorded["projective_defect"])
        close("projective distance", distance, recorded["inf_c_nonzero_relative_distance"])
        close("phase distance", phase_distance, recorded["phase_aligned_unit_distance"])
        close("best scalar re", best_scalar_re, recorded["best_scalar_raw"]["re"])
        close("best scalar im", best_scalar_im, recorded["best_scalar_raw"]["im"])

        guard = result["guarded_checks"]
        close(
            "direct/formula projection identity",
            defect,
            guard["direct_projection_residual_squared_relative"],
        )
        if not guard.get("projection_identity_pass"):
            fail("generator projection-identity guard is not PASS")
        required_true_guards = {
            "source_hashes_match",
            "cell_metadata_match",
            "coordinate_indices_match_exactly",
            "vectors_nonzero",
            "best_scalar_nonzero",
            "projection_identity_pass",
        }
        if any(guard.get(key) is not True for key in required_true_guards):
            fail("one or more generator guards are not true")
        if Decimal(guard["projection_identity_abs_error"]) > Decimal(
            guard["projection_identity_tolerance"]
        ):
            fail("recorded projection identity error exceeds tolerance")

    print("VALIDATE_EXACT_PROJECTIVE_ONE_CONTROL_CELL: PASS")
    print(f"projective_defect={result['measurement']['projective_defect']}")
    print(
        "inf_c_nonzero_relative_distance="
        f"{result['measurement']['inf_c_nonzero_relative_distance']}"
    )
    print("spectral_residual_and_gap=NO_PERSISTED_MFIN_MATVEC")
    print("scope=[FINITE_CELL][CONDITIONAL]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
