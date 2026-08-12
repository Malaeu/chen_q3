#!/usr/bin/env python3
"""Measure the exact-projective ground/trial mismatch on control cell (13, 120).

This is a source-locked finite-cell calibration only.  It deliberately does
not infer a cofinal rate and does not reconstruct an unpersisted Mfin matvec.
"""

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

TRIAL_SHA256 = "0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88"
GROUND_SHA256 = "cbc556ef7c73c9aefa9f177bb59aeca5867ed6628e3f1cca6edb270bfc13e7f0"
PRECISION = 140
IDENTITY_TOLERANCE = Decimal("1e-110")
KB_QUERY = (
    "exact projective ground to trial residual one control cell lambda_sq 13 "
    "N 120 ground_xi1 portable_k_coeffs NO_PERSISTED_MFIN_MATVEC"
)
KB_STDOUT = (
    "no hits for 'exact projective ground to trial residual one control cell "
    "lambda_sq 13 N 120 ground_xi1 portable_k_coeffs "
    "NO_PERSISTED_MFIN_MATVEC' in any layer"
)


class MeasurementError(RuntimeError):
    """Fail-closed source or arithmetic guard failure."""


def repo_relative(path: Path) -> str:
    return path.resolve().relative_to(HERE.parents[3]).as_posix()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def complex_rows(rows: list[dict[str, Any]]) -> dict[int, tuple[Decimal, Decimal]]:
    return {
        int(row["n"]): (Decimal(str(row["re"])), Decimal(str(row["im"])))
        for row in rows
    }


def norm_sq(vector: dict[int, tuple[Decimal, Decimal]]) -> Decimal:
    return sum(re * re + im * im for re, im in vector.values())


def inner(
    left: dict[int, tuple[Decimal, Decimal]],
    right: dict[int, tuple[Decimal, Decimal]],
) -> tuple[Decimal, Decimal]:
    """Return sum_n conj(left_n) * right_n."""
    real = Decimal(0)
    imag = Decimal(0)
    for n in sorted(left):
        lr, li = left[n]
        rr, ri = right[n]
        real += lr * rr + li * ri
        imag += lr * ri - li * rr
    return real, imag


def direct_residual_sq(
    ground: dict[int, tuple[Decimal, Decimal]],
    trial: dict[int, tuple[Decimal, Decimal]],
    scalar: tuple[Decimal, Decimal],
) -> Decimal:
    """Return ||ground - scalar * trial||^2."""
    cr, ci = scalar
    total = Decimal(0)
    for n in sorted(ground):
        gr, gi = ground[n]
        tr, ti = trial[n]
        rr = gr - (cr * tr - ci * ti)
        ri = gi - (cr * ti + ci * tr)
        total += rr * rr + ri * ri
    return total


def decimal_string(value: Decimal, fractional_digits: int = 79) -> str:
    return format(value, f".{fractional_digits}E")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise MeasurementError(message)


def measure() -> dict[str, Any]:
    trial_actual_sha = sha256(TRIAL_SOURCE)
    ground_actual_sha = sha256(GROUND_SOURCE)
    require(trial_actual_sha == TRIAL_SHA256, "trial source SHA-256 drift")
    require(ground_actual_sha == GROUND_SHA256, "ground source SHA-256 drift")

    trial_payload = json.loads(TRIAL_SOURCE.read_text(encoding="utf-8"))
    ground_payload = json.loads(GROUND_SOURCE.read_text(encoding="utf-8"))
    require(
        (trial_payload["lambda_sq"], trial_payload["N"]) == (13, 120),
        "trial cell metadata drift",
    )
    require(
        (ground_payload["lambda_sq"], ground_payload["N"]) == (13, 120),
        "ground cell metadata drift",
    )
    require(trial_payload["logical_vector"] == "k1", "trial is not logical k1")
    require(ground_payload["xi_m_y_cache"][0]["name"] == "xi1", "row zero is not xi1")

    trial_rows = trial_payload["coefficients"]
    ground_rows = ground_payload["xi_m_y_cache"][0]["xi_vector"]
    trial_indices = [int(row["n"]) for row in trial_rows]
    ground_indices = [int(row["n"]) for row in ground_rows]
    expected_indices = list(range(-120, 121))
    require(trial_indices == expected_indices, "trial indices are not exactly [-120,120]")
    require(ground_indices == expected_indices, "ground indices are not exactly [-120,120]")

    with localcontext() as context:
        context.prec = PRECISION
        trial = complex_rows(trial_rows)
        ground = complex_rows(ground_rows)
        trial_norm_sq = norm_sq(trial)
        ground_norm_sq = norm_sq(ground)
        require(trial_norm_sq > 0, "zero trial vector")
        require(ground_norm_sq > 0, "zero ground vector")

        dot_re, dot_im = inner(trial, ground)
        dot_abs_sq = dot_re * dot_re + dot_im * dot_im
        overlap_sq = dot_abs_sq / (trial_norm_sq * ground_norm_sq)
        require(Decimal(0) <= overlap_sq <= Decimal(1), "normalized overlap outside [0,1]")
        overlap_abs = overlap_sq.sqrt()
        projective_defect = Decimal(1) - overlap_sq

        # With <u,v> = sum conj(u_n)v_n, this scalar uniquely minimizes
        # ||ground-c*trial|| because the measured overlap is nonzero.
        best_scalar = (dot_re / trial_norm_sq, dot_im / trial_norm_sq)
        require(best_scalar != (Decimal(0), Decimal(0)), "best scalar is zero")
        residual_sq_raw = direct_residual_sq(ground, trial, best_scalar)
        residual_sq_normalized = residual_sq_raw / ground_norm_sq
        identity_abs_error = abs(residual_sq_normalized - projective_defect)
        require(identity_abs_error <= IDENTITY_TOLERANCE, "projection identity guard failed")

        projective_distance = residual_sq_normalized.sqrt()
        phase_aligned_unit_distance = (Decimal(2) - Decimal(2) * overlap_abs).sqrt()

        return {
            "schema": "exact_projective_ground_to_trial_residual_one_control_cell/v1",
            "created_on": "2026-08-12",
            "evidence_class": ["FINITE_CELL", "CONDITIONAL"],
            "cell": {"lambda_sq": 13, "N": 120, "coordinate_count": 241},
            "knowledge_preflight": {
                "command": f'./orchestrator/kb.py ask "{KB_QUERY}"',
                "exit_code": 0,
                "stdout": KB_STDOUT,
                "outcome": "NO_HITS",
            },
            "source_lock": {
                "trial": {
                    "path": repo_relative(TRIAL_SOURCE),
                    "expected_sha256": TRIAL_SHA256,
                    "actual_sha256": trial_actual_sha,
                    "sha256_match": True,
                    "selector": "coefficients; logical_vector=k1",
                },
                "ground": {
                    "path": repo_relative(GROUND_SOURCE),
                    "expected_sha256": GROUND_SHA256,
                    "actual_sha256": ground_actual_sha,
                    "sha256_match": True,
                    "selector": "xi_m_y_cache[0].xi_vector; name=xi1",
                },
            },
            "convention": {
                "inner_product": "<u,v> = sum_n conj(u_n) * v_n",
                "normalization": "both full 241-coordinate vectors are renormalized from persisted decimal strings",
                "best_scalar": "c_star=<trial,ground>/||trial||^2",
                "projective_distance": "inf_{c!=0} ||ground-c*trial||/||ground||; c_star is nonzero",
                "projective_defect": "1-|<ground/||ground||,trial/||trial||>|^2",
            },
            "measurement": {
                "decimal_precision": PRECISION,
                "trial_norm": decimal_string(trial_norm_sq.sqrt()),
                "ground_norm": decimal_string(ground_norm_sq.sqrt()),
                "normalized_inner_product": {
                    "re": decimal_string(dot_re / (trial_norm_sq * ground_norm_sq).sqrt()),
                    "im": decimal_string(dot_im / (trial_norm_sq * ground_norm_sq).sqrt()),
                },
                "normalized_overlap_abs": decimal_string(overlap_abs),
                "normalized_overlap_abs_squared": decimal_string(overlap_sq),
                "projective_defect": decimal_string(projective_defect),
                "best_scalar_raw": {
                    "re": decimal_string(best_scalar[0]),
                    "im": decimal_string(best_scalar[1]),
                },
                "inf_c_nonzero_relative_distance": decimal_string(projective_distance),
                "phase_aligned_unit_distance": decimal_string(phase_aligned_unit_distance),
            },
            "guarded_checks": {
                "source_hashes_match": True,
                "cell_metadata_match": True,
                "coordinate_indices_match_exactly": True,
                "vectors_nonzero": True,
                "best_scalar_nonzero": True,
                "direct_projection_residual_squared_relative": decimal_string(
                    residual_sq_normalized
                ),
                "one_minus_overlap_squared": decimal_string(projective_defect),
                "projection_identity_abs_error": decimal_string(identity_abs_error),
                "projection_identity_tolerance": decimal_string(IDENTITY_TOLERANCE),
                "projection_identity_pass": True,
            },
            "spectral_residual_and_gap": {
                "status": "NO_PERSISTED_MFIN_MATVEC",
                "matrix_residual": "NOT_MEASURED",
                "spectral_gap": "NOT_MEASURED",
                "reason": "the two source-locked packets do not persist a canonical Mfin matvec; eigenpair-cache metadata is not a replacement",
            },
            "outcome": "MEASURED_FINITE_CELL_CONDITIONAL_NOT_PROMOTING",
            "non_claims": [
                "not a theorem",
                "not a cofinal estimate",
                "not a Route B closure",
                "not an RH claim",
            ],
        }


def main() -> int:
    payload = measure()
    RESULT.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"wrote {RESULT}")
    print(f"projective_defect={payload['measurement']['projective_defect']}")
    print(
        "inf_c_nonzero_relative_distance="
        f"{payload['measurement']['inf_c_nonzero_relative_distance']}"
    )
    print(payload["outcome"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
