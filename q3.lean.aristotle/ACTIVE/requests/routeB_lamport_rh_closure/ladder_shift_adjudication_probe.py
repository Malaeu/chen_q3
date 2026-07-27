#!/usr/bin/env python3
"""Goal 024: shifted-ladder adjudication of the 022 floor records.

The numerical backend and the classification rule are imported unchanged from
``candidate_adjudication_probe``.  Only the per-record precision ladder moves:

    primary:   p_fail + 200, p_fail + 300, p_fail + 400
    escalated: p_fail + 400, p_fail + 600, p_fail + 800

The escalated ladder is evaluated only when the primary ladder remains on the
registered floor.  Five 022-negative controls are selected by deterministic
``random.Random(6)`` sampling.  This remains a report-only numerical
diagnostic: it does not mutate STATE, evaluate G3/Fejer/residual, or create
Bus 010.
"""

from __future__ import annotations

import csv
import hashlib
import json
import platform
import random
from collections import defaultdict
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np

import candidate_adjudication_probe as base


REQUEST_DIR = Path(__file__).resolve().parent
GOAL = REQUEST_DIR / "024_ladder_shift_adjudication.goal.md"
SOURCE_SUMMARY = REQUEST_DIR / "E_STAR_CANDIDATE_ADJUDICATION.csv"
SOURCE_POINTS = REQUEST_DIR / "E_STAR_CANDIDATE_ADJUDICATION_POINTS.csv"
SOURCE_FINGERPRINT = (
    REQUEST_DIR / "E_STAR_CANDIDATE_ADJUDICATION_FINGERPRINT.csv"
)

RESULT_JSON = REQUEST_DIR / "E_STAR_LADDER_SHIFT_ADJUDICATION.json"
RESULT_CSV = REQUEST_DIR / "E_STAR_LADDER_SHIFT_ADJUDICATION.csv"
POINTS_CSV = REQUEST_DIR / "E_STAR_LADDER_SHIFT_ADJUDICATION_POINTS.csv"
FINGERPRINT_CSV = (
    REQUEST_DIR / "E_STAR_LADDER_SHIFT_ADJUDICATION_FINGERPRINT.csv"
)

CONTROL_SEED = 6
CORE_ROLES = {"candidate", "zero_local"}
PRIMARY_OFFSETS = (200, 300, 400)
ESCALATED_OFFSETS = (400, 600, 800)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def mp_value(text: str) -> mp.mpf:
    return mp.mpf(text)


def source_index() -> tuple[
    dict[str, dict[str, Any]],
    dict[str, dict[str, str]],
    dict[tuple[str, int], list[dict[str, str]]],
]:
    records = {row["record_id"]: row for row in base.source_records()}
    summaries = {row["record_id"]: row for row in read_csv(SOURCE_SUMMARY)}
    points: dict[tuple[str, int], list[dict[str, str]]] = defaultdict(list)
    for row in read_csv(SOURCE_POINTS):
        if row["role"] in CORE_ROLES:
            points[(row["record_id"], int(row["dps"]))].append(row)
    if len(records) != 70 or len(summaries) != 70:
        raise RuntimeError(
            f"SOURCE_RECORD_COUNT_MISMATCH:{len(records)}:{len(summaries)}"
        )
    return records, summaries, points


def _derive_p_fail_at_current_precision(
    summary: dict[str, str],
    source_points: dict[
        tuple[str, int], list[dict[str, str]]
    ],
) -> tuple[int, str]:
    """Return the first failed 022 error-budget level.

    A level fails locally when its core margin is not above its pointwise
    Taylor+mode estimate.  A transition fails at its lower level when its
    drift is not below the upper-level margin.  This is the unchanged 022
    margin/error judge, applied before moving the ladder.
    """

    record_id = summary["record_id"]
    levels = tuple(int(summary[key]) for key in ("p0", "p1", "p2"))
    failures: list[tuple[int, str]] = []
    for dps in levels:
        rows = source_points[(record_id, dps)]
        margin = min(abs(mp_value(row["value"])) for row in rows)
        error = max(
            mp_value(row["total_error_estimate"]) for row in rows
        )
        if not mp.isfinite(error) or margin <= error:
            failures.append((dps, "LOCAL_ERROR_NOT_BELOW_MARGIN"))
    for lower, upper in zip(levels[:-1], levels[1:]):
        lower_rows = source_points[(record_id, lower)]
        upper_rows = source_points[(record_id, upper)]
        if len(lower_rows) != len(upper_rows):
            raise RuntimeError(
                f"SOURCE_LADDER_GRID_MISMATCH:{record_id}:{lower}:{upper}"
            )
        drift = max(
            abs(
                mp_value(lower_rows[index]["value"])
                - mp_value(upper_rows[index]["value"])
            )
            for index in range(len(lower_rows))
        )
        upper_margin = min(
            abs(mp_value(row["value"])) for row in upper_rows
        )
        if drift >= upper_margin:
            failures.append(
                (lower, "INTERLEVEL_DRIFT_NOT_BELOW_MARGIN")
            )
    if not failures:
        raise RuntimeError(f"P_FAIL_NOT_RECOVERED:{record_id}")
    p_fail = min(level for level, _ in failures)
    reasons = sorted(
        reason for level, reason in failures if level == p_fail
    )
    return p_fail, "+".join(reasons)


def derive_p_fail(
    summary: dict[str, str],
    source_points: dict[
        tuple[str, int], list[dict[str, str]]
    ],
) -> tuple[int, str]:
    with mp.workdps(120):
        return _derive_p_fail_at_current_precision(
            summary, source_points
        )


def selected_records() -> tuple[
    list[dict[str, Any]],
    dict[str, dict[str, Any]],
]:
    records, summaries, source_points = source_index()
    floor_ids = [
        record_id
        for record_id, row in summaries.items()
        if row["classification"] == "STILL_FLOOR"
    ]
    negative_ids = [
        record_id
        for record_id, row in summaries.items()
        if row["classification"] == "NEGATIVE_CONFIRMED"
    ]
    if len(floor_ids) != 51 or len(negative_ids) != 19:
        raise RuntimeError(
            f"SOURCE_CLASS_COUNT_MISMATCH:{len(floor_ids)}:{len(negative_ids)}"
        )
    controls = random.Random(CONTROL_SEED).sample(negative_ids, 5)
    selected_ids = set(floor_ids) | set(controls)
    metadata: dict[str, dict[str, Any]] = {}
    for record_id in floor_ids:
        p_fail, reason = derive_p_fail(
            summaries[record_id], source_points
        )
        metadata[record_id] = {
            "selection_role": "FLOOR_TARGET",
            "source_classification": "STILL_FLOOR",
            "p_fail": p_fail,
            "p_fail_reason": reason,
        }
    for record_id in controls:
        metadata[record_id] = {
            "selection_role": "NEGATIVE_CONTROL",
            "source_classification": "NEGATIVE_CONFIRMED",
            "p_fail": int(summaries[record_id]["p0"]),
            "p_fail_reason": "CONTROL_BASE_P0",
        }
    ordered = [
        records[row["record_id"]]
        for row in base.source_records()
        if row["record_id"] in selected_ids
    ]
    return ordered, metadata


def ladder(p_fail: int, escalated: bool) -> tuple[int, int, int]:
    offsets = ESCALATED_OFFSETS if escalated else PRIMARY_OFFSETS
    return tuple(p_fail + offset for offset in offsets)


class EvaluationCache:
    def __init__(self) -> None:
        self.points: dict[
            tuple[str, int], list[dict[str, Any]]
        ] = {}
        self.level_meta: dict[tuple[int, int], dict[str, Any]] = {}
        self.fingerprints: dict[
            tuple[int, int], list[dict[str, Any]]
        ] = {}

    def evaluate(
        self,
        schedules: dict[str, tuple[int, int, int]],
        records: dict[str, dict[str, Any]],
    ) -> None:
        groups: dict[tuple[int, int], list[str]] = defaultdict(list)
        for record_id, levels in schedules.items():
            m = int(records[record_id]["m"])
            for dps in levels:
                if (record_id, dps) not in self.points:
                    groups[(m, dps)].append(record_id)
        for (m, dps), record_ids in sorted(groups.items()):
            subset = [records[record_id] for record_id in record_ids]
            rows, meta, fingerprints = base.evaluate_level(
                m, dps, subset
            )
            for row in rows:
                self.points.setdefault(
                    (row["record_id"], dps), []
                ).append(row)
            self.level_meta[(m, dps)] = meta
            self.fingerprints[(m, dps)] = fingerprints


def _classify_at_current_precision(
    record: dict[str, Any],
    levels: tuple[int, int, int],
    cache: EvaluationCache,
) -> dict[str, Any]:
    record_id = record["record_id"]
    core_role = (
        "candidate"
        if record["source_kind"] == "candidate"
        else "zero_local"
    )
    core_by_level = [
        [
            row
            for row in cache.points[(record_id, dps)]
            if row["role"] == core_role
        ]
        for dps in levels
    ]
    signs_by_level = [
        [int(row["sign"]) for row in rows] for rows in core_by_level
    ]
    final_values = [row["_value_mp"] for row in core_by_level[-1]]
    final_margin = min(abs(value) for value in final_values)
    final_error = max(
        row["_error_mp"] for row in core_by_level[-1]
    )
    ladder_error = mp.mpf(0)
    for lower_rows, upper_rows in zip(
        core_by_level[:-1], core_by_level[1:]
    ):
        if len(lower_rows) != len(upper_rows):
            raise RuntimeError(
                f"LADDER_GRID_MISMATCH:{record_id}"
            )
        ladder_error = max(
            ladder_error,
            max(
                abs(
                    lower_rows[index]["_value_mp"]
                    - upper_rows[index]["_value_mp"]
                )
                for index in range(len(lower_rows))
            ),
        )
    decision_error = max(final_error, ladder_error)
    negative = all(
        all(sign < 0 for sign in signs) for signs in signs_by_level
    )
    positive = all(
        all(sign > 0 for sign in signs) for signs in signs_by_level
    )
    margin_pass = final_margin > decision_error
    if negative and margin_pass:
        classification = "NEGATIVE_CONFIRMED"
    elif positive and margin_pass:
        classification = "POSITIVE_CONFIRMED"
    else:
        classification = "STILL_FLOOR"
    blockers: list[str] = []
    if not negative and not positive:
        blockers.append("SIGN_NOT_STABLE_ALL_THREE_LEVELS")
    if not mp.isfinite(final_error):
        blockers.append("NONCONTRACTING_TAYLOR_OR_MODE_ERROR")
    if ladder_error >= final_margin:
        blockers.append("INTERLEVEL_DRIFT_NOT_BELOW_MARGIN")
    if not margin_pass and not blockers:
        blockers.append("MARGIN_NOT_ABOVE_ERROR")
    tooth_rows = [
        row
        for row in cache.points[(record_id, levels[-1])]
        if row["role"] in {"left_tooth", "right_tooth"}
    ]
    return {
        "classification": classification,
        "levels": levels,
        "final_margin": final_margin,
        "final_error": final_error,
        "ladder_error": ladder_error,
        "decision_error": decision_error,
        "margin_over_error_orders": (
            base.log10_abs(final_margin)
            - base.log10_abs(decision_error)
            if decision_error != 0
            else mp.inf
        ),
        "blocker": (
            "+".join(blockers) if blockers else "NONE"
        ),
        "left_tooth_sign_final": next(
            int(row["sign"])
            for row in tooth_rows
            if row["role"] == "left_tooth"
        ),
        "right_tooth_sign_final": next(
            int(row["sign"])
            for row in tooth_rows
            if row["role"] == "right_tooth"
        ),
        "core_point_count": len(core_by_level[-1]),
    }


def classify(
    record: dict[str, Any],
    levels: tuple[int, int, int],
    cache: EvaluationCache,
) -> dict[str, Any]:
    with mp.workdps(max(levels) + 30):
        return _classify_at_current_precision(record, levels, cache)


def fingerprint_crosscheck(
    cache: EvaluationCache,
) -> list[dict[str, Any]]:
    old_rows = {
        (int(row["m"]), row["t_label"]): row
        for row in read_csv(SOURCE_FINGERPRINT)
        if row["t_label"] in {"0.25", "0.5", "0.75"}
    }
    output: list[dict[str, Any]] = []
    for m in base.M_VALUES:
        available = [
            dps for mm, dps in cache.fingerprints if mm == m
        ]
        if not available:
            continue
        dps = max(available)
        for row in cache.fingerprints[(m, dps)]:
            label = row["t_label"]
            if label not in {"0.25", "0.5", "0.75"}:
                continue
            old = old_rows[(m, label)]
            with mp.workdps(max(120, dps)):
                value = mp_value(row["legendre_value"])
                old_value = mp_value(old["legendre_value"])
                log_drift = abs(
                    base.log10_abs(value)
                    - base.log10_abs(old_value)
                )
                output.append(
                    {
                        "m": m,
                        "dps": dps,
                        "t_label": label,
                        "source_022_sign": int(
                            old["computed_sign"]
                        ),
                        "computed_sign": int(mp.sign(value)),
                        "source_022_log10_abs": old[
                            "computed_log10_abs"
                        ],
                        "computed_log10_abs": base.mp_text(
                            base.log10_abs(value), 50
                        ),
                        "absolute_log10_drift_vs_022": base.mp_text(
                            log_drift, 50
                        ),
                        "sign_match_022": (
                            int(mp.sign(value))
                            == int(old["computed_sign"])
                        ),
                        "fingerprint_pass": (
                            int(mp.sign(value))
                            == int(old["computed_sign"])
                            and log_drift < mp.mpf("1e-60")
                        ),
                    }
                )
    return output


def serializable_level_meta(
    cache: EvaluationCache,
) -> list[dict[str, Any]]:
    return [
        cache.level_meta[key] for key in sorted(cache.level_meta)
    ]


def run() -> dict[str, Any]:
    selected, metadata = selected_records()
    records = {row["record_id"]: row for row in selected}
    primary = {
        record_id: ladder(int(meta["p_fail"]), False)
        for record_id, meta in metadata.items()
    }
    cache = EvaluationCache()
    cache.evaluate(primary, records)
    primary_results = {
        record_id: classify(
            records[record_id], levels, cache
        )
        for record_id, levels in primary.items()
    }
    escalation_ids = [
        record_id
        for record_id, result in primary_results.items()
        if result["classification"] == "STILL_FLOOR"
    ]
    escalated = {
        record_id: ladder(
            int(metadata[record_id]["p_fail"]), True
        )
        for record_id in escalation_ids
    }
    cache.evaluate(escalated, records)
    escalated_results = {
        record_id: classify(
            records[record_id], levels, cache
        )
        for record_id, levels in escalated.items()
    }

    final_results: dict[str, dict[str, Any]] = {}
    summary_rows: list[dict[str, Any]] = []
    for record in selected:
        record_id = record["record_id"]
        primary_result = primary_results[record_id]
        final = escalated_results.get(record_id, primary_result)
        final_results[record_id] = final
        primary_levels = primary[record_id]
        final_levels = final["levels"]
        summary_rows.append(
            {
                "record_id": record_id,
                "selection_role": metadata[record_id][
                    "selection_role"
                ],
                "source_classification": metadata[record_id][
                    "source_classification"
                ],
                "source_kind": record["source_kind"],
                "m": record["m"],
                "r": record["r"],
                "p_fail": metadata[record_id]["p_fail"],
                "p_fail_reason": metadata[record_id][
                    "p_fail_reason"
                ],
                "primary_p0": primary_levels[0],
                "primary_p1": primary_levels[1],
                "primary_p2": primary_levels[2],
                "primary_classification": primary_result[
                    "classification"
                ],
                "escalated": record_id in escalated_results,
                "final_p0": final_levels[0],
                "final_p1": final_levels[1],
                "final_p2": final_levels[2],
                "final_classification": final["classification"],
                "final_min_margin": base.mp_text(
                    final["final_margin"]
                ),
                "final_min_log10_margin": base.mp_text(
                    base.log10_abs(final["final_margin"]), 40
                ),
                "final_error_estimate": base.mp_text(
                    final["final_error"]
                ),
                "ladder_error_estimate": base.mp_text(
                    final["ladder_error"]
                ),
                "decision_error_estimate": base.mp_text(
                    final["decision_error"]
                ),
                "margin_over_error_orders": base.mp_text(
                    final["margin_over_error_orders"], 30
                ),
                "blocker": final["blocker"],
                "left_tooth_sign_final": final[
                    "left_tooth_sign_final"
                ],
                "right_tooth_sign_final": final[
                    "right_tooth_sign_final"
                ],
                "core_point_count": final["core_point_count"],
            }
        )

    target_results = [
        final_results[record_id]
        for record_id, meta in metadata.items()
        if meta["selection_role"] == "FLOOR_TARGET"
    ]
    control_results = [
        final_results[record_id]
        for record_id, meta in metadata.items()
        if meta["selection_role"] == "NEGATIVE_CONTROL"
    ]
    all_results = target_results + control_results
    positive_positions = [
        {
            "record_id": row["record_id"],
            "m": row["m"],
            "r": row["r"],
        }
        for row in summary_rows
        if row["final_classification"] == "POSITIVE_CONFIRMED"
    ]
    if positive_positions:
        verdict = "ESTAR_PHASE_SIGN_KILLED_CANONICAL"
    elif (
        all(
            result["classification"] == "NEGATIVE_CONFIRMED"
            for result in target_results
        )
        and all(
            result["classification"] == "NEGATIVE_CONFIRMED"
            for result in control_results
        )
    ):
        verdict = "CANONICAL_CANDIDATES_ALL_NEGATIVE"
    else:
        verdict = "CANDIDATES_STILL_FLOOR_2"

    fingerprint_rows = fingerprint_crosscheck(cache)
    if not all(row["fingerprint_pass"] for row in fingerprint_rows):
        raise RuntimeError("PACKET_FINGERPRINT_MISMATCH")

    point_rows: list[dict[str, Any]] = []
    final_level_use = {
        (record_id, dps)
        for record_id, result in final_results.items()
        for dps in result["levels"]
    }
    for (record_id, dps), rows in sorted(cache.points.items()):
        if (record_id, dps) not in final_level_use:
            continue
        for row in rows:
            point_rows.append(
                {
                    **base.strip_internal(row),
                    "selection_role": metadata[record_id][
                        "selection_role"
                    ],
                    "final_ladder_level": True,
                }
            )

    counts = {
        "floor_targets": len(target_results),
        "negative_controls": len(control_results),
        "primary_escalations": len(escalation_ids),
        "target_NEGATIVE_CONFIRMED": sum(
            result["classification"] == "NEGATIVE_CONFIRMED"
            for result in target_results
        ),
        "target_POSITIVE_CONFIRMED": sum(
            result["classification"] == "POSITIVE_CONFIRMED"
            for result in target_results
        ),
        "target_STILL_FLOOR": sum(
            result["classification"] == "STILL_FLOOR"
            for result in target_results
        ),
        "control_NEGATIVE_CONFIRMED": sum(
            result["classification"] == "NEGATIVE_CONFIRMED"
            for result in control_results
        ),
        "control_POSITIVE_CONFIRMED": sum(
            result["classification"] == "POSITIVE_CONFIRMED"
            for result in control_results
        ),
        "control_STILL_FLOOR": sum(
            result["classification"] == "STILL_FLOOR"
            for result in control_results
        ),
        "point_rows": len(point_rows),
    }
    payload = {
        "verdict": verdict,
        "epistemic_status": (
            "HIGH_PRECISION_GRID_DIAGNOSTIC_NOT_A_THEOREM_NOT_RH"
        ),
        "source": {
            "goal": str(GOAL),
            "goal_sha256": sha256(GOAL),
            "source_022_summary": str(SOURCE_SUMMARY),
            "source_022_summary_sha256": sha256(SOURCE_SUMMARY),
            "source_022_points": str(SOURCE_POINTS),
            "source_022_points_sha256": sha256(SOURCE_POINTS),
            "source_022_fingerprint": str(SOURCE_FINGERPRINT),
            "source_022_fingerprint_sha256": sha256(
                SOURCE_FINGERPRINT
            ),
        },
        "protocol": {
            "classification_rule": (
                "unchanged 022: same sign on all three levels and final "
                "margin > max(final Taylor+mode error, interlevel drift)"
            ),
            "p_fail_rule": (
                "first local error-budget failure or lower endpoint of "
                "first transition drift not below the upper margin"
            ),
            "primary_offsets": PRIMARY_OFFSETS,
            "escalated_offsets": ESCALATED_OFFSETS,
            "maximum_offset": 800,
            "control_seed": CONTROL_SEED,
            "control_record_ids": [
                record_id
                for record_id, meta in metadata.items()
                if meta["selection_role"] == "NEGATIVE_CONTROL"
            ],
            "mode_backend": (
                "unchanged 022 mp tridiagonal inverse iteration + "
                "prolate ODE centre Taylor recurrence"
            ),
            "packet_formula": (
                "(J4*phi0-J0*phi4)/"
                "(sqrt(lambda)*sqrt(J0^2+J4^2)); N0=N4=1"
            ),
            "mu_formula": "mu_j=lambda*J_j/c_j; never replaced by 1",
        },
        "counts": counts,
        "positive_positions": positive_positions,
        "records": summary_rows,
        "level_meta": serializable_level_meta(cache),
        "fingerprint_crosscheck": fingerprint_rows,
        "guards": {
            "criterion_changed": False,
            "float64_in_reported_E_star_chain": False,
            "float64_seed_refined_away": True,
            "mu_forced_to_one": False,
            "fingerprint_021_022_preserved": True,
            "Fejer_evaluated": False,
            "residual_evaluated": False,
            "G3_evaluated": False,
            "STATE_mutated": False,
            "Bus_010_created": False,
        },
        "environment": {
            "python": platform.python_version(),
            "mpmath": mp.__version__,
            "numpy": np.__version__,
        },
    }
    base.write_csv(RESULT_CSV, summary_rows)
    base.write_csv(POINTS_CSV, point_rows)
    base.write_csv(FINGERPRINT_CSV, fingerprint_rows)
    RESULT_JSON.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "verdict": verdict,
                "counts": counts,
                "positive_positions": positive_positions,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return payload


if __name__ == "__main__":
    run()
