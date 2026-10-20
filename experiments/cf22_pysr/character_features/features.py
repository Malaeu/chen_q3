#!/usr/bin/env python3
"""Audit arithmetic character fingerprints for the frozen full-C pair panel.

This module only reads the saved full signed pair decomposition.  It does not
recompute C, fit a model, or use the pair target when constructing features.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import sys
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
EXPERIMENTS = HERE.parent
sys.path.insert(0, str(EXPERIMENTS))

import evaluate  # noqa: E402 -- the pinned source's exact phase_index implementation
from local_block import audit as prior_audit  # noqa: E402


DEFAULT_INPUT = EXPERIMENTS / "correlation" / "decomposition.json.gz"
PINNED_DECOMPOSITION_SHA256 = (
    "74e888523228566fbb5140ed24dd8b9abbd33a07af9eba72519802dd18e9f38d"
)
PINNED_EVALUATOR_SHA256 = (
    "06c48c3075335205aeb80cdc7a142d1b0868e82a7f2a1006391764222112faeb"
)
EXPECTED_PAIRS = 13_434
PROBES: tuple[tuple[int, int], ...] = (
    (1, 0), (0, 1), (2, 0), (2, 1), (3, 1),
    (1, 3), (3, 2), (4, 1), (1, 4),
)
PREFIX_LENGTHS = (1, 3, 5, 9)
REAL2 = (2, 1, -1, -2, -1, 1)
IMAG_SQRT3_UNITS = (0, 1, 1, 0, -1, -1)


def _q(value: Any) -> Fraction:
    return Fraction(str(value))


def _source_payload(path: Path) -> tuple[dict[str, Any], str, str]:
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != PINNED_DECOMPOSITION_SHA256:
        raise ValueError(f"source hash mismatch: {digest}")
    evaluator_raw = (EXPERIMENTS / "evaluate.py").read_bytes()
    evaluator_digest = hashlib.sha256(evaluator_raw).hexdigest()
    if evaluator_digest != PINNED_EVALUATOR_SHA256:
        raise ValueError(f"phase evaluator hash mismatch: {evaluator_digest}")
    payload = json.loads(gzip.decompress(raw)) if path.suffix == ".gz" else json.loads(raw)
    if not isinstance(payload, dict):
        raise ValueError("decomposition root must be an object")
    prior_audit.audit_payload(payload, source_sha256=digest)
    return payload, digest, evaluator_digest


def _factors(column: dict[str, Any]) -> tuple[tuple[tuple[int, int], int], ...]:
    return tuple(
        (tuple(int(v) for v in item["prime_generator"]), int(item["exponent"]))
        for item in column["ideal"]["factors"]
    )


@lru_cache(maxsize=None)
def _phase(
    factors: tuple[tuple[tuple[int, int], int], ...],
    z: tuple[int, int],
    orientation: int,
) -> int | None:
    return evaluate.phase_index(factors, z, orientation)


def _canonical_phase_codes(raw: tuple[int, ...]) -> tuple[int, ...]:
    """Canonicalize pair swap by one global conjugation, never per probe."""
    conjugate = tuple(-1 if code == -1 else (-code) % 6 for code in raw)
    return min(raw, conjugate)


def _phase_channels(code: int) -> tuple[int, int, int]:
    if code == -1:
        return 1, 0, 0
    if not 0 <= code < 6:
        raise ValueError(f"invalid sixth-root phase code {code}")
    return 0, REAL2[code], IMAG_SQRT3_UNITS[code]


def pair_phase_codes(row: dict[str, Any], pair: dict[str, Any]) -> tuple[int, ...]:
    orientation = int(row["configuration"]["orientation"])
    left = _factors(pair["left_column"])
    right = _factors(pair["right_column"])
    raw: list[int] = []
    for z in PROBES:
        k_left = _phase(left, z, orientation)
        k_right = _phase(right, z, orientation)
        raw.append(-1 if k_left is None or k_right is None else (k_left - k_right) % 6)
    return _canonical_phase_codes(tuple(raw))


def _configuration_features(row: dict[str, Any]) -> tuple[list[str], list[float], list[dict[str, str]], list[Fraction]]:
    config = row["configuration"]
    p_interval = row["parameters"]["P"]
    p_lo, p_hi = _q(p_interval["lower"]), _q(p_interval["upper"])
    p_mid = (p_lo + p_hi) / 2
    exact = [
        Fraction(int(config["U"])), p_mid, _q(config["r"]), _q(config["ell"]),
        Fraction(int(config["orientation"])),
    ]
    names = ["U", "P", "r", "ell", "orientation"]
    intervals = [
        {"lower": str(v), "upper": str(v)} for v in exact
    ]
    intervals[1] = {"lower": str(p_lo), "upper": str(p_hi)}
    return names, [float(v) for v in exact], intervals, exact


def pair_numeric_features(
    row: dict[str, Any], pair: dict[str, Any], codes: tuple[int, ...],
    config_numeric: tuple[list[str], list[float], list[dict[str, str]], list[Fraction]] | None = None,
) -> tuple[list[str], list[float], list[dict[str, str]], list[Fraction]]:
    """Return flat numeric model inputs, interval inputs, and exact audit values."""
    config_names, config_values, config_bounds, config_exact = config_numeric or _configuration_features(row)
    names, values, bounds, exact = (
        list(config_names), list(config_values), list(config_bounds), list(config_exact)
    )
    columns = [pair["left_column"], pair["right_column"]]
    columns.sort(key=lambda col: (
        int(col["ideal"]["norm"]), int(col["mu"]), prior_audit._column_signature(col),
    ))
    additions: list[tuple[str, Fraction]] = []
    for side, column in zip(("low", "high"), columns):
        additions.extend((
            (f"norm_{side}", Fraction(int(column["ideal"]["norm"]))),
            (f"mu_{side}", Fraction(int(column["mu"]))),
        ))
    additions.extend((
        ("gcd_norm", Fraction(int(pair["shared_zero_mask_gcd"]["norm"]))),
        ("conductor_norm", Fraction(int(pair["primitive_quotient_conductor"]["norm"]))),
        ("period_Q", Fraction(int(pair["full_period_lcm_norm_Q"]))),
        ("A_exact", Fraction(int(pair["A_exact"]))),
        ("A_P_exact", Fraction(int(pair["A_P_exact"]))),
    ))
    for name, value in additions:
        names.append(name)
        exact.append(value)
        values.append(float(value))
        bounds.append({"lower": str(value), "upper": str(value)})

    for index, code in enumerate(codes):
        prefix = f"chi_{index:02d}"
        zero, real2, imag_unit = _phase_channels(code)
        for suffix, value in (("zero", zero), ("real2", real2), ("imag_unit", imag_unit)):
            names.append(f"{prefix}_{suffix}")
            exact_value = Fraction(value)
            exact.append(exact_value)
            values.append(float(value))
            bounds.append({"lower": str(exact_value), "upper": str(exact_value)})
    return names, values, bounds, exact


def _target(pair: dict[str, Any]) -> tuple[Fraction, Fraction]:
    return prior_audit._interval(pair["C_signed_contribution"])


def _collision_summary(entries: list[tuple[tuple[Any, ...], dict[str, Any], dict[str, Any], tuple[int, ...]]]) -> dict[str, Any]:
    groups: dict[tuple[Any, ...], list[tuple[dict[str, Any], dict[str, Any], tuple[int, ...]]]] = defaultdict(list)
    for key, row, pair, codes in entries:
        groups[key].append((row, pair, codes))
    repeated = [items for items in groups.values() if len(items) > 1]
    collisions: list[tuple[Fraction, dict[str, Any]]] = []
    for items in repeated:
        valued = [(*_target(pair), row, pair, codes) for row, pair, codes in items]
        upper = max(valued, key=lambda item: (item[0], item[2]["id"], item[3]["i"], item[3]["j"]))
        lower = min(valued, key=lambda item: (item[1], item[2]["id"], item[3]["i"], item[3]["j"]))
        gap = upper[0] - lower[1]
        if gap > 0:
            collisions.append((gap, {
                "separation_exact": str(gap),
                "upper": {"configuration_id": upper[2]["id"], "i": upper[3]["i"], "j": upper[3]["j"],
                          "group": upper[3]["group"], "target": {"lower": str(upper[0]), "upper": str(upper[1])},
                          "phase_codes": list(upper[4])},
                "lower": {"configuration_id": lower[2]["id"], "i": lower[3]["i"], "j": lower[3]["j"],
                          "group": lower[3]["group"], "target": {"lower": str(lower[0]), "upper": str(lower[1])},
                          "phase_codes": list(lower[4])},
            }))
    return {
        "distinct_keys": len(groups),
        "repeated_key_groups": len(repeated),
        "pairs_in_repeated_key_groups": sum(map(len, repeated)),
        "disjoint_target_groups": len(collisions),
        "no_disjoint_target_collision": not collisions,
        "largest_separation_witness": max(collisions, key=lambda item: item[0])[1] if collisions else None,
    }


def build_dataset(path: Path = DEFAULT_INPUT) -> dict[str, Any]:
    payload, source_hash, evaluator_hash = _source_payload(path)
    rows_out: list[dict[str, Any]] = []
    names_expected: list[str] | None = None
    entries_by_prefix: dict[int, list[tuple[tuple[Any, ...], dict[str, Any], dict[str, Any], tuple[int, ...]]]] = {
        n: [] for n in PREFIX_LENGTHS
    }
    model_entries: list[tuple[tuple[Any, ...], dict[str, Any], dict[str, Any], tuple[int, ...]]] = []
    known_witnesses: dict[str, dict[str, Any]] = {}
    group_counts: dict[str, int] = defaultdict(int)
    train_rows = test_rows = pair_count = 0
    for row in payload["rows"]:
        config = row["configuration"]
        p_label = str(config["P"])
        split = "test" if int(config["U"]) == 96 or (int(config["U"]) == 48 and p_label == "49") else "train"
        if split == "train":
            train_rows += len(row["pairs"])
        else:
            test_rows += len(row["pairs"])
        config_numeric = _configuration_features(row)
        for pair in row["pairs"]:
            codes = pair_phase_codes(row, pair)
            names, features, feature_intervals, exact_values = pair_numeric_features(row, pair, codes, config_numeric)
            if names_expected is None:
                names_expected = names
            elif names != names_expected:
                raise ValueError("numeric feature schema changed between saved pairs")
            target_lo, target_hi = _target(pair)
            row_id = f"{row['id']}:{pair['i']}:{pair['j']}"
            rows_out.append({
                "id": row_id,
                "configuration_id": row["id"],
                "split": split,
                "features": features,
                "feature_intervals": feature_intervals,
                "target": {"lower": str(target_lo), "upper": str(target_hi)},
                "pair_group": pair["group"],
                "arithmetic_character_codes": list(codes),
            })
            if row["id"] == "U96_P13_o1" and (int(pair["i"]), int(pair["j"])) in {(28, 37), (28, 38)}:
                key = f"{pair['i']}:{pair['j']}"
                known_witnesses[key] = {
                    "id": row_id,
                    "target": {"lower": str(target_lo), "upper": str(target_hi)},
                    "base_numeric_features": features[:14],
                    "strong_prior_feature_key": prior_audit.feature_key(row, pair, strong=True),
                    "phase_codes": list(codes),
                    "columns": [
                        {
                            "norm": int(column["ideal"]["norm"]),
                            "mu": int(column["mu"]),
                            "factors": column["ideal"]["factors"],
                        }
                        for column in (pair["left_column"], pair["right_column"])
                    ],
                }
            group_counts[pair["group"]] += 1
            for prefix_len in PREFIX_LENGTHS:
                prior_key = prior_audit.feature_key(row, pair, strong=True)
                prefix_codes = _canonical_phase_codes(codes[:prefix_len])
                # The prefix audit extends the previous exact strong key. The
                # final numeric feature vector is audited independently below.
                entries_by_prefix[prefix_len].append((prior_key + (prefix_codes,), row, pair, prefix_codes))
            model_entries.append((tuple(features), row, pair, codes))
            pair_count += 1
    if pair_count != EXPECTED_PAIRS:
        raise ValueError(f"expected {EXPECTED_PAIRS} pairs, got {pair_count}")
    assert names_expected is not None
    if set(known_witnesses) != {"28:37", "28:38"}:
        raise ValueError("the two frozen U96/P13 conflict witnesses were not found")

    # Prefix counts extend the prior strong exact key; the final model's numeric
    # feature vector is checked separately, with its stored values as the key.
    audits = {}
    for prefix_len, entries in entries_by_prefix.items():
        audits[str(prefix_len)] = _collision_summary(entries)
    numeric_audit = _collision_summary(model_entries)
    return {
        "schema": "cf22-arithmetic-character-pair-dataset-v1",
        "scope": "FINITE_SAVED_PANEL_ONLY",
        "feature_names": names_expected,
        "rows": rows_out,
        "metadata": {
            "source": {
                "decomposition_sha256": source_hash,
                "phase_evaluator_sha256": evaluator_hash,
                "pinned_source_commit": payload["provenance"]["pinned_input_commit"],
                "decomposition_schema": payload["schema"],
                "configurations": len(payload["rows"]),
                "pairs": pair_count,
                "group_counts": dict(sorted(group_counts.items())),
                "full_C_reassembly_interval_checked": True,
                "physical_minus_raw_target_interval_checked": True,
            },
            "probes": [{"a": a, "b": b, "norm": evaluate.norm((a, b))} for a, b in PROBES],
            "fingerprint": {
                "source_operation": "evaluate.phase_index(factors,z,orientation), exact sixth-root index mod 6",
                "pair_code": "-1 if either column character is zero, else (k_left-k_right) mod 6",
                "pair_swap_canonicalization": "lexicographic min(vector, global conjugate); zero sentinel -1 is fixed",
                "numeric_encoding": "zero flag, 2*cos(pi*k/3), sin(pi*k/3)/(sqrt(3)/2); all stored values are exact integers",
                "target_independent": True,
                "row_or_ideal_identifiers_as_features": False,
            },
            "collision_audit": {
                "strong_prior_features_plus_character_prefixes": audits,
                "exact_final_numeric_feature_vector": numeric_audit,
                "admission": "READY_FOR_BOUNDED_PYSR_ON_FINITE_PANEL" if numeric_audit["no_disjoint_target_collision"] else "HOLD_FEATURES_COLLIDE",
                "limitations": "No collision on this saved finite panel is not a universal identity, proof, or justification for asymptotic extrapolation.",
            },
            "resolved_prior_witness": {
                "configuration_id": "U96_P13_o1",
                "same_previous_strong_key": known_witnesses["28:37"]["strong_prior_feature_key"] == known_witnesses["28:38"]["strong_prior_feature_key"],
                "same_base_numeric_features": known_witnesses["28:37"]["base_numeric_features"] == known_witnesses["28:38"]["base_numeric_features"],
                "differing_probe_indices_zero_based": [
                    index for index, (first, second) in enumerate(
                        zip(known_witnesses["28:37"]["phase_codes"], known_witnesses["28:38"]["phase_codes"])
                    ) if first != second
                ],
                "pairs": [known_witnesses["28:37"], known_witnesses["28:38"]],
            },
            "split": {
                "rule": "test all U=96 rows and U=48,P=49 rows; train the remaining saved rows",
                "train_pairs": train_rows,
                "test_pairs": test_rows,
                "selection_scope": "full panel was used for feature-collision audit; test designation is not an untouched feature-selection set",
            },
            "forbidden_as_features": [
                "C_signed_contribution", "physical_signed_contribution", "raw_signed_contribution",
                "T_physical_2re", "T_raw_2re", "pair_group", "pair indices", "ideal generators",
            ],
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = build_dataset(args.input)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", encoding="utf-8") as stream:
        json.dump(report, stream, indent=2, sort_keys=True, ensure_ascii=False)
        stream.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
