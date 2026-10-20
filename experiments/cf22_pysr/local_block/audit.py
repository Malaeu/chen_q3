#!/usr/bin/env python3
"""Check whether local CF22 pair features identify the full signed pair block.

This is a finite-panel audit over every unordered pair in the pinned saved
correlation decomposition. It never fits PySR and never drops RR, cross, or AA
pairs. A collision is certified only when two target Arb intervals with the
same proposed feature key are disjoint.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

HERE = Path(__file__).resolve().parent
CORRELATION_DIR = HERE.parent / "correlation"
DEFAULT_INPUT = CORRELATION_DIR / "decomposition.json.gz"
PINNED_DECOMPOSITION_SHA256 = (
    "74e888523228566fbb5140ed24dd8b9abbd33a07af9eba72519802dd18e9f38d"
)
EXPECTED_SCHEMA = "cf22-nonunit-pair-decomposition-v1"
EXPECTED_SCOPE = "FINITE_OFF_SCHEDULE_PAIR_DIAGNOSTIC"
EXPECTED_SOURCE_COMMIT = "f1993ec6a7933418c38c305a13a3221037b9447a"
EXPECTED_CONFIGS = 20
EXPECTED_PAIRS = 13434
GROUPS = {"rough_rough", "cross", "affected_affected"}

BASE_FEATURES = (
    "U", "P_label", "r", "ell", "orientation", "columns_norm_mu_sorted",
    "gcd_norm", "conductor_norm", "full_period_Q", "A_exact", "A_P_exact",
)
STRONG_EXTRA_FEATURES = ("pair_group", "columns_prime_norm_exponent_shapes")
FORBIDDEN_FEATURES = (
    "T_physical_2re", "T_raw_2re", "physical_signed_contribution",
    "raw_signed_contribution", "C_signed_contribution", "full_C",
)


def _fraction(value: Any) -> Fraction:
    return Fraction(str(value))


def _interval(record: Any) -> tuple[Fraction, Fraction]:
    if not isinstance(record, dict) or "lower" not in record or "upper" not in record:
        raise ValueError("expected an interval record with lower and upper endpoints")
    lo, hi = _fraction(record["lower"]), _fraction(record["upper"])
    if lo > hi:
        raise ValueError("interval has reversed endpoints")
    return lo, hi


def _column_signature(column: dict[str, Any]) -> tuple[int, int]:
    ideal = column["ideal"]
    shape = tuple(sorted(
        (int(factor["prime_ideal_norm"]), int(factor["exponent"]))
        for factor in ideal["factors"]
    ))
    return int(ideal["norm"]), shape


def feature_record(row: dict[str, Any], pair: dict[str, Any], *, strong: bool) -> dict[str, Any]:
    """Return target-independent features, canonically ordering the pair."""
    config = row["configuration"]
    columns = [
        (int(pair["left_column"]["ideal"]["norm"]), int(pair["left_column"]["mu"]), pair["left_column"]),
        (int(pair["right_column"]["ideal"]["norm"]), int(pair["right_column"]["mu"]), pair["right_column"]),
    ]
    columns.sort(key=lambda item: (item[0], item[1], _column_signature(item[2])))
    result: dict[str, Any] = {
        "U": int(config["U"]),
        "P_label": str(config["P"]),
        "r": str(Fraction(str(config["r"]))),
        "ell": str(Fraction(str(config["ell"]))),
        "orientation": int(config["orientation"]),
        "columns_norm_mu_sorted": [[norm, mu] for norm, mu, _column in columns],
        "gcd_norm": int(pair["shared_zero_mask_gcd"]["norm"]),
        "conductor_norm": int(pair["primitive_quotient_conductor"]["norm"]),
        "full_period_Q": int(pair["full_period_lcm_norm_Q"]),
        "A_exact": int(pair["A_exact"]),
        "A_P_exact": int(pair["A_P_exact"]),
    }
    if strong:
        result["pair_group"] = str(pair["group"])
        result["columns_prime_norm_exponent_shapes"] = [
            {
                "norm": norm,
                "mu": mu,
                "factors": [[p_norm, exponent] for p_norm, exponent in _column_signature(column)[1]],
            }
            for norm, mu, column in columns
        ]
    return result


def _freeze(value: Any) -> Any:
    if isinstance(value, dict):
        return tuple((key, _freeze(value[key])) for key in sorted(value))
    if isinstance(value, list):
        return tuple(_freeze(item) for item in value)
    return value


def feature_key(row: dict[str, Any], pair: dict[str, Any], *, strong: bool) -> tuple[Any, ...]:
    return _freeze(feature_record(row, pair, strong=strong))


def _pair_witness(row: dict[str, Any], pair: dict[str, Any]) -> dict[str, Any]:
    """Keep the original generated ideals so a feature collision is inspectable."""
    lo, hi = _interval(pair["C_signed_contribution"])
    return {
        "configuration_id": row["id"],
        "i": int(pair["i"]),
        "j": int(pair["j"]),
        "group": pair["group"],
        "target_interval": {"lower": str(lo), "upper": str(hi)},
        "left_ideal_with_generators": pair["left_column"]["ideal"],
        "right_ideal_with_generators": pair["right_column"]["ideal"],
        "shared_zero_mask_gcd_with_generators": pair["shared_zero_mask_gcd"],
        "primitive_quotient_conductor_with_generators": pair["primitive_quotient_conductor"],
    }


def _witness(features: dict[str, Any], first: dict[str, Any], second: dict[str, Any], gap: Fraction) -> dict[str, Any]:
    return {
        "features": features,
        "separation_exact": str(gap),
        "separation_decimal": format(float(gap), ".16g"),
        "upper_target_pair": first,
        "lower_target_pair": second,
    }


def _analyze_profile(rows: list[dict[str, Any]], *, strong: bool) -> dict[str, Any]:
    groups: dict[tuple[Any, ...], list[tuple[Fraction, Fraction, dict[str, Any], dict[str, Any]]]] = defaultdict(list)
    pair_count = 0
    for row in rows:
        for pair in row["pairs"]:
            pair_count += 1
            lo, hi = _interval(pair["C_signed_contribution"])
            features = feature_record(row, pair, strong=strong)
            groups[_freeze(features)].append((lo, hi, row, pair))

    repeated = [entries for entries in groups.values() if len(entries) > 1]
    collisions: list[tuple[Fraction, dict[str, Any]]] = []
    max_cross_sign: tuple[Fraction, dict[str, Any]] | None = None
    for entries in repeated:
        lo_entry = max(entries, key=lambda entry: (entry[0], entry[2]["id"], entry[3]["i"], entry[3]["j"]))
        hi_entry = min(entries, key=lambda entry: (entry[1], entry[2]["id"], entry[3]["i"], entry[3]["j"]))
        gap = lo_entry[0] - hi_entry[1]
        if gap > 0:
            features = feature_record(lo_entry[2], lo_entry[3], strong=strong)
            collisions.append((gap, _witness(
                features,
                _pair_witness(lo_entry[2], lo_entry[3]),
                _pair_witness(hi_entry[2], hi_entry[3]),
                gap,
            )))

        if all(entry[3]["group"] == "cross" for entry in entries):
            positives = [entry for entry in entries if entry[0] > 0]
            negatives = [entry for entry in entries if entry[1] < 0]
            for positive in positives:
                for negative in negatives:
                    sign_gap = positive[0] - negative[1]
                    if sign_gap > 0 and (max_cross_sign is None or sign_gap > max_cross_sign[0]):
                        features = feature_record(positive[2], positive[3], strong=strong)
                        max_cross_sign = (sign_gap, _witness(
                            features,
                            _pair_witness(positive[2], positive[3]),
                            _pair_witness(negative[2], negative[3]),
                            sign_gap,
                        ))

    max_collision = max(collisions, key=lambda item: item[0])[1] if collisions else None
    return {
        "feature_names": list(BASE_FEATURES + (STRONG_EXTRA_FEATURES if strong else ())),
        "pair_count": pair_count,
        "distinct_feature_keys": len(groups),
        "repeated_feature_groups": len(repeated),
        "pairs_in_repeated_groups": sum(len(entries) for entries in repeated),
        "disjoint_target_groups": len(collisions),
        "no_certified_collision_on_panel": not collisions,
        "status": "COLLISION_FOUND" if collisions else "NO_COLLISION_FOUND_ON_PANEL",
        "largest_disjoint_target_gap": max_collision,
        "largest_cross_positive_negative_gap": max_cross_sign[1] if max_cross_sign else None,
        "interpretation": (
            "Same listed features have disjoint certified full signed pair intervals; at least one omitted arithmetic feature matters on this panel."
            if collisions else
            "No disjoint target intervals were found among repeated feature keys on this finite panel; this does not prove a universal identity or justify extrapolation."
        ),
    }


def _validate_payload(payload: dict[str, Any]) -> int:
    if payload.get("schema") != EXPECTED_SCHEMA or payload.get("scope") != EXPECTED_SCOPE:
        raise ValueError("unexpected decomposition schema or scope")
    provenance = payload.get("provenance", {})
    if provenance.get("pinned_input_commit") != EXPECTED_SOURCE_COMMIT:
        raise ValueError("decomposition does not name the expected pinned source commit")
    panel = payload.get("panel_checks", {})
    required = (
        "all_pair_sums_overlap_full_C",
        "all_pair_inclusion_exclusion_checks_pass",
        "all_group_reassemblies_overlap",
        "all_pair_residuals_contain_zero",
    )
    if any(panel.get(name) is not True for name in required):
        raise ValueError("saved decomposition does not pass required full-pair integrity checks")
    rows = payload.get("rows")
    if not isinstance(rows, list) or len(rows) != EXPECTED_CONFIGS:
        raise ValueError("expected all 20 frozen configurations")
    ids: set[str] = set()
    total = 0
    for row in rows:
        if row.get("id") in ids:
            raise ValueError("duplicate configuration id")
        ids.add(row["id"])
        counts: dict[str, int] = defaultdict(int)
        sum_lo = Fraction(0)
        sum_hi = Fraction(0)
        for pair in row.get("pairs", []):
            if pair.get("group") not in GROUPS:
                raise ValueError("pair missing a required signed group")
            # Require both signed legs of D_ij, its mixed-mask audit, and the full target.
            for field in (
                "physical_signed_contribution", "raw_signed_contribution",
                "mask_correction_vs_same_A_copies", "C_signed_contribution",
            ):
                if field not in pair:
                    raise ValueError(f"pair is missing complete-C field {field}")
            physical = _interval(pair["physical_signed_contribution"])
            raw = _interval(pair["raw_signed_contribution"])
            target = _interval(pair["C_signed_contribution"])
            difference = (physical[0] - raw[1], physical[1] - raw[0])
            if max(difference[0], target[0]) > min(difference[1], target[1]):
                raise ValueError("pair target interval does not overlap physical minus raw contribution")
            sum_lo += target[0]
            sum_hi += target[1]
            counts[pair["group"]] += 1
            total += 1
        if len(row.get("pairs", [])) != int(row.get("counts", {}).get("pair_count", -1)):
            raise ValueError(f"{row['id']}: pair count differs from saved row count")
        if sum_lo > sum_hi:
            raise ValueError("invalid summed pair interval")
        full_c = _interval(row["full_C"])
        if max(sum_lo, full_c[0]) > min(sum_hi, full_c[1]):
            raise ValueError(f"all-pair signed sum does not overlap saved full C for {row['id']}")
        saved_group_counts = row.get("groups", {})
        for group in GROUPS:
            if int(saved_group_counts.get(group, {}).get("pair_count", -1)) != counts[group]:
                raise ValueError(f"{row['id']}: {group} pair count does not match saved grouping")
    if total != EXPECTED_PAIRS:
        raise ValueError(f"expected {EXPECTED_PAIRS} saved unordered pairs, got {total}")
    return total


def audit_payload(payload: dict[str, Any], *, source_sha256: str) -> dict[str, Any]:
    if source_sha256 != PINNED_DECOMPOSITION_SHA256:
        raise ValueError("decomposition bytes do not match the pinned full-pair source hash")
    pair_count = _validate_payload(payload)
    rows = payload["rows"]
    base = _analyze_profile(rows, strong=False)
    strong = _analyze_profile(rows, strong=True)
    return {
        "schema": "cf22-local-pair-feature-audit-v1",
        "scope": "FINITE_SAVED_PANEL_ONLY",
        "source": {
            "sha256": source_sha256,
            "pinned_source_commit": EXPECTED_SOURCE_COMMIT,
            "decomposition_schema": EXPECTED_SCHEMA,
            "configuration_count": len(rows),
            "unordered_full_signed_pairs": pair_count,
            "full_C_reassembly_interval_checked": True,
            "physical_minus_raw_target_interval_checked": True,
            "all_pair_groups_included": sorted(GROUPS),
        },
        "target": "C_signed_contribution = complete unordered pair contribution to C, physical masks minus raw mean",
        "forbidden_as_features": list(FORBIDDEN_FEATURES),
        "profiles": {
            "base_proposed_features": base,
            "stronger_factor_shape_features": strong,
        },
        "pysr_admission": "HOLD_FEATURES_COLLIDE" if base["disjoint_target_groups"] else "REVIEW_PANEL_NO_COLLISION",
        "epistemic_limit": "A collision is a finite-panel falsifier of single-valued dependence on the listed features. No collision on this finite panel is not proof of an identity or law on the full CF22 domain.",
    }


def load_and_audit(path: Path = DEFAULT_INPUT) -> dict[str, Any]:
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != PINNED_DECOMPOSITION_SHA256:
        raise ValueError(f"source hash mismatch for {path}: {digest}")
    if path.suffix == ".gz":
        payload = json.loads(gzip.decompress(raw))
    else:
        payload = json.loads(raw)
    if not isinstance(payload, dict):
        raise ValueError("decomposition root must be a JSON object")
    return audit_payload(payload, source_sha256=digest)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, help="optional new JSON output path; existing files are refused")
    args = parser.parse_args(argv)
    result = load_and_audit(args.input)
    encoded = json.dumps(result, sort_keys=True, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as stream:
            stream.write(encoded)
    else:
        print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
