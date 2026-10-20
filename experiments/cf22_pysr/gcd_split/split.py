#!/usr/bin/env python3
"""Exact finite-panel split of the full signed CF22 pair sum by ideal gcd norm.

This reads only the pinned pair-decomposition artifact. Every pair remains in
exactly one side and keeps its signed RR/cross/AA, physical, and raw terms.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


INPUT = Path(__file__).resolve().parents[1] / "correlation" / "decomposition.json.gz"
INPUT_SHA256 = "74e888523228566fbb5140ed24dd8b9abbd33a07af9eba72519802dd18e9f38d"
ANALYSIS_BASE_COMMIT = "82116bba7c122734256a16b89457b596c0e07375"
THRESHOLDS = (1, 7, 13, 19, 31)
GROUPS = ("rough_rough", "cross", "affected_affected")
FIELDS = ("C_signed_contribution", "physical_signed_contribution", "raw_signed_contribution")
EXPECTED_ROWS = 20
EXPECTED_PAIRS = 13434
Interval = tuple[Fraction, Fraction]
ZERO: Interval = (Fraction(0), Fraction(0))


def _fraction(value: Any) -> Fraction:
    if isinstance(value, bool):
        raise ValueError("boolean is not an exact numeric endpoint")
    return Fraction(value)


def _interval(record: dict[str, Any]) -> Interval:
    lo, hi = _fraction(record["lower"]), _fraction(record["upper"])
    if lo > hi:
        raise ValueError("reversed interval")
    return lo, hi


def _add(a: Interval, b: Interval) -> Interval:
    return a[0] + b[0], a[1] + b[1]


def _sub(a: Interval, b: Interval) -> Interval:
    return a[0] - b[1], a[1] - b[0]


def _mul(a: Interval, b: Interval) -> Interval:
    products = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(products), max(products)


def _overlaps(a: Interval, b: Interval) -> bool:
    return max(a[0], b[0]) <= min(a[1], b[1])


def _positive_part(a: Interval) -> Interval:
    return max(Fraction(0), a[0]), max(Fraction(0), a[1])


def _nonnegative_enclosure(a: Interval) -> Interval:
    # For the actual M,R,C with C=M+R, M_+ + R_+ - C_+ >= 0.
    # Intervals lose that dependency, so intersect their enclosure with [0,+inf).
    if a[1] < 0:
        raise ValueError("positive-part separation contradicts C = main + remainder")
    return max(Fraction(0), a[0]), a[1]


def _divide_by_positive(a: Interval, b: Interval) -> Interval:
    if b[0] <= 0:
        raise ValueError("normalizing denominator is not certified positive")
    return _mul(a, (1 / b[1], 1 / b[0]))


def _record(value: Interval) -> dict[str, str]:
    return {
        "lower": str(value[0]),
        "upper": str(value[1]),
        "width": str(value[1] - value[0]),
    }


def _sum(values: list[Interval]) -> Interval:
    out = ZERO
    for value in values:
        out = _add(out, value)
    return out


def _factor_map(ideal: dict[str, Any]) -> dict[tuple[int, int], tuple[int, int]]:
    factors: dict[tuple[int, int], tuple[int, int]] = {}
    for item in ideal["factors"]:
        prime = tuple(item["prime_generator"])
        exponent = int(item["exponent"])
        norm = int(item["prime_ideal_norm"])
        if len(prime) != 2 or exponent < 1 or norm < 2 or prime in factors:
            raise ValueError("invalid or duplicate ideal factor")
        factors[prime] = (exponent, norm)
    return factors


def _ideal_norm(factors: dict[tuple[int, int], tuple[int, int]]) -> int:
    result = 1
    for exponent, norm in factors.values():
        result *= norm**exponent
    return result


def verify_pair_gcd(pair: dict[str, Any]) -> int:
    """Check gcd, quotient conductor, lcm and norm identities from factors."""
    left = _factor_map(pair["left_column"]["ideal"])
    right = _factor_map(pair["right_column"]["ideal"])
    if any(exponent != 1 for exponent, _norm in (*left.values(), *right.values())):
        raise ValueError("this gcd/conductor split is pinned to squarefree source columns")
    left_norm = int(pair["left_column"]["ideal"]["norm"])
    right_norm = int(pair["right_column"]["ideal"]["norm"])
    if _ideal_norm(left) != left_norm or _ideal_norm(right) != right_norm:
        raise ValueError("source column ideal norm does not match its factors")

    common = {p: (min(left[p][0], right[p][0]), left[p][1]) for p in left.keys() & right.keys()}
    if any(left[p][1] != right[p][1] for p in left.keys() & right.keys()):
        raise ValueError("a shared prime ideal has inconsistent norm")
    conductor = {p: left[p] for p in left.keys() - right.keys()}
    conductor.update({p: right[p] for p in right.keys() - left.keys()})
    lcm = {p: (max(left.get(p, (0, 0))[0], right.get(p, (0, 0))[0]),
               left.get(p, right.get(p))[1]) for p in left.keys() | right.keys()}

    saved_gcd = _factor_map(pair["shared_zero_mask_gcd"])
    saved_conductor = _factor_map(pair["primitive_quotient_conductor"])
    saved_lcm = _factor_map(pair["full_period_lcm_ideal"])
    if saved_gcd != common or saved_conductor != conductor or saved_lcm != lcm:
        raise ValueError("saved gcd/conductor/lcm factors disagree with source columns")
    gcd_norm = _ideal_norm(common)
    conductor_norm = _ideal_norm(conductor)
    lcm_norm = _ideal_norm(lcm)
    if (int(pair["shared_zero_mask_gcd"]["norm"]) != gcd_norm
            or int(pair["primitive_quotient_conductor"]["norm"]) != conductor_norm
            or int(pair["full_period_lcm_norm_Q"]) != lcm_norm
            or int(pair["full_period_lcm_ideal"]["norm"]) != lcm_norm):
        raise ValueError("saved ideal norms disagree with their factorization")
    if left_norm * right_norm != gcd_norm * lcm_norm:
        raise ValueError("ideal gcd/lcm product identity failed")
    if lcm_norm != gcd_norm * conductor_norm:
        raise ValueError("full period is not gcd norm times primitive conductor norm")
    if pair.get("shared_primes_remain_zero_mask") is not True:
        raise ValueError("shared gcd zero-mask was not preserved")
    return gcd_norm


def _validate_panel(data: dict[str, Any]) -> tuple[int, int]:
    if data.get("schema") != "cf22-nonunit-pair-decomposition-v1":
        raise ValueError("unexpected decomposition schema")
    rows = data.get("rows")
    if not isinstance(rows, list) or len(rows) != EXPECTED_ROWS:
        raise ValueError("panel must contain exactly 20 frozen rows")
    total_pairs = 0
    max_gcd = 1
    ids: set[str] = set()
    for row in rows:
        row_id = row["id"]
        if row_id in ids:
            raise ValueError("duplicate configuration id")
        ids.add(row_id)
        pairs = row.get("pairs")
        if not isinstance(pairs, list) or len(pairs) != int(row["counts"]["pair_count"]):
            raise ValueError(f"pair count mismatch in {row_id}")
        seen: set[tuple[int, int]] = set()
        group_counts = {group: 0 for group in GROUPS}
        for pair in pairs:
            key = (int(pair["i"]), int(pair["j"]))
            if key[0] >= key[1] or key in seen:
                raise ValueError(f"non-unique unordered pair in {row_id}")
            seen.add(key)
            group = pair["group"]
            if group not in group_counts:
                raise ValueError(f"unknown signed group {group!r}")
            group_counts[group] += 1
            gcd_norm = verify_pair_gcd(pair)
            max_gcd = max(max_gcd, gcd_norm)
            physical = _interval(pair["physical_signed_contribution"])
            raw = _interval(pair["raw_signed_contribution"])
            total = _interval(pair["C_signed_contribution"])
            if not _overlaps(total, _sub(physical, raw)):
                raise ValueError(f"pair physical minus raw does not reassemble C in {row_id}")
        if sum(group_counts.values()) != len(pairs):
            raise ValueError(f"signed groups do not exhaust pairs in {row_id}")
        for group in GROUPS:
            stored = int(row["groups"][group]["pair_count"])
            if stored != group_counts[group]:
                raise ValueError(f"{group} pair count mismatch in {row_id}")
        total_pairs += len(pairs)
    if total_pairs != EXPECTED_PAIRS:
        raise ValueError(f"expected {EXPECTED_PAIRS} pairs, found {total_pairs}")
    return total_pairs, max_gcd


def _accumulate(pairs: list[dict[str, Any]], threshold: int) -> dict[str, Any]:
    if isinstance(threshold, bool) or not isinstance(threshold, int) or threshold < 1:
        raise ValueError("gcd norm threshold must be a positive integer")
    sides = {side: {g: {f: ZERO for f in FIELDS} for g in GROUPS}
             for side in ("main", "remainder")}
    counts = {side: {g: 0 for g in GROUPS} for side in sides}
    gcd_norms: list[int] = []
    for pair in pairs:
        gcd_norm = verify_pair_gcd(pair)
        gcd_norms.append(gcd_norm)
        side = "main" if gcd_norm <= threshold else "remainder"
        group = pair["group"]
        counts[side][group] += 1
        for field in FIELDS:
            sides[side][group][field] = _add(
                sides[side][group][field], _interval(pair[field])
            )

    result: dict[str, Any] = {"threshold_G": threshold, "max_pair_gcd_norm": max(gcd_norms)}
    result["sides"] = {}
    for side in ("main", "remainder"):
        side_groups: dict[str, Any] = {}
        for group in GROUPS:
            side_groups[group] = {
                "pair_count": counts[side][group],
                "C_signed": _record(sides[side][group]["C_signed_contribution"]),
                "physical_signed": _record(sides[side][group]["physical_signed_contribution"]),
                "raw_signed": _record(sides[side][group]["raw_signed_contribution"]),
            }
        side_groups["total"] = {
            "pair_count": sum(counts[side].values()),
            **{name: _record(_sum([sides[side][g][field] for g in GROUPS]))
               for name, field in (("C_signed", "C_signed_contribution"),
                                   ("physical_signed", "physical_signed_contribution"),
                                   ("raw_signed", "raw_signed_contribution"))},
        }
        result["sides"][side] = side_groups
    return result


def analyze_panel(data: dict[str, Any]) -> dict[str, Any]:
    total_pairs, max_gcd = _validate_panel(data)
    outputs = []
    for row in data["rows"]:
        original_c = _interval(row["full_C"])
        original_pair_sum = _interval(row["C_pair_sum"])
        original_groups = {g: _interval(row["groups"][g]["C_contribution"]) for g in GROUPS}
        full_pair_groups = {
            g: _sum([_interval(p["C_signed_contribution"]) for p in row["pairs"] if p["group"] == g])
            for g in GROUPS
        }
        if any(not _overlaps(full_pair_groups[g], original_groups[g]) for g in GROUPS):
            raise ValueError(f"full pair group sum fails saved group C in {row['id']}")
        full_pair_sum = _sum(list(full_pair_groups.values()))
        if not _overlaps(full_pair_sum, original_pair_sum) or not _overlaps(full_pair_sum, original_c):
            raise ValueError(f"full pair sum fails saved full C in {row['id']}")

        p_interval = _interval(row["parameters"]["P"])
        u = int(row["configuration"]["U"])
        pu = _mul(p_interval, (Fraction(u), Fraction(u)))
        thresholds = []
        for threshold in THRESHOLDS:
            split = _accumulate(row["pairs"], threshold)
            main_total = _interval(split["sides"]["main"]["total"]["C_signed"])
            remainder_total = _interval(split["sides"]["remainder"]["total"]["C_signed"])
            reassembled = _add(main_total, remainder_total)
            group_checks: dict[str, bool] = {}
            for group in GROUPS:
                main_group = _interval(split["sides"]["main"][group]["C_signed"])
                rem_group = _interval(split["sides"]["remainder"][group]["C_signed"])
                group_checks[group] = _overlaps(_add(main_group, rem_group), original_groups[group])
            if split["sides"]["main"]["total"]["pair_count"] + split["sides"]["remainder"]["total"]["pair_count"] != len(row["pairs"]):
                raise ValueError(f"split pair counts do not exhaust {row['id']} at G={threshold}")
            if not all(group_checks.values()) or not _overlaps(reassembled, original_pair_sum) or not _overlaps(reassembled, original_c):
                raise ValueError(f"split C does not reassemble full panel row {row['id']} at G={threshold}")

            main_positive = _positive_part(main_total)
            remainder_positive = _positive_part(remainder_total)
            full_positive = _positive_part(original_c)
            separation = _nonnegative_enclosure(
                _sub(_add(main_positive, remainder_positive), full_positive)
            )
            split.update({
                "partition_exhaustive": True,
                "group_C_reassembly_overlaps_saved": group_checks,
                "reassembled_C": _record(reassembled),
                "reassembled_C_overlaps_saved_full_C": _overlaps(reassembled, original_c),
                "reassembled_C_overlaps_saved_pair_sum": _overlaps(reassembled, original_pair_sum),
                "positive_part_main": _record(main_positive),
                "positive_part_remainder": _record(remainder_positive),
                "positive_part_full_C": _record(full_positive),
                "positive_part_separation_penalty": _record(separation),
                "remainder_over_PU": _record(_divide_by_positive(remainder_total, pu)),
                "all_three_signed_groups_retained": True,
            })
            thresholds.append(split)
        outputs.append({
            "id": row["id"],
            "configuration": row["configuration"],
            "P": _record(p_interval),
            "U": u,
            "pair_count": len(row["pairs"]),
            "full_C_saved": _record(original_c),
            "group_C_saved": {g: _record(original_groups[g]) for g in GROUPS},
            "thresholds": thresholds,
        })

    return {
        "schema": "cf22-gcd-pair-split-v1",
        "status": "PASS_FINITE_PANEL_REASSEMBLY",
        "scope": "finite saved panel only; no cofinal CF22 estimate or gain is proved",
        "analysis_base_commit": ANALYSIS_BASE_COMMIT,
        "input": {
            "path": "experiments/cf22_pysr/correlation/decomposition.json.gz",
            "sha256": INPUT_SHA256,
            "schema": data["schema"],
            "panel_execution_head": data["provenance"]["execution_head"],
            "panel_pinned_input_commit": data["provenance"]["pinned_input_commit"],
            "rows": len(data["rows"]),
            "pairs": total_pairs,
            "groups": list(GROUPS),
            "gcd_norm_definition": "norm(shared_zero_mask_gcd), reconstructed from exact common ideal factors",
        },
        "thresholds": list(THRESHOLDS),
        "max_observed_gcd_norm": max_gcd,
        "trivial_reference": {
            "G": max_gcd + 1,
            "label": "TRIVIAL_FULL_PANEL_NO_REMAINDER",
            "meaning": "G exceeds every saved pair gcd norm, so main is all C and remainder is empty",
            "included_in_parameter_sweep": False,
        },
        "rows": outputs,
        "limitations": [
            "All pair contributions remain signed; absolute pair sums are not used as a substitute.",
            "RR, cross, and AA are retained in both main and remainder, with physical/raw signed subtotals.",
            "A smaller finite-panel remainder is a diagnostic only; no bound for the main term is proved.",
        ],
    }


def load_panel(path: Path = INPUT) -> tuple[dict[str, Any], str]:
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != INPUT_SHA256:
        raise ValueError(f"input SHA256 mismatch: expected {INPUT_SHA256}, got {digest}")
    with gzip.open(path, "rt", encoding="utf-8") as handle:
        data = json.load(handle)
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise ValueError("input changed while being read")
    return data, digest


def build_report(path: Path = INPUT) -> dict[str, Any]:
    data, digest = load_panel(path)
    report = analyze_panel(data)
    report["input"]["sha256"] = digest
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=INPUT)
    parser.add_argument("--output", type=Path, help="exclusive output JSON path; stdout if omitted")
    args = parser.parse_args()
    if args.output is not None and args.output.exists():
        raise FileExistsError(f"refusing to overwrite {args.output}")
    report = build_report(args.input)
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(payload, end="")
    else:
        with args.output.open("x", encoding="utf-8") as handle:
            handle.write(payload)


if __name__ == "__main__":
    main()
