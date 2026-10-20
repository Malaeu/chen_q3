#!/usr/bin/env python3
"""Certify finite-panel exclusions for simple envelopes of the saved full CF22 C.

This is a finite-data diagnostic. It never modifies or reconstructs C from a
subset of pair terms: every row starts from the saved full-C interval, and the
RR + cross + AA group sum is independently required to overlap it.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import platform
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

from flint import arb, ctx, fmpq

SCRIPT = Path(__file__).resolve()
PRUNING_DIR = SCRIPT.parent
REPO = SCRIPT.parents[3]
CF22_DIR = REPO / "experiments/cf22_pysr"
DEFAULT_MAIN = CF22_DIR / "nonunit/main.json"
DEFAULT_HELDOUT = CF22_DIR / "nonunit/heldout.json"
DEFAULT_FREEZE = CF22_DIR / "nonunit/heldout_freeze.json"
DEFAULT_PLAN = CF22_DIR / "nonunit/plan.json"
DEFAULT_GROUPS = CF22_DIR / "correlation/summary.json"
DEFAULT_DECOMPOSITION = CF22_DIR / "correlation/decomposition.json.gz"
DEFAULT_OUTPUT = PRUNING_DIR / "panel_pruning.json"
PRECISION_BITS = 192
DELTA_CAP = Fraction(1, 100)
ALPHA_CAPS = (Fraction(0), Fraction(1, 1000), Fraction(1, 100), Fraction(1, 10))
DELTAS = (Fraction(0), Fraction(1, 200), Fraction(1, 100))
GROUP_NAMES = ("rough_rough", "cross", "affected_affected")
EXPECTED_INPUT_SHA256 = {
    "main.json": "5986f2f5fbd8cc87116befb1ac3d08222804ec3f79c1ceb4e0408182c943bdcb",
    "heldout.json": "87b6ed649621fb428e71276fcc62701501140afc2a9bff320337ee54596c6cfe",
    "heldout_freeze.json": "941fb6ca36a1efbc0ce0d473db933b8ddd1cdbb1930504aa1b22006fb2206c06",
    "plan.json": "8fcaad6f072b58a1be182767ec0c85ca4a2a42c4856d641c5099a4bc3c3b5fb8",
    "correlation_summary.json": "c534463e782c637bf7aa467800dd571997da95e855d8443aa6f9acc47ca18ef5",
    "decomposition.json.gz": "74e888523228566fbb5140ed24dd8b9abbd33a07af9eba72519802dd18e9f38d",
}
EXPECTED_DATA_SOURCE_COMMIT = "580bd4dd68549a034ad0c0287524e714f1570b71"
EXPECTED_GROUP_SOURCE_COMMIT = "f1993ec6a7933418c38c305a13a3221037b9447a"

# The small exact helper surface is imported from the existing certified source
# evaluator. It supplies Arb rational powers and outward decimal endpoints.
if str(CF22_DIR) not in sys.path:
    sys.path.insert(0, str(CF22_DIR))
import evaluate as source  # noqa: E402


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256(path.read_bytes())


def _fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def _fraction(value: Any) -> Fraction:
    if isinstance(value, Fraction):
        return value
    return Fraction(str(value))


def _arb_fraction(value: Fraction | int) -> arb:
    f = Fraction(value)
    return arb(fmpq(f.numerator, f.denominator))


def _interval(record: dict[str, Any], label: str) -> arb:
    if not isinstance(record, dict) or "lower" not in record or "upper" not in record:
        raise ValueError(f"{label} must be a lower/upper interval record")
    try:
        record_lower = Fraction(str(record["lower"]))
        record_upper = Fraction(str(record["upper"]))
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"{label} has invalid endpoints") from exc
    if record_lower > record_upper:
        raise ValueError(f"{label} has reversed endpoints")
    return arb(str(record["lower"])).union(arb(str(record["upper"])))


def _interval_record(value: arb) -> dict[str, str]:
    lo, hi, endpoints = source.ball_endpoints(value)
    return {"lower": endpoints["lower"], "upper": endpoints["upper"],
            "width": _fraction_text(hi - lo)}


def _endpoints(value: arb) -> tuple[Fraction, Fraction]:
    lo, hi, _ = source.ball_endpoints(value)
    return lo, hi


def _read_json(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data, raw


def _plan_configs(plan: dict[str, Any]) -> dict[str, dict[str, Any]]:
    if plan.get("schema") != "cf22-nonunit-plan-v1" or plan.get("scope") != "OFF_SCHEDULE_MASK_DIAGNOSTIC":
        raise ValueError("unexpected nonunit panel plan")
    configs = plan.get("configs")
    if not isinstance(configs, list) or len(configs) != 20:
        raise ValueError("the frozen plan must contain exactly 20 configurations")
    by_id: dict[str, dict[str, Any]] = {}
    for config in configs:
        if not isinstance(config, dict) or not isinstance(config.get("id"), str):
            raise ValueError("malformed planned configuration")
        if config["id"] in by_id:
            raise ValueError(f"duplicate planned configuration {config['id']}")
        by_id[config["id"]] = config
    return by_id


def _check_config(row: dict[str, Any], planned: dict[str, Any], label: str) -> None:
    if row.get("id") != planned.get("id"):
        raise ValueError(f"configuration id mismatch in {label}")
    actual = row.get("configuration")
    if not isinstance(actual, dict):
        raise ValueError(f"missing configuration in {label}")
    for key in ("U", "P", "orientation"):
        if actual.get(key) != planned.get(key):
            raise ValueError(f"{label} {key} differs from frozen plan")
    for key in ("r", "ell"):
        if _fraction(actual.get(key, "0")) != _fraction(planned.get(key, "0")):
            raise ValueError(f"{label} {key} differs from frozen plan")
    if actual.get("scope") != "OFF_SCHEDULE_MASK_DIAGNOSTIC":
        raise ValueError(f"{label} is not in the finite off-schedule panel")


def _row_inputs(row: dict[str, Any], label: str) -> tuple[arb, arb, arb, int]:
    parameters = row.get("parameters")
    if not isinstance(parameters, dict):
        raise ValueError(f"{label} has no saved source parameters")
    config = row["configuration"]
    U = config.get("U")
    if not isinstance(U, int) or U <= 1:
        raise ValueError(f"{label} must have integer U > 1")
    P = _interval(parameters.get("P"), f"{label}.parameters.P")
    L = _interval(parameters.get("L"), f"{label}.parameters.L")
    p_lo, _ = _endpoints(P)
    l_lo, _ = _endpoints(L)
    if p_lo <= 0 or l_lo <= 0:
        raise ValueError(f"{label} requires positive saved P and L intervals")
    return P, L, _interval(row.get("full_C"), f"{label}.full_C"), U


def _group_checks(full_c: arb, group_row: dict[str, Any], row_id: str) -> dict[str, Any]:
    groups = group_row.get("groups")
    if not isinstance(groups, dict) or set(GROUP_NAMES) - set(groups):
        raise ValueError(f"{row_id} is missing one of RR, cross, AA contributions")
    intervals: dict[str, arb] = {}
    for name in GROUP_NAMES:
        intervals[name] = _interval(groups[name].get("C_contribution"),
                                    f"{row_id}.groups.{name}.C_contribution")
    group_sum = intervals["rough_rough"] + intervals["cross"] + intervals["affected_affected"]
    pair_sum = _interval(group_row.get("C_pair_sum"), f"{row_id}.C_pair_sum")
    saved_c = _interval(group_row.get("saved_C"), f"{row_id}.saved_C")
    residual = _interval(group_row.get("reassembly_residual"), f"{row_id}.reassembly_residual")
    if not group_sum.overlaps(pair_sum):
        raise ArithmeticError(f"{row_id}: RR+cross+AA do not overlap C_pair_sum")
    if not group_sum.overlaps(saved_c):
        raise ArithmeticError(f"{row_id}: RR+cross+AA do not overlap group-saved full C")
    if not group_sum.overlaps(full_c):
        raise ArithmeticError(f"{row_id}: RR+cross+AA do not directly overlap nonunit full C")
    if not pair_sum.overlaps(full_c) or not saved_c.overlaps(full_c):
        raise ArithmeticError(f"{row_id}: pair decomposition does not overlap nonunit full C")
    if not residual.overlaps(arb(0)):
        raise ArithmeticError(f"{row_id}: saved group reassembly residual excludes zero")
    cross_nonzero = not intervals["cross"].overlaps(arb(0))
    return {
        "rough_rough": _interval_record(intervals["rough_rough"]),
        "cross": _interval_record(intervals["cross"]),
        "affected_affected": _interval_record(intervals["affected_affected"]),
        "sum_RR_cross_AA": _interval_record(group_sum),
        "C_pair_sum": _interval_record(pair_sum),
        "group_saved_full_C": _interval_record(saved_c),
        "saved_reassembly_residual": _interval_record(residual),
        "sum_overlaps_pair_sum": True,
        "sum_overlaps_group_full_C": True,
        "sum_overlaps_nonunit_full_C": True,
        "cross_excludes_zero": cross_nonzero,
    }


def _expected_subsets(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    return {
        "all_20": rows,
        "production_P": [r for r in rows if r["configuration"]["P"] == "production"],
        "independent_P": [r for r in rows if r["configuration"]["P"] != "production"],
        "fixed_P_7": [r for r in rows if r["configuration"]["P"] == 7],
        "fixed_P_13": [r for r in rows if r["configuration"]["P"] == 13],
        "fixed_P_49": [r for r in rows if r["configuration"]["P"] == 49],
    }


def _threshold_table(rows: list[dict[str, Any]], prepared: dict[str, dict[str, Any]]) -> dict[str, Any]:
    entries: list[dict[str, Any]] = []
    for alpha in ALPHA_CAPS:
        for delta in DELTAS:
            row_thresholds: list[tuple[str, Fraction, Fraction]] = []
            for row in rows:
                rid = row["id"]
                item = prepared[rid]
                denominator = item["S"] * (arb(item["U"]) ** fmpq(-delta.numerator, delta.denominator))
                dlo, _ = _endpoints(denominator)
                if dlo <= 0:
                    raise ArithmeticError(f"{rid}: nonpositive S U^-delta interval")
                threshold = (item["C"] - _arb_fraction(alpha) * item["PU"]) / denominator
                tlo, thi = _endpoints(threshold)
                row_thresholds.append((rid, tlo, thi))
            witness_id, max_lower, _ = max(row_thresholds, key=lambda t: t[1])
            max_upper = max(thi for _, _, thi in row_thresholds)
            required_lo = max(Fraction(0), max_lower)
            required_hi = max(Fraction(0), max_upper)
            entries.append({
                "alpha": _fraction_text(alpha),
                "delta": _fraction_text(delta),
                "necessary_kappa_threshold_interval": {
                    "lower": _fraction_text(required_lo),
                    "upper": _fraction_text(required_hi),
                },
                "witness_by_largest_lower_threshold": witness_id,
                "row_thresholds": [
                    {"id": rid, "lower": _fraction_text(tlo), "upper": _fraction_text(thi)}
                    for rid, tlo, thi in row_thresholds
                ],
            })
    return {"formula": "kappa >= max_i (C_i - alpha*P_i*U_i)/(S_i*U_i^(-delta))",
            "thresholds": entries}


def _box_check(name: str, rows: list[dict[str, Any]], prepared: dict[str, dict[str, Any]],
               alpha_cap: Fraction, kappa_cap: Fraction,
               delta_lo: Fraction, delta_hi: Fraction,
               requested_witness: str | None = None) -> dict[str, Any]:
    # Since U>1 and kappa>=0, U^-delta is largest at the left end of the
    # interval. Testing the upper alpha/kappa faces and delta_lo therefore
    # gives the largest possible envelope over the entire box.
    if alpha_cap < 0 or kappa_cap < 0:
        raise ValueError("coefficient-box caps must respect alpha,kappa >= 0")
    if delta_lo < 0 or delta_hi < delta_lo:
        raise ValueError("delta box must be ordered and nonnegative")
    margins: list[tuple[str, arb, arb, arb]] = []
    for row in rows:
        rid = row["id"]
        item = prepared[rid]
        denom_factor = arb(item["U"]) ** fmpq(-delta_lo.numerator, delta_lo.denominator)
        envelope = _arb_fraction(alpha_cap) * item["PU"] + _arb_fraction(kappa_cap) * item["S"] * denom_factor
        margin = item["C"] - envelope
        margins.append((rid, margin, envelope, item["C"]))
    refuting = [(rid, margin, envelope, c) for rid, margin, envelope, c in margins
                if _endpoints(margin)[0] > 0]
    chosen = next((item for item in refuting if item[0] == requested_witness), None) if requested_witness else None
    if requested_witness and chosen is None:
        raise ArithmeticError(f"requested witness {requested_witness} did not strictly refute {name}")
    if chosen is None and refuting:
        chosen = max(refuting, key=lambda t: _endpoints(t[1])[0])
    if chosen is None:
        status = "NOT_REFUTED_ON_PANEL"
        witness_record = None
    else:
        rid, margin, envelope, c = chosen
        status = "REFUTED_ON_PANEL"
        witness_record = {
            "id": rid,
            "full_C": _interval_record(c),
            "max_envelope_on_box": _interval_record(envelope),
            "strict_margin_C_minus_envelope": _interval_record(margin),
            "strict_lower_margin_positive": True,
            "delta_value_used_for_largest_envelope": _fraction_text(delta_lo),
            "groups_RR_cross_AA": prepared[rid]["group_check"],
        }
    return {
        "name": name,
        "status": status,
        "coefficient_box": {
            "alpha": ["0", _fraction_text(alpha_cap)],
            "kappa": ["0", _fraction_text(kappa_cap)],
            "delta": [_fraction_text(delta_lo), _fraction_text(delta_hi)],
        },
        "subset_rows_checked": [r["id"] for r in rows],
        "row_count": len(rows),
        "proof_rule": "C.lower > (alpha_cap*P*U + kappa_cap*S*U^(-delta_lo)).upper; monotonicity over the whole coefficient box",
        "witness": witness_record,
    }


def analyze_data(main: dict[str, Any], heldout: dict[str, Any],
                 groups_data: dict[str, Any], decomposition_sha256: str,
                 plan: dict[str, Any]) -> dict[str, Any]:
    """Validate all saved rows and compute finite-panel coefficient exclusions."""
    ctx.prec = PRECISION_BITS
    planned = _plan_configs(plan)
    all_rows: list[dict[str, Any]] = []
    for dataset_name, data in (("main", main), ("heldout", heldout)):
        if data.get("scope") != "OFF_SCHEDULE_MASK_DIAGNOSTIC":
            raise ValueError(f"{dataset_name} data are outside the pinned diagnostic scope")
        if data.get("provenance", {}).get("baseline_status") != "BASELINES_FROZEN_BEFORE_NEW_EVALUATIONS":
            raise ValueError(f"{dataset_name} baseline was not frozen")
        rows = data.get("rows")
        if not isinstance(rows, list):
            raise ValueError(f"{dataset_name} has no row array")
        all_rows.extend(rows)
    if len(all_rows) != 20:
        raise ValueError(f"expected exactly 20 full-C rows, got {len(all_rows)}")
    ids = [r.get("id") for r in all_rows]
    if len(set(ids)) != 20 or set(ids) != set(planned):
        raise ValueError("full-C rows do not exactly match the frozen 20-row plan")
    if groups_data.get("scope") != "FINITE_OFF_SCHEDULE_PAIR_DIAGNOSTIC":
        raise ValueError("group summary has unexpected scope")
    if groups_data.get("decomposition_sha256") != decomposition_sha256:
        raise ValueError("group summary does not match the saved decomposition bytes")
    if groups_data.get("panel_checks", {}).get("exactly_20_configs") is not True:
        raise ValueError("saved group summary does not declare the frozen 20-row panel")
    group_rows = groups_data.get("rows")
    if not isinstance(group_rows, list) or len(group_rows) != 20:
        raise ValueError("group summary must contain exactly 20 rows")
    group_by_id = {r.get("id"): r for r in group_rows}
    if len(group_by_id) != 20 or set(group_by_id) != set(planned):
        raise ValueError("group summary rows do not exactly match frozen plan")

    output_rows: list[dict[str, Any]] = []
    prepared: dict[str, dict[str, Any]] = {}
    cross_nonzero_count = 0
    for row in all_rows:
        rid = row["id"]
        plan_row = planned[rid]
        _check_config(row, plan_row, f"full-C row {rid}")
        group_row = group_by_id[rid]
        _check_config(group_row, plan_row, f"group row {rid}")
        P, L, C, U = _row_inputs(row, rid)
        c_alias = _interval(row.get("C"), f"{rid}.C")
        if not C.overlaps(c_alias):
            raise ArithmeticError(f"{rid}: full_C and C fields disagree")
        group_check = _group_checks(C, group_row, rid)
        if group_check["cross_excludes_zero"]:
            cross_nonzero_count += 1
        S = P * source.rational_exponent(U, Fraction(1, 6)) * (L ** fmpq(5, 6))
        PU = P * U
        v = (arb(U) / L) ** fmpq(5, 6)
        slo, _ = _endpoints(S)
        if slo <= 0:
            raise ArithmeticError(f"{rid}: normalizer S is not certified positive")
        q = C / S
        prepared[rid] = {"C": C, "P": P, "L": L, "U": U, "S": S, "PU": PU,
                         "q": q, "v": v, "group_check": group_check}
        output_rows.append({
            "id": rid,
            "configuration": row["configuration"],
            "full_C": _interval_record(C),
            "P": _interval_record(P),
            "L": _interval_record(L),
            "S_equals_P_U_1/6_L_5/6": _interval_record(S),
            "P_times_U": _interval_record(PU),
            "normalized_q_C_over_S": _interval_record(q),
            "normalized_v_U_over_L_5/6": _interval_record(v),
            "pair_group_reassembly": group_check,
        })
    if cross_nonzero_count == 0:
        raise ArithmeticError("all cross-group intervals are exactly zero; mixed terms were lost")

    subsets = _expected_subsets(all_rows)
    subset_reports = {name: {"row_count": len(rows),
                             "row_ids": [r["id"] for r in rows],
                             "necessary_thresholds": _threshold_table(rows, prepared)}
                      for name, rows in subsets.items()}
    # These two boxes answer the immediate panel question: fixed independent P
    # and the production P rule are both tested against all rows in their scope.
    boxes = [
        _box_check("independent_P_alpha_le_1e-2_kappa_le_3e-3",
                   subsets["independent_P"], prepared,
                   Fraction(1, 100), Fraction(3, 1000), Fraction(0), DELTA_CAP,
                   "U64_P13_o1"),
        _box_check("all_panel_alpha_le_1e-2_kappa_le_19e-3",
                   subsets["all_20"], prepared,
                   Fraction(1, 100), Fraction(19, 1000), Fraction(0), DELTA_CAP,
                   "U64_Pproduction_o1"),
        _box_check("negative_control_alpha_le_1e-1_kappa_le_1e-1",
                   subsets["all_20"], prepared,
                   Fraction(1, 10), Fraction(1, 10), Fraction(0), DELTA_CAP),
    ]
    if boxes[0]["status"] != "REFUTED_ON_PANEL" or boxes[1]["status"] != "REFUTED_ON_PANEL":
        raise ArithmeticError("expected narrow coefficient boxes were not refuted by their saved witnesses")
    if boxes[2]["status"] != "NOT_REFUTED_ON_PANEL":
        raise ArithmeticError("negative-control box unexpectedly refuted on this panel")
    return {
        "schema": "cf22-full-C-finite-panel-pruning-v1",
        "status": "PASS_FINITE_PANEL_ONLY",
        "scope": "FINITE_OFF_SCHEDULE_MASK_PANEL",
        "source_claim": "No cofinal CF22 estimate, universal statement, or RH result is established.",
        "panel": {
            "row_count": len(output_rows),
            "mixed_cross_nonzero_rows": cross_nonzero_count,
            "all_rows_use_saved_full_C": True,
            "all_rows_reassemble_from_RR_plus_cross_plus_AA": True,
            "group_intervals_overlap_saved_full_C": True,
            "group_names": list(GROUP_NAMES),
            "rows": output_rows,
        },
        "family": {
            "raw_upper_bound": "C <= alpha*P*U + kappa*S*U^(-delta)",
            "normalizer": "S=P*U^(1/6)*L^(5/6)",
            "normalized_equivalent": "q=C/S <= alpha*(U/L)^(5/6) + kappa*U^(-delta)",
            "coefficient_domain": "alpha>=0, kappa>=0, delta in [0,1/100]",
            "interval_rule": "A box is refuted only when one saved full-C lower endpoint is strictly above the interval upper endpoint of the largest envelope allowed anywhere in the box.",
        },
        "subsets": subset_reports,
        "coefficient_boxes": boxes,
        "limitations": [
            "This is a finite panel diagnostic at the saved U, P, orientation, profile, and r/ell values only.",
            "The envelope family is a test family; its coefficient box is not a theorem about every possible CF22 bound.",
            "NOT_REFUTED_ON_PANEL means only that no saved row strictly refuted the whole box.",
            "RR, cross, and AA signed contributions are all retained and reassembled; no absolute-value or omission shortcut is used.",
        ],
    }


def load_and_analyze(root: Path = REPO) -> dict[str, Any]:
    root = root.resolve()
    base = root / "experiments/cf22_pysr"
    main, main_raw = _read_json(base / "nonunit/main.json")
    heldout, heldout_raw = _read_json(base / "nonunit/heldout.json")
    freeze, _ = _read_json(base / "nonunit/heldout_freeze.json")
    plan, plan_raw = _read_json(base / "nonunit/plan.json")
    groups, groups_raw = _read_json(base / "correlation/summary.json")
    decomposition_path = base / "correlation/decomposition.json.gz"
    decomposition_raw = decomposition_path.read_bytes()
    freeze_hashes = freeze.get("sha256", {})
    raw_inputs = {
        "main.json": main_raw,
        "heldout.json": heldout_raw,
        "heldout_freeze.json": (base / "nonunit/heldout_freeze.json").read_bytes(),
        "plan.json": plan_raw,
        "correlation_summary.json": groups_raw,
        "decomposition.json.gz": decomposition_raw,
    }
    for name, raw in raw_inputs.items():
        if _sha256(raw) != EXPECTED_INPUT_SHA256[name]:
            raise ValueError(f"{name} differs from the pinned panel artifact")
    for name in ("main.json", "plan.json"):
        if freeze_hashes.get(name) != _sha256(raw_inputs[name]):
            raise ValueError(f"{name} does not match heldout freeze hash")
    if groups.get("decomposition_sha256") != _sha256(decomposition_raw):
        raise ValueError("group summary does not match the saved decomposition hash")
    if main.get("provenance", {}).get("source_commit") != EXPECTED_DATA_SOURCE_COMMIT:
        raise ValueError("full-C data source commit differs from the pinned source")
    if heldout.get("provenance", {}).get("source_commit") != EXPECTED_DATA_SOURCE_COMMIT:
        raise ValueError("heldout full-C source commit differs from the pinned source")
    if groups.get("source_commit") != EXPECTED_GROUP_SOURCE_COMMIT:
        raise ValueError("pair decomposition source commit differs from the pinned source")
    # The compressed pair ledger is parsed as a second shape/provenance check;
    # its actual mathematical contribution is already represented by the frozen
    # group summary and independently replayed above.
    try:
        with gzip.open(decomposition_path, "rt", encoding="utf-8") as stream:
            ledger = json.load(stream)
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError("pair decomposition archive is unreadable") from exc
    if not isinstance(ledger, dict) or not isinstance(ledger.get("rows"), list) or len(ledger["rows"]) != 20:
        raise ValueError("pair decomposition archive does not contain 20 configurations")
    return analyze_data(main, heldout, groups, _sha256(decomposition_raw), plan) | {
        "provenance": {
            "analysis_git_head": _git_head(root),
            "pruner_sha256": _sha256_file(SCRIPT),
            "data_source_commit": main.get("provenance", {}).get("source_commit"),
            "pair_decomposition_source_commit": groups.get("source_commit"),
            "input_sha256": {
                "main.json": _sha256(main_raw),
                "heldout.json": _sha256(heldout_raw),
                "heldout_freeze.json": _sha256((base / "nonunit/heldout_freeze.json").read_bytes()),
                "plan.json": _sha256(plan_raw),
                "correlation_summary.json": _sha256(groups_raw),
                "decomposition.json.gz": _sha256(decomposition_raw),
            },
            "precision_bits": PRECISION_BITS,
            "python": platform.python_version(),
            "flint": __import__("flint").__version__,
        },
    }


def _git_head(root: Path) -> str | None:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root,
                                       text=True, stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO,
                        help="repository root containing the pinned CF22 data")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT,
                        help="write the report using exclusive creation")
    args = parser.parse_args()
    report = load_and_analyze(args.root)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", encoding="utf-8") as stream:
        json.dump(report, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    print(json.dumps({"status": report["status"],
                      "rows": report["panel"]["row_count"],
                      "boxes": [{"name": b["name"], "status": b["status"],
                                 "witness": (b["witness"] or {}).get("id")}
                                for b in report["coefficient_boxes"]],
                      "output": str(args.output)}, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
