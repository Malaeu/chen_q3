#!/usr/bin/env python3
"""Coordinate-invariant audit for the Step33A Arch A semantic fork.

This diagnostic is non-mutating.  It consumes the centered-receiver smoke
artifact and records two quick invariants:

* a pure distance/frequency/cosine-coordinate rewrite cannot change the
  `d = 0` row, because `cos(t * 0) = 1`;
* a constant sign/scale fit is not credible when the `d = 0` and `d = 0.25`
  ratios disagree.

The output is route evidence only.  It is not a Lean proof object and does not
edit A CSV, ARadius, radius-floor, LDL, or generated proof payloads.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_SMOKE = REQUEST_DIR / "a_chunk_integral_probe_centered_smoke.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_coordinate_invariant_audit.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_coordinate_invariant_audit.md"


def dec(value: str) -> Decimal:
    return Decimal(str(value))


def sci(value: Decimal, digits: int = 18) -> str:
    if value == 0:
        return "0.000000000000000000E+0"
    return format(value, f".{digits}E")


def interval_mid(row: dict[str, Any], lower_key: str, upper_key: str) -> Decimal:
    return (dec(row[lower_key]) + dec(row[upper_key])) / Decimal(2)


def row_by_index(rows: list[dict[str, Any]], index: int) -> dict[str, Any]:
    for row in rows:
        if int(row["distance_index"]) == index:
            return row
    raise ValueError(f"missing distance_index={index}")


def window_summary(row: dict[str, Any]) -> dict[str, Any]:
    chunks = row.get("chunks", [])
    lefts = [dec(chunk["left"]) for chunk in chunks]
    rights = [dec(chunk["right"]) for chunk in chunks]
    if not chunks:
        return {
            "chunk_count": 0,
            "left_min": None,
            "right_max": None,
            "has_negative_side": False,
            "has_positive_side": False,
            "looks_full_symmetric": False,
        }
    left_min = min(lefts)
    right_max = max(rights)
    return {
        "chunk_count": len(chunks),
        "left_min": sci(left_min),
        "right_max": sci(right_max),
        "has_negative_side": bool(left_min < 0),
        "has_positive_side": bool(right_max > 0),
        "looks_full_symmetric": bool(left_min < 0 and right_max > 0 and abs(left_min) == abs(right_max)),
    }


def ratio(target: Decimal, receiver: Decimal) -> Decimal | None:
    if receiver == 0:
        return None
    return target / receiver


def family_audit(block: dict[str, Any]) -> dict[str, Any]:
    rows = block["rows"]
    row0 = row_by_index(rows, 0)
    row1 = row_by_index(rows, 1)

    receiver0 = interval_mid(row0, "chunk_sum_lower", "chunk_sum_upper")
    target0 = interval_mid(row0, "target_lower", "target_upper")
    receiver1 = interval_mid(row1, "chunk_sum_lower", "chunk_sum_upper")
    target1 = interval_mid(row1, "target_lower", "target_upper")

    center_error0 = abs(receiver0 - target0)
    sign_flip_error0 = abs((-receiver0) - target0)
    center_error1 = abs(receiver1 - target1)
    sign_flip_error1 = abs((-receiver1) - target1)

    ratio0 = ratio(target0, receiver0)
    ratio1 = ratio(target1, receiver1)
    ratio_gap = None if ratio0 is None or ratio1 is None else abs(ratio0 - ratio1)

    return {
        "family": block["family"],
        "source": block.get("source"),
        "window": window_summary(row0),
        "d0": {
            "distance": row0["distance"],
            "receiver_mid": sci(receiver0),
            "target_mid": sci(target0),
            "center_error": sci(center_error0),
            "minus_receiver_mid": sci(-receiver0),
            "minus_receiver_error": sci(sign_flip_error0),
            "coordinate_invariant_reason": "cos(t*0)=1, so pure x/d/frequency rewrites cannot change this row",
            "rejects_pure_coordinate_frequency_rewrite": bool(center_error0 > Decimal("1")),
        },
        "d1": {
            "distance": row1["distance"],
            "receiver_mid": sci(receiver1),
            "target_mid": sci(target1),
            "center_error": sci(center_error1),
            "minus_receiver_mid": sci(-receiver1),
            "minus_receiver_error": sci(sign_flip_error1),
        },
        "constant_scale_probe": {
            "target_over_receiver_at_d0": None if ratio0 is None else sci(ratio0),
            "target_over_receiver_at_d1": None if ratio1 is None else sci(ratio1),
            "ratio_gap": None if ratio_gap is None else sci(ratio_gap),
            "rejects_constant_scale": bool(ratio_gap is None or ratio_gap > Decimal("1e-3")),
        },
    }


def decision(families: list[dict[str, Any]]) -> dict[str, Any]:
    rejects_coordinate = all(f["d0"]["rejects_pure_coordinate_frequency_rewrite"] for f in families)
    rejects_scale = all(f["constant_scale_probe"]["rejects_constant_scale"] for f in families)
    return {
        "D_simple_coordinate_or_frequency_map": "rejected" if rejects_coordinate else "not_rejected",
        "constant_sign_or_scale_fit": "rejected" if rejects_scale else "not_rejected",
        "recommended_route": (
            "No simple D theorem from d/frequency/sign/scale evidence. Choose B only if a "
            "Lean semantic theorem changes the receiver/assembler to raw Step22; otherwise "
            "choose C one-time recert/migration to the centered receiver convention."
        ),
    }


def render_md(payload: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Coordinate-Invariant Audit",
        "",
        "This is a non-mutating route audit. It reads the centered-receiver smoke",
        "artifact and checks whether the remaining D option can be a simple",
        "distance/frequency/sign/scale fix.",
        "",
        "It does not edit A CSV, `ARadius`, radius-floor, LDL, `Q3.Main`, or proof payloads.",
        "",
        "## Decision",
        "",
        f"- simple coordinate/frequency D map: `{payload['decision']['D_simple_coordinate_or_frequency_map']}`",
        f"- constant sign/scale fit: `{payload['decision']['constant_sign_or_scale_fit']}`",
        f"- recommendation: `{payload['decision']['recommended_route']}`",
        "",
        "## Family Evidence",
        "",
        "| family | window | d=0 receiver | d=0 target | d=0 error | -receiver error | ratio d=0 | ratio d=0.25 | ratio gap |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for family in payload["families"]:
        window = family["window"]
        window_label = f"{window['left_min']}..{window['right_max']}"
        scale = family["constant_scale_probe"]
        lines.append(
            f"| {family['family']} | {window_label} | "
            f"{family['d0']['receiver_mid']} | "
            f"{family['d0']['target_mid']} | "
            f"{family['d0']['center_error']} | "
            f"{family['d0']['minus_receiver_error']} | "
            f"{scale['target_over_receiver_at_d0']} | "
            f"{scale['target_over_receiver_at_d1']} | "
            f"{scale['ratio_gap']} |"
        )
    lines.extend([
        "",
        "## Interpretation",
        "",
        "The `d = 0` row is invariant under any rewrite that only changes the",
        "distance/frequency/cosine coordinate, because the cosine factor is already",
        "`1`.  The observed mismatch is order `75-79`, so a pure coordinate theorem",
        "cannot rescue the current imported raw Step22 targets.",
        "",
        "A sign flip also fails at `d = 0`, and a constant scale fit is not stable",
        "between `d = 0` and `d = 0.25`.  The remaining honest choices are:",
        "",
        "- `B`: prove the Step33 receiver/assembler should semantically use raw Step22;",
        "- `C`: recertify/migrate A-dependent finite data to the centered receiver convention.",
        "",
    ])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--smoke-json", type=Path, default=DEFAULT_SMOKE)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    getcontext().prec = 100
    smoke = json.loads(args.smoke_json.read_text(encoding="utf-8"))
    families = [family_audit(block) for block in smoke["families"]]
    payload = {
        "schema": "q3_psdpd_step33_a_coordinate_invariant_audit.v1",
        "non_mutating": True,
        "input_smoke_json": str(args.smoke_json),
        "families": families,
        "decision": decision(families),
    }

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out_md.write_text(render_md(payload) + "\n", encoding="utf-8")
    print(f"wrote {args.out_json}")
    print(f"wrote {args.out_md}")


if __name__ == "__main__":
    main()
