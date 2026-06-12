#!/usr/bin/env python3
"""Diagnose the Step33A.1-A positive-tail-window proof route.

This is a guardrail artifact, not a proof producer.  It checks the current
A-window contract and records whether a nonnegative absolute majorant can be
used as the final signed positive-window payload.  The answer is expected to
be no when any generated signed upper window is negative.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_CONTRACT = REQUEST_DIR / "a_window_contract.json"


def dec(text: str) -> Decimal:
    return Decimal(str(text))


def dstr(value: Decimal) -> str:
    if value == 0:
        return "0.000000000000000000E+0"
    return format(value, ".18E")


def load_contract(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    schema = payload.get("schema")
    if schema != "q3_psdpd_step33_a_window_contract.v1":
        raise ValueError(f"{path}: unexpected schema {schema!r}")
    return payload


def diagnose_block(block: dict) -> dict:
    positive_rows = []
    negative_rows = []
    crossing_rows = []

    for row in block["distances"]:
        lower = dec(row["positive_window_lower"])
        upper = dec(row["positive_window_upper"])
        item = {
            "index": row["index"],
            "distance": row["distance"],
            "positive_window_lower": dstr(lower),
            "positive_window_upper": dstr(upper),
        }
        if upper < 0:
            negative_rows.append(item)
        elif lower > 0:
            positive_rows.append(item)
        else:
            crossing_rows.append(item)

    obstruction = None
    if negative_rows:
        first = negative_rows[0]
        obstruction = {
            "reason": (
                "absolute_log_majorant_upper_is_nonnegative_but_generated_"
                "signed_window_upper_is_negative"
            ),
            "first_index": first["index"],
            "first_distance": first["distance"],
            "first_positive_window_upper": first["positive_window_upper"],
        }

    return {
        "block": block["block"],
        "label": block["label"],
        "k": block["k"],
        "distances": len(block["distances"]),
        "positive_window_rows": len(positive_rows),
        "negative_window_rows": len(negative_rows),
        "crossing_window_rows": len(crossing_rows),
        "absolute_two_piece_log_majorant_can_be_final_payload": obstruction is None,
        "obstruction": obstruction,
        "recommended_route": (
            "signed_chunked_comparison_integral_payload"
            if obstruction is not None
            else "two_piece_log_majorant_payload_possible"
        ),
        "positive_rows": positive_rows,
        "negative_rows": negative_rows,
        "crossing_rows": crossing_rows,
    }


def render_md(result: dict) -> str:
    lines = [
        "# Step33A.1-A Positive Tail Route Diagnostic",
        "",
        "This file is generated diagnostic data, not a Lean proof object.",
        "",
        "Conclusion: the absolute two-piece log-majorant bridge is structural",
        "support, not the final signed positive-window payload, whenever a",
        "block has negative generated positive-window upper rows.",
        "",
        "Recommended next route:",
        "",
        "`signed_chunked_comparison_integral_payload`",
        "",
    ]

    for block in result["blocks"]:
        lines.extend(
            [
                f"## {block['label']}",
                "",
                f"- distances: `{block['distances']}`",
                f"- positive signed windows: `{block['positive_window_rows']}`",
                f"- negative signed windows: `{block['negative_window_rows']}`",
                f"- crossing signed windows: `{block['crossing_window_rows']}`",
                (
                    "- absolute two-piece log-majorant final payload: "
                    f"`{block['absolute_two_piece_log_majorant_can_be_final_payload']}`"
                ),
                f"- recommended route: `{block['recommended_route']}`",
                "",
            ]
        )
        obstruction = block["obstruction"]
        if obstruction is not None:
            lines.extend(
                [
                    "First obstruction:",
                    "",
                    f"- index: `{obstruction['first_index']}`",
                    f"- distance: `{obstruction['first_distance']}`",
                    (
                        "- generated positive-window upper: "
                        f"`{obstruction['first_positive_window_upper']}`"
                    ),
                    f"- reason: `{obstruction['reason']}`",
                    "",
                ]
            )
        lines.extend(
            [
                "| idx | d | lower | upper |",
                "| ---: | ---: | ---: | ---: |",
            ]
        )
        for row in block["negative_rows"]:
            lines.append(
                "| {index} | {distance} | {positive_window_lower} | "
                "{positive_window_upper} |".format(**row)
            )
        lines.append("")

    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--out-json", type=Path)
    parser.add_argument("--out-md", type=Path)
    args = parser.parse_args()

    getcontext().prec = 100
    contract = load_contract(args.contract)
    result = {
        "schema": "q3_psdpd_step33_a_tail_route_diagnostic.v1",
        "meaning": (
            "Route guard for the Step33A.1-A signed positive-tail window. "
            "It detects when a nonnegative absolute log-majorant cannot be "
            "the final signed payload because generated window uppers are "
            "negative."
        ),
        "source_contract": str(args.contract),
        "blocks": [diagnose_block(block) for block in contract["blocks"]],
    }

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_md(result), encoding="utf-8")

    for block in result["blocks"]:
        verdict = block["recommended_route"]
        print(
            f"{block['label']}: negative_windows={block['negative_window_rows']} "
            f"recommended={verdict}"
        )


if __name__ == "__main__":
    run()
