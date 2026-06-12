#!/usr/bin/env python3
"""Build the exact Step33A.1-A window-payload contract.

This is not a proof producer.  It consolidates the checked receiver surface and
the existing Arb/acb diagnostic data into one deterministic contract for the
next proof-producing A-window generator.  It deliberately does not mutate
ARadius, CSV payloads, radius floors, or generated global radii.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"


BLOCKS = {
    "primary": {
        "label": "primary k=11",
        "k": 11,
        "prefix": "primaryK11AnalyticA",
        "finite_part_cert": "primaryK11AnalyticAFinitePartBoundsCert",
        "positive_window_cert": "primaryK11AnalyticAPositiveTailWindowBoundsCert",
        "analytic_cert": "primaryK11AnalyticAFiniteTailAnalyticBoundsCert",
        "finite_tail_assembly": (
            "primaryK11AnalyticAFiniteTailAnalyticBoundsCert_of_"
            "generatedFinitePartAndPositiveTailWindowProofRemainder"
        ),
        "manifest": REQUEST_DIR / "a_finite_tail_components_k11.json",
        "tail_probe": REQUEST_DIR / "a_signed_tail_probe_k11.json",
    },
    "control": {
        "label": "control k=9",
        "k": 9,
        "prefix": "controlK9AnalyticA",
        "finite_part_cert": "controlK9AnalyticAFinitePartBoundsCert",
        "positive_window_cert": "controlK9AnalyticAPositiveTailWindowBoundsCert",
        "analytic_cert": "controlK9AnalyticAFiniteTailAnalyticBoundsCert",
        "finite_tail_assembly": (
            "controlK9AnalyticAFiniteTailAnalyticBoundsCert_of_"
            "generatedFinitePartAndPositiveTailWindowProofRemainder"
        ),
        "manifest": REQUEST_DIR / "a_finite_tail_components_k9.json",
        "tail_probe": REQUEST_DIR / "a_signed_tail_probe_k9.json",
    },
}


def dec(text: str) -> Decimal:
    return Decimal(str(text))


def dstr(value: Decimal) -> str:
    if value == 0:
        return "0.000000000000000000E+0"
    return format(value, ".18E")


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def load_components(path: Path) -> dict:
    payload = load_json(path)
    schema = payload.get("schema")
    if schema != "q3_psdpd_step22_arch_finite_tail_components.v1":
        raise ValueError(f"{path}: unexpected schema {schema!r}")
    rows = payload.get("distances", [])
    if len(rows) != 23:
        raise ValueError(f"{path}: expected 23 distances, got {len(rows)}")
    return payload


def load_tail_probe(path: Path) -> dict:
    payload = load_json(path)
    schema = payload.get("schema")
    if schema != "q3_psdpd_step33_a_signed_tail_probe.v1":
        raise ValueError(f"{path}: unexpected schema {schema!r}")
    rows = payload.get("distances", [])
    if len(rows) != 23:
        raise ValueError(f"{path}: expected 23 distances, got {len(rows)}")
    return payload


def chunk_count(length: Decimal, chunk_size: Decimal) -> int | None:
    if chunk_size <= 0:
        return None
    q = length / chunk_size
    if q == q.to_integral_value():
        return int(q)
    return None


def build_block(name: str, config: dict) -> dict:
    components = load_components(config["manifest"])
    tail_probe = load_tail_probe(config["tail_probe"])

    params = components["parameters"]
    tail_params = tail_probe["parameters"]
    cutoff = dec(params["cutoff_t"])
    tail_end = dec(tail_params["tail_window_end"])
    chunk = dec(params["chunk_size"])
    if dec(tail_params["cutoff_t"]) != cutoff:
        raise ValueError(f"{name}: cutoff mismatch between manifest and tail probe")

    tail_by_index = {int(row["index"]): row for row in tail_probe["distances"]}
    rows = []
    worst_tail_slack = None
    worst_tail_index = None
    worst_tail_excess = Decimal("0")

    for idx, row in enumerate(components["distances"]):
        tail = tail_by_index.get(idx)
        if tail is None:
            raise ValueError(f"{name}: missing tail probe row {idx}")
        if dec(row["distance"]) != dec(tail["distance"]):
            raise ValueError(f"{name}: distance mismatch at row {idx}")

        finite_mid = dec(row["finite_mid"])
        finite_radius = dec(row["finite_radius"])
        tail_radius = dec(row["tail_radius"])
        finite_lower = finite_mid - finite_radius
        finite_upper = finite_mid + finite_radius

        window_lower = dec(tail["window_lower"])
        window_upper = dec(tail["window_upper"])
        remainder_radius = dec(tail["remainder_radius"])
        tail_lower = dec(tail["tail_lower"])
        tail_upper = dec(tail["tail_upper"])
        generated_tail_radius = dec(tail["generated_tail_radius"])
        if generated_tail_radius != tail_radius:
            raise ValueError(f"{name}: tail radius mismatch at row {idx}")

        tail_abs_upper = max(abs(tail_lower), abs(tail_upper))
        tail_slack = tail_radius - tail_abs_upper
        tail_excess = max(Decimal("0"), -tail_slack)
        if worst_tail_slack is None or tail_slack < worst_tail_slack:
            worst_tail_slack = tail_slack
            worst_tail_index = idx
        worst_tail_excess = max(worst_tail_excess, tail_excess)

        rows.append(
            {
                "index": idx,
                "distance": row["distance"],
                "finite_mid": dstr(finite_mid),
                "finite_radius": dstr(finite_radius),
                "finite_lower": dstr(finite_lower),
                "finite_upper": dstr(finite_upper),
                "positive_window_lower": dstr(window_lower),
                "positive_window_upper": dstr(window_upper),
                "proof_remainder_radius": dstr(remainder_radius),
                "two_sided_tail_lower": dstr(tail_lower),
                "two_sided_tail_upper": dstr(tail_upper),
                "generated_tail_radius": dstr(tail_radius),
                "tail_radius_slack": dstr(tail_slack),
                "tail_excess": dstr(tail_excess),
            }
        )

    return {
        "block": name,
        "label": config["label"],
        "k": config["k"],
        "lean_targets": {
            "finite_part_cert": config["finite_part_cert"],
            "positive_window_cert": config["positive_window_cert"],
            "analytic_cert": config["analytic_cert"],
            "finite_tail_assembly": config["finite_tail_assembly"],
        },
        "source_files": {
            "finite_tail_components": str(config["manifest"]),
            "signed_tail_probe": str(config["tail_probe"]),
        },
        "parameters": {
            "cutoff_t": dstr(cutoff),
            "positive_tail_window_end": dstr(tail_end),
            "chunk_size": dstr(chunk),
            "finite_positive_half_chunks": chunk_count(cutoff, chunk),
            "positive_tail_window_chunks": chunk_count(tail_end - cutoff, chunk),
            "distances": len(rows),
        },
        "summary": {
            "tail_probe_worst_excess": dstr(worst_tail_excess),
            "tail_probe_worst_slack": dstr(worst_tail_slack or Decimal("0")),
            "tail_probe_worst_slack_index": worst_tail_index,
            "tail_probe_fits_generated_tail_radius": worst_tail_excess == 0,
        },
        "distances": rows,
    }


def render_md(contract: dict) -> str:
    lines = [
        "# Step33A.1-A A-window Payload Contract",
        "",
        "This file is generated contract data, not a Lean proof object.",
        "It records the exact A finite/positive-window proof-producing payload",
        "still needed by the checked Step33A.1-A receiver route.",
        "",
        "Hard guard: no ARadius, CSV, radius-floor, or global A-radius payload",
        "mutation is part of this contract.",
        "",
        "## Receiver",
        "",
        "`psd_step33_closed_from_rationalDeltaLiveGeneratedP0AAnalyticFiniteTailFromPositiveTailWindowProofRemainderRecenterWithCenterError`",
        "",
    ]
    for block in contract["blocks"]:
        lines.extend(
            [
                f"## {block['label']}",
                "",
                f"- finite part cert: `{block['lean_targets']['finite_part_cert']}`",
                f"- positive window cert: `{block['lean_targets']['positive_window_cert']}`",
                f"- analytic cert: `{block['lean_targets']['analytic_cert']}`",
                f"- assembly theorem: `{block['lean_targets']['finite_tail_assembly']}`",
                f"- distances: `{block['parameters']['distances']}`",
                f"- finite half-window chunks: `{block['parameters']['finite_positive_half_chunks']}`",
                f"- positive tail-window chunks: `{block['parameters']['positive_tail_window_chunks']}`",
                f"- tail worst excess: `{block['summary']['tail_probe_worst_excess']}`",
                f"- tail worst slack: `{block['summary']['tail_probe_worst_slack']}` at index `{block['summary']['tail_probe_worst_slack_index']}`",
                "",
                "| idx | d | finite lower | finite upper | tail lower | tail upper | tail radius | tail slack |",
                "| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for row in block["distances"]:
            lines.append(
                "| {index} | {distance} | {finite_lower} | {finite_upper} | "
                "{two_sided_tail_lower} | {two_sided_tail_upper} | "
                "{generated_tail_radius} | {tail_radius_slack} |".format(**row)
            )
        lines.append("")
    return "\n".join(lines) + "\n"


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--block", choices=["primary", "control", "both"], default="both")
    parser.add_argument("--out-json", type=Path)
    parser.add_argument("--out-md", type=Path)
    args = parser.parse_args()

    getcontext().prec = 100
    selected = ["primary", "control"] if args.block == "both" else [args.block]
    blocks = [build_block(name, BLOCKS[name]) for name in selected]
    contract = {
        "schema": "q3_psdpd_step33_a_window_contract.v1",
        "meaning": (
            "Exact non-mutating Step33A.1-A payload contract.  The remaining "
            "Lean work is proof-producing finite-window and positive-tail-window "
            "bounds for these rows, followed by the already checked analytic "
            "assembly and local recenter bridge."
        ),
        "blocks": blocks,
    }

    for block in blocks:
        summary = block["summary"]
        print(
            f"{block['label']}: distances={block['parameters']['distances']} "
            f"tail_worst_excess={summary['tail_probe_worst_excess']} "
            f"tail_worst_slack={summary['tail_probe_worst_slack']} "
            f"at idx={summary['tail_probe_worst_slack_index']}"
        )

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(
            json.dumps(contract, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(f"Wrote {args.out_json}")

    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_md(contract), encoding="utf-8")
        print(f"Wrote {args.out_md}")


if __name__ == "__main__":
    run()
