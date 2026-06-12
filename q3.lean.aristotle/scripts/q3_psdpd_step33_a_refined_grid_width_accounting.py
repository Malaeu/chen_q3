#!/usr/bin/env python3
"""Account sampled refined-grid Taylor/model row widths against row targets.

This is diagnostic only.  It reads Taylor model probe JSON files and the
current proof-data seed, then compares model-produced row intervals against the
generated row target intervals and any recorded local refresh slack.  It does
not mutate the worklist, proof data, CSVs, or Lean payloads.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any

from q3_psdpd_step33_a_chunk_taylor_payload_inventory import (
    PROOF_DATA_SCHEMA,
    load_json,
)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_PROOF_DATA = REQUEST_DIR / "a_chunk_taylor_payload_product_abs_seed.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_refined_grid_width_accounting.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_refined_grid_width_accounting.md"
DEFAULT_FIRST_SPLIT = 50
DEFAULT_TAIL_SPLIT = 10


FAMILY_CONFIGS = [
    {
        "id": "primary_finite",
        "row_probe": "a_chunk_taylor_model_probe_primary_finite_row0_split10.json",
        "first_chunk_probe": "a_chunk_taylor_model_probe_primary_finite_0_0_split50.json",
        "policy": "first_chunk_split50_rest_split10",
    },
    {
        "id": "control_finite",
        "row_probe": "a_chunk_taylor_model_probe_control_finite_row0_split10.json",
        "first_chunk_probe": "a_chunk_taylor_model_probe_control_finite_0_0_split50.json",
        "policy": "first_chunk_split50_rest_split10",
    },
    {
        "id": "primary_tail",
        "row_probe": "a_chunk_taylor_model_probe_primary_tail_row0_split10.json",
        "first_chunk_probe": None,
        "policy": "all_split10",
    },
    {
        "id": "control_tail",
        "row_probe": "a_chunk_taylor_model_probe_control_tail_row0_split10.json",
        "first_chunk_probe": None,
        "policy": "all_split10",
    },
]


def decimal_str(x: Decimal) -> str:
    if x == 0:
        return "0.000000000000000000E+0"
    return format(x, ".18E")


def dec(value: Any, *, default: Decimal | None = None) -> Decimal:
    if value is None:
        if default is not None:
            return default
        raise ValueError("missing decimal value")
    return Decimal(str(value))


def proof_family_map(proof_data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    if proof_data.get("schema") != PROOF_DATA_SCHEMA:
        raise ValueError(f"unexpected proof-data schema {proof_data.get('schema')!r}")
    return {str(family["id"]): family for family in proof_data.get("families", [])}


def probe_cell_map(probe: dict[str, Any]) -> dict[int, dict[str, Any]]:
    if probe.get("schema") != "q3_psdpd_step33_a_chunk_taylor_model_probe.v1":
        raise ValueError(f"unexpected probe schema {probe.get('schema')!r}")
    return {int(cell["chunk_index"]): cell for cell in probe.get("cells", [])}


def virtual_result(cell: dict[str, Any], degree: int) -> dict[str, Any]:
    for result in cell.get("virtual_subchunk_results", []):
        if int(result["degree"]) == degree:
            return result
    raise ValueError(
        f"missing virtual result degree={degree} for chunk {cell.get('chunk_index')}"
    )


def account_family(
    *,
    proof_family: dict[str, Any],
    row_probe: dict[str, Any],
    first_chunk_probe: dict[str, Any] | None,
    degree: int,
    policy: str,
) -> dict[str, Any]:
    row = proof_family["distances"][0]
    target_lower = dec(row["targetLowerValue"])
    target_upper = dec(row["targetUpperValue"])
    available_slack = dec(row.get("targetRefreshSlackAfter"), default=Decimal("0"))
    row_cells = probe_cell_map(row_probe)
    first_cells = probe_cell_map(first_chunk_probe) if first_chunk_probe else {}

    chunk_records = []
    total_lower = Decimal("0")
    total_upper = Decimal("0")
    for chunk_index in sorted(row_cells):
        source = "row_probe"
        cell = row_cells[chunk_index]
        if policy.startswith("first_chunk_split") and chunk_index == 0:
            cell = first_cells.get(0, cell)
            source = "first_chunk_probe"
        result = virtual_result(cell, degree)
        lower = dec(result["total_lower_model_integral"])
        upper = dec(result["total_upper_model_integral"])
        total_lower += lower
        total_upper += upper
        chunk_records.append(
            {
                "chunk": chunk_index,
                "source": source,
                "lower": decimal_str(lower),
                "upper": decimal_str(upper),
                "width": decimal_str(upper - lower),
                "failure_mode": result.get("failure_mode"),
            }
        )

    lower_excess = max(Decimal("0"), target_lower - total_lower)
    upper_excess = max(Decimal("0"), total_upper - target_upper)
    needed_slack_sum = lower_excess + upper_excess
    needed_slack_max_side = max(lower_excess, upper_excess)
    fits_target = lower_excess == 0 and upper_excess == 0
    fits_recorded_slack_sum = needed_slack_sum <= available_slack
    fits_recorded_slack_max_side = needed_slack_max_side <= available_slack

    return {
        "family": proof_family["id"],
        "row": int(row["index"]),
        "degree": degree,
        "policy": policy,
        "target_lower": decimal_str(target_lower),
        "target_upper": decimal_str(target_upper),
        "target_width": decimal_str(target_upper - target_lower),
        "model_lower": decimal_str(total_lower),
        "model_upper": decimal_str(total_upper),
        "model_width": decimal_str(total_upper - total_lower),
        "lower_excess": decimal_str(lower_excess),
        "upper_excess": decimal_str(upper_excess),
        "needed_slack_sum": decimal_str(needed_slack_sum),
        "needed_slack_max_side": decimal_str(needed_slack_max_side),
        "available_recorded_slack": decimal_str(available_slack),
        "fits_target": fits_target,
        "fits_recorded_slack_sum": fits_recorded_slack_sum,
        "fits_recorded_slack_max_side": fits_recorded_slack_max_side,
        "verdict": (
            "fits_current_target"
            if fits_target
            else "fits_recorded_slack"
            if fits_recorded_slack_sum
            else "exceeds_recorded_slack"
        ),
        "chunks": chunk_records,
    }


def render_md(result: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Refined Grid Width Accounting",
        "",
        "Diagnostic only.  This compares sampled model-produced row intervals",
        "against current generated row targets and recorded target-refresh slack.",
        "It is not Lean proof data and does not mutate any payload.",
        "",
        "## Summary",
        "",
        f"- degree: `{result['parameters']['degree']}`",
        f"- probe suffix: `{result['parameters']['probe_suffix']}`",
        f"- first finite chunk split: `{result['parameters']['first_split']}`",
        f"- tail row split: `{result['parameters']['tail_split']}`",
        f"- proof data: `{result['proof_data_source']}`",
        "",
        "| family | policy | model width | target width | needed slack | available slack | verdict |",
        "| --- | --- | ---: | ---: | ---: | ---: | --- |",
    ]
    for row in result["families"]:
        lines.append(
            f"| `{row['family']}` | `{row['policy']}` | "
            f"`{row['model_width']}` | `{row['target_width']}` | "
            f"`{row['needed_slack_sum']}` | `{row['available_recorded_slack']}` | "
            f"`{row['verdict']}` |"
        )
    lines.extend(["", "## Guard", ""])
    for guard in result["route_guard"]:
        lines.append(f"- {guard}")
    lines.append("")
    return "\n".join(lines)


def probe_path(request_dir: Path, name: str, suffix: str) -> Path:
    path = request_dir / name
    if not suffix:
        return path
    suffixed = path.with_name(f"{path.stem}{suffix}{path.suffix}")
    return suffixed if suffixed.exists() else path


def first_split_probe_name(name: str, first_split: int) -> str:
    if first_split <= 0:
        raise ValueError("--first-split must be positive")
    return name.replace("_split50", f"_split{first_split}")


def tail_split_probe_name(name: str, tail_split: int) -> str:
    if tail_split <= 0:
        raise ValueError("--tail-split must be positive")
    return name.replace("_split10", f"_split{tail_split}")


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proof-data", type=Path, default=DEFAULT_PROOF_DATA)
    parser.add_argument("--degree", type=int, default=16)
    parser.add_argument("--request-dir", type=Path, default=REQUEST_DIR)
    parser.add_argument(
        "--probe-suffix",
        type=str,
        default="",
        help=(
            "Optional suffix inserted before .json for Taylor probe inputs, "
            "for example _decimal. Falls back to the unsuffixed file when a "
            "suffixed probe is absent."
        ),
    )
    parser.add_argument(
        "--first-split",
        type=int,
        default=DEFAULT_FIRST_SPLIT,
        help=(
            "Virtual subchunk split count to use for first finite chunk probes. "
            "This selects filenames like *_split100*.json when set to 100."
        ),
    )
    parser.add_argument(
        "--tail-split",
        type=int,
        default=DEFAULT_TAIL_SPLIT,
        help=(
            "Virtual subchunk split count to use for tail row probes. "
            "This selects filenames like *_split20*.json when set to 20."
        ),
    )
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    getcontext().prec = 100
    proof_data = load_json(args.proof_data)
    proof_families = proof_family_map(proof_data)

    family_reports = []
    for config in FAMILY_CONFIGS:
        family_id = config["id"]
        if config["first_chunk_probe"] is not None:
            policy = config["policy"].replace("split50", f"split{args.first_split}")
        elif config["policy"] == "all_split10":
            policy = f"all_split{args.tail_split}"
        else:
            policy = config["policy"]
        row_probe_name = (
            tail_split_probe_name(config["row_probe"], args.tail_split)
            if config["policy"] == "all_split10"
            else config["row_probe"]
        )
        row_probe = load_json(probe_path(args.request_dir, row_probe_name, args.probe_suffix))
        first_probe = (
            load_json(
                probe_path(
                    args.request_dir,
                    first_split_probe_name(config["first_chunk_probe"], args.first_split),
                    args.probe_suffix,
                )
            )
            if config["first_chunk_probe"] is not None
            else None
        )
        family_reports.append(
            account_family(
                proof_family=proof_families[family_id],
                row_probe=row_probe,
                first_chunk_probe=first_probe,
                degree=args.degree,
                policy=policy,
            )
        )

    result = {
        "schema": "q3_psdpd_step33_a_refined_grid_width_accounting.v1",
        "meaning": (
            "Diagnostic refined-grid row-width accounting for the raw-Omega "
            "Taylor PayloadFin route.  This is search/control-plane evidence "
            "only, not a Lean proof artifact."
        ),
        "proof_data_source": str(args.proof_data),
        "parameters": {
            "degree": args.degree,
            "probe_suffix": args.probe_suffix,
            "first_split": args.first_split,
            "tail_split": args.tail_split,
        },
        "families": family_reports,
        "route_guard": [
            "diagnostic only",
            "do not emit Lean payload from this file",
            "do not mutate CSV, ARadius, radius-floor, or LDL data",
            "row target refresh must be Lean-checked before payload emission",
        ],
    }

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(result), encoding="utf-8")

    exceeded = sum(1 for family in family_reports if family["verdict"] == "exceeds_recorded_slack")
    print(
        "status=refined_grid_width_accounting degree={degree} families={families} "
        "exceeds_recorded_slack={exceeded} out_json={out_json}".format(
            degree=args.degree,
            families=len(family_reports),
            exceeded=exceeded,
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
