#!/usr/bin/env python3
"""Emit the Step33 raw-Omega A tail-remainder proof worklist.

This is a narrow route-control artifact for Step33A.1-A.  It extracts the
46 row-level `tailRemainderAbs` proof obligations from the current
`RawOmegaAChunkTaylorPayload.PayloadFin` proof-data source and pairs them with
the diagnostic signed tail probes.  The output is not Lean proof data; it is a
precise checklist for the next proof-producing generator or reviewer.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_PROOF_DATA = REQUEST_DIR / "a_chunk_taylor_payload_proof_data_skeleton.json"
DEFAULT_OUT_JSON = REQUEST_DIR / "a_tail_remainder_worklist.json"
DEFAULT_OUT_MD = REQUEST_DIR / "a_tail_remainder_worklist.md"


@dataclass(frozen=True)
class FamilyConfig:
    family_id: str
    block: str
    k: int
    ell: str
    probe: Path
    arithmetic_payload: str
    radius_def: str
    lean_collection: str


FAMILIES = [
    FamilyConfig(
        family_id="primary_tail",
        block="primary",
        k=11,
        ell="primaryK11Ell",
        probe=REQUEST_DIR / "a_signed_tail_probe_k11.json",
        arithmetic_payload="primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated",
        radius_def="primaryK11RawOmegaATailRemainderRadius",
        lean_collection="RawOmegaAChunkTaylorPayload.PrimaryTailPayloadFin",
    ),
    FamilyConfig(
        family_id="control_tail",
        block="control",
        k=9,
        ell="controlK9Ell",
        probe=REQUEST_DIR / "a_signed_tail_probe_k9.json",
        arithmetic_payload="controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated",
        radius_def="controlK9RawOmegaATailRemainderRadius",
        lean_collection="RawOmegaAChunkTaylorPayload.ControlTailPayloadFin",
    ),
]


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_probe(payload: dict[str, Any], path: Path) -> None:
    schema = payload.get("schema")
    if schema != "q3_psdpd_step33_a_signed_tail_probe.v1":
        raise ValueError(f"{path}: unexpected schema {schema!r}")
    rows = payload.get("distances")
    if not isinstance(rows, list) or len(rows) != 23:
        raise ValueError(f"{path}: expected 23 distance rows")
    seen = sorted(int(row["index"]) for row in rows)
    if seen != list(range(23)):
        raise ValueError(f"{path}: unexpected distance indices {seen}")


def proof_family_map(proof_data: dict[str, Any] | None) -> dict[str, dict[str, Any]]:
    if proof_data is None:
        return {}
    out: dict[str, dict[str, Any]] = {}
    for family in proof_data.get("families", []):
        family_id = str(family.get("id", ""))
        if family_id:
            out[family_id] = family
    return out


def proof_rows_by_index(family: dict[str, Any] | None) -> dict[int, dict[str, Any]]:
    if family is None:
        return {}
    out: dict[int, dict[str, Any]] = {}
    for row in family.get("distances", []):
        if "index" in row:
            out[int(row["index"])] = row
    return out


def field_present(row: dict[str, Any] | None, field: str) -> bool:
    return row is not None and field in row and row[field] is not None


def lean_forall_goal(config: FamilyConfig) -> str:
    return (
        "forall n : CoeffIndex23,\n"
        "  |Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend."
        f"step22PositiveAxisOmegaATailPart {config.k} {config.ell} "
        "((n.1 : Real) / 4) "
        f"{config.arithmetic_payload}.tailEnd| <=\n"
        f"    {config.arithmetic_payload}.tailRemainderRadius n"
    )


def lean_row_goal(config: FamilyConfig, index: int) -> str:
    return (
        f"-- row index {index}; instantiate n : CoeffIndex23 with n.1 = {index}\n"
        "|Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend."
        f"step22PositiveAxisOmegaATailPart {config.k} {config.ell} "
        f"(({index} : Real) / 4) {config.arithmetic_payload}.tailEnd| <=\n"
        f"    {config.radius_def} <row {index} as CoeffIndex23>"
    )


def build_family(config: FamilyConfig, proof_family: dict[str, Any] | None) -> dict[str, Any]:
    probe = load_json(config.probe)
    validate_probe(probe, config.probe)
    params = probe["parameters"]
    proof_rows = proof_rows_by_index(proof_family)

    rows = []
    missing = 0
    present = 0
    for probe_row in sorted(probe["distances"], key=lambda row: int(row["index"])):
        index = int(probe_row["index"])
        proof_row = proof_rows.get(index)
        has_proof = field_present(proof_row, "tailRemainderAbs")
        if has_proof:
            present += 1
        else:
            missing += 1
        rows.append(
            {
                "index": index,
                "distance": probe_row["distance"],
                "proofField": "tailRemainderAbs",
                "proofPresent": has_proof,
                "tailEnd": params["tail_window_end"],
                "cutoff": params["cutoff_t"],
                "diagnosticRemainderRadius": probe_row["remainder_radius"],
                "arithmeticRadiusDef": config.radius_def,
                "fitsGeneratedTailRadius": bool(probe_row["fits_generated_tail_radius"]),
                "diagnosticExcess": probe_row["excess"],
                "leanRowGoal": lean_row_goal(config, index),
            }
        )

    return {
        "family": config.family_id,
        "block": config.block,
        "k": config.k,
        "ell": config.ell,
        "leanCollection": config.lean_collection,
        "arithmeticPayload": config.arithmetic_payload,
        "arithmeticRadiusDef": config.radius_def,
        "probe": str(config.probe),
        "tailEnd": params["tail_window_end"],
        "cutoff": params["cutoff_t"],
        "rowCount": len(rows),
        "presentProofRows": present,
        "missingProofRows": missing,
        "forallGoal": lean_forall_goal(config),
        "rows": rows,
    }


def build_worklist(proof_data: dict[str, Any] | None, proof_data_path: Path) -> dict[str, Any]:
    families_by_id = proof_family_map(proof_data)
    families = [
        build_family(config, families_by_id.get(config.family_id))
        for config in FAMILIES
    ]
    missing = sum(int(family["missingProofRows"]) for family in families)
    present = sum(int(family["presentProofRows"]) for family in families)
    total = sum(int(family["rowCount"]) for family in families)
    return {
        "schema": "q3_psdpd_step33_a_tail_remainder_worklist.v1",
        "status": "ready" if missing == 0 else "missing_tail_remainder_proof_data",
        "meaning": (
            "Exact Step33A.1-A direct-tail remainder proof obligations for the "
            "raw-Omega A PayloadFin route. This is a worklist/report, not a Lean "
            "proof object."
        ),
        "proofDataSource": str(proof_data_path),
        "proofDataStatus": None if proof_data is None else proof_data.get("status"),
        "consumer": "RawOmegaAChunkTaylorPayload.PayloadFin.toDirectTailWindowInputs",
        "landingTheorem": (
            "psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_"
            "rawOmegaADirectTailWindowInputs"
        ),
        "checkedHelperTheorems": [
            "step22OmegaArchWeight_abs_le_ten_logOmega_after_520",
            "primaryK11RawOmegaATailLogMajorant_integrable_after_520",
            "controlK9RawOmegaATailLogMajorant_integrable_after_520",
            "step22PositiveAxisOmegaATail_abs_le_of_logOmegaFullTransformTailMajorant",
            "primaryK11RawOmegaATailRemainder_abs_le_of_logOmegaFullTransformTailMajorant",
            "controlK9RawOmegaATailRemainder_abs_le_of_logOmegaFullTransformTailMajorant",
        ],
        "nextProofDataInputs": [
            "hIntegral: generated integral-majorant <= tailRemainderRadius comparisons",
        ],
        "totals": {
            "families": len(families),
            "rows": total,
            "presentProofRows": present,
            "missingProofRows": missing,
        },
        "routeGuard": [
            "do not fill tailRemainderAbs from diagnostic Arb/acb probes alone",
            "do not use step22OmegaArchWeight_linear_growth unless concrete numeric constants are exposed",
            "do not mutate A CSV, ARadius, radius-floor, or LDL for this proof gate",
            "Lean emission is allowed only after every tailRemainderAbs field is proof-bearing",
        ],
        "families": families,
    }


def render_md(worklist: dict[str, Any]) -> str:
    totals = worklist["totals"]
    lines = [
        "# Step33A.1-A Tail-Remainder Worklist",
        "",
        "This is a route-control checklist, not a Lean proof object.",
        "",
        "## Verdict",
        "",
        f"- status: `{worklist['status']}`",
        f"- proof-data source: `{worklist['proofDataSource']}`",
        f"- proof-data status: `{worklist['proofDataStatus']}`",
        f"- consumer: `{worklist['consumer']}`",
        f"- landing theorem: `{worklist['landingTheorem']}`",
        "",
        "## Checked Helper Theorems",
        "",
    ]
    for theorem in worklist["checkedHelperTheorems"]:
        lines.append(f"- `{theorem}`")
    lines.extend(
        [
            "",
            "## Next Proof-Data Inputs",
            "",
        ]
    )
    for item in worklist["nextProofDataInputs"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Counts",
            "",
            f"- families: `{totals['families']}`",
            f"- tail rows: `{totals['rows']}`",
            f"- present tailRemainderAbs proofs: `{totals['presentProofRows']}`",
            f"- missing tailRemainderAbs proofs: `{totals['missingProofRows']}`",
            "",
            "## Route Guard",
            "",
        ]
    )
    for item in worklist["routeGuard"]:
        lines.append(f"- {item}")

    lines.extend(
        [
            "",
            "## Family Summary",
            "",
            "| family | k | tailEnd | rows | present | missing | radius def |",
            "| --- | ---: | ---: | ---: | ---: | ---: | --- |",
        ]
    )
    for family in worklist["families"]:
        lines.append(
            "| {family} | {k} | {tailEnd} | {rowCount} | {presentProofRows} | "
            "{missingProofRows} | `{arithmeticRadiusDef}` |".format(**family)
        )

    lines.extend(["", "## Lean Targets", ""])
    for family in worklist["families"]:
        lines.extend(
            [
                f"### {family['family']}",
                "",
                "```lean",
                family["forallGoal"],
                "```",
                "",
            ]
        )

    lines.extend(
        [
            "## First Missing Rows",
            "",
            "| family | row | distance | diagnostic remainder radius | diagnostic excess |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for family in worklist["families"]:
        shown = 0
        for row in family["rows"]:
            if row["proofPresent"]:
                continue
            lines.append(
                "| {family} | {index} | {distance} | {diagnosticRemainderRadius} | "
                "{diagnosticExcess} |".format(family=family["family"], **row)
            )
            shown += 1
            if shown >= 5:
                break

    lines.extend(
        [
            "",
            "## PRO_REVIEW_REQUEST",
            "",
            "Route: Step33A.1-A raw-Omega direct-tail-window A route",
            "Current step: produce 46 direct tailRemainderAbs proofs",
            "Current theorem: RawOmegaAChunkTaylorPayload.PayloadFin.toDirectTailWindowInputs",
            "File: Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorPayloadImport.lean",
            "Lean blocker: tail rows need hRemainder for step22PositiveAxisOmegaATailPart at U=520",
            "Options:",
            "A. Use the checked raw-Omega log-tail helper theorems and generate the remaining hIntegral proof-data layer.",
            "B. Expose concrete numeric constants for the existing linear-growth tail lemma, then prove the 46 radius comparisons.",
            "C. If A/B fail, regenerate only the tail-remainder policy with a proof-producing cert, not A CSV/ARadius/LDL.",
            "Codex recommendation: A first; B only if concrete constants become inspectable; C only after an exact excess report.",
            "Question for Louise: With hOmega and hMajorantInt checked, should the next generator emit the 46 hIntegral comparisons directly, or add a shared closed-form integral comparison theorem first?",
            "",
        ]
    )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proof-data", type=Path, default=DEFAULT_PROOF_DATA)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    proof_data = load_json(args.proof_data) if args.proof_data.exists() else None
    worklist = build_worklist(proof_data, args.proof_data)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(worklist, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.out_md.write_text(render_md(worklist), encoding="utf-8")

    totals = worklist["totals"]
    print(
        "status={status} rows={rows} present={present} missing={missing} out_json={out_json} out_md={out_md}".format(
            status=worklist["status"],
            rows=totals["rows"],
            present=totals["presentProofRows"],
            missing=totals["missingProofRows"],
            out_json=args.out_json,
            out_md=args.out_md,
        )
    )


if __name__ == "__main__":
    run()
