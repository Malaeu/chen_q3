#!/usr/bin/env python3
"""Generate the raw-Omega Step33 A tail-window arithmetic Lean import.

This generator only emits rational arithmetic payloads.  It does not claim or
prove the finite-window or tail-window comparison integral enclosures.
"""

from __future__ import annotations

import json
import argparse
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
OUT_FILE = ROOT / "Q3/Proofs/PSD_CenteredCoeffRawOmegaATailWindowArithmeticImport.lean"


BLOCKS = [
    {
        "label": "primary k=11",
        "prefix": "primaryK11RawOmegaA",
        "family_prefix": "primary",
        "payload_prefix": "primaryK11",
        "finite": REQUEST_DIR / "a_finite_tail_components_k11.json",
        "tail": REQUEST_DIR / "a_signed_tail_probe_k11.json",
        "payload": "PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload",
        "generated": "primaryK11RawOmegaAComparisonTailWindowArithmeticPayload_generated",
        "lower_def": "primaryK11RawOmegaAAbsDistanceLower",
        "upper_def": "primaryK11RawOmegaAAbsDistanceUpper",
        "entry_rat": "primaryK11AAbsDistanceEntryRat",
        "radius_rat": "primaryK11ARadiusAbsDistanceEntryRat",
    },
    {
        "label": "control k=9",
        "prefix": "controlK9RawOmegaA",
        "family_prefix": "control",
        "payload_prefix": "controlK9",
        "finite": REQUEST_DIR / "a_finite_tail_components_k9.json",
        "tail": REQUEST_DIR / "a_signed_tail_probe_k9.json",
        "payload": "ControlK9RawOmegaAComparisonTailWindowArithmeticPayload",
        "generated": "controlK9RawOmegaAComparisonTailWindowArithmeticPayload_generated",
        "lower_def": "controlK9RawOmegaAAbsDistanceLower",
        "upper_def": "controlK9RawOmegaAAbsDistanceUpper",
        "entry_rat": "controlK9AAbsDistanceEntryRat",
        "radius_rat": "controlK9ARadiusAbsDistanceEntryRat",
    },
]


def frac(text: str) -> Fraction:
    return Fraction(Decimal(text))


def lean_rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"(({value.numerator} : Rat))"
    return f"(({value.numerator} : Rat) / ({value.denominator} : Rat))"


def load_rows(block: dict[str, str]) -> tuple[list[dict[str, Fraction]], Fraction, Fraction]:
    with Path(block["finite"]).open(encoding="utf-8") as handle:
        finite_payload = json.load(handle)
    if finite_payload.get("schema") != "q3_psdpd_step22_arch_finite_tail_components.v1":
        raise ValueError(f"{block['finite']}: unexpected schema")
    with Path(block["tail"]).open(encoding="utf-8") as handle:
        tail_payload = json.load(handle)
    if tail_payload.get("schema") != "q3_psdpd_step33_a_signed_tail_probe.v1":
        raise ValueError(f"{block['tail']}: unexpected schema")

    cutoff = frac(finite_payload["parameters"]["cutoff_t"])
    tail_cutoff = frac(tail_payload["parameters"]["cutoff_t"])
    tail_end = frac(tail_payload["parameters"]["tail_window_end"])
    if cutoff != tail_cutoff:
        raise ValueError(f"{block['label']}: finite/tail cutoffs differ")

    finite_rows = finite_payload["distances"]
    tail_rows = sorted(tail_payload["distances"], key=lambda row: int(row["index"]))
    if len(finite_rows) != 23 or len(tail_rows) != 23:
        raise ValueError(f"{block['label']}: expected 23 rows")

    rows: list[dict[str, Fraction]] = []
    for idx, (finite_row, tail_row) in enumerate(zip(finite_rows, tail_rows)):
        if int(tail_row["index"]) != idx:
            raise ValueError(f"{block['label']}: tail index mismatch at {idx}")
        finite_mid = frac(finite_row["finite_mid"])
        finite_radius = frac(finite_row["finite_radius"])
        rows.append(
            {
                "finite_lower": finite_mid - finite_radius,
                "finite_upper": finite_mid + finite_radius,
                "tail_window_lower": frac(tail_row["window_lower"]),
                "tail_window_upper": frac(tail_row["window_upper"]),
                "tail_remainder_radius": frac(tail_row["remainder_radius"]),
                "tail_radius": frac(tail_row["generated_tail_radius"]),
            }
        )
    return rows, cutoff, tail_end


def load_target_refresh(
    path: Path | None,
) -> tuple[dict[str, dict[int, dict[str, Fraction]]], int]:
    if path is None:
        return {}, 0
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("schema") != "q3_psdpd_step33_a_chunk_integral_probe.v1":
        raise ValueError(f"{path}: unexpected schema {payload.get('schema')!r}")

    refresh: dict[str, dict[int, dict[str, Fraction]]] = {}
    for family in payload.get("families", []):
        family_id = str(family["family"])
        for row in family.get("rows", []):
            if row.get("fits_target"):
                continue
            if not row.get("fits_after_local_target_refresh"):
                raise ValueError(
                    f"{path}: {family_id}[{row.get('distance_index')}] "
                    "does not fit the current target and is not slack-absorbable"
                )
            idx = int(row["distance_index"])
            lower = frac(row["suggested_target_lower"])
            upper = frac(row["suggested_target_upper"])
            if upper < lower:
                raise ValueError(f"{path}: inverted refresh interval at {family_id}[{idx}]")
            refresh.setdefault(family_id, {})[idx] = {
                "lower": lower,
                "upper": upper,
                "needed": frac(row["needed_target_refresh_slack"]),
                "available": frac(row["available_target_refresh_slack"]),
            }
    return refresh, sum(len(rows) for rows in refresh.values())


def apply_target_refresh(
    *,
    block: dict[str, str],
    rows: list[dict[str, Fraction]],
    target_refresh: dict[str, dict[int, dict[str, Fraction]]],
) -> None:
    family_prefix = block["family_prefix"]
    finite_family = f"{family_prefix}_finite"
    tail_family = f"{family_prefix}_tail"
    finite_refresh = target_refresh.get(finite_family, {})
    tail_refresh = target_refresh.get(tail_family, {})

    for family_id, refresh, lower_key, upper_key in [
        (finite_family, finite_refresh, "finite_lower", "finite_upper"),
        (tail_family, tail_refresh, "tail_window_lower", "tail_window_upper"),
    ]:
        for idx, entry in refresh.items():
            if idx < 0 or idx >= len(rows):
                raise ValueError(f"{family_id}[{idx}]: refresh index outside generated rows")
            rows[idx][lower_key] = entry["lower"]
            rows[idx][upper_key] = entry["upper"]

    for idx, finite_entry in finite_refresh.items():
        tail_entry = tail_refresh.get(idx)
        tail_needed = tail_entry["needed"] if tail_entry is not None else Fraction(0)
        available = min(
            finite_entry["available"],
            tail_entry["available"] if tail_entry is not None else finite_entry["available"],
        )
        needed = finite_entry["needed"] + tail_needed
        if available < needed:
            raise ValueError(
                f"{finite_family}[{idx}]: finite refresh plus tail refresh exceeds "
                "available local tail-radius slack"
            )
        refreshed_tail_radius = rows[idx]["tail_radius"] - finite_entry["needed"]
        if refreshed_tail_radius < 0:
            raise ValueError(f"{finite_family}[{idx}]: refreshed tail radius became negative")
        rows[idx]["tail_radius"] = refreshed_tail_radius


def emit_rat_fn(name: str, rows: list[Fraction]) -> list[str]:
    out = [f"def {name} : Nat -> Rat"]
    for idx, value in enumerate(rows):
        out.append(f"  | {idx} => {lean_rat(value)}")
    out.append("  | _ => 0")
    out.append("")
    return out


def emit_real_fn(name: str, rat_name: str) -> list[str]:
    return [
        f"def {name} (n : CoeffIndex23) : Real :=",
        f"  ({rat_name} (n.1) : Real)",
        "",
    ]


def emit_block(block: dict[str, str], rows: list[dict[str, Fraction]]) -> list[str]:
    prefix = block["prefix"]
    names = {
        "finite_lower": f"{prefix}FiniteLower",
        "finite_upper": f"{prefix}FiniteUpper",
        "tail_window_lower": f"{prefix}TailWindowLower",
        "tail_window_upper": f"{prefix}TailWindowUpper",
        "tail_remainder_radius": f"{prefix}TailRemainderRadius",
        "tail_radius": f"{prefix}TailRadius",
    }
    out: list[str] = [f"/-! Arithmetic data for {block['label']}. -/", ""]
    for key, name in names.items():
        rat_name = f"{name}Rat"
        out.extend(emit_rat_fn(rat_name, [row[key] for row in rows]))
        out.extend(emit_real_fn(name, rat_name))

    simp_names = [
        "rawOmegaAFiniteTailCutoff",
        "rawOmegaATailWindowEnd",
        f"Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.{block['lower_def']}",
        f"Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.{block['upper_def']}",
        f"Q3.PSDpd.CenteredCoeffPayloadImport.{block['entry_rat']}",
        f"Q3.PSDpd.CenteredCoeffPayloadImport.{block['radius_rat']}",
    ]
    for name in names.values():
        simp_names.append(name)
        simp_names.append(f"{name}Rat")
    simp = ",\n        ".join(simp_names)

    out.extend(
        [
            f"def {block['generated']} :",
            f"    {block['payload']} := by",
            "  refine",
            "    { cutoff := rawOmegaAFiniteTailCutoff",
            "      tailEnd := rawOmegaATailWindowEnd",
            f"      finiteLower := {names['finite_lower']}",
            f"      finiteUpper := {names['finite_upper']}",
            f"      tailWindowLower := {names['tail_window_lower']}",
            f"      tailWindowUpper := {names['tail_window_upper']}",
            f"      tailRemainderRadius := {names['tail_remainder_radius']}",
            f"      tailRadius := {names['tail_radius']}",
            "      hCutoff_nonneg := by norm_num [rawOmegaAFiniteTailCutoff]",
            "      hTailWindow := by norm_num [rawOmegaAFiniteTailCutoff, rawOmegaATailWindowEnd]",
            "      hTailLowerArith := ?_",
            "      hTailUpperArith := ?_",
            "      hPayloadLowerArith := ?_",
            "      hPayloadUpperArith := ?_ }",
        ]
    )
    for _ in range(4):
        out.extend(
            [
                "  · intro n",
                "    fin_cases n <;>",
                "      norm_num [",
                f"        {simp}",
                "      ]",
            ]
        )
    out.append("")
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--target-refresh-probe",
        type=Path,
        help=(
            "Optional local raw-Omega chunk probe JSON. Rows marked "
            "fits_after_local_target_refresh refresh only the generated "
            "finite/tail target intervals; global A payload radii are not changed."
        ),
    )
    args = parser.parse_args()

    target_refresh, refresh_count = load_target_refresh(args.target_refresh_probe)
    loaded = []
    for block in BLOCKS:
        rows, cutoff, tail_end = load_rows(block)
        apply_target_refresh(block=block, rows=rows, target_refresh=target_refresh)
        loaded.append((rows, cutoff, tail_end, block))
    cutoffs = {item[1] for item in loaded}
    tail_ends = {item[2] for item in loaded}
    if len(cutoffs) != 1 or len(tail_ends) != 1:
        raise ValueError("primary/control cutoffs or tail endpoints differ")
    cutoff = next(iter(cutoffs))
    tail_end = next(iter(tail_ends))

    lines = [
        "import Q3.Proofs.PSD_CenteredCoeffRawOmegaATailWindowArithmeticSupport",
        "",
        "set_option linter.mathlibStandardSet false",
        "set_option maxHeartbeats 0",
        "set_option autoImplicit false",
        "",
        "/-!",
        "Generated raw-Omega Step33 A tail-window arithmetic payloads.",
        "",
        "This file proves only rational arithmetic: cutoff/order checks,",
        "tail-window/remainder containment, and containment in the imported",
        "raw-Omega A payload lower/upper boxes.  It does not prove comparison",
        "integral enclosures.",
        "",
        "If a local target refresh is present, it was produced from a chunk",
        "integral probe row whose excess is bounded by the already available",
        "payload slack.  This generator does not mutate A CSV, ARadius,",
        "radius-floor, or LDL data.",
        f"local target refresh rows: {refresh_count}",
        "-/",
        "",
        "noncomputable section",
        "",
        "namespace Q3",
        "namespace PSDpd",
        "namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport",
        "",
        "open CenteredCoeffPayloadImport",
        "",
        f"def rawOmegaAFiniteTailCutoff : Real := (({cutoff.numerator} : Real) / ({cutoff.denominator} : Real))",
        "",
        f"def rawOmegaATailWindowEnd : Real := (({tail_end.numerator} : Real) / ({tail_end.denominator} : Real))",
        "",
    ]
    for rows, _cutoff, _tail_end, block in loaded:
        lines.extend(emit_block(block, rows))
    lines.extend(
        [
            "end CenteredCoeffPrimeDeltaLiveRationalPayloadImport",
            "end PSDpd",
            "end Q3",
            "",
        ]
    )
    OUT_FILE.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {OUT_FILE}")
    if refresh_count:
        print(f"Applied local target refresh rows={refresh_count}")


if __name__ == "__main__":
    main()
