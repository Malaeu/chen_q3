#!/usr/bin/env python3
"""Probe Step33 raw-Omega A chunk integral rows without mutating payloads.

This is external generator-shape evidence, not a Lean proof.  It evaluates the
active raw-Omega A chunk source on every worklist chunk, sums Arb/acb interval
bounds per distance row, and compares the result against the current generated
target lower/upper rows.

The current Step33A.1-A route is the raw Step22 positive-axis Omega source
feeding `step22PositiveAxisOmegaAFinitePart` and
`step22PositiveAxisOmegaATailWindowPart`.  The centered receiver source remains
available as a diagnostic mode only.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any

try:
    from flint import acb, arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required. Run with the repo venv, for example:\n"
        "  .venv/bin/python q3.lean.aristotle/scripts/"
        "q3_psdpd_step33_a_chunk_integral_probe.py"
    ) from exc

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    set_precision,
    spline_packet_ball,
)
from q3_psdpd_step22_arch_interval import ArchIntervalBuilder, sinc_acb


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = REQUEST_DIR / "a_distance_payload_worklist.json"


def decimal_str(x: Decimal) -> str:
    if x == 0:
        return "0.000000000000000000E+0"
    return format(x, ".18E")


def optional_decimal(text: Any) -> Decimal | None:
    if text is None:
        return None
    return Decimal(str(text))


def refresh_guard(*values: Decimal) -> Decimal:
    scale = max((abs(value) for value in values), default=Decimal("0"))
    return max(scale * Decimal("1e-18"), Decimal("1e-45"))


def load_worklist(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("schema") != "q3_psdpd_step33_a_distance_payload_worklist.v1":
        raise ValueError(f"{path}: unexpected schema {payload.get('schema')!r}")
    return payload


def parse_csv_selection(text: str, *, count: int | None = None) -> list[int] | None:
    if text == "all":
        return None
    out: list[int] = []
    for part in text.split(","):
        part = part.strip()
        if not part:
            continue
        value = int(part)
        if count is not None and (value < 0 or value >= count):
            raise ValueError(f"index {value} outside [0,{count})")
        out.append(value)
    return out


def selected_families(payload: dict[str, Any], family_text: str) -> list[dict[str, Any]]:
    families = payload.get("families", [])
    if family_text == "all":
        return families
    wanted = {part.strip() for part in family_text.split(",") if part.strip()}
    known = {family["id"] for family in families}
    missing = sorted(wanted - known)
    if missing:
        raise ValueError(f"unknown family id(s): {', '.join(missing)}")
    return [family for family in families if family["id"] in wanted]


def selected_distance_rows(family: dict[str, Any], index_text: str) -> list[dict[str, Any]]:
    rows = family.get("distances", [])
    indices = parse_csv_selection(index_text, count=len(rows))
    if indices is None:
        return rows
    return [rows[index] for index in indices]


def selected_chunks(family: dict[str, Any], chunk_text: str) -> tuple[list[dict[str, Any]], bool]:
    chunks = family.get("chunks", [])
    indices = parse_csv_selection(chunk_text, count=len(chunks))
    if indices is None:
        return chunks, True
    return [chunks[index] for index in indices], len(indices) == len(chunks)


def make_builder(args: argparse.Namespace, *, family: dict[str, Any]) -> ArchIntervalBuilder:
    chunks = family.get("chunks", [])
    if not chunks:
        raise ValueError(f"{family['id']}: no chunks in worklist")

    cutoff_t = str(Decimal(chunks[-1]["right"]))
    chunk_size = str(Decimal(chunks[0]["right"]) - Decimal(chunks[0]["left"]))
    return ArchIntervalBuilder(
        k_spline=int(family["k"]),
        ell=args.ell,
        cutoff_t=cutoff_t,
        chunk_size=chunk_size,
        rel_tol=args.rel_tol,
        abs_tol=args.abs_tol,
        deg_limit=args.deg_limit,
        eval_limit=args.eval_limit,
        depth_limit=args.depth_limit,
        sinc_terms=args.sinc_terms,
        omega_factor=args.omega_factor,
        radius_floor=args.radius_floor,
    )


def centered_receiver_integrand(*, k_spline: int, ell: str, d: Decimal, sinc_terms: int):
    ell_acb = acb(arb(ell))
    d_acb = acb(arb(str(d)))
    pi_acb = acb(arb.pi())
    two = acb(2)
    i_unit = acb(0, 1)
    s_k, c_k = spline_packet_ball(k_spline)
    s_acb = acb(s_k)
    norm_acb = acb(1) / (acb(s_k) * acb(c_k))
    sinc_power = 2 * k_spline + 2

    def f(t: acb, analytic: bool) -> acb:
        z = acb(arb("0.25")) + i_unit * pi_acb * t
        a_val = arb.pi().log() - z.digamma().real
        a_star = two * pi_acb * acb(a_val)
        x = ell_acb * t / (two * s_acb)
        e2 = norm_acb * (sinc_acb(x, sinc_terms) ** sinc_power)
        return a_star * ell_acb * (t * d_acb).cos() * e2

    return f


def chunk_integrand(
    *,
    args: argparse.Namespace,
    builder: ArchIntervalBuilder,
    family: dict[str, Any],
    d: Decimal,
):
    if args.source == "raw_step22":
        return builder.integrand(d)
    if args.source == "centered_receiver":
        return centered_receiver_integrand(
            k_spline=int(family["k"]),
            ell=args.ell,
            d=d,
            sinc_terms=args.sinc_terms,
        )
    raise ValueError(f"unknown source {args.source!r}")


def integrate_chunk(
    *,
    args: argparse.Namespace,
    builder: ArchIntervalBuilder,
    family: dict[str, Any],
    d: Decimal,
    left: Decimal,
    right: Decimal,
) -> tuple[Decimal, Decimal]:
    f = chunk_integrand(args=args, builder=builder, family=family, d=d)
    val = acb.integral(
        f,
        arb(str(left)),
        arb(str(right)),
        rel_tol=builder.rel_tol,
        abs_tol=builder.abs_tol,
        deg_limit=builder.deg_limit,
        eval_limit=builder.eval_limit,
        depth_limit=builder.depth_limit,
    ).real
    return arb_lower_decimal(val), arb_upper_decimal(val)


def probe_row(
    *,
    args: argparse.Namespace,
    builder: ArchIntervalBuilder,
    family: dict[str, Any],
    row: dict[str, Any],
    chunks: list[dict[str, Any]],
    full_chunk_row: bool,
) -> dict[str, Any]:
    d = Decimal(row["distance"])
    chunk_rows = []
    sum_lower = Decimal("0")
    sum_upper = Decimal("0")

    for chunk in chunks:
        left = Decimal(chunk["left"])
        right = Decimal(chunk["right"])
        lower, upper = integrate_chunk(
            args=args,
            builder=builder,
            family=family,
            d=d,
            left=left,
            right=right,
        )
        sum_lower += lower
        sum_upper += upper
        chunk_rows.append(
            {
                "index": int(chunk["index"]),
                "left": decimal_str(left),
                "right": decimal_str(right),
                "lower": decimal_str(lower),
                "upper": decimal_str(upper),
                "width": decimal_str(upper - lower),
            }
        )

    target_lower = Decimal(row["target_lower_value"])
    target_upper = Decimal(row["target_upper_value"])
    lower_excess = target_lower - sum_lower
    upper_excess = sum_upper - target_upper
    excess = max(Decimal("0"), lower_excess, upper_excess)
    available_slack = optional_decimal(row.get("tail_radius_slack"))
    guard = refresh_guard(target_lower, target_upper, sum_lower, sum_upper)
    needed_refresh = Decimal("0")
    if lower_excess > 0:
        needed_refresh = max(needed_refresh, lower_excess + guard)
    if upper_excess > 0:
        needed_refresh = max(needed_refresh, upper_excess + guard)
    slack_absorbable = (
        full_chunk_row
        and available_slack is not None
        and Decimal("0") < excess
        and needed_refresh <= available_slack
    )
    slack_after_refresh = (
        available_slack - needed_refresh
        if slack_absorbable and available_slack is not None
        else None
    )
    suggested_target_lower = target_lower
    suggested_target_upper = target_upper
    if lower_excess > 0:
        suggested_target_lower = sum_lower - guard
    if upper_excess > 0:
        suggested_target_upper = sum_upper + guard

    return {
        "family_id": family["id"],
        "distance_index": int(row["index"]),
        "distance": row["distance"],
        "target_interval_sign": row.get("target_interval_sign"),
        "target_lower": decimal_str(target_lower),
        "target_upper": decimal_str(target_upper),
        "chunk_sum_lower": decimal_str(sum_lower),
        "chunk_sum_upper": decimal_str(sum_upper),
        "chunk_sum_width": decimal_str(sum_upper - sum_lower),
        "full_chunk_row": full_chunk_row,
        "fits_target": full_chunk_row and excess == 0,
        "fits_after_local_target_refresh": slack_absorbable,
        "available_target_refresh_slack": (
            decimal_str(available_slack) if available_slack is not None else None
        ),
        "target_refresh_guard": decimal_str(guard),
        "needed_target_refresh_slack": decimal_str(needed_refresh),
        "slack_after_suggested_refresh": (
            decimal_str(slack_after_refresh) if slack_after_refresh is not None else None
        ),
        "lower_excess": decimal_str(max(Decimal("0"), lower_excess)),
        "upper_excess": decimal_str(max(Decimal("0"), upper_excess)),
        "excess": decimal_str(excess),
        "suggested_target_lower": decimal_str(suggested_target_lower),
        "suggested_target_upper": decimal_str(suggested_target_upper),
        "chunks": chunk_rows,
    }


def summarize_family(family_id: str, rows: list[dict[str, Any]]) -> dict[str, Any]:
    failures = [row for row in rows if not row["fits_target"]]
    slack_absorbable = [
        row for row in failures if row["fits_after_local_target_refresh"]
    ]
    worst = max((Decimal(row["excess"]) for row in rows), default=Decimal("0"))
    return {
        "id": family_id,
        "rows_checked": len(rows),
        "rows_failed": len(failures),
        "rows_slack_absorbable": len(slack_absorbable),
        "worst_excess": decimal_str(worst),
    }


def render_md(result: dict[str, Any]) -> str:
    lines = [
        "# Step33 A chunk integral probe",
        "",
        "Diagnostic only: external acb/Arb interval evidence, not a Lean proof.",
        "",
        "## Summary",
        "",
        f"- source: `{result['parameters']['source']}`",
        f"- families checked: {result['totals']['families_checked']}",
        f"- rows checked: {result['totals']['rows_checked']}",
        f"- rows failed: {result['totals']['rows_failed']}",
        f"- rows absorbable by local target slack: {result['totals']['rows_slack_absorbable']}",
        f"- worst excess: `{result['totals']['worst_excess']}`",
        f"- full chunk rows: `{result['totals']['full_chunk_rows']}`",
        "",
        "## Families",
        "",
        "| family | rows | failed | slack-absorbable | worst excess |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for summary in result["family_summaries"]:
        lines.append(
            f"| `{summary['id']}` | {summary['rows_checked']} | "
            f"{summary['rows_failed']} | {summary['rows_slack_absorbable']} | "
            f"`{summary['worst_excess']}` |"
        )

    failures = result.get("worst_failures", [])
    if failures:
        lines.extend(
            [
                "",
                "## Worst failures",
                "",
                "| family | idx | d | sign | lower excess | upper excess | excess | available slack | absorbable |",
                "| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | --- |",
            ]
        )
        for row in failures:
            lines.append(
                f"| `{row['family_id']}` | {row['distance_index']} | `{row['distance']}` | "
                f"`{row['target_interval_sign']}` | `{row['lower_excess']}` | "
                f"`{row['upper_excess']}` | `{row['excess']}` | "
                f"`{row['available_target_refresh_slack']}` | "
                f"`{row['fits_after_local_target_refresh']}` |"
            )
    refresh_rows = [
        row
        for family in result["families"]
        for row in family["rows"]
        if row["fits_after_local_target_refresh"]
    ]
    if refresh_rows:
        lines.extend(
            [
                "",
                "## Local target refresh candidates",
                "",
                "These rows do not fit the current generated target interval, but the",
                "excess is smaller than the already available payload slack.  Refreshing",
                "the local raw-Omega arithmetic target for these rows would not require",
                "A CSV, ARadius, radius-floor, or LDL changes.",
                "",
                "| family | idx | suggested lower | suggested upper | slack after refresh |",
                "| --- | ---: | ---: | ---: | ---: |",
            ]
        )
        for row in refresh_rows:
            lines.append(
                f"| `{row['family_id']}` | {row['distance_index']} | "
                f"`{row['suggested_target_lower']}` | "
                f"`{row['suggested_target_upper']}` | "
                f"`{row['slack_after_suggested_refresh']}` |"
            )
    return "\n".join(lines) + "\n"


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--families", type=str, default="all")
    parser.add_argument("--indices", type=str, default="0")
    parser.add_argument("--chunk-indices", type=str, default="all")
    parser.add_argument(
        "--source",
        choices=["centered_receiver", "raw_step22"],
        default="raw_step22",
        help=(
            "Chunk source to integrate. Use raw_step22 for the active "
            "raw-Omega Step33A.1-A route; centered_receiver is diagnostic only."
        ),
    )
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--rel-tol", type=str, default="1e-40")
    parser.add_argument("--abs-tol", type=str, default="1e-40")
    parser.add_argument("--deg-limit", type=int, default=64)
    parser.add_argument("--eval-limit", type=int, default=100000)
    parser.add_argument("--depth-limit", type=int, default=20)
    parser.add_argument("--sinc-terms", type=int, default=90)
    parser.add_argument("--omega-factor", type=str, default="10")
    parser.add_argument("--radius-floor", type=str, default="1e-30")
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--out-json", type=Path, default=REQUEST_DIR / "a_chunk_integral_probe.json")
    parser.add_argument("--out-md", type=Path, default=REQUEST_DIR / "a_chunk_integral_probe.md")
    args = parser.parse_args()

    set_precision(args.arb_prec)
    getcontext().prec = max(100, args.arb_prec // 2)

    worklist = load_worklist(args.worklist)
    family_rows = []
    family_summaries = []

    for family in selected_families(worklist, args.families):
        builder = make_builder(args, family=family)
        chunks, full_chunk_row = selected_chunks(family, args.chunk_indices)
        rows = selected_distance_rows(family, args.indices)
        checked_rows = []
        print(
            f"family={family['id']} k={family['k']} rows={len(rows)} "
            f"chunks={len(chunks)}/{len(family.get('chunks', []))} "
            f"source={args.source}"
        )
        for row in rows:
            checked = probe_row(
                args=args,
                builder=builder,
                family=family,
                row=row,
                chunks=chunks,
                full_chunk_row=full_chunk_row,
            )
            checked_rows.append(checked)
            print(
                f"  idx={checked['distance_index']:02d} d={checked['distance']} "
                f"sum=[{checked['chunk_sum_lower']}, {checked['chunk_sum_upper']}] "
                f"target=[{checked['target_lower']}, {checked['target_upper']}] "
                f"excess={checked['excess']} fits={checked['fits_target']}"
            )
        family_rows.append({"family": family["id"], "rows": checked_rows})
        family_summaries.append(summarize_family(family["id"], checked_rows))

    flat_rows = [row for family in family_rows for row in family["rows"]]
    worst = max((Decimal(row["excess"]) for row in flat_rows), default=Decimal("0"))
    worst_failures = sorted(
        [row for row in flat_rows if Decimal(row["excess"]) > 0],
        key=lambda row: Decimal(row["excess"]),
        reverse=True,
    )[:12]
    result = {
        "schema": "q3_psdpd_step33_a_chunk_integral_probe.v1",
        "meaning": (
            "Diagnostic exact-integrand acb/Arb chunk interval probe for the "
            "Step33 Arch-side A finite/tail worklist. This does not mutate "
            "ARadius, CSV files, or global payload radii, and is not a Lean "
            "proof artifact."
        ),
        "source_worklist": str(args.worklist),
        "parameters": {
            "families": args.families,
            "indices": args.indices,
            "chunk_indices": args.chunk_indices,
            "source": args.source,
            "ell": args.ell,
            "rel_tol": args.rel_tol,
            "abs_tol": args.abs_tol,
            "deg_limit": args.deg_limit,
            "eval_limit": args.eval_limit,
            "depth_limit": args.depth_limit,
            "sinc_terms": args.sinc_terms,
            "omega_factor": args.omega_factor,
            "radius_floor": args.radius_floor,
            "arb_prec": args.arb_prec,
        },
        "totals": {
            "families_checked": len(family_rows),
            "rows_checked": len(flat_rows),
            "rows_failed": sum(1 for row in flat_rows if not row["fits_target"]),
            "rows_slack_absorbable": sum(
                1 for row in flat_rows if row["fits_after_local_target_refresh"]
            ),
            "worst_excess": decimal_str(worst),
            "full_chunk_rows": args.chunk_indices == "all",
        },
        "family_summaries": family_summaries,
        "worst_failures": worst_failures,
        "families": family_rows,
    }

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Wrote {args.out_json}")
    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_md(result), encoding="utf-8")
        print(f"Wrote {args.out_md}")


if __name__ == "__main__":
    run()
