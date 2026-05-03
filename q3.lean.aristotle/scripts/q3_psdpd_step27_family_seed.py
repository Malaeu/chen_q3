#!/usr/bin/env python3
"""
Step 27 PSD-pd directed-family seed generator.

Reads Step 26 FiniteCert ledger JSON and emits a first directed-family seed.

This does not prove exhaustion.  It creates the audit object that later steps
will enrich into an actual certificate family.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal, ROUND_FLOOR
from pathlib import Path
from typing import Any


def decimal_floor_ratio(value: float, denominator: int) -> dict[str, str]:
    x = Decimal(str(value))
    den = Decimal(denominator)
    num = (x * den).to_integral_value(rounding=ROUND_FLOOR)
    return {
        "num": str(num),
        "den": str(denominator),
        "decimal": str(num / den),
    }


def cert_to_family_block(cert: dict[str, Any], floor_den: int) -> dict[str, Any]:
    params = cert["parameters"]
    guards = cert["guards"]
    artifacts = cert["artifacts"]

    return {
        "cert_id": cert["cert_id"],
        "block_id": cert["block_id"],
        "family_id": cert["family_id"],
        "role": cert["role"],
        "L": params["L"],
        "k_spline": params["k_spline"],
        "ell": params["ell"],
        "delta": params["delta"],
        "kappa": params["kappa"],
        "theta": params["theta"],
        "tau_grid": params["tau_grid"],
        "dtheta_safe_lower": guards["Dtheta_safe_lower"],
        "rkappa_safe_lower": guards["Rkappa_safe_lower"],
        "dtheta_floor": decimal_floor_ratio(guards["Dtheta_safe_lower"], floor_den),
        "rkappa_floor": decimal_floor_ratio(guards["Rkappa_safe_lower"], floor_den),
        "midpoint_csv": artifacts["midpoint_csv"],
        "radius_csv": artifacts["radius_csv"],
        "midpoint_sha256": artifacts["midpoint_sha256"],
        "radius_sha256": artifacts["radius_sha256"],
        "step18_stdout": artifacts["step18_stdout"],
        "theorem_payload": cert["theorem_payload"],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--ledger",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_finitecert_ledger.json",
    )
    parser.add_argument(
        "--out",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_directed_family_seed.json",
    )
    parser.add_argument(
        "--floor-den",
        type=int,
        default=10**12,
        help="Denominator for conservative rational floors of safe lower bounds.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    ledger_path = Path(args.ledger)
    if not ledger_path.exists():
        raise SystemExit(f"Ledger JSON not found: {ledger_path}")
    if args.floor_den <= 0 or not math.isfinite(args.floor_den):
        raise SystemExit("--floor-den must be positive")

    ledger = json.loads(ledger_path.read_text())
    certs = ledger.get("finite_certs", [])

    family_blocks = [
        cert_to_family_block(cert, args.floor_den)
        for cert in certs
    ]

    payload = {
        "schema": "q3_psdpd_directed_family_seed_v1",
        "status": "seed_only_not_exhaustive",
        "meaning": (
            "This seed records accepted finite certificate blocks. "
            "It is not yet an exhausting directed family."
        ),
        "source_ledger": args.ledger,
        "accepted_blocks": len(family_blocks),
        "known_refinements": [],
        "next_required_theorems": [
            "directed_refinement_relation",
            "boundary_null_correction",
            "finite_space_density",
            "Weil_form_continuity",
            "uniform_certificate_family",
        ],
        "blocks": family_blocks,
    }

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True))

    print("== Step 27 directed-family seed ==")
    print(f"blocks accepted: {len(family_blocks)}")
    print(f"wrote: {out}")


if __name__ == "__main__":
    main()
