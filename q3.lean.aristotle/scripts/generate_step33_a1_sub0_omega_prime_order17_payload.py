#!/usr/bin/env python3
"""OmegaPrime order-17 rational payload ledger for Step33A.1-A sub0."""

from __future__ import annotations

import hashlib
import json
import sys
from datetime import datetime, timezone
from fractions import Fraction
from math import factorial
from pathlib import Path
from typing import Any


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(2_000_000)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

LEAN_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17RationalPayload.lean"
)
JSON_OUT = REQUEST_DIR / "step33_a1_sub0_omega_prime_order17_payload.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_omega_prime_order17_payload.md"

SCHEMA = "q3_psdpd_step33_a1_sub0_omega_prime_order17_payload.v1"
FAILURE_CODE = "STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP"
BUDGET_FAIL = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_REMAINDER_BUDGET_CONSTANT_FAIL"
)

M = 17

REQUIRED_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN",
    "primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixAbs",
    "primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TailAbs",
    "primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs",
    "omegaPrimeTrigammaDerivCoeff_norm_eq_order17",
    "omegaPrimeOrder17_half_prefix_majorant_le_generated",
    "omegaPrimeOrder17_half_shifted_tsum_le_generated",
    "half_tsum_majorant_le_generated",
    "primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_generated",
]


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def rat_str(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def line_of_symbol(path: Path, symbol: str) -> int | None:
    if not path.exists():
        return None
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if symbol in line:
            return line_no
    return None


def symbol_audit(path: Path) -> dict[str, dict[str, Any]]:
    return {
        symbol: {
            "present": (line := line_of_symbol(path, symbol)) is not None,
            "line": line,
        }
        for symbol in REQUIRED_SYMBOLS
    }


def coeff_norm(m: int) -> Fraction:
    return Fraction(factorial(m + 1), 2**m)


def majorant(m: int, n: int) -> Fraction:
    return coeff_norm(m) / (Fraction(4 * n + 1, 4) ** (m + 2))


def half_prefix(m: int, prefix_n: int) -> Fraction:
    return Fraction(1, 2) * sum((majorant(m, n) for n in range(prefix_n)), Fraction(0))


def half_tail(m: int, prefix_n: int) -> Fraction:
    lower_edge = Fraction(4 * prefix_n - 3, 4)
    return Fraction(1, 2) * coeff_norm(m) / (lower_edge ** (m + 1) * (m + 1))


def choose_prefix_n() -> tuple[int, list[dict[str, Any]]]:
    candidates: list[dict[str, Any]] = []
    for prefix_n in range(2, 9):
        prefix = half_prefix(M, prefix_n)
        tail = half_tail(M, prefix_n)
        total = prefix + tail
        candidates.append(
            {
                "prefixN": prefix_n,
                "prefixAbs": rat_str(prefix),
                "tailAbs": rat_str(tail),
                "order17Abs": rat_str(total),
                "tailLeLastPrefixTerm": tail <= Fraction(1, 2) * majorant(M, prefix_n - 1),
            }
        )
    for candidate in candidates:
        if candidate["tailLeLastPrefixTerm"]:
            return int(candidate["prefixN"]), candidates
    return 8, candidates


def build_ledger() -> dict[str, Any]:
    prefix_n, candidates = choose_prefix_n()
    prefix = half_prefix(M, prefix_n)
    tail = half_tail(M, prefix_n)
    total = prefix + tail
    symbols = symbol_audit(LEAN_FILE)
    proof_grade = LEAN_FILE.exists() and all(item["present"] for item in symbols.values())
    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "omega_prime_order17_rational_tail_payload",
        "proofGrade": proof_grade,
        "firstFailure": None if proof_grade else FAILURE_CODE,
        "leanFile": rel(LEAN_FILE),
        "leanFileSha256": sha256_file(LEAN_FILE),
        "requiredSymbols": symbols,
        "theorem": (
            "Step33Sub0OmegaPrimeOrder17Payload."
            "primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_generated"
        ),
        "budgetTheorem": "Step33Sub0OmegaPrimeOrder17Payload.half_tsum_majorant_le_generated",
        "m": M,
        "prefixN": prefix_n,
        "prefixPolicy": "first candidate with tail <= last retained half-prefix term",
        "candidateScan": candidates,
        "coeffNorm": rat_str(coeff_norm(M)),
        "prefixAbs": rat_str(prefix),
        "tailAbs": rat_str(tail),
        "order17Abs": rat_str(total),
        "statement": (
            "forall eta in Set.Icc 0 (1/10), "
            "norm (D^17 step22OmegaArchWeightDerivClosedForm eta) <= order17Abs"
        ),
        "degree0Budget": {
            "status": "not_checked_here",
            "rule": "coeffErrorAbs + activeScaleAbs * order17Abs / 20 <= polyErrorAbs",
            "order17Abs": rat_str(total),
            "failureIfFalse": BUDGET_FAIL,
        },
        "notClosedByThis": [
            "RawProduct18 majorant numeric/rational assembly",
            "D16 center interval",
            "degree-0 coeffErrorAbs/polyErrorAbs budget comparison",
            "Step33A.1-A closure",
        ],
    }


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# OmegaPrime Order-17 Rational Payload",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        "",
        "## Verdict",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- firstFailure: `{ledger['firstFailure']}`",
        f"- Lean file: `{ledger['leanFile']}`",
        f"- theorem: `{ledger['theorem']}`",
        f"- budget theorem: `{ledger['budgetTheorem']}`",
        "",
        "## Exact Constants",
        "",
        f"- m: `{ledger['m']}`",
        f"- prefixN: `{ledger['prefixN']}`",
        f"- prefixPolicy: `{ledger['prefixPolicy']}`",
        f"- coeffNorm: `{ledger['coeffNorm']}`",
        f"- prefixAbs: `{ledger['prefixAbs']}`",
        f"- tailAbs: `{ledger['tailAbs']}`",
        f"- order17Abs: `{ledger['order17Abs']}`",
        "",
        "## Candidate Scan",
        "",
    ]
    for candidate in ledger["candidateScan"]:
        lines.append(
            "- "
            f"N=`{candidate['prefixN']}`, "
            f"order17Abs=`{candidate['order17Abs']}`, "
            f"tailLeLastPrefixTerm=`{candidate['tailLeLastPrefixTerm']}`"
        )
    lines.extend(
        [
            "",
            "## Required Lean Symbols",
            "",
        ]
    )
    for symbol, item in ledger["requiredSymbols"].items():
        lines.append(f"- `{symbol}`: present=`{item['present']}`, line=`{item['line']}`")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "This closes only the OmegaPrime order-17 rational source row.  It does not "
            "close the RawProduct18 majorant, the degree-0 budget, or Step33A.1-A.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(JSON_OUT.relative_to(ROOT))
    print(MD_OUT.relative_to(ROOT))
    if not ledger["proofGrade"]:
        print(ledger["firstFailure"])


if __name__ == "__main__":
    main()
