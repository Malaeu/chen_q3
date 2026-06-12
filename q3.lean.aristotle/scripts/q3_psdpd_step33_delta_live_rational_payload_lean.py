#!/usr/bin/env python3
"""Generate the Step33 delta/live rational payload Lean surface.

This generator converts the 1024-bit/36-decimal live-only audit payload into
concrete rational term midpoint/radius witness functions.  It does not trust
the audit as a proof: the emitted Lean module still requires kernel-checked
term hboxes and a kernel-checked center-error budget before the generic
Step33A.1 option-B receiver can be instantiated.
"""

from __future__ import annotations

import json
import math
import re
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, getcontext
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAYLOAD_JSON = (
    ROOT
    / "ACTIVE/requests/step33_bootstrap/"
    / "termwise_replay_audit_live_1024_payload.json"
)
OUT = ROOT / "Q3/Proofs/PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport.lean"
SUPPORT_OUT = (
    ROOT / "Q3/Proofs/PSD_CenteredCoeffPrimeDeltaLiveRationalSupportImport.lean"
)
SUPPORT_SIDE_OUTS = {
    ("primaryK11", "minus"): ROOT
    / "Q3/Proofs/PSD_CenteredCoeffPrimeDeltaLiveRationalSupportPrimaryMinusImport.lean",
    ("primaryK11", "plus"): ROOT
    / "Q3/Proofs/PSD_CenteredCoeffPrimeDeltaLiveRationalSupportPrimaryPlusImport.lean",
    ("controlK9", "minus"): ROOT
    / "Q3/Proofs/PSD_CenteredCoeffPrimeDeltaLiveRationalSupportControlMinusImport.lean",
    ("controlK9", "plus"): ROOT
    / "Q3/Proofs/PSD_CenteredCoeffPrimeDeltaLiveRationalSupportControlPlusImport.lean",
}
SUPPORT_CHUNK_SIZE = 1
SUPPORT_CHUNK_RANGES = tuple(
    (start, min(start + SUPPORT_CHUNK_SIZE - 1, 97))
    for start in range(0, 98, SUPPORT_CHUNK_SIZE)
)
SUPPORT_SIDE_TITLES = {
    ("primaryK11", "minus"): "PrimaryMinus",
    ("primaryK11", "plus"): "PrimaryPlus",
    ("controlK9", "minus"): "ControlMinus",
    ("controlK9", "plus"): "ControlPlus",
}


def support_side_chunk_out(prefix: str, side: str, chunk_idx: int) -> Path:
    title = SUPPORT_SIDE_TITLES[(prefix, side)]
    return (
        ROOT
        / "Q3/Proofs/"
        / f"PSD_CenteredCoeffPrimeDeltaLiveRationalSupport{title}Chunk{chunk_idx}Import.lean"
    )


def support_side_chunk_module(prefix: str, side: str, chunk_idx: int) -> str:
    title = SUPPORT_SIDE_TITLES[(prefix, side)]
    return (
        "Q3.Proofs."
        f"PSD_CenteredCoeffPrimeDeltaLiveRationalSupport{title}Chunk{chunk_idx}Import"
    )


def support_side_zero_chunk_out(prefix: str, side: str, chunk_idx: int) -> Path:
    title = SUPPORT_SIDE_TITLES[(prefix, side)]
    return (
        ROOT
        / "Q3/Proofs/"
        / f"PSD_CenteredCoeffPrimeDeltaLiveRationalSupport{title}ZeroChunk{chunk_idx}Import.lean"
    )


def support_side_zero_chunk_module(prefix: str, side: str, chunk_idx: int) -> str:
    title = SUPPORT_SIDE_TITLES[(prefix, side)]
    return (
        "Q3.Proofs."
        f"PSD_CenteredCoeffPrimeDeltaLiveRationalSupport{title}ZeroChunk{chunk_idx}Import"
    )


DICTIONARY_LEAN = ROOT / "Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean"
PRIME_CERT_FILES = (
    ROOT
    / "Q3/Proofs/PrimeCert/"
    / "BrangeHeatCert_2026_01_28_PrimePowBucket0Auto_0_249.lean",
    ROOT
    / "Q3/Proofs/PrimeCert/"
    / "BrangeHeatCert_2026_01_28_PrimePowBucket0Auto_250_499.lean",
)

TermWitness = tuple[str, str, str, str, str, str, str, str, str, str]

TERM_MID = 0
TERM_RAD = 1
WEIGHT_MID = 2
WEIGHT_RAD = 3
RPAIR_MID = 4
RPAIR_RAD = 5
RMINUS_MID = 6
RMINUS_RAD = 7
RPLUS_MID = 8
RPLUS_RAD = 9

getcontext().prec = 280


def parse_nat_entry_map(source: str, name: str) -> dict[int, int]:
    match = re.search(
        rf"def {re.escape(name)} : Nat -> Nat\n(.*?)(?=\n\ndef |\n/--|\Z)",
        source,
        re.S,
    )
    if match is None:
        raise SystemExit(f"{DICTIONARY_LEAN}: missing {name}")
    return {
        int(index): int(value)
        for index, value in re.findall(r"\| (\d+) => (\d+)", match.group(1))
    }


def sieve_primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = [True] * (limit + 1)
    out: list[int] = []
    for p in range(2, limit + 1):
        if not sieve[p]:
            continue
        out.append(p)
        start = p * p
        if start <= limit:
            for k in range(start, limit + 1, p):
                sieve[k] = False
    return out


def audit_to_lean_prime_shift_index() -> dict[int, int]:
    """Map audit prime-power order to Lean's active L=3 dictionary order.

    The audit code enumerates prime powers grouped by prime:
      (2,1), (2,2), ..., (3,1), ...
    Lean's `PrimeShiftIndexL3` dictionary is ordered differently.  The payload
    must be remapped by `(prime base, exponent)`, otherwise generated witnesses
    land on the wrong Lean summand index.
    """

    source = DICTIONARY_LEAN.read_text()
    base_by_lean = parse_nat_entry_map(source, "activeL3PrimeBaseEntry")
    exponent_by_lean = parse_nat_entry_map(source, "activeL3PrimeExponentEntry")
    lean_by_pair = {
        (base_by_lean[n], exponent_by_lean[n]): n
        for n in sorted(base_by_lean)
    }

    cutoff = 6.0
    max_n = int(math.floor(math.exp(cutoff))) + 1
    out: dict[int, int] = {}
    audit_index = 0
    for p in sieve_primes(max_n):
        r_pow = 1
        while r_pow * math.log(p) <= cutoff + 1e-12:
            pair = (p, r_pow)
            if pair not in lean_by_pair:
                raise SystemExit(f"missing Lean prime-shift index for {pair}")
            out[audit_index] = lean_by_pair[pair]
            audit_index += 1
            r_pow += 1

    if len(out) != len(base_by_lean):
        raise SystemExit(
            "audit/Lean prime-shift dictionary size mismatch: "
            f"audit={len(out)} lean={len(base_by_lean)}"
        )
    return out


@lru_cache(maxsize=1)
def lean_prime_shift_maps() -> tuple[dict[int, int], dict[int, int]]:
    source = DICTIONARY_LEAN.read_text()
    return (
        parse_nat_entry_map(source, "activeL3PrimeBaseEntry"),
        parse_nat_entry_map(source, "activeL3PrimeExponentEntry"),
    )


@lru_cache(maxsize=1)
def parse_prime_cert_log_constants() -> dict[str, Decimal]:
    out: dict[str, Decimal] = {}
    for path in PRIME_CERT_FILES:
        source = path.read_text()
        for name, numerator, denominator in re.findall(
            r"def ([lu]_\d+) : ℝ := \((\d+) : ℝ\) / \((\d+) : ℝ\)",
            source,
        ):
            out[name] = Decimal(numerator) / Decimal(denominator)
    return out


def assert_declared_support_is_certified_live(
    block_name: str, by_delta: dict[int, dict[int, TermWitness]]
) -> None:
    """Check the generated support against Lean's certified log bounds.

    This is only a generator guard.  The emitted Lean module still exposes the
    actual `DeclaredNonzeroSubsetLive` proof obligation until the corresponding
    kernel proof generator is added.
    """

    base_by_lean, exponent_by_lean = lean_prime_shift_maps()
    constants = parse_prime_cert_log_constants()
    ell = Decimal("0.3")
    failures: list[tuple[int, int, int, int]] = []
    for delta, terms in by_delta.items():
        d = Decimal(delta) / Decimal(4)
        for lean_n in terms:
            base = base_by_lean[lean_n]
            exponent = exponent_by_lean[lean_n]
            lo = Decimal(exponent) * constants[f"l_{base}"]
            hi = Decimal(exponent) * constants[f"u_{base}"]
            minus_live = (-2 < (d - hi) / ell) and ((d - lo) / ell < 2)
            plus_live = (-2 < (d + lo) / ell) and ((d + hi) / ell < 2)
            if not (minus_live or plus_live):
                failures.append((delta, lean_n, base, exponent))
    if failures:
        preview = ", ".join(map(str, failures[:8]))
        raise SystemExit(
            f"{block_name}: declared support is not certified-live after "
            f"audit->Lean remap; first failures: {preview}"
        )


def rat_lit(text: str) -> str:
    value = Decimal(text)
    if value.is_zero():
        return "(0 : Rat)"
    sign, digits, exponent = value.as_tuple()
    numerator = 0
    for digit in digits:
        numerator = numerator * 10 + digit
    if sign:
        numerator = -numerator
    if exponent >= 0:
        numerator *= 10**exponent
        denominator = 1
    else:
        denominator = 10 ** (-exponent)
    if denominator == 1:
        return f"({numerator} : Rat)"
    return f"(({numerator} : Rat) / {denominator} : Rat)"


def rat_lit_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : Rat)"
    return f"(({value.numerator} : Rat) / {value.denominator} : Rat)"


def rat_expr(text: str) -> str:
    return f"(({rat_lit(text)} : Rat) : Real)"


def active_log_bound_nums(base: int) -> tuple[int, int]:
    log_value = Decimal(base).ln()
    lo = int(
        (log_value * Decimal(WEIGHT_CERT_SCALE)).to_integral_value(
            rounding=ROUND_FLOOR
        )
    )
    return lo, lo + 1


def active_shift_bound_fracs(lean_n: int) -> tuple[Fraction, Fraction, int, int]:
    base_by_lean, exponent_by_lean = lean_prime_shift_maps()
    base = base_by_lean[lean_n]
    exponent = exponent_by_lean[lean_n]
    log_lo, log_hi = active_log_bound_nums(base)
    scale = WEIGHT_CERT_SCALE
    return (
        Fraction(exponent * log_lo, scale),
        Fraction(exponent * log_hi, scale),
        base,
        exponent,
    )


def split_r_arg_bound_fracs(delta: int, lean_n: int, side: str) -> tuple[Fraction, Fraction, int, int]:
    shift_lo, shift_hi, base, exponent = active_shift_bound_fracs(lean_n)
    center = Fraction(delta, 4)
    ell = Fraction(3, 10)
    if side == "minus":
        return (center - shift_hi) / ell, (center - shift_lo) / ell, base, exponent
    if side == "plus":
        return (center + shift_lo) / ell, (center + shift_hi) / ell, base, exponent
    raise ValueError(side)


def delta_key(entry: dict) -> int:
    # Centers are spaced by 1/4 and the JSON stores delta = (i - j) / 4 for
    # display.  The Lean center difference is center j - center i, so use
    # j - i directly.
    return int(entry["j"]) - int(entry["i"])


def load_blocks() -> tuple[
    dict[str, dict[int, dict[int, TermWitness]]],
    dict[int, tuple[str, str]],
]:
    payload = json.loads(PAYLOAD_JSON.read_text())
    if not isinstance(payload, list):
        raise SystemExit(f"{PAYLOAD_JSON}: expected top-level list")
    audit_to_lean = audit_to_lean_prime_shift_index()
    out: dict[str, dict[int, dict[int, TermWitness]]] = {}
    weight_payload: dict[int, tuple[str, str]] = {}
    for block in payload:
        name = block.get("block")
        if name not in {"primary", "control"}:
            raise SystemExit(f"{PAYLOAD_JSON}: unexpected block {name!r}")
        if block.get("arb_prec") != 1024:
            raise SystemExit(f"{name}: expected arb_prec=1024")
        if block.get("term_digits") != 36:
            raise SystemExit(f"{name}: expected term_digits=36")
        if int(block.get("witness_digits", 0)) < 96:
            raise SystemExit(f"{name}: expected witness_digits>=96")
        if block.get("live_only") is not True:
            raise SystemExit(f"{name}: expected live_only=true")
        if block.get("failed_entries") != 0:
            raise SystemExit(f"{name}: audit has failed entries")
        if block.get("verdict") != "termwise_receiver_fits":
            raise SystemExit(f"{name}: unexpected verdict {block.get('verdict')!r}")

        block_weight_payload = {
            audit_to_lean[int(term["n"])]: (str(term["mid"]), str(term["rad"]))
            for term in block.get("weight_payloads", [])
        }
        if set(block_weight_payload) != set(range(len(audit_to_lean))):
            missing = sorted(set(range(len(audit_to_lean))) - set(block_weight_payload))
            extra = sorted(set(block_weight_payload) - set(range(len(audit_to_lean))))
            raise SystemExit(
                f"{name}: weight payload mismatch missing={missing} extra={extra}"
            )
        if not weight_payload:
            weight_payload = block_weight_payload
        elif weight_payload != block_weight_payload:
            raise SystemExit(f"{name}: inconsistent primary/control weight payload")

        by_delta: dict[int, dict[int, TermWitness]] = {}
        seen: dict[int, tuple[tuple[int, str, str, str, str, str, str], ...]] = {}
        for entry in block["entry_payloads"]:
            delta = delta_key(entry)
            terms = tuple(
                (
                    audit_to_lean[int(term["n"])],
                    str(term["mid"]),
                    str(term["rad"]),
                    str(term["weight_mid"]),
                    str(term["weight_rad"]),
                    str(term["rpair_mid"]),
                    str(term["rpair_rad"]),
                    str(term["rminus_mid"]),
                    str(term["rminus_rad"]),
                    str(term["rplus_mid"]),
                    str(term["rplus_rad"]),
                )
                for term in entry["live_terms"]
            )
            if delta in seen and seen[delta] != terms:
                raise SystemExit(f"{name}: inconsistent live terms for delta {delta}")
            seen[delta] = terms
        for delta, terms in seen.items():
            by_delta[delta] = {
                n: (
                    mid,
                    rad,
                    weight_mid,
                    weight_rad,
                    rpair_mid,
                    rpair_rad,
                    rminus_mid,
                    rminus_rad,
                    rplus_mid,
                    rplus_rad,
                )
                for (
                    n,
                    mid,
                    rad,
                    weight_mid,
                    weight_rad,
                    rpair_mid,
                    rpair_rad,
                    rminus_mid,
                    rminus_rad,
                    rplus_mid,
                    rplus_rad,
                ) in terms
            }
        expected = set(range(-22, 23))
        if set(by_delta) != expected:
            missing = sorted(expected - set(by_delta))
            extra = sorted(set(by_delta) - expected)
            raise SystemExit(f"{name}: delta mismatch missing={missing} extra={extra}")
        assert_declared_support_is_certified_live(name, by_delta)
        out[name] = by_delta
    if set(out) != {"primary", "control"}:
        raise SystemExit(f"{PAYLOAD_JSON}: missing primary/control blocks")
    return out, weight_payload


def nonzero_terms(values: dict[int, TermWitness]) -> list[int]:
    out: list[int] = []
    for n, values_for_n in sorted(values.items()):
        mid = values_for_n[TERM_MID]
        rad = values_for_n[TERM_RAD]
        if not Decimal(mid).is_zero() or not Decimal(rad).is_zero():
            out.append(n)
    return out


def nonzero_terms_for_fields(
    values: dict[int, TermWitness], field_indices: tuple[int, ...]
) -> list[int]:
    out: list[int] = []
    for n, values_for_n in sorted(values.items()):
        if any(not Decimal(values_for_n[field_idx]).is_zero() for field_idx in field_indices):
            out.append(n)
    return out


def emit_declared_set(def_name: str, by_delta: dict[int, dict[int, TermWitness]]) -> str:
    lines = [f"def {def_name} : Int -> Finset Nat"]
    for delta in range(-22, 23):
        terms = nonzero_terms(by_delta[delta])
        if terms:
            body = "{" + ", ".join(str(n) for n in terms) + "}"
            lines.append(f"  | {delta} => ({body} : Finset Nat)")
        else:
            lines.append(f"  | {delta} => (∅ : Finset Nat)")
    lines.append("  | _ => ∅")
    return "\n".join(lines)


def emit_declared_set_for_fields(
    def_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
    field_indices: tuple[int, ...],
) -> str:
    lines = [f"def {def_name} : Int -> Finset Nat"]
    for delta in range(-22, 23):
        terms = nonzero_terms_for_fields(by_delta[delta], field_indices)
        if terms:
            body = "{" + ", ".join(str(n) for n in terms) + "}"
            lines.append(f"  | {delta} => ({body} : Finset Nat)")
        else:
            lines.append(f"  | {delta} => (∅ : Finset Nat)")
    lines.append("  | _ => ∅")
    return "\n".join(lines)


def emit_table(
    def_name: str,
    field: str,
    by_delta: dict[int, dict[int, TermWitness]],
    declared_set_name: str,
) -> str:
    field_idx_by_name = {
        "mid": TERM_MID,
        "rad": TERM_RAD,
        "weight_mid": WEIGHT_MID,
        "weight_rad": WEIGHT_RAD,
        "rpair_mid": RPAIR_MID,
        "rpair_rad": RPAIR_RAD,
        "rminus_mid": RMINUS_MID,
        "rminus_rad": RMINUS_RAD,
        "rplus_mid": RPLUS_MID,
        "rplus_rad": RPLUS_RAD,
    }
    field_idx = field_idx_by_name[field]
    rat_raw_name = f"{def_name}RatRaw"
    rat_name = f"{def_name}Rat"
    raw_name = f"{def_name}Raw"
    lines = [f"def {rat_raw_name} : Int -> Nat -> Rat"]
    for delta in range(-22, 23):
        for n, values in sorted(by_delta[delta].items()):
            lines.append(f"  | {delta}, {n} => {rat_lit(values[field_idx])}")
    lines.append("  | _, _ => 0")
    lines.append("")
    lines.append(f"def {raw_name} (delta : Int) (n : Nat) : Real :=")
    lines.append(f"  (({rat_raw_name} delta n : Rat) : Real)")
    lines.append("")
    lines.append(f"def {rat_name} (delta : Int) (n : Nat) : Rat :=")
    lines.append(
        f"  if n ∈ {declared_set_name} delta then {rat_raw_name} delta n else 0"
    )
    lines.append("")
    lines.append(f"def {def_name} (delta : Int) (n : Nat) : Real :=")
    lines.append(f"  (({rat_name} delta n : Rat) : Real)")
    return "\n".join(lines)


def emit_shift_table(
    *,
    raw_name: str,
    rat_name: str,
    real_name: str,
    values: dict[int, tuple[str, str]],
    field_idx: int,
) -> str:
    lines = [f"def {raw_name} : Nat -> Rat"]
    for n in range(98):
        lines.append(f"  | {n} => {rat_lit(values[n][field_idx])}")
    lines.append("  | _ => 0")
    lines.append("")
    lines.append(f"def {rat_name} (n : PrimeShiftIndexL3) : Rat :=")
    lines.append(f"  {raw_name} n.1")
    lines.append("")
    lines.append(f"def {real_name} (n : PrimeShiftIndexL3) : Real :=")
    lines.append(f"  (({rat_name} n : Rat) : Real)")
    return "\n".join(lines)


def lean_delta_suffix(delta: int) -> str:
    if delta < 0:
        return f"m{abs(delta)}"
    if delta > 0:
        return f"p{delta}"
    return "z0"


def disjunction(parts: list[str]) -> str:
    if not parts:
        return "False"
    out = parts[-1]
    for part in reversed(parts[:-1]):
        out = f"{part} ∨ {out}"
    return out


def support_proof_data(delta: int, lean_n: int) -> tuple[str, int, int]:
    base_by_lean, exponent_by_lean = lean_prime_shift_maps()
    constants = parse_prime_cert_log_constants()
    ell = Decimal("0.3")
    d = Decimal(delta) / Decimal(4)
    base = base_by_lean[lean_n]
    exponent = exponent_by_lean[lean_n]
    lo = Decimal(exponent) * constants[f"l_{base}"]
    hi = Decimal(exponent) * constants[f"u_{base}"]
    minus_live = (-2 < (d - hi) / ell) and ((d - lo) / ell < 2)
    plus_live = (-2 < (d + lo) / ell) and ((d + hi) / ell < 2)
    if plus_live:
        return "plus", base, exponent
    if minus_live:
        return "minus", base, exponent
    raise SystemExit(f"uncertified support pair delta={delta} n={lean_n}")


def emit_support_pair_helper(
    *,
    prefix: str,
    ell_name: str,
    ell_rat_name: str,
    live_set_name: str,
    delta: int,
    lean_n: int,
) -> str:
    side, base, exponent = support_proof_data(delta, lean_n)
    suffix = f"{lean_delta_suffix(delta)}_shift{lean_n}"
    theorem_name = f"{prefix}_mem_live_delta_{suffix}_of_val_eq"
    delta_expr = f"((({delta} : Int) : Real) / 4)"
    if side == "plus":
        return f"""
private theorem {theorem_name}
    (n : PrimeShiftIndexL3) (hv : n.1 = {lean_n}) :
    n ∈ {live_set_name} {delta_expr} := by
  cases n with
  | mk val hval =>
    simp at hv
    subst val
    exact {prefix}_mem_live_of_plus_shift_tight_bounds {delta_expr}
      (Fin.mk {lean_n} hval)
      (by
        rw [activeL3PrimeShiftLower, activeL3PrimeLogLower,
          activeL3PrimeExponent]
        change (-2 : Real) <
          ((({delta} : Int) : Real) / 4 +
            ((activeL3PrimeExponentEntry {lean_n} : Nat) : Real) *
              activeL3PrimeLogLowerEntry {lean_n}) / {ell_name}
        rw [show activeL3PrimeExponentEntry {lean_n} = {exponent} by rfl,
          show activeL3PrimeLogLowerEntry {lean_n} =
            _root_.Q3.Proofs.PrimeCert.l_{base} by rfl]
        norm_num [{ell_name}, {ell_rat_name},
          _root_.Q3.Proofs.PrimeCert.l_{base}])
      (by
        rw [activeL3PrimeShiftUpper, activeL3PrimeLogUpper,
          activeL3PrimeExponent]
        change ((({delta} : Int) : Real) / 4 +
            ((activeL3PrimeExponentEntry {lean_n} : Nat) : Real) *
              activeL3PrimeLogUpperEntry {lean_n}) / {ell_name} <
          (2 : Real)
        rw [show activeL3PrimeExponentEntry {lean_n} = {exponent} by rfl,
          show activeL3PrimeLogUpperEntry {lean_n} =
            _root_.Q3.Proofs.PrimeCert.u_{base} by rfl]
        norm_num [{ell_name}, {ell_rat_name},
          _root_.Q3.Proofs.PrimeCert.u_{base}])
"""
    return f"""
private theorem {theorem_name}
    (n : PrimeShiftIndexL3) (hv : n.1 = {lean_n}) :
    n ∈ {live_set_name} {delta_expr} := by
  cases n with
  | mk val hval =>
    simp at hv
    subst val
    exact {prefix}_mem_live_of_minus_shift_tight_bounds {delta_expr}
      (Fin.mk {lean_n} hval)
      (by
        rw [activeL3PrimeShiftUpper, activeL3PrimeLogUpper,
          activeL3PrimeExponent]
        change (-2 : Real) <
          ((({delta} : Int) : Real) / 4 -
            ((activeL3PrimeExponentEntry {lean_n} : Nat) : Real) *
              activeL3PrimeLogUpperEntry {lean_n}) / {ell_name}
        rw [show activeL3PrimeExponentEntry {lean_n} = {exponent} by rfl,
          show activeL3PrimeLogUpperEntry {lean_n} =
            _root_.Q3.Proofs.PrimeCert.u_{base} by rfl]
        norm_num [{ell_name}, {ell_rat_name},
          _root_.Q3.Proofs.PrimeCert.u_{base}])
      (by
        rw [activeL3PrimeShiftLower, activeL3PrimeLogLower,
          activeL3PrimeExponent]
        change ((({delta} : Int) : Real) / 4 -
            ((activeL3PrimeExponentEntry {lean_n} : Nat) : Real) *
              activeL3PrimeLogLowerEntry {lean_n}) / {ell_name} <
          (2 : Real)
        rw [show activeL3PrimeExponentEntry {lean_n} = {exponent} by rfl,
          show activeL3PrimeLogLowerEntry {lean_n} =
            _root_.Q3.Proofs.PrimeCert.l_{base} by rfl]
        norm_num [{ell_name}, {ell_rat_name},
          _root_.Q3.Proofs.PrimeCert.l_{base}])
"""


def emit_declared_subset_generated(
    *,
    prop_name: str,
    theorem_name: str,
    declared_set_name: str,
    prefix: str,
    ell_name: str,
    ell_rat_name: str,
    live_set_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
) -> str:
    helpers: list[str] = []
    for delta in range(-22, 23):
        for lean_n in nonzero_terms(by_delta[delta]):
            helpers.append(
                emit_support_pair_helper(
                    prefix=prefix,
                    ell_name=ell_name,
                    ell_rat_name=ell_rat_name,
                    live_set_name=live_set_name,
                    delta=delta,
                    lean_n=lean_n,
                )
            )

    lines: list[str] = []
    lines.extend(helpers)
    lines.extend(
        [
            f"theorem {theorem_name} :",
            f"    {prop_name} := by",
            "  intro δInt n hn",
        ]
    )
    neq_names: list[str] = []
    for delta in range(-22, 23):
        hname = f"hδ_{lean_delta_suffix(delta)}"
        neq_names.append(hname)
        lines.append(f"  by_cases {hname} : δInt = {delta}")
        lines.append("  · subst δInt")
        terms = nonzero_terms(by_delta[delta])
        if not terms:
            lines.extend(
                [
                    f"    have hnone : n.1 ∈ (∅ : Finset Nat) := by",
                    f"      simpa [{declared_set_name}] using hn",
                    "    simpa using hnone",
                ]
            )
            continue
        eqs = [f"n.1 = {lean_n}" for lean_n in terms]
        lines.extend(
            [
                f"    have hmem : {disjunction(eqs)} := by",
                f"      simpa [{declared_set_name}] using hn",
            ]
        )
        if len(terms) == 1:
            helper_name = (
                f"{prefix}_mem_live_delta_{lean_delta_suffix(delta)}_"
                f"shift{terms[0]}_of_val_eq"
            )
            lines.append(f"    exact {helper_name} n hmem")
            continue
        lines.append(f"    rcases hmem with {' | '.join(['hv'] * len(terms))}")
        for lean_n in terms:
            helper_name = (
                f"{prefix}_mem_live_delta_{lean_delta_suffix(delta)}_"
                f"shift{lean_n}_of_val_eq"
            )
            lines.append(f"    · exact {helper_name} n hv")
    simp_args = ", ".join([declared_set_name] + neq_names)
    lines.extend(
        [
            "  · have hnone : n.1 ∈ (∅ : Finset Nat) := by",
            f"      simpa [{simp_args}] using hn",
            "    simpa using hnone",
        ]
    )
    return "\n".join(lines)


def lean_int_expr(delta: int) -> str:
    return f"({delta} : Int)"


def emit_rpair_split_budget_delta_theorem(prefix: str, delta: int) -> str:
    suffix = lean_delta_suffix(delta)
    return f"""
private theorem {prefix}RationalDeltaLiveRPairSplitBudgetRat_delta_{suffix}
    (n : PrimeShiftIndexL3) :
    {prefix}RationalDeltaLiveRMinusRadByDeltaRat {lean_int_expr(delta)} n.1 +
        {prefix}RationalDeltaLiveRPlusRadByDeltaRat {lean_int_expr(delta)} n.1 +
        |{prefix}RationalDeltaLiveRMinusMidByDeltaRat {lean_int_expr(delta)} n.1 +
          {prefix}RationalDeltaLiveRPlusMidByDeltaRat {lean_int_expr(delta)} n.1 -
          {prefix}RationalDeltaLiveRPairMidByDeltaRat {lean_int_expr(delta)} n.1| ≤
      {prefix}RationalDeltaLiveRPairRadByDeltaRat {lean_int_expr(delta)} n.1 := by
  fin_cases n <;> native_decide
"""


def emit_rpair_split_budget_generated_split(prefix: str) -> str:
    lines: list[str] = []
    for delta in range(-22, 23):
        lines.append(emit_rpair_split_budget_delta_theorem(prefix, delta))
    lines.extend(
        [
            f"/-- Generated {prefix} split-`R` pair-sum budget, split by center delta.",
            "The audit serializes dead sides as exact zero and live sides as rational",
            "Arb witnesses, then Lean checks the exact rational budget here. -/",
            f"theorem {prefix}RationalDeltaLiveRPairSplitBudgetRatByDelta_generated_split :",
            f"    {prefix}RationalDeltaLiveRPairSplitBudgetRatByDelta := by",
            "  intro δInt n hδ",
            "  have hlow : (-22 : Int) ≤ δInt := hδ.1",
            "  have hhigh : δInt ≤ (22 : Int) := hδ.2",
            "  interval_cases δInt",
        ]
    )
    for delta in range(-22, 23):
        lines.append(
            f"  · exact {prefix}RationalDeltaLiveRPairSplitBudgetRat_delta_"
            f"{lean_delta_suffix(delta)} n"
        )
    return "\n".join(lines)


def emit_product_budget_delta_theorem(prefix: str, delta: int) -> str:
    suffix = lean_delta_suffix(delta)
    return f"""
private theorem {prefix}RationalDeltaLiveTermProductBudgetRat_delta_{suffix}
    (n : PrimeShiftIndexL3) :
    (|activeL3RationalPrimeWeightMidRat n| +
        activeL3RationalPrimeWeightRadRat n) *
        {prefix}RationalDeltaLiveRPairRadByDeltaRat {lean_int_expr(delta)} n.1 +
      activeL3RationalPrimeWeightRadRat n *
        |{prefix}RationalDeltaLiveRPairMidByDeltaRat {lean_int_expr(delta)} n.1| +
      |activeL3RationalPrimeWeightMidRat n *
          {prefix}RationalDeltaLiveRPairMidByDeltaRat {lean_int_expr(delta)} n.1 -
        {prefix}RationalDeltaLiveTermMidByDeltaRat {lean_int_expr(delta)} n.1| ≤
      {prefix}RationalDeltaLiveTermRadByDeltaRat {lean_int_expr(delta)} n.1 := by
  fin_cases n <;> native_decide
"""


def emit_product_budget_generated_split(prefix: str) -> str:
    lines: list[str] = []
    for delta in range(-22, 23):
        lines.append(emit_product_budget_delta_theorem(prefix, delta))
    lines.extend(
        [
            f"/-- Generated {prefix} product-budget check, split by center delta.",
            "This keeps each exact-rational decision proof small enough for Lean. -/",
            f"theorem {prefix}RationalDeltaLiveTermProductBudgetRatByDelta_generated_split :",
            f"    {prefix}RationalDeltaLiveTermProductBudgetRatByDelta := by",
            "  intro δInt n hδ",
            "  have hlow : (-22 : Int) ≤ δInt := hδ.1",
            "  have hhigh : δInt ≤ (22 : Int) := hδ.2",
            "  interval_cases δInt",
        ]
    )
    for delta in range(-22, 23):
        lines.append(
            f"  · exact {prefix}RationalDeltaLiveTermProductBudgetRat_delta_"
            f"{lean_delta_suffix(delta)} n"
        )
    return "\n".join(lines)


def split_r_side_is_declared(values: TermWitness | None, side: str) -> bool:
    if values is None:
        return False
    if side == "minus":
        return (not Decimal(values[RMINUS_MID]).is_zero()) or (
            not Decimal(values[RMINUS_RAD]).is_zero()
        )
    if side == "plus":
        return (not Decimal(values[RPLUS_MID]).is_zero()) or (
            not Decimal(values[RPLUS_RAD]).is_zero()
        )
    raise ValueError(side)


def split_r_dead_side(delta: int, lean_n: int, side: str) -> str:
    base_by_lean, exponent_by_lean = lean_prime_shift_maps()
    constants = parse_prime_cert_log_constants()
    ell = Decimal("0.3")
    center = Decimal(delta) / Decimal(4)
    base = base_by_lean[lean_n]
    exponent = exponent_by_lean[lean_n]
    lo = Decimal(exponent) * constants[f"l_{base}"]
    hi = Decimal(exponent) * constants[f"u_{base}"]
    if side == "minus":
        lower = (center - hi) / ell
        upper = (center - lo) / ell
    elif side == "plus":
        lower = (center + lo) / ell
        upper = (center + hi) / ell
    else:
        raise ValueError(side)
    if upper <= Decimal(-2):
        return "left"
    if Decimal(2) <= lower:
        return "right"
    raise SystemExit(
        f"nondeclared split-R side is not certified dead: "
        f"side={side} delta={delta} n={lean_n} lower={lower} upper={upper}"
    )


def split_r_zero_thresholds(
    by_delta: dict[int, dict[int, TermWitness]],
    side: str,
) -> dict[int, dict[str, int | None]]:
    thresholds: dict[int, dict[str, int | None]] = {}
    for lean_n in range(98):
        left_deltas: list[int] = []
        right_deltas: list[int] = []
        declared_deltas: list[int] = []
        for delta in range(-22, 23):
            values = by_delta[delta].get(lean_n)
            if split_r_side_is_declared(values, side):
                declared_deltas.append(delta)
                continue
            dead = split_r_dead_side(delta, lean_n, side)
            if dead == "left":
                left_deltas.append(delta)
            elif dead == "right":
                right_deltas.append(delta)
            else:
                raise ValueError(dead)
        left_max = max(left_deltas) if left_deltas else None
        right_min = min(right_deltas) if right_deltas else None
        if left_max is not None:
            bad = [delta for delta in declared_deltas if delta <= left_max]
            if bad:
                raise SystemExit(
                    f"declared split-R side inside left-dead threshold: "
                    f"side={side} n={lean_n} left_max={left_max} bad={bad[:5]}"
                )
        if right_min is not None:
            bad = [delta for delta in declared_deltas if right_min <= delta]
            if bad:
                raise SystemExit(
                    f"declared split-R side inside right-dead threshold: "
                    f"side={side} n={lean_n} right_min={right_min} bad={bad[:5]}"
                )
        thresholds[lean_n] = {"left_max": left_max, "right_min": right_min}
    return thresholds


def split_r_zero_bound_num_expr(
    *,
    side: str,
    dead: str,
    delta_real_expr: str,
    lean_n: int,
) -> str:
    if side == "minus" and dead == "left":
        shift = "activeL3RationalPrimeShiftLower"
        op = "-"
    elif side == "minus" and dead == "right":
        shift = "activeL3RationalPrimeShiftUpper"
        op = "-"
    elif side == "plus" and dead == "left":
        shift = "activeL3RationalPrimeShiftUpper"
        op = "+"
    elif side == "plus" and dead == "right":
        shift = "activeL3RationalPrimeShiftLower"
        op = "+"
    else:
        raise ValueError((side, dead))
    return (
        f"({delta_real_expr} / 4 {op} "
        f"{shift} activeL3RatWeightIndex{lean_n})"
    )


def split_r_zero_bound_expr(
    *,
    side: str,
    dead: str,
    delta_real_expr: str,
    lean_n: int,
    ell_name: str,
) -> str:
    num = split_r_zero_bound_num_expr(
        side=side,
        dead=dead,
        delta_real_expr=delta_real_expr,
        lean_n=lean_n,
    )
    return f"({num} / {ell_name})"


def emit_split_r_zero_threshold_theorem(
    *,
    prefix: str,
    k: int,
    side: str,
    dead: str,
    threshold: int,
    lean_n: int,
    ell_name: str,
    ell_rat_name: str,
    prime_shift_name: str,
) -> str:
    base_by_lean, exponent_by_lean = lean_prime_shift_maps()
    base = base_by_lean[lean_n]
    exponent = exponent_by_lean[lean_n]
    log_lo = int(
        (Decimal(base).ln() * Decimal(WEIGHT_CERT_SCALE)).to_integral_value(
            rounding=ROUND_FLOOR
        )
    )
    log_hi = log_lo + 1
    side_name = "RMinus" if side == "minus" else "RPlus"
    sign = "-" if side == "minus" else "+"
    suffix = lean_delta_suffix(threshold)
    theorem_suffix = (
        f"of_delta_le_{suffix}" if dead == "left" else f"of_{suffix}_le_delta"
    )
    hypothesis = (
        f"(hδle : δInt ≤ ({threshold} : Int))"
        if dead == "left"
        else f"(hδge : ({threshold} : Int) ≤ δInt)"
    )
    generic_suffix = (
        "upper_le_neg_two" if dead == "left" else "two_le_lower"
    )
    delta_real = "((δInt : Int) : Real)"
    threshold_real = f"(({threshold} : Int) : Real)"
    current_num = split_r_zero_bound_num_expr(
        side=side,
        dead=dead,
        delta_real_expr=delta_real,
        lean_n=lean_n,
    )
    threshold_num = split_r_zero_bound_num_expr(
        side=side,
        dead=dead,
        delta_real_expr=threshold_real,
        lean_n=lean_n,
    )
    current_expr = f"({current_num} / {ell_name})"
    threshold_expr = f"({threshold_num} / {ell_name})"
    comparison_goal = (
        f"{current_expr} ≤ {threshold_expr}"
        if dead == "left"
        else f"{threshold_expr} ≤ {current_expr}"
    )
    hdelta_real = (
        "have hδreal : ((δInt : Int) : Real) ≤ "
        f"(({threshold} : Int) : Real) := by exact_mod_cast hδle"
        if dead == "left"
        else "have hδreal : "
        f"(({threshold} : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge"
    )
    hnum_goal = (
        f"{current_num} ≤ {threshold_num}"
        if dead == "left"
        else f"{threshold_num} ≤ {current_num}"
    )
    hdiv_goal = (
        f"(((δInt : Int) : Real) / 4) ≤ ((({threshold} : Int) : Real) / 4)"
        if dead == "left"
        else f"((({threshold} : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4)"
    )
    hnum_proof = "exact sub_le_sub_right hdiv _" if side == "minus" else ""
    bound_goal = (
        f"{threshold_expr} ≤ (-2 : Real)"
        if dead == "left"
        else f"(2 : Real) ≤ {threshold_expr}"
    )
    if side == "minus" and dead == "left":
        shift = "activeL3RationalPrimeShiftLower"
        log_num = log_lo
        q_num = 5 * threshold + 12
        shift_goal = (
            f"(({q_num} : Real) / 20) ≤ "
            f"{shift} activeL3RatWeightIndex{lean_n}"
        )
        shift_change = (
            f"(({q_num} : Real) / 20) ≤ "
            f"((({exponent} : Nat) : Real) * "
            f"(({log_num} : Real) / ({WEIGHT_CERT_SCALE} : Real)))"
        )
        cross_left = q_num * WEIGHT_CERT_SCALE
        cross_right = 20 * exponent * log_num
    elif side == "minus" and dead == "right":
        shift = "activeL3RationalPrimeShiftUpper"
        log_num = log_hi
        q_num = 5 * threshold - 12
        shift_goal = (
            f"{shift} activeL3RatWeightIndex{lean_n} ≤ "
            f"(({q_num} : Real) / 20)"
        )
        shift_change = (
            f"((({exponent} : Nat) : Real) * "
            f"(({log_num} : Real) / ({WEIGHT_CERT_SCALE} : Real))) ≤ "
            f"(({q_num} : Real) / 20)"
        )
        cross_left = 20 * exponent * log_num
        cross_right = q_num * WEIGHT_CERT_SCALE
    elif side == "plus" and dead == "left":
        shift = "activeL3RationalPrimeShiftUpper"
        log_num = log_hi
        q_num = -12 - 5 * threshold
        shift_goal = (
            f"{shift} activeL3RatWeightIndex{lean_n} ≤ "
            f"(({q_num} : Real) / 20)"
        )
        shift_change = (
            f"((({exponent} : Nat) : Real) * "
            f"(({log_num} : Real) / ({WEIGHT_CERT_SCALE} : Real))) ≤ "
            f"(({q_num} : Real) / 20)"
        )
        cross_left = 20 * exponent * log_num
        cross_right = q_num * WEIGHT_CERT_SCALE
    elif side == "plus" and dead == "right":
        shift = "activeL3RationalPrimeShiftLower"
        log_num = log_lo
        q_num = 12 - 5 * threshold
        shift_goal = (
            f"(({q_num} : Real) / 20) ≤ "
            f"{shift} activeL3RatWeightIndex{lean_n}"
        )
        shift_change = (
            f"(({q_num} : Real) / 20) ≤ "
            f"((({exponent} : Nat) : Real) * "
            f"(({log_num} : Real) / ({WEIGHT_CERT_SCALE} : Real)))"
        )
        cross_left = q_num * WEIGHT_CERT_SCALE
        cross_right = 20 * exponent * log_num
    else:
        raise ValueError((side, dead))
    if side == "plus":
        shift_expr = f"{shift} activeL3RatWeightIndex{lean_n}"
        hnum_proof = (
            "simpa [add_comm, add_left_comm, add_assoc] using "
            f"add_le_add_right hdiv ({shift_expr})"
        )
    threshold_base = f"({threshold_real} / 4)"
    q_expr = f"(({q_num} : Real) / 20)"
    threshold_q_num = f"({threshold_base} {sign} {q_expr})"
    den_expr = "((3 : Real) / 10)"
    threshold_rw_expr = f"({threshold_num} / {den_expr})"
    threshold_q_expr = f"({threshold_q_num} / {den_expr})"
    if dead == "left":
        hbound_num_goal = f"{threshold_num} ≤ {threshold_q_num}"
        hbound_div_goal = f"{threshold_rw_expr} ≤ {threshold_q_expr}"
        hbound_finish = "exact le_trans hdiv_bound (by norm_num)"
    else:
        hbound_num_goal = f"{threshold_q_num} ≤ {threshold_num}"
        hbound_div_goal = f"{threshold_q_expr} ≤ {threshold_rw_expr}"
        hbound_finish = "exact le_trans (by norm_num) hdiv_bound"
    if side == "minus":
        hbound_num_proof = f"exact sub_le_sub_left hshift {threshold_base}"
    else:
        hbound_num_proof = (
            "simpa [add_comm, add_left_comm, add_assoc] using "
            f"add_le_add_left hshift {threshold_base}"
        )
    result = "le_trans hmono hbound" if dead == "left" else "le_trans hbound hmono"
    return f"""
private theorem {prefix}RationalDeltaLive{side_name}_eq_zero_idx{lean_n}_{theorem_suffix}
    {{δInt : Int}}
    {hypothesis} :
    centeredBSplineR {k}
      ((((δInt : Int) : Real) / 4 {sign}
          {prime_shift_name} activeL3RatWeightIndex{lean_n}) / {ell_name}) = 0 := by
  exact {prefix}RationalDeltaLive{side_name}_eq_zero_of_{generic_suffix}
    δInt activeL3RatWeightIndex{lean_n}
    (by
      {hdelta_real}
      have hnum : {hnum_goal} := by
        have hdiv : {hdiv_goal} := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        {hnum_proof}
      have hmono : {comparison_goal} := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt {prefix}_hell)
      have hbound : {bound_goal} := by
        have hshift : {shift_goal} := by
          change {shift_change}
          norm_num
        have hell_eq : {ell_name} = (3 : Real) / 10 := by
          norm_num [{ell_name}, {ell_rat_name}]
        rw [hell_eq]
        have hnum_bound : {hbound_num_goal} := by
          {hbound_num_proof}
        have hdiv_bound : {hbound_div_goal} := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        {hbound_finish}
      exact {result})
"""


def emit_split_r_zero_delta_theorem(
    *,
    prefix: str,
    k: int,
    side: str,
    declared_set_name: str,
    ell_name: str,
    prime_shift_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
    thresholds: dict[int, dict[str, int | None]],
    delta: int,
) -> str:
    side_name = "RMinus" if side == "minus" else "RPlus"
    sign = "-" if side == "minus" else "+"
    suffix = lean_delta_suffix(delta)
    lines = [
        f"private theorem {prefix}RationalDeltaLive{side_name}ZeroOffDeclared_delta_{suffix}",
        "    (n : PrimeShiftIndexL3)",
        f"    (hnot : n.1 ∉ {declared_set_name} {lean_int_expr(delta)}) :",
        f"    centeredBSplineR {k}",
        f"        ((((({delta} : Int) : Real) / 4 {sign} {prime_shift_name} n) /",
        f"          {ell_name})) = 0 := by",
        "  fin_cases n",
    ]
    for lean_n in range(98):
        values = by_delta[delta].get(lean_n)
        if split_r_side_is_declared(values, side):
            lines.extend(
                [
                    "  · exfalso",
                    f"    exact hnot (by norm_num [{declared_set_name}])",
                ]
            )
            continue
        dead = split_r_dead_side(delta, lean_n, side)
        if dead == "left":
            threshold = thresholds[lean_n]["left_max"]
            assert threshold is not None
            threshold_suffix = f"of_delta_le_{lean_delta_suffix(threshold)}"
        else:
            threshold = thresholds[lean_n]["right_min"]
            assert threshold is not None
            threshold_suffix = f"of_{lean_delta_suffix(threshold)}_le_delta"
        lines.extend(
            [
                f"  · exact {prefix}RationalDeltaLive{side_name}_eq_zero_idx{lean_n}_{threshold_suffix}",
                "      (by norm_num)",
            ]
        )
    return "\n".join(lines)


def emit_split_r_zero_index_theorem(
    *,
    prefix: str,
    k: int,
    side: str,
    declared_set_name: str,
    ell_name: str,
    prime_shift_name: str,
    thresholds: dict[int, dict[str, int | None]],
    lean_n: int,
) -> str:
    side_name = "RMinus" if side == "minus" else "RPlus"
    sign = "-" if side == "minus" else "+"
    t = thresholds[lean_n]
    lines = [
        f"theorem {prefix}RationalDeltaLive{side_name}ZeroOffDeclared_idx{lean_n}",
        "    (δInt : Int)",
        "    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))",
        f"    (hnot : activeL3RatWeightIndex{lean_n}.1 ∉ {declared_set_name} δInt) :",
        f"    centeredBSplineR {k}",
        f"      ((((δInt : Int) : Real) / 4 {sign}",
        f"          {prime_shift_name} activeL3RatWeightIndex{lean_n}) / {ell_name}) = 0 := by",
    ]
    if t["left_max"] is not None:
        left = t["left_max"]
        lines.extend(
            [
                f"  by_cases hleft : δInt ≤ ({left} : Int)",
                f"  · exact {prefix}RationalDeltaLive{side_name}_eq_zero_idx{lean_n}_of_delta_le_{lean_delta_suffix(left)} hleft",
            ]
        )
    if t["right_min"] is not None:
        right = t["right_min"]
        lines.extend(
            [
                f"  by_cases hright : ({right} : Int) ≤ δInt",
                f"  · exact {prefix}RationalDeltaLive{side_name}_eq_zero_idx{lean_n}_of_{lean_delta_suffix(right)}_le_delta hright",
            ]
        )
    lines.extend(
        [
            "  exfalso",
            "  have hlow : (-22 : Int) ≤ δInt := hδ.1",
            "  have hhigh : δInt ≤ (22 : Int) := hδ.2",
        ]
    )
    if t["left_max"] is not None:
        left = t["left_max"]
        lines.append(f"  have hleftGap : ({left + 1} : Int) ≤ δInt := by omega")
    if t["right_min"] is not None:
        right = t["right_min"]
        lines.append(f"  have hrightGap : δInt ≤ ({right - 1} : Int) := by omega")
    lines.append(
        "  interval_cases δInt <;> exact hnot (by native_decide)"
    )
    return "\n".join(lines)


def emit_split_r_zero_generated(
    *,
    prefix: str,
    k: int,
    side: str,
    declared_set_name: str,
    ell_name: str,
    ell_rat_name: str,
    prime_shift_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
) -> str:
    side_name = "RMinus" if side == "minus" else "RPlus"
    lines: list[str] = []
    thresholds = split_r_zero_thresholds(by_delta, side)
    for lean_n, t in thresholds.items():
        if t["left_max"] is not None:
            lines.append(
                emit_split_r_zero_threshold_theorem(
                    prefix=prefix,
                    k=k,
                    side=side,
                    dead="left",
                    threshold=t["left_max"],
                    lean_n=lean_n,
                    ell_name=ell_name,
                    ell_rat_name=ell_rat_name,
                    prime_shift_name=prime_shift_name,
                )
            )
        if t["right_min"] is not None:
            lines.append(
                emit_split_r_zero_threshold_theorem(
                    prefix=prefix,
                    k=k,
                    side=side,
                    dead="right",
                    threshold=t["right_min"],
                    lean_n=lean_n,
                    ell_name=ell_name,
                    ell_rat_name=ell_rat_name,
                    prime_shift_name=prime_shift_name,
                )
            )
    for lean_n in range(98):
        lines.append(
            emit_split_r_zero_index_theorem(
                prefix=prefix,
                k=k,
                side=side,
                declared_set_name=declared_set_name,
                ell_name=ell_name,
                prime_shift_name=prime_shift_name,
                thresholds=thresholds,
                lean_n=lean_n,
            )
        )
    lines.extend(
        [
            f"/-- Generated {prefix} {side_name} zero-off-declared support fact.",
            "Each branch uses the high-precision rational prime-shift bounds and",
            "the compact support of the normalized centered B-spline profile. -/",
            f"theorem {prefix}RationalDeltaLive{side_name}ZeroOffDeclaredByDelta_generated :",
            f"    {prefix}RationalDeltaLive{side_name}ZeroOffDeclaredByDelta := by",
            "  intro δInt n hδ hnot",
            "  fin_cases n",
        ]
    )
    for lean_n in range(98):
        lines.append(
            f"  · exact {prefix}RationalDeltaLive{side_name}ZeroOffDeclared_idx{lean_n} "
            "δInt hδ hnot"
        )
    return "\n".join(lines)


def emit_split_r_zero_chunk_generated(
    *,
    prefix: str,
    k: int,
    side: str,
    declared_set_name: str,
    ell_name: str,
    ell_rat_name: str,
    prime_shift_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
    start_idx: int,
    end_idx: int,
) -> str:
    lines: list[str] = []
    thresholds = split_r_zero_thresholds(by_delta, side)
    for lean_n in range(start_idx, end_idx + 1):
        t = thresholds[lean_n]
        if t["left_max"] is not None:
            lines.append(
                emit_split_r_zero_threshold_theorem(
                    prefix=prefix,
                    k=k,
                    side=side,
                    dead="left",
                    threshold=t["left_max"],
                    lean_n=lean_n,
                    ell_name=ell_name,
                    ell_rat_name=ell_rat_name,
                    prime_shift_name=prime_shift_name,
                )
            )
        if t["right_min"] is not None:
            lines.append(
                emit_split_r_zero_threshold_theorem(
                    prefix=prefix,
                    k=k,
                    side=side,
                    dead="right",
                    threshold=t["right_min"],
                    lean_n=lean_n,
                    ell_name=ell_name,
                    ell_rat_name=ell_rat_name,
                    prime_shift_name=prime_shift_name,
                )
            )
        lines.append(
            emit_split_r_zero_index_theorem(
                prefix=prefix,
                k=k,
                side=side,
                declared_set_name=declared_set_name,
                ell_name=ell_name,
                prime_shift_name=prime_shift_name,
                thresholds=thresholds,
                lean_n=lean_n,
            )
        )
    return "\n".join(lines)


def emit_split_r_zero_generated_final(
    *,
    prefix: str,
    side: str,
) -> str:
    side_name = "RMinus" if side == "minus" else "RPlus"
    lines = [
        f"/-- Generated {prefix} {side_name} zero-off-declared support fact.",
        "Each index theorem is checked in a small chunk module; this wrapper",
        "only dispatches by the finite active-shift index. -/",
        f"theorem {prefix}RationalDeltaLive{side_name}ZeroOffDeclaredByDelta_generated :",
        f"    {prefix}RationalDeltaLive{side_name}ZeroOffDeclaredByDelta := by",
        "  intro δInt n hδ hnot",
        "  fin_cases n",
    ]
    for lean_n in range(98):
        lines.append(
            f"  · exact {prefix}RationalDeltaLive{side_name}ZeroOffDeclared_idx{lean_n} "
            "δInt hδ hnot"
        )
    return "\n".join(lines)


def emit_split_r_hbox_delta_theorem(
    *,
    prefix: str,
    k: int,
    side: str,
    ell_name: str,
    ell_rat_name: str,
    prime_shift_name: str,
    delta: int,
    lean_n: int,
) -> str:
    side_name = "RMinus" if side == "minus" else "RPlus"
    sign = "-" if side == "minus" else "+"
    lo, hi, base, exponent = split_r_arg_bound_fracs(delta, lean_n, side)
    lo_name = f"{prefix}RationalDeltaLive{side_name}Lo_delta_{lean_delta_suffix(delta)}_shift{lean_n}"
    hi_name = f"{prefix}RationalDeltaLive{side_name}Hi_delta_{lean_delta_suffix(delta)}_shift{lean_n}"
    theorem_name = f"{prefix}RationalDeltaLive{side_name}Hbox_delta_{lean_delta_suffix(delta)}_shift{lean_n}"
    if side == "minus":
        lower_log = f"activeL3RatLogHi_p{base}"
        upper_log = f"activeL3RatLogLo_p{base}"
        lower_shift_name = "activeL3RationalPrimeShiftUpper"
        upper_shift_name = "activeL3RationalPrimeShiftLower"
    else:
        lower_log = f"activeL3RatLogLo_p{base}"
        upper_log = f"activeL3RatLogHi_p{base}"
        lower_shift_name = "activeL3RationalPrimeShiftLower"
        upper_shift_name = "activeL3RationalPrimeShiftUpper"
    lower_expr = (
        f"((((({delta} : Int) : Real) / 4 {sign} "
        f"(({exponent} : Nat) : Real) * {lower_log}) / {ell_name}))"
    )
    upper_expr = (
        f"((((({delta} : Int) : Real) / 4 {sign} "
        f"(({exponent} : Nat) : Real) * {upper_log}) / {ell_name}))"
    )
    return f"""
private theorem {theorem_name} :
    |centeredBSplineR {k}
        ((((({delta} : Int) : Real) / 4 {sign}
          {prime_shift_name} activeL3RatWeightIndex{lean_n}) / {ell_name})) -
      {prefix}RationalDeltaLive{side_name}MidByDelta ({delta} : Int) {lean_n}| <=
        {prefix}RationalDeltaLive{side_name}RadByDelta ({delta} : Int) {lean_n} := by
  let {lo_name} : Rat := {rat_lit_fraction(lo)}
  let {hi_name} : Rat := {rat_lit_fraction(hi)}
  have hb :=
    {prefix}RationalDeltaLive{side_name}_arg_bounds
      ({delta} : Int) activeL3RatWeightIndex{lean_n}
  have hlo_eq :
          (({lo_name} : Rat) : Real) =
            (((({delta} : Int) : Real) / 4 {sign}
              {lower_shift_name}
                activeL3RatWeightIndex{lean_n}) / {ell_name}) := by
    change (({lo_name} : Rat) : Real) = {lower_expr}
    norm_num [{lo_name}, {lower_log}, {ell_name}, {ell_rat_name}]
  have hhi_eq :
          (({hi_name} : Rat) : Real) =
            (((({delta} : Int) : Real) / 4 {sign}
              {upper_shift_name}
                activeL3RatWeightIndex{lean_n}) / {ell_name}) := by
    change (({hi_name} : Rat) : Real) = {upper_expr}
    norm_num [{hi_name}, {upper_log}, {ell_name}, {ell_rat_name}]
  have hdom :
      rationalDeltaLiveRatRRad {k} {lo_name} {hi_name} +
          |rationalDeltaLiveRatRMid {k} {lo_name} {hi_name} -
            {prefix}RationalDeltaLive{side_name}MidByDeltaRat ({delta} : Int) {lean_n}| <=
        {prefix}RationalDeltaLive{side_name}RadByDeltaRat ({delta} : Int) {lean_n} := by
    native_decide
  simpa [{prefix}RationalDeltaLive{side_name}MidByDelta,
    {prefix}RationalDeltaLive{side_name}RadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := {k})
      (x := (((({delta} : Int) : Real) / 4 {sign}
        {prime_shift_name} activeL3RatWeightIndex{lean_n}) / {ell_name}))
      (lo := {lo_name})
      (hi := {hi_name})
      (mid := {prefix}RationalDeltaLive{side_name}MidByDeltaRat ({delta} : Int) {lean_n})
      (rad := {prefix}RationalDeltaLive{side_name}RadByDeltaRat ({delta} : Int) {lean_n})
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom
"""


def emit_split_r_hbox_index_theorem(
    *,
    prefix: str,
    k: int,
    side: str,
    declared_set_name: str,
    ell_name: str,
    prime_shift_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
    lean_n: int,
) -> str:
    side_name = "RMinus" if side == "minus" else "RPlus"
    sign = "-" if side == "minus" else "+"
    declared_deltas = [
        delta
        for delta in range(-22, 23)
        if split_r_side_is_declared(by_delta[delta].get(lean_n), side)
    ]
    lines = [
        f"theorem {prefix}RationalDeltaLive{side_name}HboxDeclared_idx{lean_n}",
        "    (δInt : Int)",
        "    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))",
        f"    (hmem : activeL3RatWeightIndex{lean_n}.1 ∈ {declared_set_name} δInt) :",
        f"    |centeredBSplineR {k}",
        f"      ((((δInt : Int) : Real) / 4 {sign}",
        f"          {prime_shift_name} activeL3RatWeightIndex{lean_n}) / {ell_name}) -",
        f"      {prefix}RationalDeltaLive{side_name}MidByDelta δInt {lean_n}| <=",
        f"        {prefix}RationalDeltaLive{side_name}RadByDelta δInt {lean_n} := by",
        "  have hlow : (-22 : Int) ≤ δInt := hδ.1",
        "  have hhigh : δInt ≤ (22 : Int) := hδ.2",
        "  interval_cases δInt",
    ]
    for delta in range(-22, 23):
        if delta in declared_deltas:
            lines.append(
                f"  · exact {prefix}RationalDeltaLive{side_name}Hbox_delta_{lean_delta_suffix(delta)}_shift{lean_n}"
            )
        else:
            lines.extend(
                [
                    "  · exact False.elim ((by native_decide :",
                    f"        ¬ activeL3RatWeightIndex{lean_n}.1 ∈ {declared_set_name}",
                    f"          ({delta} : Int)) (by simpa using hmem))",
                ]
            )
    return "\n".join(lines)


def emit_split_r_hbox_chunk_generated(
    *,
    prefix: str,
    k: int,
    side: str,
    declared_set_name: str,
    ell_name: str,
    ell_rat_name: str,
    prime_shift_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
    start_idx: int,
    end_idx: int,
) -> str:
    lines: list[str] = []
    for lean_n in range(start_idx, end_idx + 1):
        for delta in range(-22, 23):
            if split_r_side_is_declared(by_delta[delta].get(lean_n), side):
                lines.append(
                    emit_split_r_hbox_delta_theorem(
                        prefix=prefix,
                        k=k,
                        side=side,
                        ell_name=ell_name,
                        ell_rat_name=ell_rat_name,
                        prime_shift_name=prime_shift_name,
                        delta=delta,
                        lean_n=lean_n,
                    )
                )
        lines.append(
            emit_split_r_hbox_index_theorem(
                prefix=prefix,
                k=k,
                side=side,
                declared_set_name=declared_set_name,
                ell_name=ell_name,
                prime_shift_name=prime_shift_name,
                by_delta=by_delta,
                lean_n=lean_n,
            )
        )
    return "\n".join(lines)


def emit_split_r_hbox_generated_final(
    *,
    prefix: str,
    side: str,
) -> str:
    side_name = "RMinus" if side == "minus" else "RPlus"
    lines = [
        f"/-- Generated {prefix} {side_name} declared-support hbox fact.",
        "Each active-shift index theorem is checked in a small chunk module; this",
        "wrapper dispatches by the finite active-shift index. -/",
        f"theorem {prefix}RationalDeltaLive{side_name}HboxOnDeclaredByDelta_generated :",
        f"    {prefix}RationalDeltaLive{side_name}HboxOnDeclaredByDelta := by",
        "  intro δInt n hδ hmem",
        "  fin_cases n",
    ]
    for lean_n in range(98):
        lines.append(
            f"  · exact {prefix}RationalDeltaLive{side_name}HboxDeclared_idx{lean_n} "
            "δInt hδ hmem"
        )
    return "\n".join(lines)


WEIGHT_CERT_DIGITS = 96
WEIGHT_CERT_SCALE = 10**WEIGHT_CERT_DIGITS
WEIGHT_CERT_SPLIT = 10
WEIGHT_CERT_TAYLOR_TERMS = 80
WEIGHT_CERT_EXP_DIGITS = 120
WEIGHT_CERT_EXP_SCALE = 10**WEIGHT_CERT_EXP_DIGITS


def real_div_lit(numerator: int, denominator: int) -> str:
    return f"({numerator} : Real) / {denominator}"


def emit_active_log_cert_for_base(base: int) -> str:
    log_value = Decimal(base).ln()
    lo = int(
        (log_value * Decimal(WEIGHT_CERT_SCALE)).to_integral_value(
            rounding=ROUND_FLOOR
        )
    )
    hi = lo + 1
    exp_div_upper = int(
        (
            (Decimal(lo) / Decimal(WEIGHT_CERT_SCALE) / Decimal(WEIGHT_CERT_SPLIT))
            .exp()
            * Decimal(WEIGHT_CERT_EXP_SCALE)
        ).to_integral_value(rounding=ROUND_CEILING)
    )
    return f"""
def activeL3RatLogLo_p{base} : Real := {real_div_lit(lo, WEIGHT_CERT_SCALE)}
def activeL3RatLogHi_p{base} : Real := {real_div_lit(hi, WEIGHT_CERT_SCALE)}
private def activeL3RatLogDivExpUpper_p{base} : Real :=
  {real_div_lit(exp_div_upper, WEIGHT_CERT_EXP_SCALE)}
private def activeL3RatLogMid_p{base} : Real :=
  (activeL3RatLogLo_p{base} + activeL3RatLogHi_p{base}) / 2
private def activeL3RatLogRad_p{base} : Real :=
  (activeL3RatLogHi_p{base} - activeL3RatLogLo_p{base}) / 2

private theorem activeL3RatExpLogLoDiv_le_p{base} :
    Real.exp (activeL3RatLogLo_p{base} / {WEIGHT_CERT_SPLIT}) ≤
      activeL3RatLogDivExpUpper_p{base} := by
  have hx0 : 0 ≤ activeL3RatLogLo_p{base} / {WEIGHT_CERT_SPLIT} := by
    norm_num [activeL3RatLogLo_p{base}]
  have hx1 : activeL3RatLogLo_p{base} / {WEIGHT_CERT_SPLIT} ≤ 1 := by
    norm_num [activeL3RatLogLo_p{base}]
  have htaylor :
      (∑ m ∈ Finset.range {WEIGHT_CERT_TAYLOR_TERMS},
          (activeL3RatLogLo_p{base} / {WEIGHT_CERT_SPLIT}) ^ m /
            (Nat.factorial m)) +
          (activeL3RatLogLo_p{base} / {WEIGHT_CERT_SPLIT}) ^
              {WEIGHT_CERT_TAYLOR_TERMS} *
            ({WEIGHT_CERT_TAYLOR_TERMS} + 1) /
            (Nat.factorial {WEIGHT_CERT_TAYLOR_TERMS} *
              {WEIGHT_CERT_TAYLOR_TERMS}) ≤
        activeL3RatLogDivExpUpper_p{base} := by
    norm_num [activeL3RatLogLo_p{base}, activeL3RatLogDivExpUpper_p{base}]
  exact Q3.Proofs.PrimeCert.exp_le_of_taylor_bound
    (x := activeL3RatLogLo_p{base} / {WEIGHT_CERT_SPLIT})
    (b := activeL3RatLogDivExpUpper_p{base})
    hx0 hx1 (n := {WEIGHT_CERT_TAYLOR_TERMS}) (by decide) htaylor

private theorem activeL3RatExpLogLo_le_p{base} :
    Real.exp activeL3RatLogLo_p{base} ≤ ({base} : Real) := by
  have h := Q3.Proofs.PrimeCert.exp_le_pow_of_div_le
    (x := activeL3RatLogLo_p{base})
    (b := activeL3RatLogDivExpUpper_p{base})
    (n := {WEIGHT_CERT_SPLIT}) (by decide)
    activeL3RatExpLogLoDiv_le_p{base}
  have hpow : activeL3RatLogDivExpUpper_p{base} ^
      {WEIGHT_CERT_SPLIT} ≤ ({base} : Real) := by
    norm_num [activeL3RatLogDivExpUpper_p{base}]
  exact h.trans hpow

private theorem activeL3RatBase_le_expLogHi_p{base} :
    ({base} : Real) ≤ Real.exp activeL3RatLogHi_p{base} := by
  let s : Real :=
    ∑ m ∈ Finset.range {WEIGHT_CERT_TAYLOR_TERMS},
      (activeL3RatLogHi_p{base} / {WEIGHT_CERT_SPLIT}) ^ m /
        (Nat.factorial m)
  have hx0 : 0 ≤ activeL3RatLogHi_p{base} / {WEIGHT_CERT_SPLIT} := by
    norm_num [activeL3RatLogHi_p{base}]
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg (by
      intro m hm
      have hpow :
          0 ≤ (activeL3RatLogHi_p{base} / {WEIGHT_CERT_SPLIT}) ^ m :=
        pow_nonneg hx0 m
      have hfac : 0 ≤ ((Nat.factorial m : Nat) : Real) := by
        exact_mod_cast Nat.zero_le (Nat.factorial m)
      exact div_nonneg hpow hfac)
  have hsum_le : s ≤ Real.exp
      (activeL3RatLogHi_p{base} / {WEIGHT_CERT_SPLIT}) := by
    dsimp [s]
    exact Real.sum_le_exp_of_nonneg hx0 {WEIGHT_CERT_TAYLOR_TERMS}
  have hpow_le : s ^ {WEIGHT_CERT_SPLIT} ≤
      Real.exp activeL3RatLogHi_p{base} := by
    exact Q3.Proofs.PrimeCert.pow_le_exp_of_le_div
      (x := activeL3RatLogHi_p{base}) (a := s)
      (n := {WEIGHT_CERT_SPLIT}) (by decide) hs_nonneg hsum_le
  have hp_le : ({base} : Real) ≤ s ^ {WEIGHT_CERT_SPLIT} := by
    dsimp [s]
    norm_num [activeL3RatLogHi_p{base}]
  exact hp_le.trans hpow_le

private theorem activeL3RatLogBounds_p{base} :
    activeL3RatLogLo_p{base} ≤ Real.log ({base} : Real) ∧
      Real.log ({base} : Real) ≤ activeL3RatLogHi_p{base} := by
  exact Q3.Proofs.PrimeCert.log_nat_bounds_of_exp_bounds
    (n := {base}) (by decide)
    activeL3RatExpLogLo_le_p{base}
    activeL3RatBase_le_expLogHi_p{base}

private theorem activeL3RatLogHbox_p{base} :
    |Real.log ({base} : Real) - activeL3RatLogMid_p{base}| ≤
      activeL3RatLogRad_p{base} := by
  exact Q3.Proofs.PrimeCert.abs_sub_mid_le_half_width
    activeL3RatLogBounds_p{base}.1
    activeL3RatLogBounds_p{base}.2
"""


def emit_active_inv_sqrt_cert_for_base(base: int) -> str:
    inv_sqrt = Decimal(1) / Decimal(base).sqrt()
    lo = int(
        (inv_sqrt * Decimal(WEIGHT_CERT_SCALE)).to_integral_value(
            rounding=ROUND_FLOOR
        )
    )
    hi = lo + 1
    return f"""
private def activeL3RatInvSqrtLo_p{base} : Real :=
  {real_div_lit(lo, WEIGHT_CERT_SCALE)}
private def activeL3RatInvSqrtHi_p{base} : Real :=
  {real_div_lit(hi, WEIGHT_CERT_SCALE)}
private def activeL3RatInvSqrtMid_p{base} : Real :=
  (activeL3RatInvSqrtLo_p{base} + activeL3RatInvSqrtHi_p{base}) / 2
private def activeL3RatInvSqrtRad_p{base} : Real :=
  (activeL3RatInvSqrtHi_p{base} - activeL3RatInvSqrtLo_p{base}) / 2

private theorem activeL3RatInvSqrtBounds_p{base} :
    activeL3RatInvSqrtLo_p{base} ≤ (Real.sqrt ({base} : Real))⁻¹ ∧
      (Real.sqrt ({base} : Real))⁻¹ ≤ activeL3RatInvSqrtHi_p{base} := by
  constructor
  · have hs_pos : 0 < Real.sqrt ({base} : Real) := Real.sqrt_pos.mpr (by norm_num)
    have hs_nonneg : 0 ≤ Real.sqrt ({base} : Real) := le_of_lt hs_pos
    have hsq : activeL3RatInvSqrtLo_p{base} *
        Real.sqrt ({base} : Real) ≤ 1 := by
      have hsq' : (activeL3RatInvSqrtLo_p{base} *
          Real.sqrt ({base} : Real)) ^ 2 ≤ (1 : Real) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ {base})]
        norm_num [activeL3RatInvSqrtLo_p{base}]
      have hnonneg : 0 ≤ activeL3RatInvSqrtLo_p{base} *
          Real.sqrt ({base} : Real) := by
        exact mul_nonneg (by norm_num [activeL3RatInvSqrtLo_p{base}]) hs_nonneg
      have habs := (sq_le_sq).mp hsq'
      have h1nonneg : 0 ≤ (1 : Real) := by norm_num
      simpa [abs_of_nonneg hnonneg, abs_of_nonneg h1nonneg] using habs
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hs_pos).2 hsq
  · have hs_pos : 0 < Real.sqrt ({base} : Real) := Real.sqrt_pos.mpr (by norm_num)
    have hs_nonneg : 0 ≤ Real.sqrt ({base} : Real) := le_of_lt hs_pos
    have hmul : 1 ≤ activeL3RatInvSqrtHi_p{base} *
        Real.sqrt ({base} : Real) := by
      have hsq' : (1 : Real) ^ 2 ≤
          (activeL3RatInvSqrtHi_p{base} * Real.sqrt ({base} : Real)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ {base})]
        norm_num [activeL3RatInvSqrtHi_p{base}]
      have hnonneg : 0 ≤ activeL3RatInvSqrtHi_p{base} *
          Real.sqrt ({base} : Real) := by
        exact mul_nonneg (by norm_num [activeL3RatInvSqrtHi_p{base}]) hs_nonneg
      have habs := (sq_le_sq).mp hsq'
      have h1nonneg : 0 ≤ (1 : Real) := by norm_num
      simpa [abs_of_nonneg h1nonneg, abs_of_nonneg hnonneg] using habs
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hs_pos).2 hmul

private theorem activeL3RatInvSqrtHbox_p{base} :
    |(Real.sqrt ({base} : Real))⁻¹ - activeL3RatInvSqrtMid_p{base}| ≤
      activeL3RatInvSqrtRad_p{base} := by
  exact Q3.Proofs.PrimeCert.abs_sub_mid_le_half_width
    activeL3RatInvSqrtBounds_p{base}.1
    activeL3RatInvSqrtBounds_p{base}.2
"""


def emit_active_exp_factor_defs_and_hbox(n: int, base: int, exponent: int) -> str:
    idx = f"activeL3RatWeightIndex{n}"
    if exponent % 2 == 0:
        half_exp = exponent // 2
        return f"""
private def activeL3RatExpMid_idx{n} : Real :=
  ((({base} : Real) ^ ({half_exp} : Nat)))⁻¹
private def activeL3RatExpRad_idx{n} : Real := 0

private theorem activeL3RatExpFactor_eq_idx{n} :
    Real.exp (-(activeL3PrimeShift {idx}) / 2) =
      activeL3RatExpMid_idx{n} := by
  have hshift :
      activeL3PrimeShift {idx} =
        (({exponent} : Nat) : Real) * Real.log ({base} : Real) := by
    change ((({exponent} : Nat) : Real) *
      Real.log ((({base} : Nat) : Real))) =
        (({exponent} : Nat) : Real) * Real.log ({base} : Real)
    norm_num
  rw [hshift]
  have harg :
      (-((({exponent} : Nat) : Real) * Real.log ({base} : Real))) / 2 =
        -(Real.log (({base} : Real) ^ ({half_exp} : Nat))) := by
    rw [Real.log_pow]
    ring
  rw [harg, Real.exp_neg, Real.exp_log]
  · rfl
  · positivity

private theorem activeL3RatExpFactorHbox_idx{n} :
    |Real.exp (-(activeL3PrimeShift {idx}) / 2) -
        activeL3RatExpMid_idx{n}| ≤ activeL3RatExpRad_idx{n} := by
  rw [activeL3RatExpFactor_eq_idx{n}]
  norm_num [activeL3RatExpMid_idx{n}, activeL3RatExpRad_idx{n}]
"""
    half_exp = (exponent - 1) // 2
    return f"""
private def activeL3RatExpMid_idx{n} : Real :=
  ((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ *
    activeL3RatInvSqrtMid_p{base}
private def activeL3RatExpRad_idx{n} : Real :=
  ((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ *
    activeL3RatInvSqrtRad_p{base}

private theorem activeL3RatExpFactor_eq_scaledInvSqrt_idx{n} :
    Real.exp (-(activeL3PrimeShift {idx}) / 2) =
      ((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ *
        (Real.sqrt ({base} : Real))⁻¹ := by
  have hshift :
      activeL3PrimeShift {idx} =
        (({exponent} : Nat) : Real) * Real.log ({base} : Real) := by
    change ((({exponent} : Nat) : Real) *
      Real.log ((({base} : Nat) : Real))) =
        (({exponent} : Nat) : Real) * Real.log ({base} : Real)
    norm_num
  rw [hshift]
  have hsplit :
      (-((({exponent} : Nat) : Real) * Real.log ({base} : Real))) / 2 =
        -(Real.log (({base} : Real) ^ ({half_exp} : Nat))) +
          -(Real.log (Real.sqrt ({base} : Real))) := by
    rw [Real.log_pow]
    rw [Real.log_sqrt (by norm_num : (0 : Real) ≤ {base})]
    ring
  rw [hsplit, Real.exp_add]
  rw [Real.exp_neg, Real.exp_neg]
  rw [Real.exp_log, Real.exp_log]
  · positivity
  · positivity

private theorem activeL3RatExpFactorHbox_idx{n} :
    |Real.exp (-(activeL3PrimeShift {idx}) / 2) -
        activeL3RatExpMid_idx{n}| ≤ activeL3RatExpRad_idx{n} := by
  have hscale_nonneg :
      0 ≤ ((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ := by
    positivity
  have hscaled :
      |((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ *
          (Real.sqrt ({base} : Real))⁻¹ -
        activeL3RatExpMid_idx{n}| ≤ activeL3RatExpRad_idx{n} := by
    calc
      |((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ *
          (Real.sqrt ({base} : Real))⁻¹ -
        activeL3RatExpMid_idx{n}| =
          |((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ *
            ((Real.sqrt ({base} : Real))⁻¹ -
              activeL3RatInvSqrtMid_p{base})| := by
            congr 1
            dsimp [activeL3RatExpMid_idx{n}]
            ring
      _ = |((({base} : Real) ^ ({half_exp} : Nat)))⁻¹| *
          |(Real.sqrt ({base} : Real))⁻¹ -
            activeL3RatInvSqrtMid_p{base}| := by
            rw [abs_mul]
      _ = ((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ *
          |(Real.sqrt ({base} : Real))⁻¹ -
            activeL3RatInvSqrtMid_p{base}| := by
            rw [abs_of_nonneg hscale_nonneg]
      _ ≤ ((({base} : Real) ^ ({half_exp} : Nat)))⁻¹ *
          activeL3RatInvSqrtRad_p{base} := by
            exact mul_le_mul_of_nonneg_left
              activeL3RatInvSqrtHbox_p{base} hscale_nonneg
      _ = activeL3RatExpRad_idx{n} := by
            rfl
  simpa [activeL3RatExpFactor_eq_scaledInvSqrt_idx{n}] using hscaled
"""


def emit_active_weight_index_theorem(
    n: int,
    base: int,
    exponent: int,
    mid_text: str,
    rad_text: str,
) -> str:
    idx = f"activeL3RatWeightIndex{n}"
    return f"""
def {idx} : PrimeShiftIndexL3 := ⟨{n}, by decide⟩

{emit_active_exp_factor_defs_and_hbox(n, base, exponent)}

private theorem activeL3RationalPrimeWeight_hbox_idx{n} :
    |activeL3PrimeWeight {idx} -
        activeL3RationalPrimeWeightMid {idx}| ≤
      activeL3RationalPrimeWeightRad {idx} := by
  have hlog :
      |Real.log (activeL3PrimeBase {idx} : Real) -
          activeL3RatLogMid_p{base}| ≤ activeL3RatLogRad_p{base} := by
    change |Real.log ({base} : Real) - activeL3RatLogMid_p{base}| ≤
      activeL3RatLogRad_p{base}
    exact activeL3RatLogHbox_p{base}
  have hbudget :
      (|activeL3RatLogMid_p{base}| + activeL3RatLogRad_p{base}) *
          activeL3RatExpRad_idx{n} +
        activeL3RatLogRad_p{base} * |activeL3RatExpMid_idx{n}| +
        |activeL3RatLogMid_p{base} * activeL3RatExpMid_idx{n} -
          activeL3RationalPrimeWeightMid {idx}| ≤
        activeL3RationalPrimeWeightRad {idx} := by
    have hmid : activeL3RationalPrimeWeightMid {idx} = {rat_expr(mid_text)} := by
      rfl
    have hrad : activeL3RationalPrimeWeightRad {idx} = {rat_expr(rad_text)} := by
      rfl
    rw [hmid, hrad]
    norm_num [activeL3RatLogMid_p{base}, activeL3RatLogRad_p{base},
      activeL3RatLogLo_p{base}, activeL3RatLogHi_p{base},
      activeL3RatExpMid_idx{n}, activeL3RatExpRad_idx{n},
      activeL3RatInvSqrtMid_p{base}, activeL3RatInvSqrtRad_p{base},
      activeL3RatInvSqrtLo_p{base}, activeL3RatInvSqrtHi_p{base}]
  have hprod := rational_product_hbox_transfer
    (w := Real.log (activeL3PrimeBase {idx} : Real))
    (wm := activeL3RatLogMid_p{base})
    (wr := activeL3RatLogRad_p{base})
    (r := Real.exp (-(activeL3PrimeShift {idx}) / 2))
    (rm := activeL3RatExpMid_idx{n})
    (rr := activeL3RatExpRad_idx{n})
    (mid := activeL3RationalPrimeWeightMid {idx})
    (rad := activeL3RationalPrimeWeightRad {idx})
    hlog activeL3RatExpFactorHbox_idx{n} hbudget
  change
    |Real.log (activeL3PrimeBase {idx} : Real) *
        Real.exp (-(activeL3PrimeShift {idx}) / 2) -
      activeL3RationalPrimeWeightMid {idx}| ≤
      activeL3RationalPrimeWeightRad {idx}
  exact hprod
"""


def emit_active_weight_hbox_generated(
    weight_payload: dict[int, tuple[str, str]]
) -> str:
    base_by_lean, exponent_by_lean = lean_prime_shift_maps()
    bases = sorted(set(base_by_lean.values()))
    log_blocks = [emit_active_log_cert_for_base(base) for base in bases]
    sqrt_blocks = [emit_active_inv_sqrt_cert_for_base(base) for base in bases]
    index_blocks = [
        emit_active_weight_index_theorem(
            n,
            base_by_lean[n],
            exponent_by_lean[n],
            weight_payload[n][0],
            weight_payload[n][1],
        )
        for n in range(98)
    ]
    branches: list[str] = [
        "/-- Generated shared active L3 prime-weight hbox over the rational",
        "witnesses used by both primary and control option-B payloads. -/",
        "theorem activeL3RationalPrimeWeight_hbox_generated :",
        "    ∀ n,",
        "      |activeL3PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤",
        "        activeL3RationalPrimeWeightRad n := by",
        "  intro n",
        "  fin_cases n",
    ]
    for n in range(98):
        idx = f"activeL3RatWeightIndex{n}"
        branches.extend(
            [
                f"  · change |activeL3PrimeWeight {idx} -",
                f"        activeL3RationalPrimeWeightMid {idx}| ≤",
                f"      activeL3RationalPrimeWeightRad {idx}",
                f"    exact activeL3RationalPrimeWeight_hbox_idx{n}",
            ]
        )
    return "\n".join(log_blocks + sqrt_blocks + index_blocks + ["\n".join(branches)])


def emit_active_shift_bounds_generated() -> str:
    base_by_lean, exponent_by_lean = lean_prime_shift_maps()
    lower_lines = ["def activeL3RationalPrimeShiftLowerRaw : Nat -> Real"]
    upper_lines = ["def activeL3RationalPrimeShiftUpperRaw : Nat -> Real"]
    for n in range(98):
        base = base_by_lean[n]
        exponent = exponent_by_lean[n]
        lower_lines.append(
            f"  | {n} => (({exponent} : Nat) : Real) * activeL3RatLogLo_p{base}"
        )
        upper_lines.append(
            f"  | {n} => (({exponent} : Nat) : Real) * activeL3RatLogHi_p{base}"
        )
    lower_lines.append("  | _ => 0")
    upper_lines.append("  | _ => 0")

    def_lines: list[str] = [
        "",
        "def activeL3RationalPrimeShiftLower (n : PrimeShiftIndexL3) : Real :=",
        "  activeL3RationalPrimeShiftLowerRaw n.1",
        "",
        "def activeL3RationalPrimeShiftUpper (n : PrimeShiftIndexL3) : Real :=",
        "  activeL3RationalPrimeShiftUpperRaw n.1",
    ]

    index_blocks: list[str] = []
    for n in range(98):
        base = base_by_lean[n]
        exponent = exponent_by_lean[n]
        idx = f"activeL3RatWeightIndex{n}"
        index_blocks.append(
            f"""
private theorem activeL3RationalPrimeShift_bounds_idx{n} :
    (({exponent} : Nat) : Real) * activeL3RatLogLo_p{base} ≤
        activeL3PrimeShift {idx} ∧
      activeL3PrimeShift {idx} ≤
        (({exponent} : Nat) : Real) * activeL3RatLogHi_p{base} := by
  have hshift :
      activeL3PrimeShift {idx} =
        (({exponent} : Nat) : Real) * Real.log ({base} : Real) := by
    change ((({exponent} : Nat) : Real) *
      Real.log ((({base} : Nat) : Real))) =
        (({exponent} : Nat) : Real) * Real.log ({base} : Real)
    norm_num
  rw [hshift]
  constructor
  · exact mul_le_mul_of_nonneg_left activeL3RatLogBounds_p{base}.1 (by norm_num)
  · exact mul_le_mul_of_nonneg_left activeL3RatLogBounds_p{base}.2 (by norm_num)
"""
        )

    prop_parts: list[str] = []
    for n in range(98):
        base = base_by_lean[n]
        exponent = exponent_by_lean[n]
        idx = f"activeL3RatWeightIndex{n}"
        prop_parts.append(
            f"    ((({exponent} : Nat) : Real) * activeL3RatLogLo_p{base} ≤\n"
            f"        activeL3PrimeShift {idx} ∧\n"
            f"      activeL3PrimeShift {idx} ≤\n"
            f"        (({exponent} : Nat) : Real) * activeL3RatLogHi_p{base})"
        )
    packed_prop = " ∧\n".join(prop_parts)

    branches: list[str] = [
        "def activeL3RationalPrimeShiftBoundsGenerated : Prop :=",
        packed_prop,
        "",
        "/-- Generated high-precision active L3 prime-shift bounds.",
        "These reuse the 90-decimal log certificates from the rational weight",
        "payload and are the intended shift interval layer for the split `R`",
        "B-spline hboxes. -/",
        "theorem activeL3RationalPrimeShift_bounds_generated :",
        "    activeL3RationalPrimeShiftBoundsGenerated := by",
        "  exact ⟨",
    ]
    for n in range(98):
        comma = "," if n < 97 else ""
        branches.append(f"    activeL3RationalPrimeShift_bounds_idx{n}{comma}")
    branches.append("  ⟩")

    branches.extend(
        [
            "",
            "/-- Usable generated high-precision active L3 prime-shift bounds.",
            "This is the theorem form consumed by the split `R` interval",
            "argument receivers. -/",
            "theorem activeL3RationalPrimeShift_bounds (n : PrimeShiftIndexL3) :",
            "    activeL3RationalPrimeShiftLower n ≤ activeL3PrimeShift n ∧",
            "      activeL3PrimeShift n ≤ activeL3RationalPrimeShiftUpper n := by",
            "  fin_cases n",
        ]
    )
    for n in range(98):
        base = base_by_lean[n]
        exponent = exponent_by_lean[n]
        idx = f"activeL3RatWeightIndex{n}"
        branches.extend(
            [
                f"  · change (({exponent} : Nat) : Real) * activeL3RatLogLo_p{base} ≤",
                f"        activeL3PrimeShift {idx} ∧",
                f"      activeL3PrimeShift {idx} ≤",
                f"        (({exponent} : Nat) : Real) * activeL3RatLogHi_p{base}",
                f"    exact activeL3RationalPrimeShift_bounds_idx{n}",
            ]
        )
    return "\n".join(lower_lines + [""] + upper_lines + def_lines + index_blocks + branches)


def emit_rat_centered_bspline_hbox_helpers() -> str:
    return r"""
private theorem rationalDeltaLive_abs_sub_mid_le_half_width {lo y hi : Real}
    (hlo : lo <= y) (hhi : y <= hi) :
    |y - ((lo + hi) / 2)| <= (hi - lo) / 2 := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

private theorem rationalDeltaLive_positivePartPower_succ_mono (d : Nat) :
    Monotone (positivePartPower (d + 1)) := by
  intro x y hxy
  rw [positivePartPower_succ_eq_max d x, positivePartPower_succ_eq_max d y]
  exact pow_le_pow_left₀ (le_max_right x 0) (max_le_max hxy le_rfl) (d + 1)

private theorem rationalDeltaLive_positivePartPower_mono_autocorr (k : Nat) :
    Monotone (positivePartPower (bsplineAutocorrDegree k)) := by
  have h := rationalDeltaLive_positivePartPower_succ_mono (2 * k)
  simpa [bsplineAutocorrDegree, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

private theorem rationalDeltaLive_positivePartPower_hbox_of_bounds
    {d : Nat} {x lo hi : Real}
    (hmono : Monotone (positivePartPower d))
    (hlo : lo <= x) (hhi : x <= hi) :
    |positivePartPower d x -
      ((positivePartPower d lo + positivePartPower d hi) / 2)| <=
        (positivePartPower d hi - positivePartPower d lo) / 2 :=
  rationalDeltaLive_abs_sub_mid_le_half_width (hmono hlo) (hmono hhi)

private def rationalDeltaLiveRPowerMid (k : Nat) (lo hi : Real) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree k)
      (bsplineScale k * lo +
        (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
        (m : Real)) +
    positivePartPower (bsplineAutocorrDegree k)
      (bsplineScale k * hi +
        (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
        (m : Real))) / 2

private def rationalDeltaLiveRPowerRad (k : Nat) (lo hi : Real) (m : Nat) : Real :=
  (positivePartPower (bsplineAutocorrDegree k)
      (bsplineScale k * hi +
        (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
        (m : Real)) -
    positivePartPower (bsplineAutocorrDegree k)
      (bsplineScale k * lo +
        (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
        (m : Real))) / 2

private def rationalDeltaLiveRTermMid (k : Nat) (lo hi : Real) (m : Nat) : Real :=
  (((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree k + 1) m : Real)) *
      rationalDeltaLiveRPowerMid k lo hi m

private def rationalDeltaLiveRTermRad (k : Nat) (lo hi : Real) (m : Nat) : Real :=
  |((-1 : Real) ^ m) *
    (Nat.choose (bsplineAutocorrDegree k + 1) m : Real)| *
      rationalDeltaLiveRPowerRad k lo hi m

private def rationalDeltaLiveRCardMid (k : Nat) (lo hi : Real) : Real :=
  ((Nat.factorial (bsplineAutocorrDegree k) : Real)⁻¹) *
    ((Finset.range (bsplineAutocorrDegree k + 2)).sum fun m =>
      rationalDeltaLiveRTermMid k lo hi m)

private def rationalDeltaLiveRCardRad (k : Nat) (lo hi : Real) : Real :=
  |((Nat.factorial (bsplineAutocorrDegree k) : Real)⁻¹)| *
    ((Finset.range (bsplineAutocorrDegree k + 2)).sum fun m =>
      rationalDeltaLiveRTermRad k lo hi m)

private def rationalDeltaLiveRMidReal (k : Nat) (lo hi : Real) : Real :=
  rationalDeltaLiveRCardMid k lo hi / bsplineAutocorrNorm k

private def rationalDeltaLiveRRadReal (k : Nat) (lo hi : Real) : Real :=
  rationalDeltaLiveRCardRad k lo hi / bsplineAutocorrNorm k

private theorem rationalDeltaLive_centeredBSplineR_hbox_of_real_arg_bounds
    (k : Nat) {x lo hi mid rad : Real}
    (hlo : lo <= x) (hhi : x <= hi)
    (hdom : rationalDeltaLiveRRadReal k lo hi +
        |rationalDeltaLiveRMidReal k lo hi - mid| <= rad) :
    |centeredBSplineR k x - mid| <= rad := by
  have hscale_lo :
      bsplineScale k * lo <= bsplineScale k * x := by
    exact mul_le_mul_of_nonneg_left hlo (le_of_lt (bsplineScale_pos k))
  have hscale_hi :
      bsplineScale k * x <= bsplineScale k * hi := by
    exact mul_le_mul_of_nonneg_left hhi (le_of_lt (bsplineScale_pos k))
  have hcard :
      |centeredCardinalBSpline (bsplineAutocorrDegree k)
          (bsplineScale k * x) -
        rationalDeltaLiveRCardMid k lo hi| <=
          rationalDeltaLiveRCardRad k lo hi := by
    exact
      _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSpline_hbox_of_summand_hboxes
        (bsplineAutocorrDegree k)
        (bsplineScale k * x)
        (rationalDeltaLiveRCardMid k lo hi)
        (rationalDeltaLiveRCardRad k lo hi)
        (rationalDeltaLiveRTermMid k lo hi)
        (rationalDeltaLiveRTermRad k lo hi)
        (by
          intro m hm
          exact
            _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand_hbox_of_positivePartPower_hbox
              (bsplineAutocorrDegree k)
              (bsplineScale k * x)
              m
              (rationalDeltaLiveRPowerMid k lo hi m)
              (rationalDeltaLiveRPowerRad k lo hi m)
              (rationalDeltaLiveRTermMid k lo hi m)
              (rationalDeltaLiveRTermRad k lo hi m)
              (by
                have hlo' :
                    bsplineScale k * lo +
                          (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
                          (m : Real) <=
                        bsplineScale k * x +
                          (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
                          (m : Real) := by
                  linarith
                have hhi' :
                    bsplineScale k * x +
                          (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
                          (m : Real) <=
                        bsplineScale k * hi +
                          (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
                          (m : Real) := by
                  linarith
                simpa [rationalDeltaLiveRPowerMid, rationalDeltaLiveRPowerRad] using
                  rationalDeltaLive_positivePartPower_hbox_of_bounds
                    (d := bsplineAutocorrDegree k)
                    (x := bsplineScale k * x +
                      (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
                      (m : Real))
                    (lo := bsplineScale k * lo +
                      (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
                      (m : Real))
                    (hi := bsplineScale k * hi +
                      (((bsplineAutocorrDegree k + 1 : Nat) : Real) / 2) -
                      (m : Real))
                    (rationalDeltaLive_positivePartPower_mono_autocorr k)
                    hlo' hhi')
              (by rfl)
              (by rfl))
        (by rfl)
        (by rfl)
  have hr :=
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR_hbox_of_cardinal_hbox
      k x (rationalDeltaLiveRCardMid k lo hi)
      (rationalDeltaLiveRCardRad k lo hi) hcard
  exact rational_hbox_transfer
    (by simpa [rationalDeltaLiveRMidReal, rationalDeltaLiveRRadReal] using hr)
    hdom

def rationalDeltaLiveRatPositivePartPower (d : Nat) (x : Rat) : Rat :=
  if 0 < x then x ^ d else 0

def rationalDeltaLiveRatBsplineScale (k : Nat) : Rat :=
  ((k + 1 : Nat) : Rat) / 2

def rationalDeltaLiveRatBsplineAutocorrDegree (k : Nat) : Nat :=
  2 * k + 1

def rationalDeltaLiveRatCenteredCardinalBSplineSummand
    (degree : Nat) (x : Rat) (j : Nat) : Rat :=
  ((-1 : Rat) ^ j) *
    (Nat.choose (degree + 1) j : Rat) *
      rationalDeltaLiveRatPositivePartPower degree
        (x + (((degree + 1 : Nat) : Rat) / 2) - (j : Rat))

def rationalDeltaLiveRatCenteredCardinalBSpline
    (degree : Nat) (x : Rat) : Rat :=
  ((Nat.factorial degree : Rat)⁻¹) *
    ((Finset.range (degree + 2)).sum fun j =>
      rationalDeltaLiveRatCenteredCardinalBSplineSummand degree x j)

def rationalDeltaLiveRatBsplineAutocorrNorm (k : Nat) : Rat :=
  rationalDeltaLiveRatCenteredCardinalBSpline
    (rationalDeltaLiveRatBsplineAutocorrDegree k) 0

def rationalDeltaLiveRatRPowerMid (k : Nat) (lo hi : Rat) (m : Nat) : Rat :=
  (rationalDeltaLiveRatPositivePartPower (rationalDeltaLiveRatBsplineAutocorrDegree k)
      (rationalDeltaLiveRatBsplineScale k * lo +
        (((rationalDeltaLiveRatBsplineAutocorrDegree k + 1 : Nat) : Rat) / 2) -
        (m : Rat)) +
    rationalDeltaLiveRatPositivePartPower (rationalDeltaLiveRatBsplineAutocorrDegree k)
      (rationalDeltaLiveRatBsplineScale k * hi +
        (((rationalDeltaLiveRatBsplineAutocorrDegree k + 1 : Nat) : Rat) / 2) -
        (m : Rat))) / 2

def rationalDeltaLiveRatRPowerRad (k : Nat) (lo hi : Rat) (m : Nat) : Rat :=
  (rationalDeltaLiveRatPositivePartPower (rationalDeltaLiveRatBsplineAutocorrDegree k)
      (rationalDeltaLiveRatBsplineScale k * hi +
        (((rationalDeltaLiveRatBsplineAutocorrDegree k + 1 : Nat) : Rat) / 2) -
        (m : Rat)) -
    rationalDeltaLiveRatPositivePartPower (rationalDeltaLiveRatBsplineAutocorrDegree k)
      (rationalDeltaLiveRatBsplineScale k * lo +
        (((rationalDeltaLiveRatBsplineAutocorrDegree k + 1 : Nat) : Rat) / 2) -
        (m : Rat))) / 2

def rationalDeltaLiveRatRTermMid (k : Nat) (lo hi : Rat) (m : Nat) : Rat :=
  (((-1 : Rat) ^ m) *
    (Nat.choose (rationalDeltaLiveRatBsplineAutocorrDegree k + 1) m : Rat)) *
      rationalDeltaLiveRatRPowerMid k lo hi m

def rationalDeltaLiveRatRTermRad (k : Nat) (lo hi : Rat) (m : Nat) : Rat :=
  |((-1 : Rat) ^ m) *
    (Nat.choose (rationalDeltaLiveRatBsplineAutocorrDegree k + 1) m : Rat)| *
      rationalDeltaLiveRatRPowerRad k lo hi m

def rationalDeltaLiveRatRCardMid (k : Nat) (lo hi : Rat) : Rat :=
  ((Nat.factorial (rationalDeltaLiveRatBsplineAutocorrDegree k) : Rat)⁻¹) *
    ((Finset.range (rationalDeltaLiveRatBsplineAutocorrDegree k + 2)).sum fun m =>
      rationalDeltaLiveRatRTermMid k lo hi m)

def rationalDeltaLiveRatRCardRad (k : Nat) (lo hi : Rat) : Rat :=
  |((Nat.factorial (rationalDeltaLiveRatBsplineAutocorrDegree k) : Rat)⁻¹)| *
    ((Finset.range (rationalDeltaLiveRatBsplineAutocorrDegree k + 2)).sum fun m =>
      rationalDeltaLiveRatRTermRad k lo hi m)

def rationalDeltaLiveRatRMid (k : Nat) (lo hi : Rat) : Rat :=
  rationalDeltaLiveRatRCardMid k lo hi /
    rationalDeltaLiveRatBsplineAutocorrNorm k

def rationalDeltaLiveRatRRad (k : Nat) (lo hi : Rat) : Rat :=
  rationalDeltaLiveRatRCardRad k lo hi /
    rationalDeltaLiveRatBsplineAutocorrNorm k

private theorem rationalDeltaLiveRatPositivePartPower_cast (d : Nat) (x : Rat) :
    ((rationalDeltaLiveRatPositivePartPower d x : Rat) : Real) =
      positivePartPower d ((x : Rat) : Real) := by
  by_cases hx : 0 < x
  · have hxReal : 0 < ((x : Rat) : Real) := by exact_mod_cast hx
    simp [rationalDeltaLiveRatPositivePartPower, hx, positivePartPower, hxReal]
  · have hxReal : ¬ 0 < ((x : Rat) : Real) := by
      intro h
      exact hx (by exact_mod_cast h)
    simp [rationalDeltaLiveRatPositivePartPower, hx, positivePartPower, hxReal]

private theorem rationalDeltaLiveRatBsplineScale_cast (k : Nat) :
    ((rationalDeltaLiveRatBsplineScale k : Rat) : Real) = bsplineScale k := by
  norm_num [rationalDeltaLiveRatBsplineScale, bsplineScale]

private theorem rationalDeltaLiveRatBsplineAutocorrDegree_eq (k : Nat) :
    rationalDeltaLiveRatBsplineAutocorrDegree k = bsplineAutocorrDegree k := by
  simp [rationalDeltaLiveRatBsplineAutocorrDegree, bsplineAutocorrDegree]

private theorem rationalDeltaLiveRatRPowerMid_cast
    (k : Nat) (lo hi : Rat) (m : Nat) :
    ((rationalDeltaLiveRatRPowerMid k lo hi m : Rat) : Real) =
      rationalDeltaLiveRPowerMid k ((lo : Rat) : Real) ((hi : Rat) : Real) m := by
  simp [rationalDeltaLiveRatRPowerMid, rationalDeltaLiveRPowerMid,
    rationalDeltaLiveRatPositivePartPower_cast,
    rationalDeltaLiveRatBsplineScale_cast,
    rationalDeltaLiveRatBsplineAutocorrDegree_eq]

private theorem rationalDeltaLiveRatRPowerRad_cast
    (k : Nat) (lo hi : Rat) (m : Nat) :
    ((rationalDeltaLiveRatRPowerRad k lo hi m : Rat) : Real) =
      rationalDeltaLiveRPowerRad k ((lo : Rat) : Real) ((hi : Rat) : Real) m := by
  simp [rationalDeltaLiveRatRPowerRad, rationalDeltaLiveRPowerRad,
    rationalDeltaLiveRatPositivePartPower_cast,
    rationalDeltaLiveRatBsplineScale_cast,
    rationalDeltaLiveRatBsplineAutocorrDegree_eq]

private theorem rationalDeltaLiveRatRTermMid_cast
    (k : Nat) (lo hi : Rat) (m : Nat) :
    ((rationalDeltaLiveRatRTermMid k lo hi m : Rat) : Real) =
      rationalDeltaLiveRTermMid k ((lo : Rat) : Real) ((hi : Rat) : Real) m := by
  simp [rationalDeltaLiveRatRTermMid, rationalDeltaLiveRTermMid,
    rationalDeltaLiveRatRPowerMid_cast,
    rationalDeltaLiveRatBsplineAutocorrDegree_eq]

private theorem rationalDeltaLiveRatRTermRad_cast
    (k : Nat) (lo hi : Rat) (m : Nat) :
    ((rationalDeltaLiveRatRTermRad k lo hi m : Rat) : Real) =
      rationalDeltaLiveRTermRad k ((lo : Rat) : Real) ((hi : Rat) : Real) m := by
  simp [rationalDeltaLiveRatRTermRad, rationalDeltaLiveRTermRad,
    rationalDeltaLiveRatRPowerRad_cast,
    rationalDeltaLiveRatBsplineAutocorrDegree_eq]

private theorem rationalDeltaLiveRatRCardMid_cast
    (k : Nat) (lo hi : Rat) :
    ((rationalDeltaLiveRatRCardMid k lo hi : Rat) : Real) =
      rationalDeltaLiveRCardMid k ((lo : Rat) : Real) ((hi : Rat) : Real) := by
  simp [rationalDeltaLiveRatRCardMid, rationalDeltaLiveRCardMid,
    rationalDeltaLiveRatRTermMid_cast,
    rationalDeltaLiveRatBsplineAutocorrDegree_eq]

private theorem rationalDeltaLiveRatRCardRad_cast
    (k : Nat) (lo hi : Rat) :
    ((rationalDeltaLiveRatRCardRad k lo hi : Rat) : Real) =
      rationalDeltaLiveRCardRad k ((lo : Rat) : Real) ((hi : Rat) : Real) := by
  simp [rationalDeltaLiveRatRCardRad, rationalDeltaLiveRCardRad,
    rationalDeltaLiveRatRTermRad_cast,
    rationalDeltaLiveRatBsplineAutocorrDegree_eq]

private theorem rationalDeltaLiveRatCenteredCardinalBSplineSummand_cast
    (degree : Nat) (x : Rat) (j : Nat) :
    ((rationalDeltaLiveRatCenteredCardinalBSplineSummand degree x j : Rat) : Real) =
      _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand
        degree ((x : Rat) : Real) j := by
  simp [
    rationalDeltaLiveRatCenteredCardinalBSplineSummand,
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand,
    rationalDeltaLiveRatPositivePartPower_cast]

private theorem rationalDeltaLiveRatCenteredCardinalBSpline_cast
    (degree : Nat) (x : Rat) :
    ((rationalDeltaLiveRatCenteredCardinalBSpline degree x : Rat) : Real) =
      centeredCardinalBSpline degree ((x : Rat) : Real) := by
  simp [rationalDeltaLiveRatCenteredCardinalBSpline, centeredCardinalBSpline,
    rationalDeltaLiveRatCenteredCardinalBSplineSummand_cast,
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredCardinalBSplineSummand]

private theorem rationalDeltaLiveRatBsplineAutocorrNorm_cast (k : Nat) :
    ((rationalDeltaLiveRatBsplineAutocorrNorm k : Rat) : Real) =
      bsplineAutocorrNorm k := by
  simp [rationalDeltaLiveRatBsplineAutocorrNorm, bsplineAutocorrNorm,
    rationalDeltaLiveRatCenteredCardinalBSpline_cast,
    rationalDeltaLiveRatBsplineAutocorrDegree_eq]

private theorem rationalDeltaLiveRatRMid_cast (k : Nat) (lo hi : Rat) :
    ((rationalDeltaLiveRatRMid k lo hi : Rat) : Real) =
      rationalDeltaLiveRMidReal k ((lo : Rat) : Real) ((hi : Rat) : Real) := by
  simp [rationalDeltaLiveRatRMid, rationalDeltaLiveRMidReal,
    rationalDeltaLiveRatRCardMid_cast,
    rationalDeltaLiveRatBsplineAutocorrNorm_cast]

private theorem rationalDeltaLiveRatRRad_cast (k : Nat) (lo hi : Rat) :
    ((rationalDeltaLiveRatRRad k lo hi : Rat) : Real) =
      rationalDeltaLiveRRadReal k ((lo : Rat) : Real) ((hi : Rat) : Real) := by
  simp [rationalDeltaLiveRatRRad, rationalDeltaLiveRRadReal,
    rationalDeltaLiveRatRCardRad_cast,
    rationalDeltaLiveRatBsplineAutocorrNorm_cast]

theorem rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
    (k : Nat) {x : Real} {lo hi mid rad : Rat}
    (hlo : ((lo : Rat) : Real) <= x)
    (hhi : x <= ((hi : Rat) : Real))
    (hdom : rationalDeltaLiveRatRRad k lo hi +
        |rationalDeltaLiveRatRMid k lo hi - mid| <= rad) :
    |centeredBSplineR k x - ((mid : Rat) : Real)| <= ((rad : Rat) : Real) := by
  have hdomReal :
      rationalDeltaLiveRRadReal k ((lo : Rat) : Real) ((hi : Rat) : Real) +
          |rationalDeltaLiveRMidReal k ((lo : Rat) : Real) ((hi : Rat) : Real) -
            ((mid : Rat) : Real)| <=
        ((rad : Rat) : Real) := by
    have hcast :
        ((rationalDeltaLiveRatRRad k lo hi +
          |rationalDeltaLiveRatRMid k lo hi - mid| : Rat) : Real) <=
          ((rad : Rat) : Real) := by
      exact_mod_cast hdom
    simpa [rationalDeltaLiveRatRRad_cast, rationalDeltaLiveRatRMid_cast] using hcast
  exact
    rationalDeltaLive_centeredBSplineR_hbox_of_real_arg_bounds
      (k := k) hlo hhi hdomReal
"""


def emit_module(
    blocks: dict[str, dict[int, dict[int, TermWitness]]],
    weight_payload: dict[int, tuple[str, str]],
) -> str:
    primary = blocks["primary"]
    control = blocks["control"]
    return f"""import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLivePayloadImport
import Q3.Proofs.PrimeCert.IntervalLemmas

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B rational delta/live payload witnesses.

Source:
`ACTIVE/requests/step33_bootstrap/termwise_replay_audit_live_1024_payload.json`.

This module contains concrete rational midpoint/radius witness functions.  It
does not trust the JSON as a proof: the final payload still requires
Lean-checked term hboxes and center-error budget facts for these witnesses.
-/

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffPrimeEntryHboxImport
open CenteredCoeffPrimeDeltaLivePayloadImport
open CenteredCoeffPrimePositivePartTightImport
open CenteredCoeffEntryHboxImport

/-- Integer packet-center delta `j - i`; the actual center difference is this
integer divided by four. -/
def coeffIndexDeltaInt (i j : CoeffIndex23) : Int :=
  Int.ofNat j.1 - Int.ofNat i.1

/-- Primary packet-center difference as the integer delta divided by four. -/
theorem primaryK11Center_sub_eq_coeffIndexDeltaInt (i j : CoeffIndex23) :
    primaryK11Center j - primaryK11Center i =
      ((coeffIndexDeltaInt i j : Int) : Real) / 4 := by
  rw [primaryK11Center_sub_eq_index_delta, coeffIndexDeltaInt]
  norm_num

/-- Control packet-center difference as the integer delta divided by four. -/
theorem controlK9Center_sub_eq_coeffIndexDeltaInt (i j : CoeffIndex23) :
    controlK9Center j - controlK9Center i =
      ((coeffIndexDeltaInt i j : Int) : Real) / 4 := by
  rw [controlK9Center_sub_eq_index_delta, coeffIndexDeltaInt]
  norm_num

{emit_shift_table(
    raw_name="activeL3RationalPrimeWeightMidRatRaw",
    rat_name="activeL3RationalPrimeWeightMidRat",
    real_name="activeL3RationalPrimeWeightMid",
    values=weight_payload,
    field_idx=0,
)}

{emit_shift_table(
    raw_name="activeL3RationalPrimeWeightRadRatRaw",
    rat_name="activeL3RationalPrimeWeightRadRat",
    real_name="activeL3RationalPrimeWeightRad",
    values=weight_payload,
    field_idx=1,
)}

{emit_declared_set("primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta", primary)}

{emit_declared_set_for_fields(
    "primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta",
    primary,
    (RMINUS_MID, RMINUS_RAD),
)}

{emit_declared_set_for_fields(
    "primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta",
    primary,
    (RPLUS_MID, RPLUS_RAD),
)}

{emit_table("primaryK11RationalDeltaLiveTermMidByDelta", "mid", primary, "primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta")}

{emit_table("primaryK11RationalDeltaLiveTermRadByDelta", "rad", primary, "primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta")}

{emit_table("primaryK11RationalDeltaLiveRPairMidByDelta", "rpair_mid", primary, "primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta")}

{emit_table("primaryK11RationalDeltaLiveRPairRadByDelta", "rpair_rad", primary, "primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta")}

{emit_table("primaryK11RationalDeltaLiveRMinusMidByDelta", "rminus_mid", primary, "primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta")}

{emit_table("primaryK11RationalDeltaLiveRMinusRadByDelta", "rminus_rad", primary, "primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta")}

{emit_table("primaryK11RationalDeltaLiveRPlusMidByDelta", "rplus_mid", primary, "primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta")}

{emit_table("primaryK11RationalDeltaLiveRPlusRadByDelta", "rplus_rad", primary, "primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta")}

{emit_declared_set("controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta", control)}

{emit_declared_set_for_fields(
    "controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta",
    control,
    (RMINUS_MID, RMINUS_RAD),
)}

{emit_declared_set_for_fields(
    "controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta",
    control,
    (RPLUS_MID, RPLUS_RAD),
)}

{emit_table("controlK9RationalDeltaLiveTermMidByDelta", "mid", control, "controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta")}

{emit_table("controlK9RationalDeltaLiveTermRadByDelta", "rad", control, "controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta")}

{emit_table("controlK9RationalDeltaLiveRPairMidByDelta", "rpair_mid", control, "controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta")}

{emit_table("controlK9RationalDeltaLiveRPairRadByDelta", "rpair_rad", control, "controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta")}

{emit_table("controlK9RationalDeltaLiveRMinusMidByDelta", "rminus_mid", control, "controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta")}

{emit_table("controlK9RationalDeltaLiveRMinusRadByDelta", "rminus_rad", control, "controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta")}

{emit_table("controlK9RationalDeltaLiveRPlusMidByDelta", "rplus_mid", control, "controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta")}

{emit_table("controlK9RationalDeltaLiveRPlusRadByDelta", "rplus_rad", control, "controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta")}

/-- Concrete primary rational live-term midpoint witness. -/
def primaryK11RationalDeltaLiveTermMidRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  primaryK11RationalDeltaLiveTermMidByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete primary rational live-term midpoint witness as a real. -/
def primaryK11RationalDeltaLiveTermMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((primaryK11RationalDeltaLiveTermMidRat i j n : Rat) : Real)

/-- Concrete primary rational live-term radius witness. -/
def primaryK11RationalDeltaLiveTermRadRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  primaryK11RationalDeltaLiveTermRadByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete primary rational live-term radius witness as a real. -/
def primaryK11RationalDeltaLiveTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((primaryK11RationalDeltaLiveTermRadRat i j n : Rat) : Real)

/-- Concrete primary rational `R_minus + R_plus` midpoint witness. -/
def primaryK11RationalDeltaLiveRPairMidRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  primaryK11RationalDeltaLiveRPairMidByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete primary rational `R_minus + R_plus` midpoint witness as a real. -/
def primaryK11RationalDeltaLiveRPairMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((primaryK11RationalDeltaLiveRPairMidRat i j n : Rat) : Real)

/-- Concrete primary rational `R_minus + R_plus` radius witness. -/
def primaryK11RationalDeltaLiveRPairRadRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  primaryK11RationalDeltaLiveRPairRadByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete primary rational `R_minus + R_plus` radius witness as a real. -/
def primaryK11RationalDeltaLiveRPairRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((primaryK11RationalDeltaLiveRPairRadRat i j n : Rat) : Real)

/-- Concrete primary rational `R_minus` midpoint witness. -/
def primaryK11RationalDeltaLiveRMinusMidRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  primaryK11RationalDeltaLiveRMinusMidByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete primary rational `R_minus` midpoint witness as a real. -/
def primaryK11RationalDeltaLiveRMinusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((primaryK11RationalDeltaLiveRMinusMidRat i j n : Rat) : Real)

/-- Concrete primary rational `R_minus` radius witness. -/
def primaryK11RationalDeltaLiveRMinusRadRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  primaryK11RationalDeltaLiveRMinusRadByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete primary rational `R_minus` radius witness as a real. -/
def primaryK11RationalDeltaLiveRMinusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((primaryK11RationalDeltaLiveRMinusRadRat i j n : Rat) : Real)

/-- Concrete primary rational `R_plus` midpoint witness. -/
def primaryK11RationalDeltaLiveRPlusMidRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  primaryK11RationalDeltaLiveRPlusMidByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete primary rational `R_plus` midpoint witness as a real. -/
def primaryK11RationalDeltaLiveRPlusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((primaryK11RationalDeltaLiveRPlusMidRat i j n : Rat) : Real)

/-- Concrete primary rational `R_plus` radius witness. -/
def primaryK11RationalDeltaLiveRPlusRadRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  primaryK11RationalDeltaLiveRPlusRadByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete primary rational `R_plus` radius witness as a real. -/
def primaryK11RationalDeltaLiveRPlusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((primaryK11RationalDeltaLiveRPlusRadRat i j n : Rat) : Real)

/-- Concrete control rational live-term midpoint witness. -/
def controlK9RationalDeltaLiveTermMidRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  controlK9RationalDeltaLiveTermMidByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete control rational live-term midpoint witness as a real. -/
def controlK9RationalDeltaLiveTermMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((controlK9RationalDeltaLiveTermMidRat i j n : Rat) : Real)

/-- Concrete control rational live-term radius witness. -/
def controlK9RationalDeltaLiveTermRadRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  controlK9RationalDeltaLiveTermRadByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete control rational live-term radius witness as a real. -/
def controlK9RationalDeltaLiveTermRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((controlK9RationalDeltaLiveTermRadRat i j n : Rat) : Real)

/-- Concrete control rational `R_minus + R_plus` midpoint witness. -/
def controlK9RationalDeltaLiveRPairMidRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  controlK9RationalDeltaLiveRPairMidByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete control rational `R_minus + R_plus` midpoint witness as a real. -/
def controlK9RationalDeltaLiveRPairMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((controlK9RationalDeltaLiveRPairMidRat i j n : Rat) : Real)

/-- Concrete control rational `R_minus + R_plus` radius witness. -/
def controlK9RationalDeltaLiveRPairRadRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  controlK9RationalDeltaLiveRPairRadByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete control rational `R_minus + R_plus` radius witness as a real. -/
def controlK9RationalDeltaLiveRPairRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((controlK9RationalDeltaLiveRPairRadRat i j n : Rat) : Real)

/-- Concrete control rational `R_minus` midpoint witness. -/
def controlK9RationalDeltaLiveRMinusMidRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  controlK9RationalDeltaLiveRMinusMidByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete control rational `R_minus` midpoint witness as a real. -/
def controlK9RationalDeltaLiveRMinusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((controlK9RationalDeltaLiveRMinusMidRat i j n : Rat) : Real)

/-- Concrete control rational `R_minus` radius witness. -/
def controlK9RationalDeltaLiveRMinusRadRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  controlK9RationalDeltaLiveRMinusRadByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete control rational `R_minus` radius witness as a real. -/
def controlK9RationalDeltaLiveRMinusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((controlK9RationalDeltaLiveRMinusRadRat i j n : Rat) : Real)

/-- Concrete control rational `R_plus` midpoint witness. -/
def controlK9RationalDeltaLiveRPlusMidRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  controlK9RationalDeltaLiveRPlusMidByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete control rational `R_plus` midpoint witness as a real. -/
def controlK9RationalDeltaLiveRPlusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((controlK9RationalDeltaLiveRPlusMidRat i j n : Rat) : Real)

/-- Concrete control rational `R_plus` radius witness. -/
def controlK9RationalDeltaLiveRPlusRadRat
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Rat :=
  controlK9RationalDeltaLiveRPlusRadByDeltaRat (coeffIndexDeltaInt i j) n.1

/-- Concrete control rational `R_plus` radius witness as a real. -/
def controlK9RationalDeltaLiveRPlusRad
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  ((controlK9RationalDeltaLiveRPlusRadRat i j n : Rat) : Real)

/-- The declared primary nonzero rational support is contained in the
analytic live-shift set.  This is the finite generated support fact preferred
over separate midpoint/radius dead-shift proofs. -/
def primaryK11RationalDeltaLiveDeclaredNonzeroSubsetLive : Prop :=
  ∀ δInt n,
    n.1 ∈ primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta δInt ->
      n ∈ primaryK11LivePrimeShiftSet (((δInt : Int) : Real) / 4)

/-- The declared control nonzero rational support is contained in the analytic
live-shift set. -/
def controlK9RationalDeltaLiveDeclaredNonzeroSubsetLive : Prop :=
  ∀ δInt n,
    n.1 ∈ controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta δInt ->
      n ∈ controlK9LivePrimeShiftSet (((δInt : Int) : Real) / 4)

/-- A certified primary minus-side shift interval inside the support window
puts the shift into the analytic live set. -/
theorem primaryK11_mem_live_of_minus_shift_tight_bounds
    (δ : Real) (n : PrimeShiftIndexL3)
    (hleft :
      (-2 : Real) < (δ - activeL3PrimeShiftUpper n) / primaryK11Ell)
    (hright :
      (δ - activeL3PrimeShiftLower n) / primaryK11Ell < (2 : Real)) :
    n ∈ primaryK11LivePrimeShiftSet δ := by
  classical
  have hs := activeL3PrimeShift_tight_bounds n
  have hell : 0 < primaryK11Ell := primaryK11_hell
  have hactual_ge :
      (δ - activeL3PrimeShiftUpper n) / primaryK11Ell ≤
        (δ - primaryK11PrimeShift n) / primaryK11Ell := by
    have hsub :
        δ - activeL3PrimeShiftUpper n ≤ δ - primaryK11PrimeShift n := by
      simpa [primaryK11PrimeShift] using sub_le_sub_left hs.2 δ
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  have hactual_le :
      (δ - primaryK11PrimeShift n) / primaryK11Ell ≤
        (δ - activeL3PrimeShiftLower n) / primaryK11Ell := by
    have hsub :
        δ - primaryK11PrimeShift n ≤ δ - activeL3PrimeShiftLower n := by
      simpa [primaryK11PrimeShift] using sub_le_sub_left hs.1 δ
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  have hminus_not_dead :
      ¬ (((δ - primaryK11PrimeShift n) / primaryK11Ell ≤ -2) ∨
        (2 ≤ (δ - primaryK11PrimeShift n) / primaryK11Ell)) := by
    intro hdead
    rcases hdead with hle | hge <;> linarith
  have hlive : primaryK11PrimeShiftIsLive δ n := by
    intro hdead
    exact hminus_not_dead hdead.1
  simpa [primaryK11LivePrimeShiftSet] using hlive

/-- A certified primary plus-side shift interval inside the support window
puts the shift into the analytic live set. -/
theorem primaryK11_mem_live_of_plus_shift_tight_bounds
    (δ : Real) (n : PrimeShiftIndexL3)
    (hleft :
      (-2 : Real) < (δ + activeL3PrimeShiftLower n) / primaryK11Ell)
    (hright :
      (δ + activeL3PrimeShiftUpper n) / primaryK11Ell < (2 : Real)) :
    n ∈ primaryK11LivePrimeShiftSet δ := by
  classical
  have hs := activeL3PrimeShift_tight_bounds n
  have hell : 0 < primaryK11Ell := primaryK11_hell
  have hactual_ge :
      (δ + activeL3PrimeShiftLower n) / primaryK11Ell ≤
        (δ + primaryK11PrimeShift n) / primaryK11Ell := by
    have hsum :
        δ + activeL3PrimeShiftLower n ≤ δ + primaryK11PrimeShift n := by
      simpa [primaryK11PrimeShift] using add_le_add_left hs.1 δ
    exact div_le_div_of_nonneg_right hsum (le_of_lt hell)
  have hactual_le :
      (δ + primaryK11PrimeShift n) / primaryK11Ell ≤
        (δ + activeL3PrimeShiftUpper n) / primaryK11Ell := by
    have hsum :
        δ + primaryK11PrimeShift n ≤ δ + activeL3PrimeShiftUpper n := by
      simpa [primaryK11PrimeShift] using add_le_add_left hs.2 δ
    exact div_le_div_of_nonneg_right hsum (le_of_lt hell)
  have hplus_not_dead :
      ¬ (((δ + primaryK11PrimeShift n) / primaryK11Ell ≤ -2) ∨
        (2 ≤ (δ + primaryK11PrimeShift n) / primaryK11Ell)) := by
    intro hdead
    rcases hdead with hle | hge <;> linarith
  have hlive : primaryK11PrimeShiftIsLive δ n := by
    intro hdead
    exact hplus_not_dead hdead.2
  simpa [primaryK11LivePrimeShiftSet] using hlive

/-- A certified control minus-side shift interval inside the support window
puts the shift into the analytic live set. -/
theorem controlK9_mem_live_of_minus_shift_tight_bounds
    (δ : Real) (n : PrimeShiftIndexL3)
    (hleft :
      (-2 : Real) < (δ - activeL3PrimeShiftUpper n) / controlK9Ell)
    (hright :
      (δ - activeL3PrimeShiftLower n) / controlK9Ell < (2 : Real)) :
    n ∈ controlK9LivePrimeShiftSet δ := by
  classical
  have hs := activeL3PrimeShift_tight_bounds n
  have hell : 0 < controlK9Ell := controlK9_hell
  have hactual_ge :
      (δ - activeL3PrimeShiftUpper n) / controlK9Ell ≤
        (δ - controlK9PrimeShift n) / controlK9Ell := by
    have hsub :
        δ - activeL3PrimeShiftUpper n ≤ δ - controlK9PrimeShift n := by
      simpa [controlK9PrimeShift] using sub_le_sub_left hs.2 δ
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  have hactual_le :
      (δ - controlK9PrimeShift n) / controlK9Ell ≤
        (δ - activeL3PrimeShiftLower n) / controlK9Ell := by
    have hsub :
        δ - controlK9PrimeShift n ≤ δ - activeL3PrimeShiftLower n := by
      simpa [controlK9PrimeShift] using sub_le_sub_left hs.1 δ
    exact div_le_div_of_nonneg_right hsub (le_of_lt hell)
  have hminus_not_dead :
      ¬ (((δ - controlK9PrimeShift n) / controlK9Ell ≤ -2) ∨
        (2 ≤ (δ - controlK9PrimeShift n) / controlK9Ell)) := by
    intro hdead
    rcases hdead with hle | hge <;> linarith
  have hlive : controlK9PrimeShiftIsLive δ n := by
    intro hdead
    exact hminus_not_dead hdead.1
  simpa [controlK9LivePrimeShiftSet] using hlive

/-- A certified control plus-side shift interval inside the support window
puts the shift into the analytic live set. -/
theorem controlK9_mem_live_of_plus_shift_tight_bounds
    (δ : Real) (n : PrimeShiftIndexL3)
    (hleft :
      (-2 : Real) < (δ + activeL3PrimeShiftLower n) / controlK9Ell)
    (hright :
      (δ + activeL3PrimeShiftUpper n) / controlK9Ell < (2 : Real)) :
    n ∈ controlK9LivePrimeShiftSet δ := by
  classical
  have hs := activeL3PrimeShift_tight_bounds n
  have hell : 0 < controlK9Ell := controlK9_hell
  have hactual_ge :
      (δ + activeL3PrimeShiftLower n) / controlK9Ell ≤
        (δ + controlK9PrimeShift n) / controlK9Ell := by
    have hsum :
        δ + activeL3PrimeShiftLower n ≤ δ + controlK9PrimeShift n := by
      simpa [controlK9PrimeShift] using add_le_add_left hs.1 δ
    exact div_le_div_of_nonneg_right hsum (le_of_lt hell)
  have hactual_le :
      (δ + controlK9PrimeShift n) / controlK9Ell ≤
        (δ + activeL3PrimeShiftUpper n) / controlK9Ell := by
    have hsum :
        δ + controlK9PrimeShift n ≤ δ + activeL3PrimeShiftUpper n := by
      simpa [controlK9PrimeShift] using add_le_add_left hs.2 δ
    exact div_le_div_of_nonneg_right hsum (le_of_lt hell)
  have hplus_not_dead :
      ¬ (((δ + controlK9PrimeShift n) / controlK9Ell ≤ -2) ∨
        (2 ≤ (δ + controlK9PrimeShift n) / controlK9Ell)) := by
    intro hdead
    rcases hdead with hle | hge <;> linarith
  have hlive : controlK9PrimeShiftIsLive δ n := by
    intro hdead
    exact hplus_not_dead hdead.2
  simpa [controlK9LivePrimeShiftSet] using hlive

{emit_declared_subset_generated(
    prop_name="primaryK11RationalDeltaLiveDeclaredNonzeroSubsetLive",
    theorem_name="primaryK11RationalDeltaLiveDeclaredNonzeroSubsetLive_generated",
    declared_set_name="primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta",
    prefix="primaryK11",
    ell_name="primaryK11Ell",
    ell_rat_name="primaryK11EllRat",
    live_set_name="primaryK11LivePrimeShiftSet",
    by_delta=primary,
)}

{emit_declared_subset_generated(
    prop_name="controlK9RationalDeltaLiveDeclaredNonzeroSubsetLive",
    theorem_name="controlK9RationalDeltaLiveDeclaredNonzeroSubsetLive_generated",
    declared_set_name="controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta",
    prefix="controlK9",
    ell_name="controlK9Ell",
    ell_rat_name="controlK9EllRat",
    live_set_name="controlK9LivePrimeShiftSet",
    by_delta=control,
)}

/-- Nonzero primary midpoint witnesses must belong to the declared generated
support set by construction of the rational table. -/
theorem primaryK11RationalDeltaLiveTermMid_declared_of_ne
    {{i j : CoeffIndex23}} {{n : PrimeShiftIndexL3}}
    (hne : primaryK11RationalDeltaLiveTermMid i j n ≠ 0) :
    n.1 ∈ primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta
      (coeffIndexDeltaInt i j) := by
  by_contra hn
  apply hne
  simp [primaryK11RationalDeltaLiveTermMid,
    primaryK11RationalDeltaLiveTermMidRat,
    primaryK11RationalDeltaLiveTermMidByDeltaRat, hn]

/-- Nonzero primary radius witnesses must belong to the declared generated
support set by construction of the rational table. -/
theorem primaryK11RationalDeltaLiveTermRad_declared_of_ne
    {{i j : CoeffIndex23}} {{n : PrimeShiftIndexL3}}
    (hne : primaryK11RationalDeltaLiveTermRad i j n ≠ 0) :
    n.1 ∈ primaryK11RationalDeltaLiveDeclaredNonzeroShiftSetByDelta
      (coeffIndexDeltaInt i j) := by
  by_contra hn
  apply hne
  simp [primaryK11RationalDeltaLiveTermRad,
    primaryK11RationalDeltaLiveTermRadRat,
    primaryK11RationalDeltaLiveTermRadByDeltaRat, hn]

/-- Nonzero control midpoint witnesses must belong to the declared generated
support set by construction of the rational table. -/
theorem controlK9RationalDeltaLiveTermMid_declared_of_ne
    {{i j : CoeffIndex23}} {{n : PrimeShiftIndexL3}}
    (hne : controlK9RationalDeltaLiveTermMid i j n ≠ 0) :
    n.1 ∈ controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta
      (coeffIndexDeltaInt i j) := by
  by_contra hn
  apply hne
  simp [controlK9RationalDeltaLiveTermMid,
    controlK9RationalDeltaLiveTermMidRat,
    controlK9RationalDeltaLiveTermMidByDeltaRat, hn]

/-- Nonzero control radius witnesses must belong to the declared generated
support set by construction of the rational table. -/
theorem controlK9RationalDeltaLiveTermRad_declared_of_ne
    {{i j : CoeffIndex23}} {{n : PrimeShiftIndexL3}}
    (hne : controlK9RationalDeltaLiveTermRad i j n ≠ 0) :
    n.1 ∈ controlK9RationalDeltaLiveDeclaredNonzeroShiftSetByDelta
      (coeffIndexDeltaInt i j) := by
  by_contra hn
  apply hne
  simp [controlK9RationalDeltaLiveTermRad,
    controlK9RationalDeltaLiveTermRadRat,
    controlK9RationalDeltaLiveTermRadByDeltaRat, hn]

private theorem rational_hbox_transfer
    {{x tightMid tightRad mid rad : Real}}
    (htight : |x - tightMid| ≤ tightRad)
    (hdom : tightRad + |tightMid - mid| ≤ rad) :
    |x - mid| ≤ rad := by
  have hsplit : x - mid = (x - tightMid) + (tightMid - mid) := by ring
  calc
    |x - mid| = |(x - tightMid) + (tightMid - mid)| := by rw [hsplit]
    _ ≤ |x - tightMid| + |tightMid - mid| := abs_add_le _ _
    _ ≤ tightRad + |tightMid - mid| := by
      exact add_le_add htight (le_refl _)
    _ ≤ rad := hdom

private theorem rational_product_hbox_transfer
    {{w wm wr r rm rr mid rad : Real}}
    (hw : |w - wm| ≤ wr)
    (hr : |r - rm| ≤ rr)
    (hbudget : (|wm| + wr) * rr + wr * |rm| +
        |wm * rm - mid| ≤ rad) :
    |w * r - mid| ≤ rad := by
  have hwr_nonneg : 0 ≤ wr := le_trans (abs_nonneg _) hw
  have hr_abs : |r| ≤ |rm| + rr := by
    have hrewrite : r = (r - rm) + rm := by ring
    calc
      |r| = |(r - rm) + rm| := by
        exact congrArg (fun t => |t|) hrewrite
      _ ≤ |r - rm| + |rm| := abs_add_le _ _
      _ ≤ rr + |rm| := add_le_add hr (le_refl _)
      _ = |rm| + rr := by ring
  have hprod_decomp :
      w * r - wm * rm = wm * (r - rm) + (w - wm) * r := by
    ring
  have hprod_bound :
      |w * r - wm * rm| ≤ |wm| * rr + wr * (|rm| + rr) := by
    calc
      |w * r - wm * rm| =
          |wm * (r - rm) + (w - wm) * r| := by rw [hprod_decomp]
      _ ≤ |wm * (r - rm)| + |(w - wm) * r| := abs_add_le _ _
      _ = |wm| * |r - rm| + |w - wm| * |r| := by
          simp [abs_mul]
      _ ≤ |wm| * rr + wr * (|rm| + rr) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
            (mul_le_mul hw hr_abs (abs_nonneg _) hwr_nonneg)
  have hprod :
      |w * r - wm * rm| ≤ (|wm| + wr) * rr + wr * |rm| := by
    calc
      |w * r - wm * rm| ≤ |wm| * rr + wr * (|rm| + rr) := hprod_bound
      _ = (|wm| + wr) * rr + wr * |rm| := by ring
  have hsplit :
      w * r - mid = (w * r - wm * rm) + (wm * rm - mid) := by
    ring
  calc
    |w * r - mid| =
        |(w * r - wm * rm) + (wm * rm - mid)| := by rw [hsplit]
    _ ≤ |w * r - wm * rm| + |wm * rm - mid| := abs_add_le _ _
    _ ≤ ((|wm| + wr) * rr + wr * |rm|) +
          |wm * rm - mid| := by
        exact add_le_add hprod (le_refl _)
    _ ≤ rad := hbudget

{emit_rat_centered_bspline_hbox_helpers()}

{emit_active_weight_hbox_generated(weight_payload)}

{emit_active_shift_bounds_generated()}

private theorem normalized_minus_arg_bounds
    {{center shift lo hi ell : Real}}
    (hell : 0 < ell)
    (hlo : lo ≤ shift) (hhi : shift ≤ hi) :
    (center - hi) / ell ≤ (center - shift) / ell ∧
      (center - shift) / ell ≤ (center - lo) / ell := by
  have hsub_low : center - hi ≤ center - shift := by linarith
  have hsub_high : center - shift ≤ center - lo := by linarith
  exact ⟨
    div_le_div_of_nonneg_right hsub_low (le_of_lt hell),
    div_le_div_of_nonneg_right hsub_high (le_of_lt hell)⟩

private theorem normalized_plus_arg_bounds
    {{center shift lo hi ell : Real}}
    (hell : 0 < ell)
    (hlo : lo ≤ shift) (hhi : shift ≤ hi) :
    (center + lo) / ell ≤ (center + shift) / ell ∧
      (center + shift) / ell ≤ (center + hi) / ell := by
  have hsum_low : center + lo ≤ center + shift := by linarith
  have hsum_high : center + shift ≤ center + hi := by linarith
  exact ⟨
    div_le_div_of_nonneg_right hsum_low (le_of_lt hell),
    div_le_div_of_nonneg_right hsum_high (le_of_lt hell)⟩

/-- High-precision bounds for the normalized primary minus-side `R` argument. -/
theorem primaryK11RationalDeltaLiveRMinus_arg_bounds
    (δInt : Int) (n : PrimeShiftIndexL3) :
    (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper n) /
        primaryK11Ell ≤
      (((δInt : Int) : Real) / 4 - primaryK11PrimeShift n) /
        primaryK11Ell ∧
    (((δInt : Int) : Real) / 4 - primaryK11PrimeShift n) /
        primaryK11Ell ≤
      (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower n) /
        primaryK11Ell := by
  have hs := activeL3RationalPrimeShift_bounds n
  simpa [primaryK11PrimeShift] using
    normalized_minus_arg_bounds
      (center := (((δInt : Int) : Real) / 4))
      (shift := activeL3PrimeShift n)
      (lo := activeL3RationalPrimeShiftLower n)
      (hi := activeL3RationalPrimeShiftUpper n)
      (ell := primaryK11Ell)
      primaryK11_hell hs.1 hs.2

/-- High-precision bounds for the normalized primary plus-side `R` argument. -/
theorem primaryK11RationalDeltaLiveRPlus_arg_bounds
    (δInt : Int) (n : PrimeShiftIndexL3) :
    (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower n) /
        primaryK11Ell ≤
      (((δInt : Int) : Real) / 4 + primaryK11PrimeShift n) /
        primaryK11Ell ∧
    (((δInt : Int) : Real) / 4 + primaryK11PrimeShift n) /
        primaryK11Ell ≤
      (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper n) /
        primaryK11Ell := by
  have hs := activeL3RationalPrimeShift_bounds n
  simpa [primaryK11PrimeShift] using
    normalized_plus_arg_bounds
      (center := (((δInt : Int) : Real) / 4))
      (shift := activeL3PrimeShift n)
      (lo := activeL3RationalPrimeShiftLower n)
      (hi := activeL3RationalPrimeShiftUpper n)
      (ell := primaryK11Ell)
      primaryK11_hell hs.1 hs.2

/-- High-precision bounds for the normalized control minus-side `R` argument. -/
theorem controlK9RationalDeltaLiveRMinus_arg_bounds
    (δInt : Int) (n : PrimeShiftIndexL3) :
    (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper n) /
        controlK9Ell ≤
      (((δInt : Int) : Real) / 4 - controlK9PrimeShift n) /
        controlK9Ell ∧
    (((δInt : Int) : Real) / 4 - controlK9PrimeShift n) /
        controlK9Ell ≤
      (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower n) /
        controlK9Ell := by
  have hs := activeL3RationalPrimeShift_bounds n
  simpa [controlK9PrimeShift] using
    normalized_minus_arg_bounds
      (center := (((δInt : Int) : Real) / 4))
      (shift := activeL3PrimeShift n)
      (lo := activeL3RationalPrimeShiftLower n)
      (hi := activeL3RationalPrimeShiftUpper n)
      (ell := controlK9Ell)
      controlK9_hell hs.1 hs.2

/-- High-precision bounds for the normalized control plus-side `R` argument. -/
theorem controlK9RationalDeltaLiveRPlus_arg_bounds
    (δInt : Int) (n : PrimeShiftIndexL3) :
    (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower n) /
        controlK9Ell ≤
      (((δInt : Int) : Real) / 4 + controlK9PrimeShift n) /
        controlK9Ell ∧
    (((δInt : Int) : Real) / 4 + controlK9PrimeShift n) /
        controlK9Ell ≤
      (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper n) /
        controlK9Ell := by
  have hs := activeL3RationalPrimeShift_bounds n
  simpa [controlK9PrimeShift] using
    normalized_plus_arg_bounds
      (center := (((δInt : Int) : Real) / 4))
      (shift := activeL3PrimeShift n)
      (lo := activeL3RationalPrimeShiftLower n)
      (hi := activeL3RationalPrimeShiftUpper n)
      (ell := controlK9Ell)
      controlK9_hell hs.1 hs.2

/-- Primary minus-side `R` value is zero when the rational argument interval
lies to the left of compact support. -/
theorem primaryK11RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    (δInt : Int) (n : PrimeShiftIndexL3)
    (h :
      ((((δInt : Int) : Real) / 4 -
          activeL3RationalPrimeShiftLower n) / primaryK11Ell) ≤
        (-2 : Real)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 - primaryK11PrimeShift n) /
        primaryK11Ell) = 0 := by
  have hb := primaryK11RationalDeltaLiveRMinus_arg_bounds δInt n
  exact
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_le_neg_two
      (le_trans hb.2 h)

/-- Primary minus-side `R` value is zero when the rational argument interval
lies to the right of compact support. -/
theorem primaryK11RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    (δInt : Int) (n : PrimeShiftIndexL3)
    (h :
      (2 : Real) ≤
        ((((δInt : Int) : Real) / 4 -
          activeL3RationalPrimeShiftUpper n) / primaryK11Ell)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 - primaryK11PrimeShift n) /
        primaryK11Ell) = 0 := by
  have hb := primaryK11RationalDeltaLiveRMinus_arg_bounds δInt n
  exact
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
      (le_trans h hb.1)

/-- Primary plus-side `R` value is zero when the rational argument interval
lies to the left of compact support. -/
theorem primaryK11RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    (δInt : Int) (n : PrimeShiftIndexL3)
    (h :
      ((((δInt : Int) : Real) / 4 +
          activeL3RationalPrimeShiftUpper n) / primaryK11Ell) ≤
        (-2 : Real)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 + primaryK11PrimeShift n) /
        primaryK11Ell) = 0 := by
  have hb := primaryK11RationalDeltaLiveRPlus_arg_bounds δInt n
  exact
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_le_neg_two
      (le_trans hb.2 h)

/-- Primary plus-side `R` value is zero when the rational argument interval
lies to the right of compact support. -/
theorem primaryK11RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    (δInt : Int) (n : PrimeShiftIndexL3)
    (h :
      (2 : Real) ≤
        ((((δInt : Int) : Real) / 4 +
          activeL3RationalPrimeShiftLower n) / primaryK11Ell)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 + primaryK11PrimeShift n) /
        primaryK11Ell) = 0 := by
  have hb := primaryK11RationalDeltaLiveRPlus_arg_bounds δInt n
  exact
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
      (le_trans h hb.1)

/-- Control minus-side `R` value is zero when the rational argument interval
lies to the left of compact support. -/
theorem controlK9RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    (δInt : Int) (n : PrimeShiftIndexL3)
    (h :
      ((((δInt : Int) : Real) / 4 -
          activeL3RationalPrimeShiftLower n) / controlK9Ell) ≤
        (-2 : Real)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 - controlK9PrimeShift n) /
        controlK9Ell) = 0 := by
  have hb := controlK9RationalDeltaLiveRMinus_arg_bounds δInt n
  exact
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_le_neg_two
      (le_trans hb.2 h)

/-- Control minus-side `R` value is zero when the rational argument interval
lies to the right of compact support. -/
theorem controlK9RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    (δInt : Int) (n : PrimeShiftIndexL3)
    (h :
      (2 : Real) ≤
        ((((δInt : Int) : Real) / 4 -
          activeL3RationalPrimeShiftUpper n) / controlK9Ell)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 - controlK9PrimeShift n) /
        controlK9Ell) = 0 := by
  have hb := controlK9RationalDeltaLiveRMinus_arg_bounds δInt n
  exact
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le
      (le_trans h hb.1)

/-- Control plus-side `R` value is zero when the rational argument interval
lies to the left of compact support. -/
theorem controlK9RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    (δInt : Int) (n : PrimeShiftIndexL3)
    (h :
      ((((δInt : Int) : Real) / 4 +
          activeL3RationalPrimeShiftUpper n) / controlK9Ell) ≤
        (-2 : Real)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 + controlK9PrimeShift n) /
        controlK9Ell) = 0 := by
  have hb := controlK9RationalDeltaLiveRPlus_arg_bounds δInt n
  exact
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_le_neg_two
      (le_trans hb.2 h)

/-- Control plus-side `R` value is zero when the rational argument interval
lies to the right of compact support. -/
theorem controlK9RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    (δInt : Int) (n : PrimeShiftIndexL3)
    (h :
      (2 : Real) ≤
        ((((δInt : Int) : Real) / 4 +
          activeL3RationalPrimeShiftLower n) / controlK9Ell)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 + controlK9PrimeShift n) /
        controlK9Ell) = 0 := by
  have hb := controlK9RationalDeltaLiveRPlus_arg_bounds δInt n
  exact
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR9_eq_zero_of_two_le
      (le_trans h hb.1)

/-- Generated rational primary term boxes dominate the existing tight symbolic
term boxes.  This is a pure finite rational check; the analytic term hbox is
still supplied by the already-compiled tight receiver. -/
def primaryK11RationalDeltaLiveTermDominatesTight : Prop :=
  ∀ i j n,
    n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
      primaryK11PositivePartPowerTightPrimeTermRad
          activeL3PrimeWeightMid activeL3PrimeWeightRad i j n +
        |primaryK11PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n -
          primaryK11RationalDeltaLiveTermMid i j n| ≤
        primaryK11RationalDeltaLiveTermRad i j n

/-- Generated rational control term boxes dominate the existing tight symbolic
term boxes. -/
def controlK9RationalDeltaLiveTermDominatesTight : Prop :=
  ∀ i j n,
    n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
      controlK9PositivePartPowerTightPrimeTermRad
          activeL3PrimeWeightMid activeL3PrimeWeightRad i j n +
        |controlK9PositivePartPowerTightPrimeTermMid
            activeL3PrimeWeightMid i j n -
          controlK9RationalDeltaLiveTermMid i j n| ≤
        controlK9RationalDeltaLiveTermRad i j n

/-- Missing analytic bridge for the generated primary rational term boxes. -/
def primaryK11RationalDeltaLiveTermHboxBridge : Prop :=
  ∀ i j n,
    n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
      |primaryK11FinitePrimeProfileTermOfDelta
          (primaryK11Center j - primaryK11Center i) n -
        primaryK11RationalDeltaLiveTermMid i j n| ≤
          primaryK11RationalDeltaLiveTermRad i j n

/-- Missing rational center-error budget bridge for the generated primary
witnesses. -/
def primaryK11RationalDeltaLiveCenterErrorBudget : Prop :=
  ∀ i j,
    |(∑ n ∈ primaryK11LivePrimeShiftSet
        (primaryK11Center j - primaryK11Center i),
      primaryK11RationalDeltaLiveTermMid i j n) - primaryK11P i j| +
      (∑ n ∈ primaryK11LivePrimeShiftSet
        (primaryK11Center j - primaryK11Center i),
      primaryK11RationalDeltaLiveTermRad i j n) ≤ primaryK11PRadius i j

/-- Missing analytic bridge for the generated control rational term boxes. -/
def controlK9RationalDeltaLiveTermHboxBridge : Prop :=
  ∀ i j n,
    n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
      |controlK9FinitePrimeProfileTermOfDelta
          (controlK9Center j - controlK9Center i) n -
        controlK9RationalDeltaLiveTermMid i j n| ≤
          controlK9RationalDeltaLiveTermRad i j n

/-- Primary `R_minus + R_plus` factor of one finite-prime term.  This is the
next honest generated surface: the final term hbox should come from a
Lean-checked hbox for this factor and the already-separate prime weight hbox. -/
def primaryK11FinitePrimeProfileRPairOfDelta
    (δ : Real) (n : PrimeShiftIndexL3) : Real :=
  centeredBSplineR 11
      ((δ - primaryK11PrimeShift n) / primaryK11Ell) +
    centeredBSplineR 11
      ((δ + primaryK11PrimeShift n) / primaryK11Ell)

/-- Control `R_minus + R_plus` factor of one finite-prime term. -/
def controlK9FinitePrimeProfileRPairOfDelta
    (δ : Real) (n : PrimeShiftIndexL3) : Real :=
  centeredBSplineR 9
      ((δ - controlK9PrimeShift n) / controlK9Ell) +
    centeredBSplineR 9
      ((δ + controlK9PrimeShift n) / controlK9Ell)

/-- Kernel-checked primary rational hboxes for the `R_minus + R_plus` factor
on generated live shifts. -/
def primaryK11RationalDeltaLiveRPairHboxBridge
    (rPairMid rPairRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real) : Prop :=
  ∀ i j n,
    n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
      |primaryK11FinitePrimeProfileRPairOfDelta
          (primaryK11Center j - primaryK11Center i) n -
        rPairMid i j n| ≤ rPairRad i j n

/-- Kernel-checked control rational hboxes for the `R_minus + R_plus` factor
on generated live shifts. -/
def controlK9RationalDeltaLiveRPairHboxBridge
    (rPairMid rPairRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real) : Prop :=
  ∀ i j n,
    n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
      |controlK9FinitePrimeProfileRPairOfDelta
          (controlK9Center j - controlK9Center i) n -
        rPairMid i j n| ≤ rPairRad i j n

/-- Delta-compressed primary `R_minus` hbox receiver.  This is the preferred
generated surface: prove one fact per center delta and live prime shift, then
transport it to the entry-indexed receiver. -/
def primaryK11RationalDeltaLiveRMinusHboxByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n ∈ primaryK11LivePrimeShiftSet (((δInt : Int) : Real) / 4) ->
        |centeredBSplineR 11
            ((((δInt : Int) : Real) / 4 - primaryK11PrimeShift n) /
              primaryK11Ell) -
          primaryK11RationalDeltaLiveRMinusMidByDelta δInt n.1| ≤
            primaryK11RationalDeltaLiveRMinusRadByDelta δInt n.1

/-- Delta-compressed primary `R_plus` hbox receiver. -/
def primaryK11RationalDeltaLiveRPlusHboxByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n ∈ primaryK11LivePrimeShiftSet (((δInt : Int) : Real) / 4) ->
        |centeredBSplineR 11
            ((((δInt : Int) : Real) / 4 + primaryK11PrimeShift n) /
              primaryK11Ell) -
          primaryK11RationalDeltaLiveRPlusMidByDelta δInt n.1| ≤
            primaryK11RationalDeltaLiveRPlusRadByDelta δInt n.1

/-- Delta-compressed control `R_minus` hbox receiver. -/
def controlK9RationalDeltaLiveRMinusHboxByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n ∈ controlK9LivePrimeShiftSet (((δInt : Int) : Real) / 4) ->
        |centeredBSplineR 9
            ((((δInt : Int) : Real) / 4 - controlK9PrimeShift n) /
              controlK9Ell) -
          controlK9RationalDeltaLiveRMinusMidByDelta δInt n.1| ≤
            controlK9RationalDeltaLiveRMinusRadByDelta δInt n.1

/-- Delta-compressed control `R_plus` hbox receiver. -/
def controlK9RationalDeltaLiveRPlusHboxByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n ∈ controlK9LivePrimeShiftSet (((δInt : Int) : Real) / 4) ->
        |centeredBSplineR 9
            ((((δInt : Int) : Real) / 4 + controlK9PrimeShift n) /
              controlK9Ell) -
          controlK9RationalDeltaLiveRPlusMidByDelta δInt n.1| ≤
            controlK9RationalDeltaLiveRPlusRadByDelta δInt n.1

/-- Primary `R_minus` hbox restricted to the generated minus-side support.
This is the compact nonzero target for the next finite hbox generator; the
full live receiver additionally needs the corresponding outside-support
zero/exhaustion fact. -/
def primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
        δInt ->
        |centeredBSplineR 11
            ((((δInt : Int) : Real) / 4 - primaryK11PrimeShift n) /
              primaryK11Ell) -
          primaryK11RationalDeltaLiveRMinusMidByDelta δInt n.1| ≤
            primaryK11RationalDeltaLiveRMinusRadByDelta δInt n.1

/-- Primary `R_plus` hbox restricted to the generated plus-side support. -/
def primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
        δInt ->
        |centeredBSplineR 11
            ((((δInt : Int) : Real) / 4 + primaryK11PrimeShift n) /
              primaryK11Ell) -
          primaryK11RationalDeltaLiveRPlusMidByDelta δInt n.1| ≤
            primaryK11RationalDeltaLiveRPlusRadByDelta δInt n.1

/-- Control `R_minus` hbox restricted to the generated minus-side support. -/
def controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
        δInt ->
        |centeredBSplineR 9
            ((((δInt : Int) : Real) / 4 - controlK9PrimeShift n) /
              controlK9Ell) -
          controlK9RationalDeltaLiveRMinusMidByDelta δInt n.1| ≤
            controlK9RationalDeltaLiveRMinusRadByDelta δInt n.1

/-- Control `R_plus` hbox restricted to the generated plus-side support. -/
def controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
        δInt ->
        |centeredBSplineR 9
            ((((δInt : Int) : Real) / 4 + controlK9PrimeShift n) /
              controlK9Ell) -
          controlK9RationalDeltaLiveRPlusMidByDelta δInt n.1| ≤
            controlK9RationalDeltaLiveRPlusRadByDelta δInt n.1

/-- Primary `R_minus` is zero outside its generated minus-side support. -/
def primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n.1 ∉ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
        δInt ->
        centeredBSplineR 11
          ((((δInt : Int) : Real) / 4 - primaryK11PrimeShift n) /
            primaryK11Ell) = 0

/-- Primary `R_plus` is zero outside its generated plus-side support. -/
def primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n.1 ∉ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
        δInt ->
        centeredBSplineR 11
          ((((δInt : Int) : Real) / 4 + primaryK11PrimeShift n) /
            primaryK11Ell) = 0

/-- Control `R_minus` is zero outside its generated minus-side support. -/
def controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n.1 ∉ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
        δInt ->
        centeredBSplineR 9
          ((((δInt : Int) : Real) / 4 - controlK9PrimeShift n) /
            controlK9Ell) = 0

/-- Control `R_plus` is zero outside its generated plus-side support. -/
def controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      n.1 ∉ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
        δInt ->
        centeredBSplineR 9
          ((((δInt : Int) : Real) / 4 + controlK9PrimeShift n) /
            controlK9Ell) = 0

/-- Declared primary minus-side hboxes plus zero-off-declared support imply
the full live `R_minus` hbox receiver. -/
theorem primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
    (hdecl : primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta)
    (hzero : primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta) :
    primaryK11RationalDeltaLiveRMinusHboxByDelta := by
  intro δInt n hδ _hn
  by_cases hmem :
      n.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
        δInt
  · exact hdecl δInt n hδ hmem
  · have hz := hzero δInt n hδ hmem
    have hmid :
        primaryK11RationalDeltaLiveRMinusMidByDelta δInt n.1 = 0 := by
      simp [primaryK11RationalDeltaLiveRMinusMidByDelta,
        primaryK11RationalDeltaLiveRMinusMidByDeltaRat, hmem]
    have hrad :
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt n.1 = 0 := by
      simp [primaryK11RationalDeltaLiveRMinusRadByDelta,
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat, hmem]
    rw [hz, hmid, hrad]
    norm_num

/-- Declared primary plus-side hboxes plus zero-off-declared support imply
the full live `R_plus` hbox receiver. -/
theorem primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
    (hdecl : primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta)
    (hzero : primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta) :
    primaryK11RationalDeltaLiveRPlusHboxByDelta := by
  intro δInt n hδ _hn
  by_cases hmem :
      n.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
        δInt
  · exact hdecl δInt n hδ hmem
  · have hz := hzero δInt n hδ hmem
    have hmid :
        primaryK11RationalDeltaLiveRPlusMidByDelta δInt n.1 = 0 := by
      simp [primaryK11RationalDeltaLiveRPlusMidByDelta,
        primaryK11RationalDeltaLiveRPlusMidByDeltaRat, hmem]
    have hrad :
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt n.1 = 0 := by
      simp [primaryK11RationalDeltaLiveRPlusRadByDelta,
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat, hmem]
    rw [hz, hmid, hrad]
    norm_num

/-- Declared control minus-side hboxes plus zero-off-declared support imply
the full live `R_minus` hbox receiver. -/
theorem controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
    (hdecl : controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta)
    (hzero : controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta) :
    controlK9RationalDeltaLiveRMinusHboxByDelta := by
  intro δInt n hδ _hn
  by_cases hmem :
      n.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
        δInt
  · exact hdecl δInt n hδ hmem
  · have hz := hzero δInt n hδ hmem
    have hmid :
        controlK9RationalDeltaLiveRMinusMidByDelta δInt n.1 = 0 := by
      simp [controlK9RationalDeltaLiveRMinusMidByDelta,
        controlK9RationalDeltaLiveRMinusMidByDeltaRat, hmem]
    have hrad :
        controlK9RationalDeltaLiveRMinusRadByDelta δInt n.1 = 0 := by
      simp [controlK9RationalDeltaLiveRMinusRadByDelta,
        controlK9RationalDeltaLiveRMinusRadByDeltaRat, hmem]
    rw [hz, hmid, hrad]
    norm_num

/-- Declared control plus-side hboxes plus zero-off-declared support imply
the full live `R_plus` hbox receiver. -/
theorem controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
    (hdecl : controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta)
    (hzero : controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta) :
    controlK9RationalDeltaLiveRPlusHboxByDelta := by
  intro δInt n hδ _hn
  by_cases hmem :
      n.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
        δInt
  · exact hdecl δInt n hδ hmem
  · have hz := hzero δInt n hδ hmem
    have hmid :
        controlK9RationalDeltaLiveRPlusMidByDelta δInt n.1 = 0 := by
      simp [controlK9RationalDeltaLiveRPlusMidByDelta,
        controlK9RationalDeltaLiveRPlusMidByDeltaRat, hmem]
    have hrad :
        controlK9RationalDeltaLiveRPlusRadByDelta δInt n.1 = 0 := by
      simp [controlK9RationalDeltaLiveRPlusRadByDelta,
        controlK9RationalDeltaLiveRPlusRadByDeltaRat, hmem]
    rw [hz, hmid, hrad]
    norm_num

/-- A split pair hbox receiver.  This is the bridge wanted by the
piecewise-polynomial/de-Boor payload route: bound the two normalized
`centeredBSplineR` evaluations separately, then pay only the generated rational
sum budget for the selected `R_minus + R_plus` midpoint. -/
private theorem sum_pair_hbox_transfer
    {{x y xm xr ym yr mid rad : Real}}
    (hx : |x - xm| ≤ xr)
    (hy : |y - ym| ≤ yr)
    (hbudget : xr + yr + |xm + ym - mid| ≤ rad) :
    |(x + y) - mid| ≤ rad := by
  have hsplit :
      (x + y) - mid = (x - xm) + (y - ym) + (xm + ym - mid) := by
    ring
  calc
    |(x + y) - mid| =
        |(x - xm) + (y - ym) + (xm + ym - mid)| := by rw [hsplit]
    _ ≤ |(x - xm) + (y - ym)| + |xm + ym - mid| := abs_add_le _ _
    _ ≤ (|x - xm| + |y - ym|) + |xm + ym - mid| := by
          exact add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ (xr + yr) + |xm + ym - mid| := by
          have hxy : |x - xm| + |y - ym| ≤ xr + yr := add_le_add hx hy
          exact add_le_add hxy (le_refl _)
    _ = xr + yr + |xm + ym - mid| := by ring
    _ ≤ rad := hbudget

/-- Primary generated split `R` hboxes plus a rational pair-sum budget imply
the live generated `R_minus + R_plus` hbox bridge.  No dead-shift hboxes are
required because the receiver is restricted to the analytic live set. -/
theorem primaryK11RationalDeltaLiveRPairHboxBridge_of_split_R_hboxes
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hminus :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i) ->
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) -
          minusMid i j n| ≤ minusRad i j n)
    (hplus :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i) ->
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) -
          plusMid i j n| ≤ plusRad i j n)
    (hbudget :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i) ->
        minusRad i j n + plusRad i j n +
            |minusMid i j n + plusMid i j n -
              primaryK11RationalDeltaLiveRPairMid i j n| ≤
          primaryK11RationalDeltaLiveRPairRad i j n) :
    primaryK11RationalDeltaLiveRPairHboxBridge
      primaryK11RationalDeltaLiveRPairMid
      primaryK11RationalDeltaLiveRPairRad := by
  intro i j n hn
  have hpair :=
    sum_pair_hbox_transfer
      (hminus i j n hn)
      (hplus i j n hn)
      (hbudget i j n hn)
  simpa [primaryK11FinitePrimeProfileRPairOfDelta] using hpair

/-- Control generated split `R` hboxes plus a rational pair-sum budget imply
the live generated `R_minus + R_plus` hbox bridge. -/
theorem controlK9RationalDeltaLiveRPairHboxBridge_of_split_R_hboxes
    (minusMid minusRad plusMid plusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hminus :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i) ->
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) -
          minusMid i j n| ≤ minusRad i j n)
    (hplus :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i) ->
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) -
          plusMid i j n| ≤ plusRad i j n)
    (hbudget :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i) ->
        minusRad i j n + plusRad i j n +
            |minusMid i j n + plusMid i j n -
              controlK9RationalDeltaLiveRPairMid i j n| ≤
          controlK9RationalDeltaLiveRPairRad i j n) :
    controlK9RationalDeltaLiveRPairHboxBridge
      controlK9RationalDeltaLiveRPairMid
      controlK9RationalDeltaLiveRPairRad := by
  intro i j n hn
  have hpair :=
    sum_pair_hbox_transfer
      (hminus i j n hn)
      (hplus i j n hn)
      (hbudget i j n hn)
  simpa [controlK9FinitePrimeProfileRPairOfDelta] using hpair

/-- Pure rational primary product budget turning weight and `R`-pair hboxes
into the generated live term boxes. -/
def primaryK11RationalDeltaLiveTermProductBudget
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (rPairMid rPairRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real) : Prop :=
  ∀ i j n,
    n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
      (|weightMid n| + weightRad n) * rPairRad i j n +
          weightRad n * |rPairMid i j n| +
          |weightMid n * rPairMid i j n -
            primaryK11RationalDeltaLiveTermMid i j n| ≤
        primaryK11RationalDeltaLiveTermRad i j n

/-- Pure rational control product budget turning weight and `R`-pair hboxes
into the generated live term boxes. -/
def controlK9RationalDeltaLiveTermProductBudget
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (rPairMid rPairRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real) : Prop :=
  ∀ i j n,
    n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
      (|weightMid n| + weightRad n) * rPairRad i j n +
          weightRad n * |rPairMid i j n| +
          |weightMid n * rPairMid i j n -
            controlK9RationalDeltaLiveTermMid i j n| ≤
        controlK9RationalDeltaLiveTermRad i j n

private theorem rat_product_budget_to_real
    {{weightMid weightRad rPairMid rPairRad termMid termRad : Rat}}
    (h :
      (|weightMid| + weightRad) * rPairRad +
          weightRad * |rPairMid| +
          |weightMid * rPairMid - termMid| ≤ termRad) :
    (|((weightMid : Rat) : Real)| + ((weightRad : Rat) : Real)) *
          ((rPairRad : Rat) : Real) +
        ((weightRad : Rat) : Real) * |((rPairMid : Rat) : Real)| +
        |((weightMid : Rat) : Real) * ((rPairMid : Rat) : Real) -
          ((termMid : Rat) : Real)| ≤ ((termRad : Rat) : Real) := by
  exact_mod_cast h

/-- The packet-center delta always stays in the generated range. -/
private theorem coeffIndexDeltaInt_range (i j : CoeffIndex23) :
    (-22 : Int) ≤ coeffIndexDeltaInt i j ∧
      coeffIndexDeltaInt i j ≤ (22 : Int) := by
  cases i with
  | mk iv hi =>
    cases j with
    | mk jv hj =>
      simp [coeffIndexDeltaInt] at *
      omega

/-- Delta-compressed primary `R_minus` hboxes transport to the entry-indexed
split-`R` receiver. -/
theorem primaryK11RationalDeltaLiveRMinusHbox_of_by_delta
    (h : primaryK11RationalDeltaLiveRMinusHboxByDelta) :
    ∀ i j n,
      n ∈ primaryK11LivePrimeShiftSet
        (primaryK11Center j - primaryK11Center i) ->
      |centeredBSplineR 11
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell) -
        primaryK11RationalDeltaLiveRMinusMid i j n| ≤
          primaryK11RationalDeltaLiveRMinusRad i j n := by
  intro i j n hn
  have hn_delta :
      n ∈ primaryK11LivePrimeShiftSet
        (((coeffIndexDeltaInt i j : Int) : Real) / 4) := by
    simpa [primaryK11Center_sub_eq_coeffIndexDeltaInt i j] using hn
  have hdelta :=
    h (coeffIndexDeltaInt i j) n (coeffIndexDeltaInt_range i j) hn_delta
  simpa [primaryK11Center_sub_eq_coeffIndexDeltaInt i j,
    primaryK11RationalDeltaLiveRMinusMid,
    primaryK11RationalDeltaLiveRMinusRad,
    primaryK11RationalDeltaLiveRMinusMidRat,
    primaryK11RationalDeltaLiveRMinusRadRat,
    primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using hdelta

/-- Delta-compressed primary `R_plus` hboxes transport to the entry-indexed
split-`R` receiver. -/
theorem primaryK11RationalDeltaLiveRPlusHbox_of_by_delta
    (h : primaryK11RationalDeltaLiveRPlusHboxByDelta) :
    ∀ i j n,
      n ∈ primaryK11LivePrimeShiftSet
        (primaryK11Center j - primaryK11Center i) ->
      |centeredBSplineR 11
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell) -
        primaryK11RationalDeltaLiveRPlusMid i j n| ≤
          primaryK11RationalDeltaLiveRPlusRad i j n := by
  intro i j n hn
  have hn_delta :
      n ∈ primaryK11LivePrimeShiftSet
        (((coeffIndexDeltaInt i j : Int) : Real) / 4) := by
    simpa [primaryK11Center_sub_eq_coeffIndexDeltaInt i j] using hn
  have hdelta :=
    h (coeffIndexDeltaInt i j) n (coeffIndexDeltaInt_range i j) hn_delta
  simpa [primaryK11Center_sub_eq_coeffIndexDeltaInt i j,
    primaryK11RationalDeltaLiveRPlusMid,
    primaryK11RationalDeltaLiveRPlusRad,
    primaryK11RationalDeltaLiveRPlusMidRat,
    primaryK11RationalDeltaLiveRPlusRadRat,
    primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using hdelta

/-- Delta-compressed control `R_minus` hboxes transport to the entry-indexed
split-`R` receiver. -/
theorem controlK9RationalDeltaLiveRMinusHbox_of_by_delta
    (h : controlK9RationalDeltaLiveRMinusHboxByDelta) :
    ∀ i j n,
      n ∈ controlK9LivePrimeShiftSet
        (controlK9Center j - controlK9Center i) ->
      |centeredBSplineR 9
          (((controlK9Center j - controlK9Center i) -
            controlK9PrimeShift n) / controlK9Ell) -
        controlK9RationalDeltaLiveRMinusMid i j n| ≤
          controlK9RationalDeltaLiveRMinusRad i j n := by
  intro i j n hn
  have hn_delta :
      n ∈ controlK9LivePrimeShiftSet
        (((coeffIndexDeltaInt i j : Int) : Real) / 4) := by
    simpa [controlK9Center_sub_eq_coeffIndexDeltaInt i j] using hn
  have hdelta :=
    h (coeffIndexDeltaInt i j) n (coeffIndexDeltaInt_range i j) hn_delta
  simpa [controlK9Center_sub_eq_coeffIndexDeltaInt i j,
    controlK9RationalDeltaLiveRMinusMid,
    controlK9RationalDeltaLiveRMinusRad,
    controlK9RationalDeltaLiveRMinusMidRat,
    controlK9RationalDeltaLiveRMinusRadRat,
    controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using hdelta

/-- Delta-compressed control `R_plus` hboxes transport to the entry-indexed
split-`R` receiver. -/
theorem controlK9RationalDeltaLiveRPlusHbox_of_by_delta
    (h : controlK9RationalDeltaLiveRPlusHboxByDelta) :
    ∀ i j n,
      n ∈ controlK9LivePrimeShiftSet
        (controlK9Center j - controlK9Center i) ->
      |centeredBSplineR 9
          (((controlK9Center j - controlK9Center i) +
            controlK9PrimeShift n) / controlK9Ell) -
        controlK9RationalDeltaLiveRPlusMid i j n| ≤
          controlK9RationalDeltaLiveRPlusRad i j n := by
  intro i j n hn
  have hn_delta :
      n ∈ controlK9LivePrimeShiftSet
        (((coeffIndexDeltaInt i j : Int) : Real) / 4) := by
    simpa [controlK9Center_sub_eq_coeffIndexDeltaInt i j] using hn
  have hdelta :=
    h (coeffIndexDeltaInt i j) n (coeffIndexDeltaInt_range i j) hn_delta
  simpa [controlK9Center_sub_eq_coeffIndexDeltaInt i j,
    controlK9RationalDeltaLiveRPlusMid,
    controlK9RationalDeltaLiveRPlusRad,
    controlK9RationalDeltaLiveRPlusMidRat,
    controlK9RationalDeltaLiveRPlusRadRat,
    controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using hdelta

/-- Primary generated rational split-`R` budget by center delta.  This is an
exact-rational check that the separately serialized `R_minus` and `R_plus`
witnesses fit inside the generated `R_minus + R_plus` witness. -/
def primaryK11RationalDeltaLiveRPairSplitBudgetRatByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      primaryK11RationalDeltaLiveRMinusRadByDeltaRat δInt n.1 +
          primaryK11RationalDeltaLiveRPlusRadByDeltaRat δInt n.1 +
          |primaryK11RationalDeltaLiveRMinusMidByDeltaRat δInt n.1 +
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat δInt n.1 -
            primaryK11RationalDeltaLiveRPairMidByDeltaRat δInt n.1| ≤
        primaryK11RationalDeltaLiveRPairRadByDeltaRat δInt n.1

/-- Control generated rational split-`R` budget by center delta. -/
def controlK9RationalDeltaLiveRPairSplitBudgetRatByDelta : Prop :=
  ∀ δInt (n : PrimeShiftIndexL3),
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      controlK9RationalDeltaLiveRMinusRadByDeltaRat δInt n.1 +
          controlK9RationalDeltaLiveRPlusRadByDeltaRat δInt n.1 +
          |controlK9RationalDeltaLiveRMinusMidByDeltaRat δInt n.1 +
            controlK9RationalDeltaLiveRPlusMidByDeltaRat δInt n.1 -
            controlK9RationalDeltaLiveRPairMidByDeltaRat δInt n.1| ≤
        controlK9RationalDeltaLiveRPairRadByDeltaRat δInt n.1

private theorem rat_pair_sum_budget_to_real
    {{minusMid minusRad plusMid plusRad rPairMid rPairRad : Rat}}
    (h :
      minusRad + plusRad + |minusMid + plusMid - rPairMid| ≤ rPairRad) :
    ((minusRad : Rat) : Real) + ((plusRad : Rat) : Real) +
        |((minusMid : Rat) : Real) + ((plusMid : Rat) : Real) -
          ((rPairMid : Rat) : Real)| ≤ ((rPairRad : Rat) : Real) := by
  exact_mod_cast h

{emit_rpair_split_budget_generated_split("primaryK11")}

{emit_rpair_split_budget_generated_split("controlK9")}

/-- Transfer the generated primary rational split-`R` pair budget to the
real-valued receiver surface. -/
theorem primaryK11RationalDeltaLiveRPairSplitBudget_generated :
    ∀ i j n,
      n ∈ primaryK11LivePrimeShiftSet
        (primaryK11Center j - primaryK11Center i) ->
      primaryK11RationalDeltaLiveRMinusRad i j n +
          primaryK11RationalDeltaLiveRPlusRad i j n +
          |primaryK11RationalDeltaLiveRMinusMid i j n +
            primaryK11RationalDeltaLiveRPlusMid i j n -
            primaryK11RationalDeltaLiveRPairMid i j n| ≤
        primaryK11RationalDeltaLiveRPairRad i j n := by
  intro i j n _hn
  have hrat :=
    primaryK11RationalDeltaLiveRPairSplitBudgetRatByDelta_generated_split
      (coeffIndexDeltaInt i j) n (coeffIndexDeltaInt_range i j)
  have hreal := rat_pair_sum_budget_to_real hrat
  simpa [primaryK11RationalDeltaLiveRMinusMid,
    primaryK11RationalDeltaLiveRMinusRad,
    primaryK11RationalDeltaLiveRPlusMid,
    primaryK11RationalDeltaLiveRPlusRad,
    primaryK11RationalDeltaLiveRPairMid,
    primaryK11RationalDeltaLiveRPairRad,
    primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta,
    primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta,
    primaryK11RationalDeltaLiveRPairMidByDelta,
    primaryK11RationalDeltaLiveRPairRadByDelta] using hreal

/-- Transfer the generated control rational split-`R` pair budget to the
real-valued receiver surface. -/
theorem controlK9RationalDeltaLiveRPairSplitBudget_generated :
    ∀ i j n,
      n ∈ controlK9LivePrimeShiftSet
        (controlK9Center j - controlK9Center i) ->
      controlK9RationalDeltaLiveRMinusRad i j n +
          controlK9RationalDeltaLiveRPlusRad i j n +
          |controlK9RationalDeltaLiveRMinusMid i j n +
            controlK9RationalDeltaLiveRPlusMid i j n -
            controlK9RationalDeltaLiveRPairMid i j n| ≤
        controlK9RationalDeltaLiveRPairRad i j n := by
  intro i j n _hn
  have hrat :=
    controlK9RationalDeltaLiveRPairSplitBudgetRatByDelta_generated_split
      (coeffIndexDeltaInt i j) n (coeffIndexDeltaInt_range i j)
  have hreal := rat_pair_sum_budget_to_real hrat
  simpa [controlK9RationalDeltaLiveRMinusMid,
    controlK9RationalDeltaLiveRMinusRad,
    controlK9RationalDeltaLiveRPlusMid,
    controlK9RationalDeltaLiveRPlusRad,
    controlK9RationalDeltaLiveRPairMid,
    controlK9RationalDeltaLiveRPairRad,
    controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta,
    controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta,
    controlK9RationalDeltaLiveRPairMidByDelta,
    controlK9RationalDeltaLiveRPairRadByDelta] using hreal

/-- Primary generated split-`R` hboxes imply the generated `R_minus + R_plus`
hbox bridge.  The rational pair-sum budget is already kernel-checked by the
generated split-budget theorem above. -/
theorem primaryK11RationalDeltaLiveRPairHboxBridge_of_generated_split_R_hboxes
    (hminus :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i) ->
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) -
          primaryK11RationalDeltaLiveRMinusMid i j n| ≤
            primaryK11RationalDeltaLiveRMinusRad i j n)
    (hplus :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i) ->
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) -
          primaryK11RationalDeltaLiveRPlusMid i j n| ≤
            primaryK11RationalDeltaLiveRPlusRad i j n) :
    primaryK11RationalDeltaLiveRPairHboxBridge
      primaryK11RationalDeltaLiveRPairMid
      primaryK11RationalDeltaLiveRPairRad :=
  primaryK11RationalDeltaLiveRPairHboxBridge_of_split_R_hboxes
    primaryK11RationalDeltaLiveRMinusMid
    primaryK11RationalDeltaLiveRMinusRad
    primaryK11RationalDeltaLiveRPlusMid
    primaryK11RationalDeltaLiveRPlusRad
    hminus
    hplus
    primaryK11RationalDeltaLiveRPairSplitBudget_generated

/-- Control generated split-`R` hboxes imply the generated `R_minus + R_plus`
hbox bridge. -/
theorem controlK9RationalDeltaLiveRPairHboxBridge_of_generated_split_R_hboxes
    (hminus :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i) ->
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) -
          controlK9RationalDeltaLiveRMinusMid i j n| ≤
            controlK9RationalDeltaLiveRMinusRad i j n)
    (hplus :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i) ->
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) -
          controlK9RationalDeltaLiveRPlusMid i j n| ≤
            controlK9RationalDeltaLiveRPlusRad i j n) :
    controlK9RationalDeltaLiveRPairHboxBridge
      controlK9RationalDeltaLiveRPairMid
      controlK9RationalDeltaLiveRPairRad :=
  controlK9RationalDeltaLiveRPairHboxBridge_of_split_R_hboxes
    controlK9RationalDeltaLiveRMinusMid
    controlK9RationalDeltaLiveRMinusRad
    controlK9RationalDeltaLiveRPlusMid
    controlK9RationalDeltaLiveRPlusRad
    hminus
    hplus
    controlK9RationalDeltaLiveRPairSplitBudget_generated

/-- Primary delta-compressed split-`R` hboxes imply the generated `R`-pair
bridge.  This is the non-entry-crawl receiver for the next arithmetic payload. -/
theorem primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
    (hminus : primaryK11RationalDeltaLiveRMinusHboxByDelta)
    (hplus : primaryK11RationalDeltaLiveRPlusHboxByDelta) :
    primaryK11RationalDeltaLiveRPairHboxBridge
      primaryK11RationalDeltaLiveRPairMid
      primaryK11RationalDeltaLiveRPairRad :=
  primaryK11RationalDeltaLiveRPairHboxBridge_of_generated_split_R_hboxes
    (primaryK11RationalDeltaLiveRMinusHbox_of_by_delta hminus)
    (primaryK11RationalDeltaLiveRPlusHbox_of_by_delta hplus)

/-- Control delta-compressed split-`R` hboxes imply the generated `R`-pair
bridge. -/
theorem controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
    (hminus : controlK9RationalDeltaLiveRMinusHboxByDelta)
    (hplus : controlK9RationalDeltaLiveRPlusHboxByDelta) :
    controlK9RationalDeltaLiveRPairHboxBridge
      controlK9RationalDeltaLiveRPairMid
      controlK9RationalDeltaLiveRPairRad :=
  controlK9RationalDeltaLiveRPairHboxBridge_of_generated_split_R_hboxes
    (controlK9RationalDeltaLiveRMinusHbox_of_by_delta hminus)
    (controlK9RationalDeltaLiveRPlusHbox_of_by_delta hplus)

/-- Primary generated rational product-budget check by center delta.  Outside
the declared generated support, the emitted term and `R`-pair witnesses are
zero, so this all-shift version can feed the analytic live-set receiver. -/
def primaryK11RationalDeltaLiveTermProductBudgetRatByDelta : Prop :=
  ∀ δInt n,
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      (|activeL3RationalPrimeWeightMidRat n| +
          activeL3RationalPrimeWeightRadRat n) *
          primaryK11RationalDeltaLiveRPairRadByDeltaRat δInt n.1 +
        activeL3RationalPrimeWeightRadRat n *
          |primaryK11RationalDeltaLiveRPairMidByDeltaRat δInt n.1| +
        |activeL3RationalPrimeWeightMidRat n *
            primaryK11RationalDeltaLiveRPairMidByDeltaRat δInt n.1 -
          primaryK11RationalDeltaLiveTermMidByDeltaRat δInt n.1| ≤
        primaryK11RationalDeltaLiveTermRadByDeltaRat δInt n.1

/-- Control generated rational product-budget check by center delta. -/
def controlK9RationalDeltaLiveTermProductBudgetRatByDelta : Prop :=
  ∀ δInt n,
    (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int) ->
      (|activeL3RationalPrimeWeightMidRat n| +
          activeL3RationalPrimeWeightRadRat n) *
          controlK9RationalDeltaLiveRPairRadByDeltaRat δInt n.1 +
        activeL3RationalPrimeWeightRadRat n *
          |controlK9RationalDeltaLiveRPairMidByDeltaRat δInt n.1| +
        |activeL3RationalPrimeWeightMidRat n *
            controlK9RationalDeltaLiveRPairMidByDeltaRat δInt n.1 -
          controlK9RationalDeltaLiveTermMidByDeltaRat δInt n.1| ≤
        controlK9RationalDeltaLiveTermRadByDeltaRat δInt n.1

{emit_product_budget_generated_split("primaryK11")}

{emit_product_budget_generated_split("controlK9")}

/-- Transfer the generated primary rational product budget to the real-valued
receiver surface. -/
theorem primaryK11RationalDeltaLiveTermProductBudget_generated :
    primaryK11RationalDeltaLiveTermProductBudget
      activeL3RationalPrimeWeightMid
      activeL3RationalPrimeWeightRad
      primaryK11RationalDeltaLiveRPairMid
      primaryK11RationalDeltaLiveRPairRad := by
  intro i j n _hn
  have hrat :=
    primaryK11RationalDeltaLiveTermProductBudgetRatByDelta_generated_split
      (coeffIndexDeltaInt i j) n (coeffIndexDeltaInt_range i j)
  have hreal := rat_product_budget_to_real hrat
  simpa [activeL3RationalPrimeWeightMid,
    activeL3RationalPrimeWeightRad,
    primaryK11RationalDeltaLiveRPairMid,
    primaryK11RationalDeltaLiveRPairRad,
    primaryK11RationalDeltaLiveRPairMidByDelta,
    primaryK11RationalDeltaLiveRPairRadByDelta,
    primaryK11RationalDeltaLiveTermMid,
    primaryK11RationalDeltaLiveTermRad,
    primaryK11RationalDeltaLiveTermMidByDelta,
    primaryK11RationalDeltaLiveTermRadByDelta] using hreal

/-- Transfer the generated control rational product budget to the real-valued
receiver surface. -/
theorem controlK9RationalDeltaLiveTermProductBudget_generated :
    controlK9RationalDeltaLiveTermProductBudget
      activeL3RationalPrimeWeightMid
      activeL3RationalPrimeWeightRad
      controlK9RationalDeltaLiveRPairMid
      controlK9RationalDeltaLiveRPairRad := by
  intro i j n _hn
  have hrat :=
    controlK9RationalDeltaLiveTermProductBudgetRatByDelta_generated_split
      (coeffIndexDeltaInt i j) n (coeffIndexDeltaInt_range i j)
  have hreal := rat_product_budget_to_real hrat
  simpa [activeL3RationalPrimeWeightMid,
    activeL3RationalPrimeWeightRad,
    controlK9RationalDeltaLiveRPairMid,
    controlK9RationalDeltaLiveRPairRad,
    controlK9RationalDeltaLiveRPairMidByDelta,
    controlK9RationalDeltaLiveRPairRadByDelta,
    controlK9RationalDeltaLiveTermMid,
    controlK9RationalDeltaLiveTermRad,
    controlK9RationalDeltaLiveTermMidByDelta,
    controlK9RationalDeltaLiveTermRadByDelta] using hreal

/-- Primary option-B bridge: no symbolic `PositivePartPowerTightPrimeTermMid`
is needed.  Weight hboxes, `R`-pair hboxes, and rational product budgets imply
the generated live term hboxes. -/
theorem primaryK11RationalDeltaLiveTermHboxBridge_of_weight_and_rpair_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (rPairMid rPairRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n, |primaryK11PrimeWeight n - weightMid n| ≤ weightRad n)
    (hrpair :
      primaryK11RationalDeltaLiveRPairHboxBridge rPairMid rPairRad)
    (hbudget :
      primaryK11RationalDeltaLiveTermProductBudget
        weightMid weightRad rPairMid rPairRad) :
    primaryK11RationalDeltaLiveTermHboxBridge := by
  intro i j n hn
  have hterm :=
    rational_product_hbox_transfer
      (w := primaryK11PrimeWeight n)
      (wm := weightMid n)
      (wr := weightRad n)
      (r := primaryK11FinitePrimeProfileRPairOfDelta
        (primaryK11Center j - primaryK11Center i) n)
      (rm := rPairMid i j n)
      (rr := rPairRad i j n)
      (mid := primaryK11RationalDeltaLiveTermMid i j n)
      (rad := primaryK11RationalDeltaLiveTermRad i j n)
      (hweight n) (hrpair i j n hn) (hbudget i j n hn)
  simpa [primaryK11FinitePrimeProfileTermOfDelta,
    primaryK11FinitePrimeProfileRPairOfDelta] using hterm

/-- Control option-B bridge: no symbolic `PositivePartPowerTightPrimeTermMid`
is needed. -/
theorem controlK9RationalDeltaLiveTermHboxBridge_of_weight_and_rpair_hboxes
    (weightMid weightRad : PrimeShiftIndexL3 -> Real)
    (rPairMid rPairRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (hweight :
      ∀ n, |controlK9PrimeWeight n - weightMid n| ≤ weightRad n)
    (hrpair :
      controlK9RationalDeltaLiveRPairHboxBridge rPairMid rPairRad)
    (hbudget :
      controlK9RationalDeltaLiveTermProductBudget
        weightMid weightRad rPairMid rPairRad) :
    controlK9RationalDeltaLiveTermHboxBridge := by
  intro i j n hn
  have hterm :=
    rational_product_hbox_transfer
      (w := controlK9PrimeWeight n)
      (wm := weightMid n)
      (wr := weightRad n)
      (r := controlK9FinitePrimeProfileRPairOfDelta
        (controlK9Center j - controlK9Center i) n)
      (rm := rPairMid i j n)
      (rr := rPairRad i j n)
      (mid := controlK9RationalDeltaLiveTermMid i j n)
      (rad := controlK9RationalDeltaLiveTermRad i j n)
      (hweight n) (hrpair i j n hn) (hbudget i j n hn)
  simpa [controlK9FinitePrimeProfileTermOfDelta,
    controlK9FinitePrimeProfileRPairOfDelta] using hterm

/-- Primary generated rational product budgets reduce the remaining term-hbox
bridge to two analytic factor hboxes: prime weight and `R`-pair. -/
theorem primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
    (hweight :
      ∀ n,
        |primaryK11PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
          activeL3RationalPrimeWeightRad n)
    (hrpair :
      primaryK11RationalDeltaLiveRPairHboxBridge
        primaryK11RationalDeltaLiveRPairMid
        primaryK11RationalDeltaLiveRPairRad) :
    primaryK11RationalDeltaLiveTermHboxBridge := by
  exact
    primaryK11RationalDeltaLiveTermHboxBridge_of_weight_and_rpair_hboxes
      activeL3RationalPrimeWeightMid
      activeL3RationalPrimeWeightRad
      primaryK11RationalDeltaLiveRPairMid
      primaryK11RationalDeltaLiveRPairRad
      hweight
      hrpair
      primaryK11RationalDeltaLiveTermProductBudget_generated

/-- Control generated rational product budgets reduce the remaining term-hbox
bridge to two analytic factor hboxes: prime weight and `R`-pair. -/
theorem controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
    (hweight :
      ∀ n,
        |controlK9PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
          activeL3RationalPrimeWeightRad n)
    (hrpair :
      controlK9RationalDeltaLiveRPairHboxBridge
        controlK9RationalDeltaLiveRPairMid
        controlK9RationalDeltaLiveRPairRad) :
    controlK9RationalDeltaLiveTermHboxBridge := by
  exact
    controlK9RationalDeltaLiveTermHboxBridge_of_weight_and_rpair_hboxes
      activeL3RationalPrimeWeightMid
      activeL3RationalPrimeWeightRad
      controlK9RationalDeltaLiveRPairMid
      controlK9RationalDeltaLiveRPairRad
      hweight
      hrpair
      controlK9RationalDeltaLiveTermProductBudget_generated

/-- Rational primary term domination transfers the existing tight symbolic
term hbox to the generated rational witnesses. -/
theorem primaryK11RationalDeltaLiveTermHboxBridge_of_tight_domination
    (hdom : primaryK11RationalDeltaLiveTermDominatesTight) :
    primaryK11RationalDeltaLiveTermHboxBridge := by
  have hweight :
      ∀ n,
        |primaryK11PrimeWeight n - activeL3PrimeWeightMid n| ≤
          activeL3PrimeWeightRad n := by
    exact
      primaryK11PrimeWeight_hbox_of_log_exp_factor_hboxes
        activeL3PrimeLogMid
        activeL3PrimeLogRad
        activeL3PrimeExpMid
        activeL3PrimeExpRad
        activeL3PrimeWeightMid
        activeL3PrimeWeightRad
        activeL3PrimeLog_hbox_of_tight_payload
        activeL3PrimeExp_exact_hbox
        activeL3PrimeWeight_mid_eq
        activeL3PrimeWeight_rad_bound
  have htight :=
    primaryK11PositivePartPowerTightFinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
      activeL3PrimeWeightMid activeL3PrimeWeightRad hweight
  intro i j n hn
  have htight_delta :
      |primaryK11FinitePrimeProfileTermOfDelta
          (primaryK11Center j - primaryK11Center i) n -
        primaryK11PositivePartPowerTightPrimeTermMid
          activeL3PrimeWeightMid i j n| ≤
        primaryK11PositivePartPowerTightPrimeTermRad
          activeL3PrimeWeightMid activeL3PrimeWeightRad i j n := by
    simpa [← primaryK11FinitePrimeProfileTerm_eq_termOfDelta i j n] using
      htight i j n
  exact rational_hbox_transfer htight_delta (hdom i j n hn)

/-- Rational control term domination transfers the existing tight symbolic
term hbox to the generated rational witnesses. -/
theorem controlK9RationalDeltaLiveTermHboxBridge_of_tight_domination
    (hdom : controlK9RationalDeltaLiveTermDominatesTight) :
    controlK9RationalDeltaLiveTermHboxBridge := by
  have hweight :
      ∀ n,
        |controlK9PrimeWeight n - activeL3PrimeWeightMid n| ≤
          activeL3PrimeWeightRad n := by
    exact
      controlK9PrimeWeight_hbox_of_log_exp_factor_hboxes
        activeL3PrimeLogMid
        activeL3PrimeLogRad
        activeL3PrimeExpMid
        activeL3PrimeExpRad
        activeL3PrimeWeightMid
        activeL3PrimeWeightRad
        activeL3PrimeLog_hbox_of_tight_payload
        activeL3PrimeExp_exact_hbox
        activeL3PrimeWeight_mid_eq
        activeL3PrimeWeight_rad_bound
  have htight :=
    controlK9PositivePartPowerTightFinitePrimeProfileTerm_hbox_of_tight_R_and_weight_hboxes
      activeL3PrimeWeightMid activeL3PrimeWeightRad hweight
  intro i j n hn
  have htight_delta :
      |controlK9FinitePrimeProfileTermOfDelta
          (controlK9Center j - controlK9Center i) n -
        controlK9PositivePartPowerTightPrimeTermMid
          activeL3PrimeWeightMid i j n| ≤
        controlK9PositivePartPowerTightPrimeTermRad
          activeL3PrimeWeightMid activeL3PrimeWeightRad i j n := by
    simpa [← controlK9FinitePrimeProfileTerm_eq_termOfDelta i j n] using
      htight i j n
  exact rational_hbox_transfer htight_delta (hdom i j n hn)

/-- Missing rational center-error budget bridge for the generated control
witnesses. -/
def controlK9RationalDeltaLiveCenterErrorBudget : Prop :=
  ∀ i j,
    |(∑ n ∈ controlK9LivePrimeShiftSet
        (controlK9Center j - controlK9Center i),
      controlK9RationalDeltaLiveTermMid i j n) - controlK9P i j| +
      (∑ n ∈ controlK9LivePrimeShiftSet
        (controlK9Center j - controlK9Center i),
      controlK9RationalDeltaLiveTermRad i j n) ≤ controlK9PRadius i j

/-- Generated primary midpoint witnesses are zero outside the analytic live
set.  The generator can prove this with only nonzero-term live-membership
facts; no dead-shift hboxes are needed. -/
def primaryK11RationalDeltaLiveTermMidZeroOffLive : Prop :=
  ∀ i j n,
    n ∉ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
      primaryK11RationalDeltaLiveTermMid i j n = 0

/-- Every nonzero generated primary midpoint witness is analytically live.
This is the finite generated fact preferred over dead-shift hboxes. -/
def primaryK11RationalDeltaLiveTermMidNonzeroLive : Prop :=
  ∀ i j n,
    primaryK11RationalDeltaLiveTermMid i j n ≠ 0 ->
      n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i)

/-- Declared-support primary facts imply midpoint nonzero-live facts. -/
theorem primaryK11RationalDeltaLiveTermMidNonzeroLive_of_declared_subset
    (hsubset : primaryK11RationalDeltaLiveDeclaredNonzeroSubsetLive) :
    primaryK11RationalDeltaLiveTermMidNonzeroLive := by
  intro i j n hne
  simpa [primaryK11Center_sub_eq_coeffIndexDeltaInt] using
    hsubset (coeffIndexDeltaInt i j) n
      (primaryK11RationalDeltaLiveTermMid_declared_of_ne hne)

/-- Nonzero-live primary midpoint facts imply the zero-off-live receiver
contract by contraposition. -/
theorem primaryK11RationalDeltaLiveTermMidZeroOffLive_of_nonzero_live
    (hlive : primaryK11RationalDeltaLiveTermMidNonzeroLive) :
    primaryK11RationalDeltaLiveTermMidZeroOffLive := by
  intro i j n hn
  by_contra hne
  exact hn (hlive i j n hne)

/-- Generated primary radius witnesses are zero outside the analytic live set. -/
def primaryK11RationalDeltaLiveTermRadZeroOffLive : Prop :=
  ∀ i j n,
    n ∉ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i) ->
      primaryK11RationalDeltaLiveTermRad i j n = 0

/-- Every nonzero generated primary radius witness is analytically live. -/
def primaryK11RationalDeltaLiveTermRadNonzeroLive : Prop :=
  ∀ i j n,
    primaryK11RationalDeltaLiveTermRad i j n ≠ 0 ->
      n ∈ primaryK11LivePrimeShiftSet (primaryK11Center j - primaryK11Center i)

/-- Declared-support primary facts imply radius nonzero-live facts. -/
theorem primaryK11RationalDeltaLiveTermRadNonzeroLive_of_declared_subset
    (hsubset : primaryK11RationalDeltaLiveDeclaredNonzeroSubsetLive) :
    primaryK11RationalDeltaLiveTermRadNonzeroLive := by
  intro i j n hne
  simpa [primaryK11Center_sub_eq_coeffIndexDeltaInt] using
    hsubset (coeffIndexDeltaInt i j) n
      (primaryK11RationalDeltaLiveTermRad_declared_of_ne hne)

/-- Nonzero-live primary radius facts imply the zero-off-live receiver
contract by contraposition. -/
theorem primaryK11RationalDeltaLiveTermRadZeroOffLive_of_nonzero_live
    (hlive : primaryK11RationalDeltaLiveTermRadNonzeroLive) :
    primaryK11RationalDeltaLiveTermRadZeroOffLive := by
  intro i j n hn
  by_contra hne
  exact hn (hlive i j n hne)

private theorem rat_sum_cast_real
    {{α : Type*}} [Fintype α] (f : α -> Rat) :
    (((∑ x : α, f x) : Rat) : Real) =
      ∑ x : α, ((f x : Rat) : Real) := by
  exact_mod_cast rfl

private theorem rat_center_error_budget_to_real
    {{midSum target radSum radius : Rat}}
    (h : |midSum - target| + radSum ≤ radius) :
    |((midSum : Rat) : Real) - ((target : Rat) : Real)| +
      ((radSum : Rat) : Real) ≤ ((radius : Rat) : Real) := by
  exact_mod_cast h

/-- Primary all-shift rational center-error budget over `Rat`.  This keeps
the finite generated arithmetic check out of huge `Real` normalization. -/
def primaryK11RationalDeltaLiveAllShiftCenterErrorBudgetRat : Prop :=
  ∀ i j,
    |(∑ n : PrimeShiftIndexL3,
      primaryK11RationalDeltaLiveTermMidRat i j n) - primaryK11PRat i j| +
      (∑ n : PrimeShiftIndexL3,
        primaryK11RationalDeltaLiveTermRadRat i j n) ≤ primaryK11PRadiusRat i j

/-- Primary all-shift rational center-error budget.  This is the preferred
finite generated arithmetic check: the live-set sums are recovered from it by
zero-off-live facts. -/
def primaryK11RationalDeltaLiveAllShiftCenterErrorBudget : Prop :=
  ∀ i j,
    |(∑ n : PrimeShiftIndexL3,
      primaryK11RationalDeltaLiveTermMid i j n) - primaryK11P i j| +
      (∑ n : PrimeShiftIndexL3,
        primaryK11RationalDeltaLiveTermRad i j n) ≤ primaryK11PRadius i j

/-- Generated primary all-shift center-error budget, checked as exact rational
arithmetic. -/
theorem primaryK11RationalDeltaLiveAllShiftCenterErrorBudgetRat_generated :
    primaryK11RationalDeltaLiveAllShiftCenterErrorBudgetRat := by
  intro i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- Exact rational budget facts transfer to the real-valued receiver
contract. -/
theorem primaryK11RationalDeltaLiveAllShiftCenterErrorBudget_of_rat
    (h : primaryK11RationalDeltaLiveAllShiftCenterErrorBudgetRat) :
    primaryK11RationalDeltaLiveAllShiftCenterErrorBudget := by
  intro i j
  have hrat := h i j
  have hreal :=
    rat_center_error_budget_to_real
      (midSum := ∑ n : PrimeShiftIndexL3,
        primaryK11RationalDeltaLiveTermMidRat i j n)
      (target := primaryK11PRat i j)
      (radSum := ∑ n : PrimeShiftIndexL3,
        primaryK11RationalDeltaLiveTermRadRat i j n)
      (radius := primaryK11PRadiusRat i j)
      hrat
  simpa [primaryK11RationalDeltaLiveAllShiftCenterErrorBudget,
    primaryK11RationalDeltaLiveTermMid,
    primaryK11RationalDeltaLiveTermRad,
    primaryK11P, primaryK11PRadius, rat_sum_cast_real] using hreal

/-- Generated primary all-shift center-error budget, transferred to the
real-valued receiver contract. -/
theorem primaryK11RationalDeltaLiveAllShiftCenterErrorBudget_generated :
    primaryK11RationalDeltaLiveAllShiftCenterErrorBudget :=
  primaryK11RationalDeltaLiveAllShiftCenterErrorBudget_of_rat
    primaryK11RationalDeltaLiveAllShiftCenterErrorBudgetRat_generated

/-- Generated control midpoint witnesses are zero outside the analytic live
set. -/
def controlK9RationalDeltaLiveTermMidZeroOffLive : Prop :=
  ∀ i j n,
    n ∉ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
      controlK9RationalDeltaLiveTermMid i j n = 0

/-- Every nonzero generated control midpoint witness is analytically live. -/
def controlK9RationalDeltaLiveTermMidNonzeroLive : Prop :=
  ∀ i j n,
    controlK9RationalDeltaLiveTermMid i j n ≠ 0 ->
      n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i)

/-- Declared-support control facts imply midpoint nonzero-live facts. -/
theorem controlK9RationalDeltaLiveTermMidNonzeroLive_of_declared_subset
    (hsubset : controlK9RationalDeltaLiveDeclaredNonzeroSubsetLive) :
    controlK9RationalDeltaLiveTermMidNonzeroLive := by
  intro i j n hne
  simpa [controlK9Center_sub_eq_coeffIndexDeltaInt] using
    hsubset (coeffIndexDeltaInt i j) n
      (controlK9RationalDeltaLiveTermMid_declared_of_ne hne)

/-- Nonzero-live control midpoint facts imply the zero-off-live receiver
contract by contraposition. -/
theorem controlK9RationalDeltaLiveTermMidZeroOffLive_of_nonzero_live
    (hlive : controlK9RationalDeltaLiveTermMidNonzeroLive) :
    controlK9RationalDeltaLiveTermMidZeroOffLive := by
  intro i j n hn
  by_contra hne
  exact hn (hlive i j n hne)

/-- Generated control radius witnesses are zero outside the analytic live set. -/
def controlK9RationalDeltaLiveTermRadZeroOffLive : Prop :=
  ∀ i j n,
    n ∉ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i) ->
      controlK9RationalDeltaLiveTermRad i j n = 0

/-- Every nonzero generated control radius witness is analytically live. -/
def controlK9RationalDeltaLiveTermRadNonzeroLive : Prop :=
  ∀ i j n,
    controlK9RationalDeltaLiveTermRad i j n ≠ 0 ->
      n ∈ controlK9LivePrimeShiftSet (controlK9Center j - controlK9Center i)

/-- Declared-support control facts imply radius nonzero-live facts. -/
theorem controlK9RationalDeltaLiveTermRadNonzeroLive_of_declared_subset
    (hsubset : controlK9RationalDeltaLiveDeclaredNonzeroSubsetLive) :
    controlK9RationalDeltaLiveTermRadNonzeroLive := by
  intro i j n hne
  simpa [controlK9Center_sub_eq_coeffIndexDeltaInt] using
    hsubset (coeffIndexDeltaInt i j) n
      (controlK9RationalDeltaLiveTermRad_declared_of_ne hne)

/-- Nonzero-live control radius facts imply the zero-off-live receiver
contract by contraposition. -/
theorem controlK9RationalDeltaLiveTermRadZeroOffLive_of_nonzero_live
    (hlive : controlK9RationalDeltaLiveTermRadNonzeroLive) :
    controlK9RationalDeltaLiveTermRadZeroOffLive := by
  intro i j n hn
  by_contra hne
  exact hn (hlive i j n hne)

/-- Control all-shift rational center-error budget over `Rat`. -/
def controlK9RationalDeltaLiveAllShiftCenterErrorBudgetRat : Prop :=
  ∀ i j,
    |(∑ n : PrimeShiftIndexL3,
      controlK9RationalDeltaLiveTermMidRat i j n) - controlK9PRat i j| +
      (∑ n : PrimeShiftIndexL3,
        controlK9RationalDeltaLiveTermRadRat i j n) ≤ controlK9PRadiusRat i j

/-- Control all-shift rational center-error budget. -/
def controlK9RationalDeltaLiveAllShiftCenterErrorBudget : Prop :=
  ∀ i j,
    |(∑ n : PrimeShiftIndexL3,
      controlK9RationalDeltaLiveTermMid i j n) - controlK9P i j| +
      (∑ n : PrimeShiftIndexL3,
        controlK9RationalDeltaLiveTermRad i j n) ≤ controlK9PRadius i j

/-- Generated control all-shift center-error budget, checked as exact rational
arithmetic. -/
theorem controlK9RationalDeltaLiveAllShiftCenterErrorBudgetRat_generated :
    controlK9RationalDeltaLiveAllShiftCenterErrorBudgetRat := by
  intro i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- Exact rational budget facts transfer to the real-valued control receiver
contract. -/
theorem controlK9RationalDeltaLiveAllShiftCenterErrorBudget_of_rat
    (h : controlK9RationalDeltaLiveAllShiftCenterErrorBudgetRat) :
    controlK9RationalDeltaLiveAllShiftCenterErrorBudget := by
  intro i j
  have hrat := h i j
  have hreal :=
    rat_center_error_budget_to_real
      (midSum := ∑ n : PrimeShiftIndexL3,
        controlK9RationalDeltaLiveTermMidRat i j n)
      (target := controlK9PRat i j)
      (radSum := ∑ n : PrimeShiftIndexL3,
        controlK9RationalDeltaLiveTermRadRat i j n)
      (radius := controlK9PRadiusRat i j)
      hrat
  simpa [controlK9RationalDeltaLiveAllShiftCenterErrorBudget,
    controlK9RationalDeltaLiveTermMid,
    controlK9RationalDeltaLiveTermRad,
    controlK9P, controlK9PRadius, rat_sum_cast_real] using hreal

/-- Generated control all-shift center-error budget, transferred to the
real-valued receiver contract. -/
theorem controlK9RationalDeltaLiveAllShiftCenterErrorBudget_generated :
    controlK9RationalDeltaLiveAllShiftCenterErrorBudget :=
  controlK9RationalDeltaLiveAllShiftCenterErrorBudget_of_rat
    controlK9RationalDeltaLiveAllShiftCenterErrorBudgetRat_generated

private theorem live_sum_eq_univ_sum_of_zero_off_live
    {{α : Type*}} [DecidableEq α] [Fintype α] (live : Finset α) (f : α -> Real)
    (hzero : ∀ n, n ∉ live -> f n = 0) :
    (∑ n ∈ live, f n) = ∑ n : α, f n := by
  classical
  exact Finset.sum_subset
    (s₁ := live)
    (s₂ := Finset.univ)
    (by intro n _; exact Finset.mem_univ n)
    (by intro n _ hn; exact hzero n hn)

/-- The generated all-shift primary budget implies the receiver's live-set
budget once the rational witnesses are zero outside the live set. -/
theorem primaryK11RationalDeltaLiveCenterErrorBudget_of_allShift_budget
    (hmid_zero : primaryK11RationalDeltaLiveTermMidZeroOffLive)
    (hrad_zero : primaryK11RationalDeltaLiveTermRadZeroOffLive)
    (hall : primaryK11RationalDeltaLiveAllShiftCenterErrorBudget) :
    primaryK11RationalDeltaLiveCenterErrorBudget := by
  intro i j
  let live := primaryK11LivePrimeShiftSet
    (primaryK11Center j - primaryK11Center i)
  have hmid :
      (∑ n ∈ live, primaryK11RationalDeltaLiveTermMid i j n) =
        ∑ n : PrimeShiftIndexL3, primaryK11RationalDeltaLiveTermMid i j n := by
    exact live_sum_eq_univ_sum_of_zero_off_live live
      (primaryK11RationalDeltaLiveTermMid i j)
      (fun n hn => hmid_zero i j n (by simpa [live] using hn))
  have hrad :
      (∑ n ∈ live, primaryK11RationalDeltaLiveTermRad i j n) =
        ∑ n : PrimeShiftIndexL3, primaryK11RationalDeltaLiveTermRad i j n := by
    exact live_sum_eq_univ_sum_of_zero_off_live live
      (primaryK11RationalDeltaLiveTermRad i j)
      (fun n hn => hrad_zero i j n (by simpa [live] using hn))
  simpa [primaryK11RationalDeltaLiveAllShiftCenterErrorBudget,
    primaryK11RationalDeltaLiveCenterErrorBudget, live, hmid, hrad] using
    hall i j

/-- The generated all-shift control budget implies the receiver's live-set
budget once the rational witnesses are zero outside the live set. -/
theorem controlK9RationalDeltaLiveCenterErrorBudget_of_allShift_budget
    (hmid_zero : controlK9RationalDeltaLiveTermMidZeroOffLive)
    (hrad_zero : controlK9RationalDeltaLiveTermRadZeroOffLive)
    (hall : controlK9RationalDeltaLiveAllShiftCenterErrorBudget) :
    controlK9RationalDeltaLiveCenterErrorBudget := by
  intro i j
  let live := controlK9LivePrimeShiftSet
    (controlK9Center j - controlK9Center i)
  have hmid :
      (∑ n ∈ live, controlK9RationalDeltaLiveTermMid i j n) =
        ∑ n : PrimeShiftIndexL3, controlK9RationalDeltaLiveTermMid i j n := by
    exact live_sum_eq_univ_sum_of_zero_off_live live
      (controlK9RationalDeltaLiveTermMid i j)
      (fun n hn => hmid_zero i j n (by simpa [live] using hn))
  have hrad :
      (∑ n ∈ live, controlK9RationalDeltaLiveTermRad i j n) =
        ∑ n : PrimeShiftIndexL3, controlK9RationalDeltaLiveTermRad i j n := by
    exact live_sum_eq_univ_sum_of_zero_off_live live
      (controlK9RationalDeltaLiveTermRad i j)
      (fun n hn => hrad_zero i j n (by simpa [live] using hn))
  simpa [controlK9RationalDeltaLiveAllShiftCenterErrorBudget,
    controlK9RationalDeltaLiveCenterErrorBudget, live, hmid, hrad] using
    hall i j

/-- Concrete primary rational witnesses instantiate the generic center-error
payload once their two proof bridges are supplied. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_witnesses
    (hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (hbudget : primaryK11RationalDeltaLiveCenterErrorBudget) :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact ⟨
    primaryK11RationalDeltaLiveTermMid,
    primaryK11RationalDeltaLiveTermRad,
    hterm,
    hbudget⟩

/-- Concrete control rational witnesses instantiate the generic center-error
payload once their two proof bridges are supplied. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_witnesses
    (hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (hbudget : controlK9RationalDeltaLiveCenterErrorBudget) :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact ⟨
    controlK9RationalDeltaLiveTermMid,
    controlK9RationalDeltaLiveTermRad,
    hterm,
    hbudget⟩

/-- Primary rational generated facts instantiate the generic center-error
payload through direct rational term hboxes and the all-shift budget receiver. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_generated_checks
    (hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (hmid_zero : primaryK11RationalDeltaLiveTermMidZeroOffLive)
    (hrad_zero : primaryK11RationalDeltaLiveTermRadZeroOffLive)
    (hall : primaryK11RationalDeltaLiveAllShiftCenterErrorBudget) :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_witnesses
      hterm
      (primaryK11RationalDeltaLiveCenterErrorBudget_of_allShift_budget
        hmid_zero hrad_zero hall)

/-- Control rational generated facts instantiate the generic center-error
payload through direct rational term hboxes and the all-shift budget receiver. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_generated_checks
    (hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (hmid_zero : controlK9RationalDeltaLiveTermMidZeroOffLive)
    (hrad_zero : controlK9RationalDeltaLiveTermRadZeroOffLive)
    (hall : controlK9RationalDeltaLiveAllShiftCenterErrorBudget) :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_witnesses
      hterm
      (controlK9RationalDeltaLiveCenterErrorBudget_of_allShift_budget
        hmid_zero hrad_zero hall)

/-- Primary rational generated facts can use nonzero-live membership facts
directly; zero-off-live is recovered without any dead-shift hboxes. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_nonzero_live_generated_checks
    (hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (hmid_live : primaryK11RationalDeltaLiveTermMidNonzeroLive)
    (hrad_live : primaryK11RationalDeltaLiveTermRadNonzeroLive)
    (hall : primaryK11RationalDeltaLiveAllShiftCenterErrorBudget) :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_generated_checks
      hterm
      (primaryK11RationalDeltaLiveTermMidZeroOffLive_of_nonzero_live hmid_live)
      (primaryK11RationalDeltaLiveTermRadZeroOffLive_of_nonzero_live hrad_live)
      hall

/-- Control rational generated facts can use nonzero-live membership facts
directly; zero-off-live is recovered without any dead-shift hboxes. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_nonzero_live_generated_checks
    (hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (hmid_live : controlK9RationalDeltaLiveTermMidNonzeroLive)
    (hrad_live : controlK9RationalDeltaLiveTermRadNonzeroLive)
    (hall : controlK9RationalDeltaLiveAllShiftCenterErrorBudget) :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_generated_checks
      hterm
      (controlK9RationalDeltaLiveTermMidZeroOffLive_of_nonzero_live hmid_live)
      (controlK9RationalDeltaLiveTermRadZeroOffLive_of_nonzero_live hrad_live)
      hall

/-- Primary rational generated facts can use one declared-support subset proof
for both midpoint and radius nonzero-live contracts. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_declared_support_generated_checks
    (hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (hdecl : primaryK11RationalDeltaLiveDeclaredNonzeroSubsetLive)
    (hall : primaryK11RationalDeltaLiveAllShiftCenterErrorBudget) :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_nonzero_live_generated_checks
      hterm
      (primaryK11RationalDeltaLiveTermMidNonzeroLive_of_declared_subset hdecl)
      (primaryK11RationalDeltaLiveTermRadNonzeroLive_of_declared_subset hdecl)
      hall

/-- Control rational generated facts can use one declared-support subset proof
for both midpoint and radius nonzero-live contracts. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_declared_support_generated_checks
    (hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (hdecl : controlK9RationalDeltaLiveDeclaredNonzeroSubsetLive)
    (hall : controlK9RationalDeltaLiveAllShiftCenterErrorBudget) :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_nonzero_live_generated_checks
      hterm
      (controlK9RationalDeltaLiveTermMidNonzeroLive_of_declared_subset hdecl)
      (controlK9RationalDeltaLiveTermRadNonzeroLive_of_declared_subset hdecl)
      hall

/-- Primary generated support and center-error budget are now closed; the only
remaining primary payload bridge is the analytic rational term hbox. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
    (hterm : primaryK11RationalDeltaLiveTermHboxBridge) :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_declared_support_generated_checks
      hterm
      primaryK11RationalDeltaLiveDeclaredNonzeroSubsetLive_generated
      primaryK11RationalDeltaLiveAllShiftCenterErrorBudget_generated

/-- Control generated support and center-error budget are now closed; the only
remaining control payload bridge is the analytic rational term hbox. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
    (hterm : controlK9RationalDeltaLiveTermHboxBridge) :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_declared_support_generated_checks
      hterm
      controlK9RationalDeltaLiveDeclaredNonzeroSubsetLive_generated
      controlK9RationalDeltaLiveAllShiftCenterErrorBudget_generated

/-- Option-B generated-witness closure surface.  This theorem is intentionally
thin: all numeric content lives in the two concrete witness tables above plus
the remaining Lean-checked bridge facts. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedWitnesses
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (primary_hbudget : primaryK11RationalDeltaLiveCenterErrorBudget)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (control_hbudget : controlK9RationalDeltaLiveCenterErrorBudget)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_witnesses
        primary_hterm primary_hbudget)
      primary_hP0
      control_hA
      (controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_witnesses
        control_hterm control_hbudget)
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_witnesses
        primary_hterm primary_hbudget)
      primary_hP0
      control_hA
      (controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_witnesses
        control_hterm control_hbudget)
      control_hP0

/-- Option-B generated-check closure surface.  This is the intended next
generated target: direct rational term hboxes, zero-off-live, and all-shift
center-error budget checks feed the Step33 receiver without exact-midpoint
requirements.  The separate `...TermDominatesTight` receiver remains
compatibility-only because the symbolic tight radii can be too loose for the
active 1024-bit rational payload. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedChecks
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (primary_hmid_zero : primaryK11RationalDeltaLiveTermMidZeroOffLive)
    (primary_hrad_zero : primaryK11RationalDeltaLiveTermRadZeroOffLive)
    (primary_hall : primaryK11RationalDeltaLiveAllShiftCenterErrorBudget)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (control_hmid_zero : controlK9RationalDeltaLiveTermMidZeroOffLive)
    (control_hrad_zero : controlK9RationalDeltaLiveTermRadZeroOffLive)
    (control_hall : controlK9RationalDeltaLiveAllShiftCenterErrorBudget)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_generated_checks
        primary_hterm primary_hmid_zero primary_hrad_zero primary_hall
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_generated_checks
        control_hterm control_hmid_zero control_hrad_zero control_hall
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_generated_checks
        primary_hterm primary_hmid_zero primary_hrad_zero primary_hall)
      primary_hP0
      control_hA
      (controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_rational_generated_checks
        control_hterm control_hmid_zero control_hrad_zero control_hall)
      control_hP0

/-- Option-B generated-check closure surface with nonzero-live facts as the
preferred generated support contract.  This keeps dead shifts out of the
payload theorem surface. -/
theorem psd_step33_closed_from_rationalDeltaLiveNonzeroLiveGeneratedChecks
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (primary_hmid_live : primaryK11RationalDeltaLiveTermMidNonzeroLive)
    (primary_hrad_live : primaryK11RationalDeltaLiveTermRadNonzeroLive)
    (primary_hall : primaryK11RationalDeltaLiveAllShiftCenterErrorBudget)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (control_hmid_live : controlK9RationalDeltaLiveTermMidNonzeroLive)
    (control_hrad_live : controlK9RationalDeltaLiveTermRadNonzeroLive)
    (control_hall : controlK9RationalDeltaLiveAllShiftCenterErrorBudget)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_nonzero_live_generated_checks
        primary_hterm primary_hmid_live primary_hrad_live primary_hall
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_nonzero_live_generated_checks
        control_hterm control_hmid_live control_hrad_live control_hall
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_nonzero_live_generated_checks
        primary_hterm primary_hmid_live primary_hrad_live primary_hall)
      primary_hP0
      control_hA
      (controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_nonzero_live_generated_checks
        control_hterm control_hmid_live control_hrad_live control_hall)
      control_hP0

/-- Option-B generated-check closure surface with declared generated support
as the preferred support contract.  One subset-to-live proof per block feeds
both midpoint and radius support obligations. -/
theorem psd_step33_closed_from_rationalDeltaLiveDeclaredSupportGeneratedChecks
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (primary_hdecl : primaryK11RationalDeltaLiveDeclaredNonzeroSubsetLive)
    (primary_hall : primaryK11RationalDeltaLiveAllShiftCenterErrorBudget)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (control_hdecl : controlK9RationalDeltaLiveDeclaredNonzeroSubsetLive)
    (control_hall : controlK9RationalDeltaLiveAllShiftCenterErrorBudget)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_declared_support_generated_checks
        primary_hterm primary_hdecl primary_hall
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_declared_support_generated_checks
        control_hterm control_hdecl control_hall
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_declared_support_generated_checks
        primary_hterm primary_hdecl primary_hall)
      primary_hP0
      control_hA
      (controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_declared_support_generated_checks
        control_hterm control_hdecl control_hall)
      control_hP0

/-- Option-B closure surface after generated support and center-error budgets
are discharged.  The remaining prime-side obligation is exactly the rational
term hbox bridge for primary and control. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedSupportAndBudgets
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hterm : primaryK11RationalDeltaLiveTermHboxBridge)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hterm : controlK9RationalDeltaLiveTermHboxBridge)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primary_hterm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        control_hterm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      (primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primary_hterm)
      primary_hP0
      control_hA
      (controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        control_hterm)
      control_hP0

/-- Option-B closure surface after generated support, center-error budgets,
and product budgets are discharged.  The remaining analytic obligations are
exactly the rational prime-weight hboxes and the cancellation-preserving
`R_minus + R_plus` hboxes for the generated witnesses. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedFactorHboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hweight :
      ∀ n,
        |primaryK11PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
          activeL3RationalPrimeWeightRad n)
    (primary_hrpair :
      primaryK11RationalDeltaLiveRPairHboxBridge
        primaryK11RationalDeltaLiveRPairMid
        primaryK11RationalDeltaLiveRPairRad)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hweight :
      ∀ n,
        |controlK9PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
          activeL3RationalPrimeWeightRad n)
    (control_hrpair :
      controlK9RationalDeltaLiveRPairHboxBridge
        controlK9RationalDeltaLiveRPairMid
        controlK9RationalDeltaLiveRPairRad)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryTerm :=
      primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        primary_hweight primary_hrpair
    let controlTerm :=
      controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        control_hweight control_hrpair
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primaryTerm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        controlTerm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedSupportAndBudgets
      primary_hA
      (primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        primary_hweight primary_hrpair)
      primary_hP0
      control_hA
      (controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        control_hweight control_hrpair)
      control_hP0

/-- Primary and control use the same active L3 prime-weight function.  This
adapter keeps the generated closure surface from carrying duplicate weight
hypotheses. -/
theorem primaryK11RationalPrimeWeight_hbox_of_active
    (hweight :
      ∀ n,
        |activeL3PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
          activeL3RationalPrimeWeightRad n) :
    ∀ n,
      |primaryK11PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
        activeL3RationalPrimeWeightRad n := by
  intro n
  simpa [primaryK11PrimeWeight] using hweight n

/-- Control wrapper for the shared active L3 rational prime-weight hbox. -/
theorem controlK9RationalPrimeWeight_hbox_of_active
    (hweight :
      ∀ n,
        |activeL3PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
          activeL3RationalPrimeWeightRad n) :
    ∀ n,
      |controlK9PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
        activeL3RationalPrimeWeightRad n := by
  intro n
  simpa [controlK9PrimeWeight] using hweight n

/-- Option-B closure surface with the duplicate primary/control weight hboxes
compressed to one shared active L3 rational prime-weight hbox.  The remaining
analytic obligations are now exactly:

* one shared active prime-weight hbox over the generated rational witnesses;
* the primary cancellation-preserving `R_minus + R_plus` hbox bridge;
* the control cancellation-preserving `R_minus + R_plus` hbox bridge.
-/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedSharedWeightAndRPairHboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (hweight :
      ∀ n,
        |activeL3PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
          activeL3RationalPrimeWeightRad n)
    (primary_hrpair :
      primaryK11RationalDeltaLiveRPairHboxBridge
        primaryK11RationalDeltaLiveRPairMid
        primaryK11RationalDeltaLiveRPairRad)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hrpair :
      controlK9RationalDeltaLiveRPairHboxBridge
        controlK9RationalDeltaLiveRPairMid
        controlK9RationalDeltaLiveRPairRad)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryTerm :=
      primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (primaryK11RationalPrimeWeight_hbox_of_active hweight)
        primary_hrpair
    let controlTerm :=
      controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (controlK9RationalPrimeWeight_hbox_of_active hweight)
        control_hrpair
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primaryTerm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        controlTerm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedFactorHboxes
      primary_hA
      (primaryK11RationalPrimeWeight_hbox_of_active hweight)
      primary_hrpair
      primary_hP0
      control_hA
      (controlK9RationalPrimeWeight_hbox_of_active hweight)
      control_hrpair
      control_hP0

/-- Option-B closure surface after generated support, all-shift center-error
budgets, rational product budgets, split-pair budgets, and the shared active
prime-weight hbox are closed.  The remaining analytic obligations are exactly
the four delta-compressed split-`R` B-spline hbox facts. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedWeightAndByDeltaSplitRHboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hminus : primaryK11RationalDeltaLiveRMinusHboxByDelta)
    (primary_hplus : primaryK11RationalDeltaLiveRPlusHboxByDelta)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hminus : controlK9RationalDeltaLiveRMinusHboxByDelta)
    (control_hplus : controlK9RationalDeltaLiveRPlusHboxByDelta)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryRPair :=
      primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        primary_hminus primary_hplus
    let controlRPair :=
      controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        control_hminus control_hplus
    let primaryTerm :=
      primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (primaryK11RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        primaryRPair
    let controlTerm :=
      controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (controlK9RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        controlRPair
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primaryTerm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        controlTerm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedSharedWeightAndRPairHboxes
      primary_hA
      activeL3RationalPrimeWeight_hbox_generated
      (primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        primary_hminus primary_hplus)
      primary_hP0
      control_hA
      (controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        control_hminus control_hplus)
      control_hP0

/-- Option-B closure surface with split normalized-`R` hboxes.  This is the
non-swamp landing surface for the next generated payload: prove live-only
minus/plus `centeredBSplineR` hboxes by segment/de-Boor rational arithmetic,
then discharge the exact rational pair-sum budgets. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedSharedWeightAndSplitRPairHboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (hweight :
      ∀ n,
        |activeL3PrimeWeight n - activeL3RationalPrimeWeightMid n| ≤
          activeL3RationalPrimeWeightRad n)
    (primaryMinusMid primaryMinusRad primaryPlusMid primaryPlusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (primary_hminus :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i) ->
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) -
              primaryK11PrimeShift n) / primaryK11Ell) -
          primaryMinusMid i j n| ≤ primaryMinusRad i j n)
    (primary_hplus :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i) ->
        |centeredBSplineR 11
            (((primaryK11Center j - primaryK11Center i) +
              primaryK11PrimeShift n) / primaryK11Ell) -
          primaryPlusMid i j n| ≤ primaryPlusRad i j n)
    (primary_hsum :
      ∀ i j n,
        n ∈ primaryK11LivePrimeShiftSet
          (primaryK11Center j - primaryK11Center i) ->
        primaryMinusRad i j n + primaryPlusRad i j n +
            |primaryMinusMid i j n + primaryPlusMid i j n -
              primaryK11RationalDeltaLiveRPairMid i j n| ≤
          primaryK11RationalDeltaLiveRPairRad i j n)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (controlMinusMid controlMinusRad controlPlusMid controlPlusRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    (control_hminus :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i) ->
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) -
              controlK9PrimeShift n) / controlK9Ell) -
          controlMinusMid i j n| ≤ controlMinusRad i j n)
    (control_hplus :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i) ->
        |centeredBSplineR 9
            (((controlK9Center j - controlK9Center i) +
              controlK9PrimeShift n) / controlK9Ell) -
          controlPlusMid i j n| ≤ controlPlusRad i j n)
    (control_hsum :
      ∀ i j n,
        n ∈ controlK9LivePrimeShiftSet
          (controlK9Center j - controlK9Center i) ->
        controlMinusRad i j n + controlPlusRad i j n +
            |controlMinusMid i j n + controlPlusMid i j n -
              controlK9RationalDeltaLiveRPairMid i j n| ≤
          controlK9RationalDeltaLiveRPairRad i j n)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryRPair :=
      primaryK11RationalDeltaLiveRPairHboxBridge_of_split_R_hboxes
        primaryMinusMid primaryMinusRad primaryPlusMid primaryPlusRad
        primary_hminus primary_hplus primary_hsum
    let controlRPair :=
      controlK9RationalDeltaLiveRPairHboxBridge_of_split_R_hboxes
        controlMinusMid controlMinusRad controlPlusMid controlPlusRad
        control_hminus control_hplus control_hsum
    let primaryTerm :=
      primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (primaryK11RationalPrimeWeight_hbox_of_active hweight)
        primaryRPair
    let controlTerm :=
      controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (controlK9RationalPrimeWeight_hbox_of_active hweight)
        controlRPair
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primaryTerm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        controlTerm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedSharedWeightAndRPairHboxes
      primary_hA
      hweight
      (primaryK11RationalDeltaLiveRPairHboxBridge_of_split_R_hboxes
        primaryMinusMid primaryMinusRad primaryPlusMid primaryPlusRad
        primary_hminus primary_hplus primary_hsum)
      primary_hP0
      control_hA
      (controlK9RationalDeltaLiveRPairHboxBridge_of_split_R_hboxes
        controlMinusMid controlMinusRad controlPlusMid controlPlusRad
        control_hminus control_hplus control_hsum)
      control_hP0

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
"""


def emit_support_side_chunk_module(
    *,
    prefix: str,
    k: int,
    side: str,
    declared_set_name: str,
    ell_name: str,
    ell_rat_name: str,
    prime_shift_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
    chunk_idx: int,
    start_idx: int,
    end_idx: int,
) -> str:
    side_title = "minus" if side == "minus" else "plus"
    return f"""import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B {prefix} split-`R` {side_title}-side
declared-support hbox facts, index chunk {chunk_idx}: {start_idx}..{end_idx}.
-/

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffPrimeEntryHboxImport
open CenteredCoeffPrimeDeltaLivePayloadImport
open CenteredCoeffPrimePositivePartTightImport
open CenteredCoeffEntryHboxImport

{emit_split_r_hbox_chunk_generated(
    prefix=prefix,
    k=k,
    side=side,
    declared_set_name=declared_set_name,
    ell_name=ell_name,
    ell_rat_name=ell_rat_name,
    prime_shift_name=prime_shift_name,
    by_delta=by_delta,
    start_idx=start_idx,
    end_idx=end_idx,
)}

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
"""


def emit_support_side_zero_chunk_module(
    *,
    prefix: str,
    k: int,
    side: str,
    declared_set_name: str,
    ell_name: str,
    ell_rat_name: str,
    prime_shift_name: str,
    by_delta: dict[int, dict[int, TermWitness]],
    chunk_idx: int,
    start_idx: int,
    end_idx: int,
) -> str:
    side_title = "minus" if side == "minus" else "plus"
    return f"""import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B {prefix} split-`R` {side_title}-side
zero-off-declared support facts, index chunk {chunk_idx}: {start_idx}..{end_idx}.
-/

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffPrimeEntryHboxImport
open CenteredCoeffPrimeDeltaLivePayloadImport
open CenteredCoeffPrimePositivePartTightImport
open CenteredCoeffEntryHboxImport

{emit_split_r_zero_chunk_generated(
    prefix=prefix,
    k=k,
    side=side,
    declared_set_name=declared_set_name,
    ell_name=ell_name,
    ell_rat_name=ell_rat_name,
    prime_shift_name=prime_shift_name,
    by_delta=by_delta,
    start_idx=start_idx,
    end_idx=end_idx,
)}

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
"""


def emit_support_side_module(
    *,
    prefix: str,
    side: str,
) -> str:
    side_title = "minus" if side == "minus" else "plus"
    hbox_imports = [
        f"import {support_side_chunk_module(prefix, side, chunk_idx)}"
        for chunk_idx in range(len(SUPPORT_CHUNK_RANGES))
    ]
    zero_imports = [
        f"import {support_side_zero_chunk_module(prefix, side, chunk_idx)}"
        for chunk_idx in range(len(SUPPORT_CHUNK_RANGES))
    ]
    imports = "\n".join(hbox_imports + zero_imports)
    return f"""{imports}

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B {prefix} split-`R` {side_title}-side
zero-off-declared support wrapper.
-/

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffPrimeEntryHboxImport
open CenteredCoeffPrimeDeltaLivePayloadImport
open CenteredCoeffPrimePositivePartTightImport
open CenteredCoeffEntryHboxImport

{emit_split_r_zero_generated_final(prefix=prefix, side=side)}

{emit_split_r_hbox_generated_final(prefix=prefix, side=side)}

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
"""


def emit_support_module(
    blocks: dict[str, dict[int, dict[int, TermWitness]]],
) -> str:
    return f"""import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalSupportPrimaryMinusImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalSupportPrimaryPlusImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalSupportControlMinusImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalSupportControlPlusImport
import Q3.Proofs.PSD_CenteredCoeffBaseP0HboxImport
import Q3.Proofs.PSD_CenteredCoeffBaseAHboxImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B split-`R` declared-support closure surface.

The four side support proofs are split into separate modules so each side can be
checked and cached independently.
-/

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffPrimeEntryHboxImport
open CenteredCoeffPrimeDeltaLivePayloadImport
open CenteredCoeffPrimePositivePartTightImport
open CenteredCoeffEntryHboxImport

/-- Generated primary minus-side full live split-`R` hbox receiver. -/
theorem primaryK11RationalDeltaLiveRMinusHboxByDelta_generated :
    primaryK11RationalDeltaLiveRMinusHboxByDelta := by
  exact
    primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
      primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
      primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated

/-- Generated primary plus-side full live split-`R` hbox receiver. -/
theorem primaryK11RationalDeltaLiveRPlusHboxByDelta_generated :
    primaryK11RationalDeltaLiveRPlusHboxByDelta := by
  exact
    primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
      primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
      primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated

/-- Generated control minus-side full live split-`R` hbox receiver. -/
theorem controlK9RationalDeltaLiveRMinusHboxByDelta_generated :
    controlK9RationalDeltaLiveRMinusHboxByDelta := by
  exact
    controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
      controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
      controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated

/-- Generated control plus-side full live split-`R` hbox receiver. -/
theorem controlK9RationalDeltaLiveRPlusHboxByDelta_generated :
    controlK9RationalDeltaLiveRPlusHboxByDelta := by
  exact
    controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
      controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
      controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated

/-- Generated primary `R_minus + R_plus` hbox bridge. -/
theorem primaryK11RationalDeltaLiveRPairHboxBridge_generated :
    primaryK11RationalDeltaLiveRPairHboxBridge
      primaryK11RationalDeltaLiveRPairMid
      primaryK11RationalDeltaLiveRPairRad := by
  exact
    primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
      primaryK11RationalDeltaLiveRMinusHboxByDelta_generated
      primaryK11RationalDeltaLiveRPlusHboxByDelta_generated

/-- Generated control `R_minus + R_plus` hbox bridge. -/
theorem controlK9RationalDeltaLiveRPairHboxBridge_generated :
    controlK9RationalDeltaLiveRPairHboxBridge
      controlK9RationalDeltaLiveRPairMid
      controlK9RationalDeltaLiveRPairRad := by
  exact
    controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
      controlK9RationalDeltaLiveRMinusHboxByDelta_generated
      controlK9RationalDeltaLiveRPlusHboxByDelta_generated

/-- Generated primary rational term hbox bridge from the JSON witnesses. -/
theorem primaryK11RationalDeltaLiveTermHboxBridge_generated :
    primaryK11RationalDeltaLiveTermHboxBridge := by
  exact
    primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
      (primaryK11RationalPrimeWeight_hbox_of_active
        activeL3RationalPrimeWeight_hbox_generated)
      primaryK11RationalDeltaLiveRPairHboxBridge_generated

/-- Generated control rational term hbox bridge from the JSON witnesses. -/
theorem controlK9RationalDeltaLiveTermHboxBridge_generated :
    controlK9RationalDeltaLiveTermHboxBridge := by
  exact
    controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
      (controlK9RationalPrimeWeight_hbox_of_active
        activeL3RationalPrimeWeight_hbox_generated)
      controlK9RationalDeltaLiveRPairHboxBridge_generated

/-- Concrete generated primary rational payload witness with center error. -/
theorem primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated :
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
      primaryK11RationalDeltaLiveTermHboxBridge_generated

/-- Concrete generated control rational payload witness with center error. -/
theorem controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated :
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError := by
  exact
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
      controlK9RationalDeltaLiveTermHboxBridge_generated

/-- Option-B closure using the two concrete generated rational payload hboxes.
This is the explicit generated landing surface for
`psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError`. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedPayloadHboxesWithCenterError
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0

/-- Generated closure after the base `A/P0` matrix hboxes have been reduced to
compact absolute-distance scalar certificate structures.  This is the checked
Step33A.1 bridge from four `23`-distance scalar certs to the active generated
rational payload closure surface. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedAbsDistanceBaseCertsWithCenterError
    (primary_hA_cert :
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert)
    (primary_hP0_cert :
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert)
    (control_hA_cert :
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert)
    (control_hP0_cert :
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert) :
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedPayloadHboxesWithCenterError
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert)
      (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert)
      (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert)

/-- Generated closure after the base `A/P0` compact scalar certificates have
been shifted to lower/upper interval certificate structures.  This keeps the
remaining Step21/Step22 proof obligation in the natural interval-output shape
while still closing the active generated rational payload surface. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedIntervalBaseCertsWithCenterError
    (primary_hA_interval :
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceIntervalCert)
    (primary_hP0_interval :
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert)
    (control_hA_interval :
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceIntervalCert)
    (control_hP0_interval :
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert) :
    let primary_hA_cert :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
        primary_hA_interval
    let primary_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        primary_hP0_interval
    let control_hA_cert :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
        control_hA_interval
    let control_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        control_hP0_interval
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedAbsDistanceBaseCertsWithCenterError
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
        primary_hA_interval)
      (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        primary_hP0_interval)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
        control_hA_interval)
      (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        control_hP0_interval)

/-- Generated closure after the base `A/P0` compact scalar interval facts have
been packaged as named distance-bound certificate structures.  This is the
intended landing surface for a proof-producing Step21/Step22 scalar backend:
one checked cert term per active primary/control `A/P0` block. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedDistanceBoundBaseCertsWithCenterError
    (primary_hA_bounds :
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceBoundsCert)
    (primary_hP0_bounds :
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceBoundsCert)
    (control_hA_bounds :
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceBoundsCert)
    (control_hP0_bounds :
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceBoundsCert) :
    let primary_hA_interval :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
        primary_hA_bounds
    let primary_hP0_interval :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
        primary_hP0_bounds
    let control_hA_interval :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
        control_hA_bounds
    let control_hP0_interval :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
        control_hP0_bounds
    let primary_hA_cert :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
        primary_hA_interval
    let primary_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
        primary_hP0_interval
    let control_hA_cert :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
        control_hA_interval
    let control_hP0_cert :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
        control_hP0_interval
    let primary_hA :=
      CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
        primary_hA_cert
    let primary_hP0 :=
      CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
        primary_hP0_cert
    let control_hA :=
      CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
        control_hA_cert
    let control_hP0 :=
      CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
        control_hP0_cert
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      primary_hP0
      control_hA
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
      control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedIntervalBaseCertsWithCenterError
      (CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
        primary_hA_bounds)
      (CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
        primary_hP0_bounds)
      (CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
        control_hA_bounds)
      (CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
        control_hP0_bounds)

/-- One named base scalar gate for the active Step33A.1 `A/P0` layer.  This
packages the four primary/control `A/P0` distance-bound certificates without
changing the checked receiver theorem. -/
structure RationalDeltaLiveBaseScalarBoundsCert : Prop where
  primary_hA_bounds :
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceBoundsCert
  primary_hP0_bounds :
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceBoundsCert
  control_hA_bounds :
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceBoundsCert
  control_hP0_bounds :
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceBoundsCert

/-- The closure proposition exposed by the one-cert Step33A.1 base scalar gate. -/
def RationalDeltaLiveBaseScalarBoundsClosure
    (base_bounds : RationalDeltaLiveBaseScalarBoundsCert) : Prop :=
  let primary_hA_interval :=
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
      base_bounds.primary_hA_bounds
  let primary_hP0_interval :=
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
      base_bounds.primary_hP0_bounds
  let control_hA_interval :=
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceIntervalCert_of_distance_bounds_cert
      base_bounds.control_hA_bounds
  let control_hP0_interval :=
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceIntervalCert_of_distance_bounds_cert
      base_bounds.control_hP0_bounds
  let primary_hA_cert :=
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticAAbsDistanceHboxCert_of_interval_cert
      primary_hA_interval
  let primary_hP0_cert :=
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0AbsDistanceHboxCert_of_interval_cert
      primary_hP0_interval
  let control_hA_cert :=
    CenteredCoeffBaseAHboxImport.controlK9AnalyticAAbsDistanceHboxCert_of_interval_cert
      control_hA_interval
  let control_hP0_cert :=
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0AbsDistanceHboxCert_of_interval_cert
      control_hP0_interval
  let primary_hA :=
    CenteredCoeffBaseAHboxImport.primaryK11AnalyticA_entry_hbox_of_abs_distance_cert
      primary_hA_cert
  let primary_hP0 :=
    CenteredCoeffBaseP0HboxImport.primaryK11AnalyticP0_entry_hbox_of_abs_distance_cert
      primary_hP0_cert
  let control_hA :=
    CenteredCoeffBaseAHboxImport.controlK9AnalyticA_entry_hbox_of_abs_distance_cert
      control_hA_cert
  let control_hP0 :=
    CenteredCoeffBaseP0HboxImport.controlK9AnalyticP0_entry_hbox_of_abs_distance_cert
      control_hP0_cert
  let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
    primary_hA
    primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
    primary_hP0
    control_hA
    controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_generated
    control_hP0
  PsdStep33FiniteAnalyticPositivity cert ∧
    PsdStep33SingletonDirectedFamilyHandoff cert

/-- Generated one-cert closure bridge for the active Step33A.1 base scalar gate.
The remaining backend target is now one proof-producing
`RationalDeltaLiveBaseScalarBoundsCert` inhabitant. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedBaseScalarBoundsCertWithCenterError
    (base_bounds : RationalDeltaLiveBaseScalarBoundsCert) :
    RationalDeltaLiveBaseScalarBoundsClosure base_bounds := by
  rcases base_bounds with
    ⟨primary_hA_bounds, primary_hP0_bounds, control_hA_bounds, control_hP0_bounds⟩
  simpa [RationalDeltaLiveBaseScalarBoundsClosure] using
    psd_step33_closed_from_rationalDeltaLiveGeneratedDistanceBoundBaseCertsWithCenterError
      primary_hA_bounds
      primary_hP0_bounds
      control_hA_bounds
      control_hP0_bounds

/-- Option-B closure surface after generated zero-off-declared split-`R`
support facts are closed.  The remaining analytic obligations are exactly the
four compact nonzero-side `HboxOnDeclaredByDelta` facts. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedWeightAndDeclaredSplitRHboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hminus :
      primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta)
    (primary_hplus :
      primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hminus :
      controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta)
    (control_hplus :
      controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryMinus :=
      primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        primary_hminus
        primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated
    let primaryPlus :=
      primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        primary_hplus
        primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated
    let controlMinus :=
      controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        control_hminus
        controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated
    let controlPlus :=
      controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        control_hplus
        controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated
    let primaryRPair :=
      primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        primaryMinus primaryPlus
    let controlRPair :=
      controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        controlMinus controlPlus
    let primaryTerm :=
      primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (primaryK11RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        primaryRPair
    let controlTerm :=
      controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (controlK9RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        controlRPair
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primaryTerm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        controlTerm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedWeightAndByDeltaSplitRHboxes
      primary_hA
      (primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        primary_hminus
        primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated)
      (primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        primary_hplus
        primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated)
      primary_hP0
      control_hA
      (controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        control_hminus
        controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated)
      (controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        control_hplus
        controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated)
      control_hP0

/-- Option-B closure surface after generated split-`R` hboxes and
zero-off-declared support facts are closed.  The remaining assumptions are the
base `A/P0` matrix hboxes, not the prime-profile payload hboxes. -/
theorem psd_step33_closed_from_rationalDeltaLiveGeneratedSplitRHboxes
    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.primaryK11AnalyticA
      primaryK11A primaryK11ARadius)
    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)
    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe
      CenteredCoeffBaseHboxImport.controlK9AnalyticA
      controlK9A controlK9ARadius)
    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    let primaryMinus :=
      primaryK11RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
        primaryK11RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated
    let primaryPlus :=
      primaryK11RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
        primaryK11RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated
    let controlMinus :=
      controlK9RationalDeltaLiveRMinusHboxByDelta_of_declared_or_zero
        controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
        controlK9RationalDeltaLiveRMinusZeroOffDeclaredByDelta_generated
    let controlPlus :=
      controlK9RationalDeltaLiveRPlusHboxByDelta_of_declared_or_zero
        controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
        controlK9RationalDeltaLiveRPlusZeroOffDeclaredByDelta_generated
    let primaryRPair :=
      primaryK11RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        primaryMinus primaryPlus
    let controlRPair :=
      controlK9RationalDeltaLiveRPairHboxBridge_of_by_delta_split_R_hboxes
        controlMinus controlPlus
    let primaryTerm :=
      primaryK11RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (primaryK11RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        primaryRPair
    let controlTerm :=
      controlK9RationalDeltaLiveTermHboxBridge_of_generated_factor_hboxes
        (controlK9RationalPrimeWeight_hbox_of_active
          activeL3RationalPrimeWeight_hbox_generated)
        controlRPair
    let primaryPayload :=
      primaryK11DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        primaryTerm
    let controlPayload :=
      controlK9DeltaLiveFinitePrimeProfilePayloadHboxWithCenterError_of_generated_support_and_term_hbox
        controlTerm
    let cert := psd_step33_active_entry_hbox_cert_from_rationalDeltaLivePayloadHboxesWithCenterError
      primary_hA primaryPayload primary_hP0
      control_hA controlPayload control_hP0
    PsdStep33FiniteAnalyticPositivity cert ∧
      PsdStep33SingletonDirectedFamilyHandoff cert := by
  exact
    psd_step33_closed_from_rationalDeltaLiveGeneratedWeightAndDeclaredSplitRHboxes
      primary_hA
      primaryK11RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
      primaryK11RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
      primary_hP0
      control_hA
      controlK9RationalDeltaLiveRMinusHboxOnDeclaredByDelta_generated
      controlK9RationalDeltaLiveRPlusHboxOnDeclaredByDelta_generated
      control_hP0

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
"""


def write_if_changed(path: Path, text: str) -> None:
    if path.exists() and path.read_text() == text:
        print(f"unchanged {path}")
        return
    path.write_text(text)
    print(f"wrote {path}")


def main() -> None:
    blocks, weight_payload = load_blocks()
    write_if_changed(OUT, emit_module(blocks, weight_payload))
    side_specs = [
        (
            "primaryK11",
            11,
            "minus",
            "primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta",
            "primaryK11Ell",
            "primaryK11EllRat",
            "primaryK11PrimeShift",
            blocks["primary"],
        ),
        (
            "primaryK11",
            11,
            "plus",
            "primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta",
            "primaryK11Ell",
            "primaryK11EllRat",
            "primaryK11PrimeShift",
            blocks["primary"],
        ),
        (
            "controlK9",
            9,
            "minus",
            "controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta",
            "controlK9Ell",
            "controlK9EllRat",
            "controlK9PrimeShift",
            blocks["control"],
        ),
        (
            "controlK9",
            9,
            "plus",
            "controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta",
            "controlK9Ell",
            "controlK9EllRat",
            "controlK9PrimeShift",
            blocks["control"],
        ),
    ]
    for (
        prefix,
        k,
        side,
        declared_set_name,
        ell_name,
        ell_rat_name,
        prime_shift_name,
        by_delta,
    ) in side_specs:
        for chunk_idx, (start_idx, end_idx) in enumerate(SUPPORT_CHUNK_RANGES):
            chunk_out = support_side_chunk_out(prefix, side, chunk_idx)
            write_if_changed(
                chunk_out,
                emit_support_side_chunk_module(
                    prefix=prefix,
                    k=k,
                    side=side,
                    declared_set_name=declared_set_name,
                    ell_name=ell_name,
                    ell_rat_name=ell_rat_name,
                    prime_shift_name=prime_shift_name,
                    by_delta=by_delta,
                    chunk_idx=chunk_idx,
                    start_idx=start_idx,
                    end_idx=end_idx,
                ),
            )
            zero_chunk_out = support_side_zero_chunk_out(prefix, side, chunk_idx)
            write_if_changed(
                zero_chunk_out,
                emit_support_side_zero_chunk_module(
                    prefix=prefix,
                    k=k,
                    side=side,
                    declared_set_name=declared_set_name,
                    ell_name=ell_name,
                    ell_rat_name=ell_rat_name,
                    prime_shift_name=prime_shift_name,
                    by_delta=by_delta,
                    chunk_idx=chunk_idx,
                    start_idx=start_idx,
                    end_idx=end_idx,
                ),
            )
        out = SUPPORT_SIDE_OUTS[(prefix, side)]
        write_if_changed(
            out,
            emit_support_side_module(
                prefix=prefix,
                side=side,
            ),
        )
    write_if_changed(SUPPORT_OUT, emit_support_module(blocks))


if __name__ == "__main__":
    main()
