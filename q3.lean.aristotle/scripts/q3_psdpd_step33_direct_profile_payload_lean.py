#!/usr/bin/env python3
"""Generate the Step33 direct-profile payload Lean surface.

This generator intentionally does not turn Arb output into trusted Lean facts.
It emits the checked row/entry receiver surface for the direct finite-prime
profile payload.  A later numeric replay generator can fill the scalar entry
hboxes without changing the Step33 theorem shape.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "Q3/Proofs/PSD_CenteredCoeffPrimeDirectProfilePayloadImport.lean"
PAYLOAD_IMPORT = ROOT / "Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean"
PRIMARY_MID = ROOT / "docs/insights/q3_psdpd_step22_midpoints_k11.csv"
PRIMARY_RAD = ROOT / "docs/insights/q3_psdpd_step22_radii_k11.csv"
CONTROL_MID = ROOT / "docs/insights/q3_psdpd_step22_midpoints_k9.csv"
CONTROL_RAD = ROOT / "docs/insights/q3_psdpd_step22_radii_k9.csv"
AUDIT_JSON = (
    ROOT
    / "ACTIVE/requests/step33_bootstrap/"
    / "direct_profile_payload_audit_current_step20_p_radii.json"
)


def read_p_shape(path: Path) -> set[tuple[int, int]]:
    out: set[tuple[int, int]] = set()
    with path.open() as f:
        reader = csv.DictReader(f)
        required = {"matrix", "i", "j"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise SystemExit(f"{path}: missing columns {sorted(missing)}")
        for row in reader:
            if row["matrix"].strip() == "P":
                out.add((int(row["i"]), int(row["j"])))
    return out


def read_p_values(path: Path, column: str) -> dict[tuple[int, int], Decimal]:
    out: dict[tuple[int, int], Decimal] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        required = {"matrix", "i", "j", column}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise SystemExit(f"{path}: missing columns {sorted(missing)}")
        for row in reader:
            if row["matrix"].strip() == "P":
                out[(int(row["i"]), int(row["j"]))] = Decimal(row[column])
    return out


def check_payload_shapes() -> None:
    expected = {(i, j) for i in range(23) for j in range(23)}
    for path in [PRIMARY_MID, PRIMARY_RAD, CONTROL_MID, CONTROL_RAD]:
        shape = read_p_shape(path)
        if shape != expected:
            missing = sorted(expected - shape)[:8]
            extra = sorted(shape - expected)[:8]
            raise SystemExit(
                f"{path}: unexpected P shape; "
                f"missing={missing} extra={extra}"
            )


def check_audit(path: Path) -> None:
    if not path.exists():
        return
    payload = json.loads(path.read_text())
    bad = [
        item
        for item in payload
        if item.get("verdict") != "direct_profile_payload_fits_imported_radius"
    ]
    if bad:
        raise SystemExit(f"{path}: direct-profile audit did not pass: {bad}")


def fin(n: int) -> str:
    return f"(Fin.mk {n} (by norm_num) : CoeffIndex23)"


def delta_name(delta: int) -> str:
    if delta < 0:
        return f"m{abs(delta)}"
    if delta > 0:
        return f"p{delta}"
    return "z0"


def rat_expr(value: Decimal | Fraction) -> str:
    if isinstance(value, Fraction):
        if value.denominator == 1:
            return f"(({value.numerator} : Rat) : Real)"
        return f"((({value.numerator} : Rat) / {value.denominator} : Rat) : Real)"
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
        return f"(({numerator} : Rat) : Real)"
    return f"((({numerator} : Rat) / {denominator} : Rat) : Real)"


def delta_bounds(midpoint_csv: Path, radius_csv: Path) -> dict[int, tuple[Decimal, Decimal]]:
    mids = read_p_values(midpoint_csv, "mid")
    rads = read_p_values(radius_csv, "rad")
    out: dict[int, tuple[Decimal, Decimal]] = {}
    for delta in range(-22, 23):
        lows: list[Decimal] = []
        uppers: list[Decimal] = []
        for i in range(23):
            j = i + delta
            if 0 <= j < 23:
                mid = mids[(i, j)]
                rad = rads[(i, j)]
                lows.append(mid - rad)
                uppers.append(mid + rad)
        lower = max(lows)
        upper = min(uppers)
        if lower > upper:
            raise SystemExit(
                f"{midpoint_csv}: empty synchronized P delta interval "
                f"for delta={delta}: lower={lower} upper={upper}"
            )
        out[delta] = (lower, upper)
    return out


def read_lean_rat_table(def_name: str) -> dict[tuple[int, int], str]:
    text = PAYLOAD_IMPORT.read_text()
    start = text.index(f"def {def_name} : Nat -> Nat -> Rat")
    next_def = text.find("\ndef ", start + 1)
    if next_def == -1:
        next_def = len(text)
    block = text[start:next_def]
    out: dict[tuple[int, int], str] = {}
    pattern = re.compile(r"^  \| (\d+), (\d+) => (.+)$")
    for line in block.splitlines():
        match = pattern.match(line)
        if match:
            out[(int(match.group(1)), int(match.group(2)))] = match.group(3)
    expected = {(i, j) for i in range(23) for j in range(23)}
    if set(out) != expected:
        missing = sorted(expected - set(out))[:8]
        extra = sorted(set(out) - expected)[:8]
        raise SystemExit(
            f"{PAYLOAD_IMPORT}: {def_name} shape mismatch; "
            f"missing={missing} extra={extra}"
        )
    return out


def lean_rat_expr_to_fraction(expr: str) -> Fraction:
    div_match = re.fullmatch(r"\(\(([-0-9]+) : Rat\) / ([0-9]+)\)", expr)
    if div_match:
        return Fraction(int(div_match.group(1)), int(div_match.group(2)))
    int_match = re.fullmatch(r"\(\(([-0-9]+) : Rat\)\)", expr)
    if int_match:
        return Fraction(int(int_match.group(1)), 1)
    raise SystemExit(f"unsupported Rat expression: {expr}")


def read_lean_rat_fraction_table(def_name: str) -> dict[tuple[int, int], Fraction]:
    return {
        key: lean_rat_expr_to_fraction(expr)
        for key, expr in read_lean_rat_table(def_name).items()
    }


def delta_bounds_from_lean_tables(
    p_table_name: str, radius_table_name: str
) -> dict[int, tuple[Fraction, Fraction]]:
    mids = read_lean_rat_fraction_table(p_table_name)
    rads = read_lean_rat_fraction_table(radius_table_name)
    out: dict[int, tuple[Fraction, Fraction]] = {}
    for delta in range(-22, 23):
        lows: list[Fraction] = []
        uppers: list[Fraction] = []
        for i in range(23):
            j = i + delta
            if 0 <= j < 23:
                mid = mids[(i, j)]
                rad = rads[(i, j)]
                lows.append(mid - rad)
                uppers.append(mid + rad)
        lower = max(lows)
        upper = min(uppers)
        if lower > upper:
            raise SystemExit(
                f"{PAYLOAD_IMPORT}: empty exact P delta interval "
                f"for {p_table_name}, delta={delta}: lower={lower} upper={upper}"
            )
        out[delta] = (lower, upper)
    return out


def entry_prop(prefix: str, k: int, ell: str, weight: str, shift: str, center: str) -> str:
    cap = prefix_cap(prefix)
    return f"""
/-- Scalar direct-profile value for the {prefix} block. -/
def {prefix}DirectFinitePrimeProfileEntryValue
    (i j : CoeffIndex23) : Real :=
  centeredBSplineFinitePrimeKernelProfile
    {k} {ell} {weight} {shift}
    ({center} j - {center} i)

/-- Lower endpoint for the synchronized {prefix} direct-profile entry box. -/
def {prefix}DirectFinitePrimeProfileEntryLower
    (i j : CoeffIndex23) : Real :=
  {prefix}DirectFinitePrimeProfileMid i j -
    {prefix}DirectFinitePrimeProfileRad i j

/-- Upper endpoint for the synchronized {prefix} direct-profile entry box. -/
def {prefix}DirectFinitePrimeProfileEntryUpper
    (i j : CoeffIndex23) : Real :=
  {prefix}DirectFinitePrimeProfileMid i j +
    {prefix}DirectFinitePrimeProfileRad i j

/-- Scalar direct-profile payload hbox for the {prefix} block. -/
def {prefix}DirectFinitePrimeProfileEntryHbox
    (i j : CoeffIndex23) : Prop :=
  |{prefix}DirectFinitePrimeProfileEntryValue i j -
    {prefix}DirectFinitePrimeProfileMid i j| <=
      {prefix}DirectFinitePrimeProfileRad i j

/-- Lower/upper interval certificate for one {prefix} scalar entry. -/
structure {cap}DirectFinitePrimeProfileEntryIntervalCert
    (i j : CoeffIndex23) : Prop where
  hLower :
    {prefix}DirectFinitePrimeProfileEntryLower i j <=
      {prefix}DirectFinitePrimeProfileEntryValue i j
  hUpper :
    {prefix}DirectFinitePrimeProfileEntryValue i j <=
      {prefix}DirectFinitePrimeProfileEntryUpper i j

/-- A generated lower/upper interval certificate gives the scalar hbox. -/
theorem {prefix}DirectFinitePrimeProfileEntryHbox_of_interval_cert
    {{i j : CoeffIndex23}}
    (cert : {cap}DirectFinitePrimeProfileEntryIntervalCert i j) :
    {prefix}DirectFinitePrimeProfileEntryHbox i j := by
  unfold {prefix}DirectFinitePrimeProfileEntryHbox
  exact abs_sub_le_of_lower_upper
    (x := {prefix}DirectFinitePrimeProfileEntryValue i j)
    (mid := {prefix}DirectFinitePrimeProfileMid i j)
    (rad := {prefix}DirectFinitePrimeProfileRad i j)
    (by simpa [{prefix}DirectFinitePrimeProfileEntryLower] using cert.hLower)
    (by simpa [{prefix}DirectFinitePrimeProfileEntryUpper] using cert.hUpper)

/-- A scalar hbox gives the equivalent lower/upper interval certificate. -/
theorem {prefix}DirectFinitePrimeProfileEntryIntervalCert_of_hbox
    {{i j : CoeffIndex23}}
    (h : {prefix}DirectFinitePrimeProfileEntryHbox i j) :
    {cap}DirectFinitePrimeProfileEntryIntervalCert i j := by
  unfold {prefix}DirectFinitePrimeProfileEntryHbox at h
  rcases lower_upper_of_abs_sub_le
    (x := {prefix}DirectFinitePrimeProfileEntryValue i j)
    (mid := {prefix}DirectFinitePrimeProfileMid i j)
    (rad := {prefix}DirectFinitePrimeProfileRad i j)
    h with ⟨hLower, hUpper⟩
  exact ⟨
    by simpa [{prefix}DirectFinitePrimeProfileEntryLower] using hLower,
    by simpa [{prefix}DirectFinitePrimeProfileEntryUpper] using hUpper
  ⟩

/-- Row bundle for generated {prefix} direct-profile scalar hboxes. -/
structure {prefix_cap(prefix)}DirectFinitePrimeProfileRowPayloadHbox
    (i : CoeffIndex23) : Prop where
  h : forall j, {prefix}DirectFinitePrimeProfileEntryHbox i j
"""


def prefix_cap(prefix: str) -> str:
    if prefix == "primaryK11":
        return "PrimaryK11"
    if prefix == "controlK9":
        return "ControlK9"
    raise ValueError(prefix)


def row_constructor(prefix: str, row: int) -> str:
    cap = prefix_cap(prefix)
    args = [
        f"    (h{row}_{j} : {prefix}DirectFinitePrimeProfileEntryHbox {fin(row)} {fin(j)})"
        for j in range(23)
    ]
    cases: list[str] = ["    · exact h%s_%s" % (row, j) for j in range(23)]
    return "\n".join(
        [
            f"/-- Assemble generated {prefix} row {row} from scalar entry hboxes. -/",
            f"theorem {prefix}DirectFinitePrimeProfileRowPayloadHbox_of_entries_{row}",
            *args,
            f"    : {cap}DirectFinitePrimeProfileRowPayloadHbox {fin(row)} where",
            "  h := by",
            "    intro j",
            "    fin_cases j",
            *cases,
            "",
        ]
    )


def primary_00_support_zero_cert() -> str:
    i0 = fin(0)
    return f"""
/-- The primary `(0,0)` direct-profile scalar value is zero by support. -/
theorem primaryK11DirectFinitePrimeProfileEntryValue_0_0_eq_zero :
    primaryK11DirectFinitePrimeProfileEntryValue {i0} {i0} = 0 := by
  unfold primaryK11DirectFinitePrimeProfileEntryValue
  unfold centeredBSplineFinitePrimeKernelProfile
  refine Finset.sum_eq_zero ?_
  intro n hn
  have hshift :=
    _root_.Q3.PSDpd.CenteredCoeffPrimeDictionaryBoundsImport.primaryK11_two_le_primeShift_div_ell n
  have hleft_arg : -primaryK11PrimeShift n / primaryK11Ell <= -2 := by
    have hneg : -(primaryK11PrimeShift n / primaryK11Ell) <= -2 := by
      linarith
    simpa [neg_div] using hneg
  have hright_arg : 2 <= primaryK11PrimeShift n / primaryK11Ell := by
    linarith
  have hleft :
      centeredBSplineR 11 (-primaryK11PrimeShift n / primaryK11Ell) = 0 :=
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_le_neg_two
      hleft_arg
  have hright :
      centeredBSplineR 11 (primaryK11PrimeShift n / primaryK11Ell) = 0 :=
    _root_.Q3.PSDpd.CenteredBSplineRBoundsImport.centeredBSplineR11_eq_zero_of_two_le
      hright_arg
  rw [show
    centeredBSplineR 11
      (((primaryK11Center {i0} - primaryK11Center {i0}) -
        primaryK11PrimeShift n) / primaryK11Ell) = 0 by
      simpa [primaryK11Center, activeL3Ell030Delta025Center,
        activeL3Ell030Delta025CenterRatEntry] using hleft]
  rw [show
    centeredBSplineR 11
      (((primaryK11Center {i0} - primaryK11Center {i0}) +
        primaryK11PrimeShift n) / primaryK11Ell) = 0 by
      simpa [primaryK11Center, activeL3Ell030Delta025Center,
        activeL3Ell030Delta025CenterRatEntry] using hright]
  ring

/-- First primary direct-profile scalar hbox, closed by support-zero replay. -/
theorem primaryK11DirectFinitePrimeProfileEntryHbox_0_0 :
    primaryK11DirectFinitePrimeProfileEntryHbox {i0} {i0} := by
  unfold primaryK11DirectFinitePrimeProfileEntryHbox
  rw [primaryK11DirectFinitePrimeProfileEntryValue_0_0_eq_zero]
  change
    |0 -
      (((2166638994247518151 : Rat) /
        10000000000000000000000000000000000000000000000000000000000000000
        : Rat) : Real)| <=
      (((1176041310026068113 : Rat) /
        100000000000000000000000000000000000000000000000000000000000
        : Rat) : Real)
  norm_num

/-- First primary direct-profile lower/upper interval certificate. -/
theorem primaryK11DirectFinitePrimeProfileEntryIntervalCert_0_0 :
    PrimaryK11DirectFinitePrimeProfileEntryIntervalCert {i0} {i0} :=
  primaryK11DirectFinitePrimeProfileEntryIntervalCert_of_hbox
    primaryK11DirectFinitePrimeProfileEntryHbox_0_0
"""


def row_constructor_from_interval_certs(prefix: str, row: int) -> str:
    cap = prefix_cap(prefix)
    args = [
        (
            f"    (c{row}_{j} : {cap}DirectFinitePrimeProfileEntryIntervalCert "
            f"{fin(row)} {fin(j)})"
        )
        for j in range(23)
    ]
    converted = [
        f"    ({prefix}DirectFinitePrimeProfileEntryHbox_of_interval_cert c{row}_{j})"
        for j in range(23)
    ]
    return "\n".join(
        [
            f"/-- Assemble generated {prefix} row {row} from interval certs. -/",
            f"theorem {prefix}DirectFinitePrimeProfileRowPayloadHbox_of_interval_certs_{row}",
            *args,
            f"    : {cap}DirectFinitePrimeProfileRowPayloadHbox {fin(row)} := by",
            f"  exact {prefix}DirectFinitePrimeProfileRowPayloadHbox_of_entries_{row}",
            *converted,
            "",
        ]
    )


def payload_from_rows(prefix: str) -> str:
    cap = prefix_cap(prefix)
    row_args = [
        f"    (row{r} : {cap}DirectFinitePrimeProfileRowPayloadHbox {fin(r)})"
        for r in range(23)
    ]
    payload_name = f"{prefix}DirectFinitePrimeProfilePayloadHbox"
    entry_name = f"{prefix}DirectFinitePrimeProfileEntryHbox"
    cases = [
        f"  · simpa [{entry_name}] using row{r}.h j"
        for r in range(23)
    ]
    return "\n".join(
        [
            f"/-- Row hboxes assemble the generated {prefix} direct-profile payload. -/",
            f"theorem {payload_name}_of_row_payloads",
            *row_args,
            f"    : {payload_name} := by",
            "  intro i j",
            "  fin_cases i",
            *cases,
            "",
        ]
    )


def payload_from_entries(prefix: str) -> str:
    cap = prefix_cap(prefix)
    entry_args = [
        (
            f"    (h{r}_{c} : {prefix}DirectFinitePrimeProfileEntryHbox "
            f"{fin(r)} {fin(c)})"
        )
        for r in range(23)
        for c in range(23)
    ]
    row_calls = [
        "      ("
        + f"{prefix}DirectFinitePrimeProfileRowPayloadHbox_of_entries_{r}"
        + "".join(f"\n        h{r}_{c}" for c in range(23))
        + ")"
        for r in range(23)
    ]
    return "\n".join(
        [
            f"/-- Scalar entry hboxes assemble the generated {prefix} direct-profile payload. -/",
            f"theorem {prefix}DirectFinitePrimeProfilePayloadHbox_of_entries",
            *entry_args,
            f"    : {prefix}DirectFinitePrimeProfilePayloadHbox := by",
            f"  exact {prefix}DirectFinitePrimeProfilePayloadHbox_of_row_payloads",
            *row_calls,
            "",
        ]
    )


def payload_from_interval_certs(prefix: str) -> str:
    cap = prefix_cap(prefix)
    cert_args = [
        (
            f"    (c{r}_{c} : {cap}DirectFinitePrimeProfileEntryIntervalCert "
            f"{fin(r)} {fin(c)})"
        )
        for r in range(23)
        for c in range(23)
    ]
    row_calls = [
        "      ("
        + f"{prefix}DirectFinitePrimeProfileRowPayloadHbox_of_interval_certs_{r}"
        + "".join(f"\n        c{r}_{c}" for c in range(23))
        + ")"
        for r in range(23)
    ]
    return "\n".join(
        [
            f"/-- Entry interval certs assemble the generated {prefix} direct-profile payload. -/",
            f"theorem {prefix}DirectFinitePrimeProfilePayloadHbox_of_interval_certs",
            *cert_args,
            f"    : {prefix}DirectFinitePrimeProfilePayloadHbox := by",
            f"  exact {prefix}DirectFinitePrimeProfilePayloadHbox_of_row_payloads",
            *row_calls,
            "",
        ]
    )


def interval_payload_cert(prefix: str) -> str:
    cap = prefix_cap(prefix)
    return f"""
/-- Global lower/upper interval payload certificate for the generated
{prefix} direct-profile replay.  A correlated replay generator should prove this
single bundled contract rather than emitting unrelated scalar hboxes by hand. -/
structure {cap}DirectFinitePrimeProfileIntervalPayloadCert : Prop where
  hLower :
    ∀ i j,
      {prefix}DirectFinitePrimeProfileEntryLower i j <=
        {prefix}DirectFinitePrimeProfileEntryValue i j
  hUpper :
    ∀ i j,
      {prefix}DirectFinitePrimeProfileEntryValue i j <=
        {prefix}DirectFinitePrimeProfileEntryUpper i j

/-- The global interval payload gives every scalar interval certificate. -/
theorem {prefix}DirectFinitePrimeProfileEntryIntervalCert_of_interval_payload_cert
    (cert : {cap}DirectFinitePrimeProfileIntervalPayloadCert)
    (i j : CoeffIndex23) :
    {cap}DirectFinitePrimeProfileEntryIntervalCert i j :=
  ⟨cert.hLower i j, cert.hUpper i j⟩

/-- A generated global interval payload gives the {prefix} direct-profile hbox. -/
theorem {prefix}DirectFinitePrimeProfilePayloadHbox_of_interval_payload_cert
    (cert : {cap}DirectFinitePrimeProfileIntervalPayloadCert) :
    {prefix}DirectFinitePrimeProfilePayloadHbox := by
  intro i j
  exact {prefix}DirectFinitePrimeProfileEntryHbox_of_interval_cert
    ({prefix}DirectFinitePrimeProfileEntryIntervalCert_of_interval_payload_cert
      cert i j)
"""


def delta_interval_payload_cert(
    prefix: str,
    k: int,
    ell: str,
    weight: str,
    shift: str,
    p_table_name: str,
    radius_table_name: str,
) -> str:
    cap = prefix_cap(prefix)
    bounds = delta_bounds_from_lean_tables(p_table_name, radius_table_name)
    lower_cases = [
        f"  | {delta} => {rat_expr(bounds[delta][0])}" for delta in range(-22, 23)
    ]
    upper_cases = [
        f"  | {delta} => {rat_expr(bounds[delta][1])}" for delta in range(-22, 23)
    ]
    return "\n".join(
        [
            f"/-- Coefficient index delta for the {prefix} direct-profile replay. -/",
            f"def {prefix}DirectFinitePrimeProfileEntryDelta",
            "    (i j : CoeffIndex23) : Int :=",
            "  (j.1 : Int) - (i.1 : Int)",
            "",
            f"theorem {prefix}DirectFinitePrimeProfileEntryDelta_ge_neg22",
            "    (i j : CoeffIndex23) :",
            f"    -22 <= {prefix}DirectFinitePrimeProfileEntryDelta i j := by",
            f"  unfold {prefix}DirectFinitePrimeProfileEntryDelta",
            "  omega",
            "",
            f"theorem {prefix}DirectFinitePrimeProfileEntryDelta_le_22",
            "    (i j : CoeffIndex23) :",
            f"    {prefix}DirectFinitePrimeProfileEntryDelta i j <= 22 := by",
            f"  unfold {prefix}DirectFinitePrimeProfileEntryDelta",
            "  omega",
            "",
            f"/-- Delta-compressed {prefix} direct finite-prime profile value. -/",
            f"def {prefix}DirectFinitePrimeProfileDeltaValue (delta : Int) : Real :=",
            "  centeredBSplineFinitePrimeKernelProfile",
            f"    {k} {ell} {weight} {shift}",
            "    ((delta : Real) / 4)",
            "",
            f"theorem {prefix}DirectFinitePrimeProfileEntryValue_eq_deltaValue",
            "    (i j : CoeffIndex23) :",
            f"    {prefix}DirectFinitePrimeProfileEntryValue i j =",
            f"      {prefix}DirectFinitePrimeProfileDeltaValue",
            f"        ({prefix}DirectFinitePrimeProfileEntryDelta i j) := by",
            f"  unfold {prefix}DirectFinitePrimeProfileEntryValue",
            f"  unfold {prefix}DirectFinitePrimeProfileDeltaValue",
            f"  unfold {prefix}DirectFinitePrimeProfileEntryDelta",
            f"  rw [{prefix}Center_sub_eq_index_delta]",
            "  congr 1",
            "  norm_num",
            "",
            f"/-- Synchronized lower endpoint for each {prefix} index delta.",
            "It is the maximum imported entry lower endpoint over that diagonal. -/",
            f"def {prefix}DirectFinitePrimeProfileDeltaLower",
            "    (delta : Int) : Real :=",
            "  match delta with",
            *lower_cases,
            "  | _ => 0",
            "",
            f"/-- Synchronized upper endpoint for each {prefix} index delta.",
            "It is the minimum imported entry upper endpoint over that diagonal. -/",
            f"def {prefix}DirectFinitePrimeProfileDeltaUpper",
            "    (delta : Int) : Real :=",
            "  match delta with",
            *upper_cases,
            "  | _ => 0",
            "",
            f"/-- Exact table-envelope check connecting entry boxes to the",
            f"delta-compressed {prefix} boxes.  This is separate from the analytic",
            "direct-profile replay: it is only a rational table containment layer. -/",
            f"structure {cap}DirectFinitePrimeProfileDeltaEnvelopeCert : Prop where",
            "  hLower :",
            "    forall i j,",
            f"      {prefix}DirectFinitePrimeProfileEntryLower i j <=",
            f"        {prefix}DirectFinitePrimeProfileDeltaLower",
            f"          ({prefix}DirectFinitePrimeProfileEntryDelta i j)",
            "  hUpper :",
            "    forall i j,",
            f"      {prefix}DirectFinitePrimeProfileDeltaUpper",
            f"          ({prefix}DirectFinitePrimeProfileEntryDelta i j) <=",
            f"        {prefix}DirectFinitePrimeProfileEntryUpper i j",
            "",
            f"/-- Delta-compressed analytic interval payload for the {prefix}",
            "direct-profile replay.  Proving this contract needs only the 45",
            "index-delta profiles, not 529 unrelated entry profiles. -/",
            f"structure {cap}DirectFinitePrimeProfileDeltaIntervalPayloadCert : Prop where",
            "  hLower :",
            "    forall delta : Int,",
            "      -22 <= delta ->",
            "      delta <= 22 ->",
            f"      {prefix}DirectFinitePrimeProfileDeltaLower delta <=",
            f"        {prefix}DirectFinitePrimeProfileDeltaValue delta",
            "  hUpper :",
            "    forall delta : Int,",
            "      -22 <= delta ->",
            "      delta <= 22 ->",
            f"      {prefix}DirectFinitePrimeProfileDeltaValue delta <=",
            f"        {prefix}DirectFinitePrimeProfileDeltaUpper delta",
            "",
            f"/-- Delta interval payload plus the exact table envelope gives the",
            f"global {prefix} direct-profile interval payload. -/",
            f"theorem {prefix}DirectFinitePrimeProfileIntervalPayloadCert_of_delta_interval_payload_cert",
            f"    (envelope : {cap}DirectFinitePrimeProfileDeltaEnvelopeCert)",
            f"    (delta_cert : {cap}DirectFinitePrimeProfileDeltaIntervalPayloadCert) :",
            f"    {cap}DirectFinitePrimeProfileIntervalPayloadCert := by",
            "  constructor",
            "  · intro i j",
            "    have henv := envelope.hLower i j",
            "    have hdelta := delta_cert.hLower",
            f"      ({prefix}DirectFinitePrimeProfileEntryDelta i j)",
            f"      ({prefix}DirectFinitePrimeProfileEntryDelta_ge_neg22 i j)",
            f"      ({prefix}DirectFinitePrimeProfileEntryDelta_le_22 i j)",
            f"    rw [{prefix}DirectFinitePrimeProfileEntryValue_eq_deltaValue i j]",
            "    exact le_trans henv hdelta",
            "  · intro i j",
            "    have hdelta := delta_cert.hUpper",
            f"      ({prefix}DirectFinitePrimeProfileEntryDelta i j)",
            f"      ({prefix}DirectFinitePrimeProfileEntryDelta_ge_neg22 i j)",
            f"      ({prefix}DirectFinitePrimeProfileEntryDelta_le_22 i j)",
            "    have henv := envelope.hUpper i j",
            f"    rw [{prefix}DirectFinitePrimeProfileEntryValue_eq_deltaValue i j]",
            "    exact le_trans hdelta henv",
            "",
            f"/-- Delta interval payload plus the exact table envelope gives the",
            f"{prefix} direct-profile hbox payload. -/",
            f"theorem {prefix}DirectFinitePrimeProfilePayloadHbox_of_delta_interval_payload_cert",
            f"    (envelope : {cap}DirectFinitePrimeProfileDeltaEnvelopeCert)",
            f"    (delta_cert : {cap}DirectFinitePrimeProfileDeltaIntervalPayloadCert) :",
            f"    {prefix}DirectFinitePrimeProfilePayloadHbox := by",
            f"  exact {prefix}DirectFinitePrimeProfilePayloadHbox_of_interval_payload_cert",
            f"    ({prefix}DirectFinitePrimeProfileIntervalPayloadCert_of_delta_interval_payload_cert",
            "      envelope delta_cert)",
            "",
        ]
    )


def delta_envelope_proof(
    prefix: str,
    p_table_name: str,
    radius_table_name: str,
) -> str:
    cap = prefix_cap(prefix)
    p_table = read_lean_rat_table(p_table_name)
    radius_table = read_lean_rat_table(radius_table_name)
    pieces: list[str] = []
    for i in range(23):
        for j in range(23):
            p_expr = p_table[(i, j)]
            rad_expr = radius_table[(i, j)]
            pieces.extend(
                [
                    f"private theorem {prefix}DirectFinitePrimeProfileDeltaEnvelope_lower_{i}_{j} :",
                    f"    {prefix}DirectFinitePrimeProfileEntryLower {fin(i)} {fin(j)} <=",
                    f"      {prefix}DirectFinitePrimeProfileDeltaLower",
                    f"        ({prefix}DirectFinitePrimeProfileEntryDelta {fin(i)} {fin(j)}) := by",
                    f"  unfold {prefix}DirectFinitePrimeProfileEntryLower",
                    f"  unfold {prefix}DirectFinitePrimeProfileMid {prefix}DirectFinitePrimeProfileRad",
                    f"  unfold {prefix}P {prefix}PRat {prefix}PRadius {prefix}PRadiusRat",
                    f"  change (({p_table_name} {i} {j} : Real) - ({radius_table_name} {i} {j} : Real) <=",
                    f"    {prefix}DirectFinitePrimeProfileDeltaLower",
                    f"      ({prefix}DirectFinitePrimeProfileEntryDelta {fin(i)} {fin(j)}))",
                    f"  rw [show {p_table_name} {i} {j} = {p_expr} by rfl]",
                    f"  rw [show {radius_table_name} {i} {j} = {rad_expr} by rfl]",
                    f"  norm_num [{prefix}DirectFinitePrimeProfileEntryDelta,",
                    f"    {prefix}DirectFinitePrimeProfileDeltaLower]",
                    "",
                    f"private theorem {prefix}DirectFinitePrimeProfileDeltaEnvelope_upper_{i}_{j} :",
                    f"    {prefix}DirectFinitePrimeProfileDeltaUpper",
                    f"        ({prefix}DirectFinitePrimeProfileEntryDelta {fin(i)} {fin(j)}) <=",
                    f"      {prefix}DirectFinitePrimeProfileEntryUpper {fin(i)} {fin(j)} := by",
                    f"  unfold {prefix}DirectFinitePrimeProfileEntryUpper",
                    f"  unfold {prefix}DirectFinitePrimeProfileMid {prefix}DirectFinitePrimeProfileRad",
                    f"  unfold {prefix}P {prefix}PRat {prefix}PRadius {prefix}PRadiusRat",
                    f"  change ({prefix}DirectFinitePrimeProfileDeltaUpper",
                    f"      ({prefix}DirectFinitePrimeProfileEntryDelta {fin(i)} {fin(j)}) <=",
                    f"    ({p_table_name} {i} {j} : Real) + ({radius_table_name} {i} {j} : Real))",
                    f"  rw [show {p_table_name} {i} {j} = {p_expr} by rfl]",
                    f"  rw [show {radius_table_name} {i} {j} = {rad_expr} by rfl]",
                    f"  norm_num [{prefix}DirectFinitePrimeProfileEntryDelta,",
                    f"    {prefix}DirectFinitePrimeProfileDeltaUpper]",
                    "",
                ]
            )
    lower_cases = [
        f"    · exact {prefix}DirectFinitePrimeProfileDeltaEnvelope_lower_{i}_{j}"
        for i in range(23)
        for j in range(23)
    ]
    upper_cases = [
        f"    · exact {prefix}DirectFinitePrimeProfileDeltaEnvelope_upper_{i}_{j}"
        for i in range(23)
        for j in range(23)
    ]
    pieces.extend(
        [
            f"/-- Generated exact rational table-envelope certificate for the",
            f"{prefix} delta-compressed direct-profile replay. -/",
            f"theorem {prefix}DirectFinitePrimeProfileDeltaEnvelopeCert :",
            f"    {cap}DirectFinitePrimeProfileDeltaEnvelopeCert := by",
            "  constructor",
            "  · intro i j",
            "    fin_cases i <;> fin_cases j",
            *lower_cases,
            "  · intro i j",
            "    fin_cases i <;> fin_cases j",
            *upper_cases,
            "",
        ]
    )
    return "\n".join(pieces)


def analytic_p_from_rows(prefix: str) -> str:
    cap = prefix_cap(prefix)
    row_args = [
        f"    (row{r} : {cap}DirectFinitePrimeProfileRowPayloadHbox {fin(r)})"
        for r in range(23)
    ]
    theorem_name = f"{prefix}AnalyticP_entry_hbox_of_direct_profile_rows"
    payload_name = f"{prefix}DirectFinitePrimeProfilePayloadHbox_of_row_payloads"
    receiver = f"{prefix}AnalyticP_entry_hbox_of_direct_profile_payload_hbox"
    analytic = (
        "CenteredCoeffBaseHboxImport.primaryK11AnalyticP"
        if prefix == "primaryK11"
        else "CenteredCoeffBaseHboxImport.controlK9AnalyticP"
    )
    matrix = "primaryK11P" if prefix == "primaryK11" else "controlK9P"
    radius = "primaryK11PRadius" if prefix == "primaryK11" else "controlK9PRadius"
    return "\n".join(
        [
            f"/-- Generated {prefix} row payloads feed the analytic P hbox. -/",
            f"theorem {theorem_name}",
            *row_args,
            "    : Q3.Proofs.matrixEntrywiseAbsLe",
            f"      {analytic} {matrix} {radius} := by",
            f"  exact {receiver}",
            f"    ({payload_name}",
            *[f"      row{r}" for r in range(23)],
            "    )",
            "",
        ]
    )


def analytic_p_from_interval_payload_cert(prefix: str) -> str:
    cap = prefix_cap(prefix)
    theorem_name = f"{prefix}AnalyticP_entry_hbox_of_direct_profile_interval_payload_cert"
    receiver = f"{prefix}AnalyticP_entry_hbox_of_direct_profile_payload_hbox"
    payload = f"{prefix}DirectFinitePrimeProfilePayloadHbox_of_interval_payload_cert"
    analytic = (
        "CenteredCoeffBaseHboxImport.primaryK11AnalyticP"
        if prefix == "primaryK11"
        else "CenteredCoeffBaseHboxImport.controlK9AnalyticP"
    )
    matrix = "primaryK11P" if prefix == "primaryK11" else "controlK9P"
    radius = "primaryK11PRadius" if prefix == "primaryK11" else "controlK9PRadius"
    return "\n".join(
        [
            f"/-- A generated {prefix} interval payload feeds the analytic P hbox. -/",
            f"theorem {theorem_name}",
            f"    (cert : {cap}DirectFinitePrimeProfileIntervalPayloadCert)",
            "    : Q3.Proofs.matrixEntrywiseAbsLe",
            f"      {analytic} {matrix} {radius} := by",
            f"  exact {receiver} ({payload} cert)",
            "",
        ]
    )


def analytic_p_from_delta_interval_payload_cert(prefix: str) -> str:
    cap = prefix_cap(prefix)
    theorem_name = f"{prefix}AnalyticP_entry_hbox_of_delta_interval_payload_cert"
    receiver = f"{prefix}AnalyticP_entry_hbox_of_direct_profile_payload_hbox"
    payload = f"{prefix}DirectFinitePrimeProfilePayloadHbox_of_delta_interval_payload_cert"
    analytic = (
        "CenteredCoeffBaseHboxImport.primaryK11AnalyticP"
        if prefix == "primaryK11"
        else "CenteredCoeffBaseHboxImport.controlK9AnalyticP"
    )
    matrix = "primaryK11P" if prefix == "primaryK11" else "controlK9P"
    radius = "primaryK11PRadius" if prefix == "primaryK11" else "controlK9PRadius"
    return "\n".join(
        [
            f"/-- A generated {prefix} delta interval payload feeds the analytic P hbox. -/",
            f"theorem {theorem_name}",
            f"    (envelope : {cap}DirectFinitePrimeProfileDeltaEnvelopeCert)",
            f"    (delta_cert : {cap}DirectFinitePrimeProfileDeltaIntervalPayloadCert)",
            "    : Q3.Proofs.matrixEntrywiseAbsLe",
            f"      {analytic} {matrix} {radius} := by",
            f"  exact {receiver} ({payload} envelope delta_cert)",
            "",
        ]
    )


def active_cert_from_rows() -> str:
    primary_rows = [
        f"    (primary_row{r} : PrimaryK11DirectFinitePrimeProfileRowPayloadHbox {fin(r)})"
        for r in range(23)
    ]
    control_rows = [
        f"    (control_row{r} : ControlK9DirectFinitePrimeProfileRowPayloadHbox {fin(r)})"
        for r in range(23)
    ]
    return "\n".join(
        [
            "/-- Generated direct-profile row payloads feed the active entry-hbox bundle. -/",
            "theorem activeCenteredCoeffEntryHboxCert_of_directProfileRows",
            "    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe",
            "      CenteredCoeffBaseHboxImport.primaryK11AnalyticA",
            "      primaryK11A primaryK11ARadius)",
            *primary_rows,
            "    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe",
            "      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)",
            "    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe",
            "      CenteredCoeffBaseHboxImport.controlK9AnalyticA",
            "      controlK9A controlK9ARadius)",
            *control_rows,
            "    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe",
            "      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :",
            "    CenteredCoeffEntryHboxImport.ActiveCenteredCoeffEntryHboxCert := by",
            "  exact",
            "    CenteredCoeffEntryHboxImport.activeCenteredCoeffEntryHboxCert_of_directPrimeProfilePayloadHboxes",
            "      primary_hA",
            "      (primaryK11DirectFinitePrimeProfilePayloadHbox_of_row_payloads",
            *[f"        primary_row{r}" for r in range(23)],
            "      )",
            "      primary_hP0",
            "      control_hA",
            "      (controlK9DirectFinitePrimeProfilePayloadHbox_of_row_payloads",
            *[f"        control_row{r}" for r in range(23)],
            "      )",
            "      control_hP0",
            "",
        ]
    )


def active_cert_from_interval_payload_certs() -> str:
    return "\n".join(
        [
            "/-- Generated direct-profile interval payloads feed the active entry-hbox bundle. -/",
            "theorem activeCenteredCoeffEntryHboxCert_of_directProfileIntervalPayloadCerts",
            "    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe",
            "      CenteredCoeffBaseHboxImport.primaryK11AnalyticA",
            "      primaryK11A primaryK11ARadius)",
            "    (primary_profile : PrimaryK11DirectFinitePrimeProfileIntervalPayloadCert)",
            "    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe",
            "      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)",
            "    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe",
            "      CenteredCoeffBaseHboxImport.controlK9AnalyticA",
            "      controlK9A controlK9ARadius)",
            "    (control_profile : ControlK9DirectFinitePrimeProfileIntervalPayloadCert)",
            "    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe",
            "      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :",
            "    CenteredCoeffEntryHboxImport.ActiveCenteredCoeffEntryHboxCert := by",
            "  exact",
            "    CenteredCoeffEntryHboxImport.activeCenteredCoeffEntryHboxCert_of_directPrimeProfilePayloadHboxes",
            "      primary_hA",
            "      (primaryK11DirectFinitePrimeProfilePayloadHbox_of_interval_payload_cert",
            "        primary_profile)",
            "      primary_hP0",
            "      control_hA",
            "      (controlK9DirectFinitePrimeProfilePayloadHbox_of_interval_payload_cert",
            "        control_profile)",
            "      control_hP0",
            "",
        ]
    )


def active_cert_from_delta_interval_payload_certs() -> str:
    return "\n".join(
        [
            "/-- Generated delta-compressed direct-profile interval payloads feed the active entry-hbox bundle. -/",
            "theorem activeCenteredCoeffEntryHboxCert_of_deltaDirectProfileIntervalPayloadCerts",
            "    (primary_hA : Q3.Proofs.matrixEntrywiseAbsLe",
            "      CenteredCoeffBaseHboxImport.primaryK11AnalyticA",
            "      primaryK11A primaryK11ARadius)",
            "    (primary_envelope : PrimaryK11DirectFinitePrimeProfileDeltaEnvelopeCert)",
            "    (primary_delta : PrimaryK11DirectFinitePrimeProfileDeltaIntervalPayloadCert)",
            "    (primary_hP0 : Q3.Proofs.matrixEntrywiseAbsLe",
            "      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius)",
            "    (control_hA : Q3.Proofs.matrixEntrywiseAbsLe",
            "      CenteredCoeffBaseHboxImport.controlK9AnalyticA",
            "      controlK9A controlK9ARadius)",
            "    (control_envelope : ControlK9DirectFinitePrimeProfileDeltaEnvelopeCert)",
            "    (control_delta : ControlK9DirectFinitePrimeProfileDeltaIntervalPayloadCert)",
            "    (control_hP0 : Q3.Proofs.matrixEntrywiseAbsLe",
            "      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :",
            "    CenteredCoeffEntryHboxImport.ActiveCenteredCoeffEntryHboxCert := by",
            "  exact",
            "    CenteredCoeffEntryHboxImport.activeCenteredCoeffEntryHboxCert_of_directPrimeProfilePayloadHboxes",
            "      primary_hA",
            "      (primaryK11DirectFinitePrimeProfilePayloadHbox_of_delta_interval_payload_cert",
            "        primary_envelope primary_delta)",
            "      primary_hP0",
            "      control_hA",
            "      (controlK9DirectFinitePrimeProfilePayloadHbox_of_delta_interval_payload_cert",
            "        control_envelope control_delta)",
            "      control_hP0",
            "",
        ]
    )


def block(
    prefix: str,
    k: int,
    ell: str,
    weight: str,
    shift: str,
    center: str,
    midpoint_csv: Path,
    radius_csv: Path,
) -> str:
    pieces: list[str] = [
        entry_prop(prefix, k, ell, weight, shift, center),
    ]
    if prefix == "primaryK11":
        pieces.append(primary_00_support_zero_cert())
    pieces.extend(row_constructor(prefix, row) for row in range(23))
    pieces.extend(row_constructor_from_interval_certs(prefix, row) for row in range(23))
    pieces.append(payload_from_rows(prefix))
    pieces.append(payload_from_entries(prefix))
    pieces.append(payload_from_interval_certs(prefix))
    pieces.append(interval_payload_cert(prefix))
    if prefix == "primaryK11":
        pieces.append(
            delta_interval_payload_cert(
                prefix,
                k,
                ell,
                weight,
                shift,
                "primaryK11PEntryRat",
                "primaryK11PRadiusEntryRat",
            )
        )
        pieces.append(
            delta_envelope_proof(
                prefix,
                "primaryK11PEntryRat",
                "primaryK11PRadiusEntryRat",
            )
        )
    else:
        pieces.append(
            delta_interval_payload_cert(
                prefix,
                k,
                ell,
                weight,
                shift,
                "controlK9PEntryRat",
                "controlK9PRadiusEntryRat",
            )
        )
        pieces.append(
            delta_envelope_proof(
                prefix,
                "controlK9PEntryRat",
                "controlK9PRadiusEntryRat",
            )
        )
    pieces.append(analytic_p_from_rows(prefix))
    pieces.append(analytic_p_from_interval_payload_cert(prefix))
    pieces.append(analytic_p_from_delta_interval_payload_cert(prefix))
    return "\n".join(pieces)


def render() -> str:
    lines: Iterable[str] = [
        "import Q3.Proofs.PSD_CenteredCoeffEntryHboxImport",
        "",
        "set_option linter.mathlibStandardSet false",
        "set_option maxHeartbeats 0",
        "",
        "/-!",
        "Generated Step33 direct finite-prime profile payload receiver surface.",
        "",
        "This module does not trust Arb output.  It only creates the kernel-checked",
        "row/entry assembly layer expected by the direct-profile numeric replay",
        "generator.  The remaining scalar entry hboxes must still be proved by",
        "ordinary Lean terms, with no holes or unsupported assumptions.",
        "-/",
        "",
        "noncomputable section",
        "",
        "namespace Q3",
        "namespace PSDpd",
        "namespace CenteredCoeffPrimeDirectProfilePayloadImport",
        "",
        "open CenteredCoeffPayloadImport",
        "open CenteredCoeffDictionaryImport",
        "open CenteredCoeffBaseHboxImport",
        "open CenteredCoeffAnalyticP0Import",
        "open CenteredCoeffPrimeEntryHboxImport",
        "open CenteredCoeffEntryHboxImport",
        "",
        "private theorem abs_sub_le_of_lower_upper",
        "    (x mid rad : Real)",
        "    (hLower : mid - rad <= x)",
        "    (hUpper : x <= mid + rad) :",
        "    |x - mid| <= rad := by",
        "  rw [abs_sub_le_iff]",
        "  constructor <;> linarith",
        "",
        "private theorem lower_upper_of_abs_sub_le",
        "    (x mid rad : Real)",
        "    (h : |x - mid| <= rad) :",
        "    mid - rad <= x ∧ x <= mid + rad := by",
        "  rw [abs_sub_le_iff] at h",
        "  constructor <;> linarith",
        "",
        block(
            "primaryK11",
            11,
            "primaryK11Ell",
            "primaryK11PrimeWeight",
            "primaryK11PrimeShift",
            "primaryK11Center",
            PRIMARY_MID,
            PRIMARY_RAD,
        ),
        block(
            "controlK9",
            9,
            "controlK9Ell",
            "controlK9PrimeWeight",
            "controlK9PrimeShift",
            "controlK9Center",
            CONTROL_MID,
            CONTROL_RAD,
        ),
        active_cert_from_rows(),
        active_cert_from_interval_payload_certs(),
        active_cert_from_delta_interval_payload_certs(),
        "end CenteredCoeffPrimeDirectProfilePayloadImport",
        "end PSDpd",
        "end Q3",
        "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=OUT)
    parser.add_argument("--audit-json", type=Path, default=AUDIT_JSON)
    parser.add_argument("--skip-audit-check", action="store_true")
    args = parser.parse_args()

    check_payload_shapes()
    if not args.skip_audit_check:
        check_audit(args.audit_json)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(render())
    print(f"wrote {args.out.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
