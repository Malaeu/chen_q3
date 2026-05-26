#!/usr/bin/env python3
"""Generate Lean Q-row hbox certificates for the active Step32F payload."""

from __future__ import annotations

import csv
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
OUT = REPO / "Q3/Proofs/PSD_CenteredCoeffQRowImport.lean"
PRIMARY_MID = REPO / "docs/insights/q3_psdpd_step22_midpoints_k11.csv"
PRIMARY_RAD = REPO / "docs/insights/q3_psdpd_step22_radii_k11.csv"
CONTROL_MID = REPO / "docs/insights/q3_psdpd_step22_midpoints_k9.csv"
CONTROL_RAD = REPO / "docs/insights/q3_psdpd_step22_radii_k9.csv"
TAYLOR_ORDER = 23


def dec_frac(text: str) -> Fraction:
    return Fraction(Decimal(text.strip()))


def read_q_csv(path: Path, column: str) -> dict[tuple[int, int], Fraction]:
    out: dict[tuple[int, int], Fraction] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["matrix"].strip() != "Q":
                continue
            out[(int(row["i"]), int(row["j"]))] = dec_frac(row[column])
    return out


def lean_real(q: Fraction) -> str:
    if q.denominator == 1:
        return f"(({q.numerator} : Real))"
    return f"(({q.numerator} : Real) / ({q.denominator} : Real))"


def center(j: int) -> Fraction:
    return Fraction(-27, 10) + Fraction(j, 4)


def x_for(row: int, col: int) -> Fraction:
    c = center(col)
    if row == 0:
        return c / 2
    if row == 1:
        return -c / 2
    raise ValueError(row)


def qrow_bound_name(row: int, col: int) -> str:
    return f"qrow_bound_{row}_{col}"


def scalar_lemma(row: int, col: int, mid: Fraction, rad: Fraction) -> list[str]:
    x = lean_real(x_for(row, col))
    m = lean_real(mid)
    r = lean_real(rad)
    name = qrow_bound_name(row, col)
    return [
        f"private lemma {name} :",
        f"    |Real.exp {x} - {m}| <= {r} := by",
        "  exact exp_abs_sub_le_of_half_taylor",
        f"    {x} {m} {r} (n := {TAYLOR_ORDER})",
        "    (by norm_num)",
        "    (by norm_num)",
        "    (by norm_num [qrowTaylorS, qrowTaylorE])",
        "    (by norm_num [qrowTaylorS, qrowTaylorE])",
        "    (by norm_num [qrowTaylorS, qrowTaylorE])",
        "",
    ]


def primary_case(row: int, col: int) -> list[str]:
    return [
        "  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,",
        "      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,",
        "      primaryK11Center, activeL3Ell030Delta025Center,",
        "      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,",
        "      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,",
        "      primaryK11QRadiusEntryRat]",
        f"    simpa [neg_div] using {qrow_bound_name(row, col)}",
    ]


def control_case(row: int, col: int) -> list[str]:
    return [
        "  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,",
        "      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,",
        "      controlK9Center, activeL3Ell030Delta025Center,",
        "      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,",
        "      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,",
        "      controlK9QRadiusEntryRat]",
        f"    simpa [neg_div] using {qrow_bound_name(row, col)}",
    ]


def main() -> None:
    primary_mid = read_q_csv(PRIMARY_MID, "mid")
    primary_rad = read_q_csv(PRIMARY_RAD, "rad")
    control_mid = read_q_csv(CONTROL_MID, "mid")
    control_rad = read_q_csv(CONTROL_RAD, "rad")
    if primary_mid != control_mid or primary_rad != control_rad:
        raise SystemExit("primary/control Q midpoint or radius payloads differ")
    expected = {(i, j) for i in range(2) for j in range(23)}
    if set(primary_mid) != expected or set(primary_rad) != expected:
        raise SystemExit("unexpected Q payload shape")

    lines: list[str] = [
        "import Q3.Proofs.PSD_CenteredCoeffDictionaryImport",
        "import Q3.Proofs.PSD_PenaltyCertificate",
        "import Q3.Proofs.PrimeCert.IntervalLemmas",
        "",
        "set_option linter.mathlibStandardSet false",
        "set_option maxHeartbeats 0",
        "",
        "/-!",
        "Generated Step32G Q-row hbox certificates.",
        "",
        "The scalar certificates use `Real.exp_bound` at Taylor order 23 after",
        "splitting each active exponent as `exp x = exp (x / 2) ^ 2`, so all",
        "Taylor arguments satisfy `|x / 2| <= 1`.",
        "-/",
        "",
        "noncomputable section",
        "",
        "namespace Q3",
        "namespace PSDpd",
        "namespace CenteredCoeffQRowImport",
        "",
        "open CenteredCoeffPayloadImport",
        "open CenteredCoeffDictionaryImport",
        "",
        "private def qrowTaylorS (x : Real) (n : Nat) : Real :=",
        "  ∑ m ∈ Finset.range n, (x / 2) ^ m / (Nat.factorial m)",
        "",
        "private def qrowTaylorE (x : Real) (n : Nat) : Real :=",
        "  |x / 2| ^ n * ((n.succ : Real) / (Nat.factorial n * n))",
        "",
        "private lemma exp_abs_sub_le_of_half_taylor",
        "    (x m r : Real) {n : Nat}",
        "    (hn : 0 < n)",
        "    (hy : |x / 2| <= (1 : Real))",
        "    (hlow0 : 0 <= qrowTaylorS x n - qrowTaylorE x n)",
        "    (htargetLow : m - r <= (qrowTaylorS x n - qrowTaylorE x n) ^ 2)",
        "    (htargetHigh : (qrowTaylorS x n + qrowTaylorE x n) ^ 2 <= m + r) :",
        "    |Real.exp x - m| <= r := by",
        "  have hbound : |Real.exp (x / 2) - qrowTaylorS x n| <= qrowTaylorE x n := by",
        "    simpa [qrowTaylorS, qrowTaylorE] using",
        "      (Real.exp_bound (x := x / 2) hy (n := n) hn)",
        "  have hlow : qrowTaylorS x n - qrowTaylorE x n <= Real.exp (x / 2) := by",
        "    have h := (abs_sub_le_iff.mp hbound).2",
        "    linarith",
        "  have hhigh : Real.exp (x / 2) <= qrowTaylorS x n + qrowTaylorE x n := by",
        "    have h := (abs_sub_le_iff.mp hbound).1",
        "    linarith",
        "  have hexp : Real.exp x = Real.exp (x / 2) ^ 2 := by",
        "    exact Q3.Proofs.PrimeCert.exp_eq_pow_div_nat x (n := 2) (by norm_num)",
        "  have hpowLow : (qrowTaylorS x n - qrowTaylorE x n) ^ 2 <= Real.exp x := by",
        "    rw [hexp]",
        "    exact pow_le_pow_left₀ hlow0 hlow 2",
        "  have hpowHigh : Real.exp x <= (qrowTaylorS x n + qrowTaylorE x n) ^ 2 := by",
        "    rw [hexp]",
        "    exact pow_le_pow_left₀ (Real.exp_nonneg _) hhigh 2",
        "  rw [abs_sub_le_iff]",
        "  constructor <;> nlinarith",
        "",
    ]

    for row in range(2):
        for col in range(23):
            lines.extend(scalar_lemma(row, col, primary_mid[(row, col)], primary_rad[(row, col)]))

    lines.extend(
        [
            "/-- Imported primary `k=11` Q rows enclose the active analytic boundary rows. -/",
            "theorem primaryK11QRadius_hbox :",
            "    Q3.Proofs.matrixEntrywiseAbsLe",
            "      primaryK11AnalyticQ primaryK11Q primaryK11QRadius := by",
            "  intro i j",
            "  fin_cases i <;> fin_cases j",
        ]
    )
    for row in range(2):
        for col in range(23):
            lines.extend(primary_case(row, col))
    lines.append("")

    lines.extend(
        [
            "/-- Imported control `k=9` Q rows enclose the active analytic boundary rows. -/",
            "theorem controlK9QRadius_hbox :",
            "    Q3.Proofs.matrixEntrywiseAbsLe",
            "      controlK9AnalyticQ controlK9Q controlK9QRadius := by",
            "  intro i j",
            "  fin_cases i <;> fin_cases j",
        ]
    )
    for row in range(2):
        for col in range(23):
            lines.extend(control_case(row, col))

    lines.extend(
        [
            "",
            "end CenteredCoeffQRowImport",
            "end PSDpd",
            "end Q3",
            "",
        ]
    )

    OUT.write_text("\n".join(lines))
    print(f"wrote {OUT.relative_to(REPO)}")


if __name__ == "__main__":
    main()
