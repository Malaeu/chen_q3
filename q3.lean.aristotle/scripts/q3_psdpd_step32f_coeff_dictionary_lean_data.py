#!/usr/bin/env python3
"""
Generate the concrete coefficient dictionary import for the active Step 32F
centered B-spline coefficient blocks.

This file deliberately emits only exact dictionary data:

  * the 23 center locations used by the Step22 payload matrices;
  * the finite prime-power shift index for L = 3;
  * the exact analytic shift/weight functions used by the finite Prime receiver.

It does not claim that midpoint CSV matrices are definitionally equal to the
analytic contract matrices.  That equality/interval bridge is a later proof
node.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


HEADER = """import Q3.Proofs.PSD_CenteredCoeffPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffDictionaryImport

open CenteredCoeffPayloadImport

/-!
Exact dictionary data for the active Step 32F centered coefficient payloads.

The midpoint/radius matrix import records checked numerical matrices.  This
file records the generator-side finite dictionaries that those matrices came
from: the 23 packet centers and the L=3 finite prime-power shifts.

This is not yet a `CertifiedCenteredBSplineCoeffBlock`.  The remaining bridge is
to connect the analytic contract entries, or interval enclosures for them, to
the imported midpoint/radius payload.
-/

"""

FOOTER = """
end CenteredCoeffDictionaryImport
end PSDpd
end Q3
"""


@dataclass(frozen=True)
class PrimeShift:
    p: int
    r_pow: int

    @property
    def value(self) -> float:
        return self.r_pow * math.log(self.p)


def sieve_primes(n: int) -> list[int]:
    if n < 2:
        return []
    is_prime = [True] * (n + 1)
    is_prime[0] = False
    is_prime[1] = False
    q = 2
    while q * q <= n:
        if is_prime[q]:
            for k in range(q * q, n + 1, q):
                is_prime[k] = False
        q += 1
    return [i for i, ok in enumerate(is_prime) if ok]


def prime_power_shifts(L: float) -> list[PrimeShift]:
    max_n = int(math.floor(math.exp(2.0 * L))) + 1
    cutoff = 2.0 * L + 1e-14
    out: list[PrimeShift] = []
    for p in sieve_primes(max_n):
        logp = math.log(p)
        r_pow = 1
        while r_pow * logp <= cutoff:
            out.append(PrimeShift(p=p, r_pow=r_pow))
            r_pow += 1
    out.sort(key=lambda item: item.value)
    return out


def lean_rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"(({value.numerator} : Rat))"
    return f"(({value.numerator} : Rat) / {value.denominator})"


def emit_nat_entry(name: str, values: list[int]) -> list[str]:
    lines = [f"def {name} : Nat -> Nat"]
    for i, value in enumerate(values):
        lines.append(f"  | {i} => {value}")
    lines.append("  | _ => 0")
    lines.append("")
    return lines


def emit_rat_entry(name: str, values: list[Fraction]) -> list[str]:
    lines = [f"def {name} : Nat -> Rat"]
    for i, value in enumerate(values):
        lines.append(f"  | {i} => {lean_rat(value)}")
    lines.append("  | _ => 0")
    lines.append("")
    return lines


def build_lean() -> str:
    centers = [Fraction(-27, 10) + Fraction(i, 4) for i in range(23)]
    shifts = prime_power_shifts(3.0)
    if len(shifts) != 98:
        raise SystemExit(f"unexpected L=3 prime-shift count: {len(shifts)}")

    lines: list[str] = [HEADER.rstrip(), ""]
    lines.append("abbrev PrimeShiftIndexL3 := Fin 98")
    lines.append("")
    lines.extend(
        emit_rat_entry("activeL3Ell030Delta025CenterRatEntry", centers)
    )
    lines.append("/-- The 23 packet centers used by the active L=3, ell=0.30, delta=0.25 blocks. -/")
    lines.append("def activeL3Ell030Delta025Center (i : CoeffIndex23) : Real :=")
    lines.append("  (activeL3Ell030Delta025CenterRatEntry i.1 : Real)")
    lines.append("")

    lines.extend(emit_nat_entry("activeL3PrimeBaseEntry", [s.p for s in shifts]))
    lines.extend(
        emit_nat_entry("activeL3PrimeExponentEntry", [s.r_pow for s in shifts])
    )
    lines.append("/-- Prime base for the L=3 finite prime-power shift dictionary. -/")
    lines.append("def activeL3PrimeBase (n : PrimeShiftIndexL3) : Nat :=")
    lines.append("  activeL3PrimeBaseEntry n.1")
    lines.append("")
    lines.append("/-- Prime-power exponent for the L=3 finite prime-power shift dictionary. -/")
    lines.append("def activeL3PrimeExponent (n : PrimeShiftIndexL3) : Nat :=")
    lines.append("  activeL3PrimeExponentEntry n.1")
    lines.append("")
    lines.append("/-- Analytic prime-power shift `r * log p` for the L=3 dictionary. -/")
    lines.append("def activeL3PrimeShift (n : PrimeShiftIndexL3) : Real :=")
    lines.append("  (activeL3PrimeExponent n : Real) * Real.log (activeL3PrimeBase n : Real)")
    lines.append("")
    lines.append("/-- Analytic prime weight `log p / p^(r/2)`, written as `log p * exp(-(r log p)/2)`. -/")
    lines.append("def activeL3PrimeWeight (n : PrimeShiftIndexL3) : Real :=")
    lines.append("  Real.log (activeL3PrimeBase n : Real) * Real.exp (-(activeL3PrimeShift n) / 2)")
    lines.append("")
    lines.append("structure CenteredCoeffDictionaryData where")
    lines.append("  center : CoeffIndex23 -> Real")
    lines.append("  weight : PrimeShiftIndexL3 -> Real")
    lines.append("  shift : PrimeShiftIndexL3 -> Real")
    lines.append("")
    lines.append("/-- Dictionary shared by the active primary and control L=3 blocks. -/")
    lines.append("def activeL3Ell030Delta025DictionaryData : CenteredCoeffDictionaryData where")
    lines.append("  center := activeL3Ell030Delta025Center")
    lines.append("  weight := activeL3PrimeWeight")
    lines.append("  shift := activeL3PrimeShift")
    lines.append("")
    lines.append("def primaryK11Center : CoeffIndex23 -> Real := activeL3Ell030Delta025Center")
    lines.append("def primaryK11PrimeWeight : PrimeShiftIndexL3 -> Real := activeL3PrimeWeight")
    lines.append("def primaryK11PrimeShift : PrimeShiftIndexL3 -> Real := activeL3PrimeShift")
    lines.append("")
    lines.append("def controlK9Center : CoeffIndex23 -> Real := activeL3Ell030Delta025Center")
    lines.append("def controlK9PrimeWeight : PrimeShiftIndexL3 -> Real := activeL3PrimeWeight")
    lines.append("def controlK9PrimeShift : PrimeShiftIndexL3 -> Real := activeL3PrimeShift")
    lines.append("")
    lines.append("def primaryK11DictionaryData : CenteredCoeffDictionaryData where")
    lines.append("  center := primaryK11Center")
    lines.append("  weight := primaryK11PrimeWeight")
    lines.append("  shift := primaryK11PrimeShift")
    lines.append("")
    lines.append("def controlK9DictionaryData : CenteredCoeffDictionaryData where")
    lines.append("  center := controlK9Center")
    lines.append("  weight := controlK9PrimeWeight")
    lines.append("  shift := controlK9PrimeShift")
    lines.append("")
    lines.append("theorem primaryK11_hk : 0 < 11 := by")
    lines.append("  norm_num")
    lines.append("")
    lines.append("theorem controlK9_hk : 0 < 9 := by")
    lines.append("  norm_num")
    lines.append("")
    lines.append("theorem primaryK11_hell : 0 < primaryK11Ell := by")
    lines.append("  norm_num [primaryK11Ell, primaryK11EllRat]")
    lines.append("")
    lines.append("theorem controlK9_hell : 0 < controlK9Ell := by")
    lines.append("  norm_num [controlK9Ell, controlK9EllRat]")
    lines.append("")
    lines.append("/-- Concrete analytic contract generated from the active primary dictionary. -/")
    lines.append("noncomputable def primaryK11CoeffAnalyticKernelContract :")
    lines.append("    BSplineAnalyticKernelContract CoeffIndex23 (CoeffIndex23 -> Complex) :=")
    lines.append("  centeredBSplineCoeffAnalyticKernelContract")
    lines.append("    11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift")
    lines.append("    primaryK11_hk primaryK11_hell")
    lines.append("")
    lines.append("def primaryK11AnalyticC : Matrix CoeffIndex23 CoeffIndex23 Real :=")
    lines.append("  primaryK11CoeffAnalyticKernelContract.toFormulaContract.C")
    lines.append("")
    lines.append("def primaryK11AnalyticQ : Matrix BoundaryIndex2 CoeffIndex23 Real :=")
    lines.append("  primaryK11CoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q")
    lines.append("")
    lines.append("/-- Concrete analytic contract generated from the active control dictionary. -/")
    lines.append("noncomputable def controlK9CoeffAnalyticKernelContract :")
    lines.append("    BSplineAnalyticKernelContract CoeffIndex23 (CoeffIndex23 -> Complex) :=")
    lines.append("  centeredBSplineCoeffAnalyticKernelContract")
    lines.append("    9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift")
    lines.append("    controlK9_hk controlK9_hell")
    lines.append("")
    lines.append("def controlK9AnalyticC : Matrix CoeffIndex23 CoeffIndex23 Real :=")
    lines.append("  controlK9CoeffAnalyticKernelContract.toFormulaContract.C")
    lines.append("")
    lines.append("def controlK9AnalyticQ : Matrix BoundaryIndex2 CoeffIndex23 Real :=")
    lines.append("  controlK9CoeffAnalyticKernelContract.toFormulaContract.boundaryRows.Q")
    lines.append("")
    lines.append(FOOTER.strip())
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean"),
    )
    args = parser.parse_args()
    args.out.write_text(build_lean())
    print(args.out)


if __name__ == "__main__":
    main()
