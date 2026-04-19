# H1 / PO3 — first-zeta witness stub at `a = 1`

## Status

Work stub only. This is not a formal proof of nonzero yet.

## Purpose

Freeze one concrete `prefix2/prefix3` witness target so that the remaining gap
is only:

1. an external certificate that a named complex number is nonzero;
2. plugging that certificate into an already compiled Lean bridge lemma.

## Lean objects

In
[`Q3/Proofs/HBridge_PO3_Shell.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/HBridge_PO3_Shell.lean)
we now have:

- `po3_first_zeta_gamma0_decimal28`
- `po3_first_zeta_gamma1_decimal28`
- `po3_first_zeta_gamma2_decimal28`
- `po3_first_zeta_gap_sum2_a1_decimal28`
- `po3_first_zeta_gap_sum3_a1_decimal28`

and the two conditional witness lemmas:

- `po3_no_suzuki_raw_gamma_pm_prefix2_of_first_zeta_decimal28_witness`
- `po3_no_suzuki_raw_gamma_pm_prefix3_of_first_zeta_decimal28_witness`

## External certificate targets

The direct targets are now simply:

```lean
hgap2 : po3_first_zeta_gap_sum2_a1_decimal28 ≠ 0
hgap3 : po3_first_zeta_gap_sum3_a1_decimal28 ≠ 0
```

Once one of these is available, the corresponding formal conclusion is already
compiled.

## Numerical source

The decimal-28 witness values come from the local script
[`scripts/po3_gamma_gap_witness.py`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/scripts/po3_gamma_gap_witness.py),
using `mpmath.zetazero(n)`.

For the current frozen run:

- `γ₀ ≈ 14.1347251417346937904572519836`
- `γ₁ ≈ 21.0220396387715549926284795939`
- `γ₂ ≈ 25.0108575801456887632137909926`

and the witness JSON snapshot is
[`ACTIVE/pipeline/po3_gamma_gap_witness_2026_04_19.json`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/pipeline/po3_gamma_gap_witness_2026_04_19.json).

## Current numerical signal

For `a = 1` the frozen run gives:

- `po3_first_zeta_gap_sum2_a1_decimal28 ≈ 8.012376722781014e-4`
- `po3_first_zeta_gap_sum3_a1_decimal28 ≈ 8.013257563312617e-4`

So the local numerical signal is comfortably away from zero.

## Intended next formal move

Either:

1. accept an external numerical certificate for one of the two named gap sums;
2. or produce a tiny imported certificate layer proving the corresponding
   nonzero statement for the frozen decimal witness.

No new Suzuki shell infrastructure is needed after this stub.

## Current certificate landing

That certificate layer now exists as the separate off-chain file
[`Q3/Proofs/PO3Cert/FirstZetaGapWitness_2026_04_19_Data.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PO3Cert/FirstZetaGapWitness_2026_04_19_Data.lean).

It exports:

- `Q3.Proofs.PO3Cert.po3_first_zeta_gap_sum2_a1_decimal28_ne_zero` as the
  named external certificate axiom for the concrete `prefix2` gap;
- `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_prefix2_from_first_zeta_gap_cert`
  as the closure point for the compiled `prefix2` shell;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gap_sum3_a1_decimal28_ne_zero` as the
  named external certificate axiom;
- `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_cert`
  as the closure point back into the compiled `PO3` shell.

## Current honest singleton landing

There is now also a theorem-level singleton obstruction with no external axiom
in
[`Q3/Proofs/PO3Cert/FirstZetaSingleton_2026_04_19.lean`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PO3Cert/FirstZetaSingleton_2026_04_19.lean).

It exports:

- `Q3.Proofs.PO3Cert.po3_first_zeta_gamma0_decimal28_ne_int_mul_pi`;
- `Q3.Proofs.PO3Cert.po3_first_zeta_gamma0_decimal28_sin_ne_zero`;
- `Q3.Proofs.PO3Cert.po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma0_decimal28`.

The key point is structural:
the decimal-28 witness `γ₀` is rational, so it cannot equal an integer
multiple of `π`, and that already kills the singleton `(+,-)` candidate at
`a = 1`.
