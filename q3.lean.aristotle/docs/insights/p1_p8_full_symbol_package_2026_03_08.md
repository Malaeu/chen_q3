# P1--P8 Full-Symbol Package

Date: 2026-03-08

## Summary

The corrected `PSD-pd` route now has a strict theorem package:

- `P1`: exact packet sesquilinear identity;
- `P2`: Toeplitz reduction on translation packet dictionaries;
- `P3`: desired PSD factorization of the packet prime block;
- `P4`: prime-block obstruction, showing `P3` is false on dense packet spaces;
- `P5`: full sequence split `\kappa=\alpha-\beta`;
- `P6`: Toeplitz--Herglotz criterion for PSD of the full sequence;
- `P7`: full-symbol domination `A_{g,\Delta}\ge P_{g,\Delta}` as the clean
  sufficient criterion;
- `PSD-pd`: positive semidefiniteness of the full packet kernel.

## Core verdict

The literal theorem shape

`prime block PSD factorization or Hilbert lift -> Archimedean domination`

is not the live constructive route anymore. `P4` kills it on dense packet
spaces containing an active node.

The immediate constructive target is `P7`:

`A_{g,\Delta}(\theta)\ge P_{g,\Delta}(\theta)`

in the regular symbol regime, or the corresponding measure/distribution
statement in the general Herglotz form.

## Why this is the honest package

- `P1/P2` preserve the exact packet-level algebra.
- `P4` records the real obstruction instead of hiding it.
- `P6` keeps the clean spectral equivalence language.
- `P7` is the first honest sufficient criterion that can still feed `PSD-pd`
  without pretending the prime block is PSD by itself.

## Operational consequence

- Public manuscript/control-plane wording should expose `P1--P8`.
- `P7` is the active constructive target.
- A new operator package for the full kernel is fallback-only.

## File pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Main_closure.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/Weil_pack.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/full/sections/introduction.tex`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
