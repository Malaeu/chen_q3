# NODE BRIEF - Q3/Clean/MainClean.lean

## Location
- File: `Q3/Clean/MainClean.lean`
- Sorries:
- RH_proven_clean @ L59

## Goal (informal)
Fill all remaining `sorry` in this file without touching imports/defs.

## Fixed assumptions / invariants
- Single-scale mainline (t_critical).
- Avoid two-scale bridges.
- Use only already-imported lemmas.

## Preferred finish
- simp / linarith / nlinarith
- Avoid heavy `aesop` unless non-terminal
