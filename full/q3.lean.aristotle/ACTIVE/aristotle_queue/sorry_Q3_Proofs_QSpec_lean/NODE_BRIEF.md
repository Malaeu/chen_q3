# NODE BRIEF - Q3/Proofs/QSpec.lean

## Location
- File: `Q3/Proofs/QSpec.lean`
- Sorries:
- prime_term_small_support @ L169
- prime_term_small_support @ L177
- prime_term_small_support @ L201
- prime_term_small_support @ L208

## Goal (informal)
Fill all remaining `sorry` in this file without touching imports/defs.

## Fixed assumptions / invariants
- Single-scale mainline (t_critical).
- Avoid two-scale bridges.
- Use only already-imported lemmas.

## Preferred finish
- simp / linarith / nlinarith
- Avoid heavy `aesop` unless non-terminal
