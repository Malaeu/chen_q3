# NODE BRIEF - Q3.prime_term_le_at_t_critical_axiom

## Location
- File: `Q3/Proofs/Q_nonneg_t_critical.lean`
- Declaration: `Q3.prime_term_le_at_t_critical_axiom`

## Goal (informal)
Replace axiom with theorem; no new axioms, no new imports.

## Fixed assumptions / invariants
- Single-scale mainline (t_critical).
- Avoid two-scale bridges.
- Use only already-imported lemmas.

## Preferred finish
- simp / linarith / nlinarith
- Avoid heavy `aesop` unless non-terminal
