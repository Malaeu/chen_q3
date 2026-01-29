# Node: Q_Lipschitz

## Status
- state: verified
- updated: 2026-01-25

## Source
- request: `../../input/Q_Lipschitz.md`
- related outputs:
  - `../../output/Q_Lipschitz_aristotle.lean`
  - `../../output/Q_Lipschitz_aristotle.lean`
  - `../../output/Q_Lipschitz_aristotle.lean`
  - `../../output/Q_Lipschitz_aristotle.lean`

## Why we are here
- A2 continuity: Lipschitz control of Q on W_K is required to pass from atoms to all W_K.
- This node tracks the main Q-Lipschitz lemma used in the closure step.

## Evidence / checks
- Lemma is fully proved in `Q3/Proofs/Q_Lipschitz.lean` (no `sorry`/`admit`).
- Bridge components are in `Q3/Proofs/Q_Lipschitz_arch_bridge.lean` and `Q3/Proofs/Q_Lipschitz_prime_bridge.lean`.

## Decision
- Use `Q3.Proofs.Q_Lipschitz_on_W_K_thm` as the mainline A2 lemma.
- No need to import Aristotle drafts.
