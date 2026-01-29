# Node: Lipschitz_Bridge_v1

## Status
- state: verified
- updated: 2026-01-25

## Source
- request: `../../input/Lipschitz_Bridge_v1.md`
- related outputs:
  - `../../output/Lipschitz_Bridge_v1_aristotle.lean`
  - `../../output/Lipschitz_Bridge_v1_aristotle.lean`
  - `../../output/Lipschitz_Bridge_v1_aristotle.lean`
  - `../../output/Lipschitz_Bridge_v1_aristotle.lean`

## Why we are here
- This is the bridge lemma tying Q-Lipschitz to the A1 density step (A2 in the chain).
- Needed to formalize the “atoms dense + continuity => positivity on all W_K” step.

## Evidence / checks
- Bridge is implemented in `Q3/Proofs/Q_Lipschitz_Bridge.lean` (Tier-1 axioms, no holes).
- Main theorem `Q3.Proofs.QLipschitzBridgeV2.Q_Lipschitz_on_W_K` is available for wiring.

## Decision
- Use the Lean bridge file for A2 wiring; ignore Aristotle drafts.
- Wire it directly after A1 density and before final Q >= 0 on W_K.
