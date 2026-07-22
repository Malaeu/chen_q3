# Entire square-root rigidity — Aristotle run

Status: `SOFT_L2_ENTIRE_SQUARE_ROOT_RIGIDITY_LEAN / LOCALLY_NOTARIZED / NOT_RH`

- Prompt: `aristotle_input/routeb_entire_square_root_rigidity_2026_07_22.md`.
- Authorized SHA-256: `287af18afae811502764cafa2728f2e5acf0daf3aebc98aaa336b63f0d5d040d`.
- Owner authorization: `OK RIGIDITY 287af18a`.
- Project: `5a62a655-5d8d-4bb4-8a9f-1216c730b5aa`.
- Task: `0e8da32e-1505-4956-92f4-5635bfdbbe0a`.
- Aristotle task status: `COMPLETE`.
- Result archive SHA-256:
  `dfb9a4065291cb7590fee22c8a8ac6cd05aeca5e45c9f7cd4fcd72b5eb53536f`.
- Integrated theorem:
  `Q3/Proofs/RouteB/EntireSquareRootRigidity.lean`.

## K1 verification

The theorem statement is mathematically valid.  From `F² = G²` one obtains
`(F-G)(F+G)=0`; the identity theorem for entire functions forces one factor to
vanish globally.  The degenerate case `F=G=0` is covered.  This is a reusable
uniqueness kernel only; it proves neither existence of a square root nor RH.

## K6 registered predictions

- `P-R1`: expected `PROVED` by
  `Complex.analyticOnNhd_univ_iff_differentiable.mpr` followed by
  `AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero`.
- `P-R2`: expected axiom print exactly
  `[propext, Classical.choice, Quot.sound]`.
- One permitted recovery hint if the submitted run gets stuck: work on the
  open set `{F ≠ G}`, derive `F+G=0` there, then use analytic connectedness.
- Success code is withheld until a hole scan and local Lean build pass:
  `SOFT_L2_ENTIRE_SQUARE_ROOT_RIGIDITY_LEAN`.

## Two intended landings

1. Round-12 `EvenRealAutocorrelationRigidity`: convert equality of transform
   squares to a single global sign.
2. S2/3Q.5: convert the quadratic `H H^sharp` identification to a linear
   identification, with the remaining sign fixed by the anchor.

## Result and local notarization

- Aristotle followed the registered identity-theorem route (`P-R1`).
- Strict scan found no `sorry`, `admit`, `exact?`, `native_decide`, declared
  axiom, or `@[implemented_by]` in the returned theorem file.
- `lake env lean Q3/Proofs/RouteB/EntireSquareRootRigidity.lean`: exit `0`.
- Local axiom print (`P-R2`):
  `[propext, Classical.choice, Quot.sound]`.
- The theorem was imported into `aristotle_proofs.db` with status `proven`.

This closes only the analytic global-sign uniqueness kernel.  It does not
construct an entire square root, prove the Round-12 reconstruction contract,
supply the Theorem-5.10 transform layer, or prove RH.
