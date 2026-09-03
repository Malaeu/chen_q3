# Probe 6 report -- center Schur-pairing sign structure (R2)

Precommit: `PRECOMMIT_2026-09-03_edge_ledger_probes.md`, ADDENDUM 4 (2026-09-03 13:22). Judge context: attack R2 (`P59_CURVATURE_CENTER_SCHUR_STIELTJES`), section 4 of `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md`.

## Sanity check: 1/12 - f(lambda1) vs Probe 5's a_1/xi_0

| m | 1/12 - f(lambda1) | a_1/xi_0 (Probe 5, recomputed here bit-for-bit) | agree (8 sig) | status |
|---|---|---|---|---|
| 13 | 0.00787244394607 | 0.00787244394607 | True | OK |
| 23 | 0.00534272221391 | 0.00534272221391 | True | OK |
| 43 | 0.00365359998001 | 0.00365359998001 | True | OK |
| 83 | 0.00257788335003 | 0.00257788335003 | True | OK |

## Per-cell table

| m | dps | minority_mass | S_+ | S_- | # poles | midpoint sign changes | # uncertain midpoints | monotone b_i |
|---|---|---|---|---|---|---|---|---|
| 13 | 240 | 0 | 0.00728367 | 0 | 13 | 1 | 0 | not_monotone |
| 23 | 240 | 0 | 0.00540481 | 0 | 23 | 5 | 0 | decreasing |
| 43 | 240 | 4.32284e-06 | 0.00540271 | 2.33552e-08 | 43 | 3 | 0 | decreasing |
| 83 | 360 | 5.74081e-06 | 0.00316988 | 1.81978e-08 | 83 | 9 | 0 | decreasing |

## Midpoint sign sequences (interlacing proxy)

One evaluation of f per gap (mu_j, mu_{j+1}), sign only ('+', '-', '0' = ball straddles zero). This is a coarse proxy, not a scan for a zero crossing inside each gap (see module docstring).

- m=13: `++++++++----`
- m=23: `++++++++++++++-++-++--`
- m=43: `++++++++++++++++++++++++++++++-+++--------`
- m=83: `++++++++++++++++++++++++++++++++++++++++++++++-+++++++----------++-++--+----------`

## Verdict: UNRESOLVED

Frozen rule quoted verbatim from the precommit: - else UNRESOLVED. Also descriptive: the Loewner structure of the off-diagonal entries tau_{ij} = (b_i - b_j)/(i - j) (CCM Lemma 5.1) -- report whether the sequence b_i is monotone on 1..N at each cell. DIAGNOSTIC_NEVER_A_PROOF.

minority_mass by cell: m=13: 0, m=23: 0, m=43: 4.32284e-06, m=83: 5.74081e-06

DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE. No Lean, no route promotion.
