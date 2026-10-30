# Retro test 2026-10-28: does the question text predict progress?

Observer (Linux Claude). Trigger: owner asked whether the OpenAI ETH release (26.10) works as a "direct ladder", a shortcut in the search over variants.

## Design
- Corpus: 72 Proshka questions, 06.10–22.10. 53 request headers `PROSHKA_*.txt` (text before the first attached evidence block),
  9 early-phase questions (answers 1–5, 7–10; question 6 not found in git), 10 growth rollover questions.
- Blind predictor saw only questions (`pred.tsv`). Blind labeler saw only conclusions/verdicts (`outcome.tsv`). Join: `join_retro.py`.
- Hypothesis H (observer, 0.7): progress on the main term needs A = one-sided inequality on the main signed quantity
  AND B = new external input. Class P1 = A∧B.

## Result: H refuted (ЕСЛИ_B)
| | MAIN_GAIN | EXACT_RETURN | REMAINDER_ONLY | SHAPE_KILL |
|---|---|---|---|---|
| P1 (2) | 0 | 1 | 1 | 0 |
| P0 (70) | 4 | 7 | 34 | 25 |

- All 4 MAIN_GAIN rows have B=NO in the question. A is not discriminating: 52/72 questions have A=YES.
- EXACT_RETURN: predicted 6 of 8, but the prediction fired 25 times (precision 6/25).
- Exact-outcome accuracy 29/72.

## What the table shows instead
- 0 of 72 rounds moved the exponent of the main quantity unconditionally.
  GROWTH_ANSWER3: log-power gain only, exponent 1/2−o(1) (NEXT.md:70).
  Q03/Q10/PERTURBED_Q07: conditional on ZF78, log factors or a 2.5e-6 margin (labeler: borderline).
- New inputs that moved anything came from the answers (twisted Perron + MTY in answer3; ZF78 = OpenAI manuscript), not from the questions.
  Only 2/72 questions carried a new external input.

## Candidate law (observer, 0.8): floor exponent = zero-free abscissa − 1/2
- Upper side: DIRECT_Q3_THEOREM_TRANSFER.md:24–31 moves the contour of the existing twisted Perron proof to Re s = σ−1/2+η.
  Zero-free Re s > σ ⇒ λ_min(K_m) ≥ −C m^(σ−1/2+ε). σ=7/8 gives 3/8. Vinogradov-type region gives 1/2−o(1) with the exp(−c(L/log L)^(1/3)) factor (answer3).
- Lower side: off-critical zero 1/2+δ ⇒ λ_min(K_m) ≤ −c m^δ/(log m)^(2δ) (NEXT.md:60–61).
- So the floor exponent e = Θ − 1/2, Θ = sup Re ρ, on both data points. DIRECT_Q3 line 72 already says the floor "only recovers the imported strip".
- Search consequence: a rewrite that injects no information on zeros in Θ>Re s>1/2 cannot move e. An unconditional power saving on the floor would be a new zero-free strip.
- Status: the parametric upper direction is read from our own text, not reproved; the law is not a theorem here.

## Proposed sieve line for NEXT.md §2 (not applied)
Before a question: name what the move would imply for Θ. If it would lower e without an input on zeros, it repeats an exact return.
