# PARITYSPLIT — observer audit (2026-10-28)

Verdict: `PROSHKA_VERDICT_PARITYSPLIT_2026-10-28.md` (copied verbatim from the owner's Downloads, 1018 lines).
Request: `PROSHKA_REQUEST_PARITYSPLIT_2026-10-28.txt` (5086bf3f).

## Codes
Q1 G1B_KILL_PARTIAL (odd upper envelope B_m paid, eq. 2.12–2.13; selected-row lower margin 3.2 unpaid).
Q1 consumers: G1b NOT necessary for the roof given G1a and direct transform-level G3 (P1c confirmed).
Q2a G1A_REDUCED_TO_SIGN_LEMMA: G1a ⟺ λ_min(E) < λ_min(O) (4.6) ⟺ ∃t < λ_min(O) with f_m(t) < 0 (4.10).
Q2b G1A_UNDECIDED_FIRST_FACT: no Θ-witness; a shifted structured example shows a negative bottom alone does not break parity.
Q2c: exact boundary-resolvent identity cos² = −1/S'(λ) (6.4); no cofinal ratio law.

## Two findings against the observer — accepted (signature: observer)
1. The table realified the row: `q = real(zp)` dropped an odd imaginary part (3.9e−3 at m=2, 1.5e−41 at m=16).
   My claim "q is exactly even, so every odd y ⊥ q" was about the realified row, not the complex reference. Proshka's repair (1.5) keeps δ < 0 when s² < 1/2.
2. cos²(ξ,η) in the script is |η·ξ|²/(2m+1). My reading "η·ξ ≍ √λ_min" lacked the factor 2m+1.

## Independent numeric checks of the verdict on the literal K_m (DIAGNOSTIC_NEVER_A_PROOF)
Script `docs/routeB_bus/thetagrade_2026-10-28/parity_residue_probe.py`; rows `residue_dps120.jsonl`, `residue_dps170.jsonl` (agree to 12 printed digits).
| m | displacement (4.1) err | det identity (4.8) rel err | μ/λ_even | f_m(midpoint) | R_m (4.13) | R_m/μ |
|---|---|---|---|---|---|---|
| 2 | 3e−173 | 4e−171 | 41 | −0.844 | −0.095 | −0.76 |
| 4 | 1e−171 | 7e−166 | 179 | −2.7e−3 | −8.0e−10 | −2.6e−3 |
| 8 | 2e−171 | 2e−155 | 326 | −3.6e−8 | −1.2e−24 | −3.5e−8 |
| 12 | 2e−171 | 2e−146 | 611 | −1.6e−12 | −6.7e−38 | −1.6e−12 |
| 16 | 4e−171 | 4e−138 | 1256 | −8.3e−17 | −5.7e−51 | −8.3e−17 |
All 15 cells m = 2..16: identities hold to working precision; R_m < 0 and f_m(midpoint) < 0 on every cell.
So the cheap sufficient sign (4.16) has the right orientation on all computed cells. Its normalized size R_m/μ shrinks fast,
and the second odd gap g_o falls to 2e−29 at m=16, so the bracket ε_m from (4.16) will be very small. A cofinal proof must handle shrinking margins.

## Prediction score (frozen)
P1 partial (0.45) hit · P1c 0.75 hit · P2a sign reduction (0.55) hit · P2b no Θ-witness (0.85 implied) hit · P2c exact identity partial (0.40) partial.

## What changes
G1 is now one sign: λ_min(E_m) < λ_min(O_m) eventually. Simplicity and η·ξ ≠ 0 follow from it (4.5).
G1b drops out of the roof once G3 is attacked at transform level. The roof chain reads: G1a (one parity sign) + G3 (Θ-graded) + closed links.
Next (Proshka's directive): a cofinal bracket (4.11) — positive lower envelope for O_m − t_m and negative upper envelope for f_m(t_m); first try the residue R_m.
