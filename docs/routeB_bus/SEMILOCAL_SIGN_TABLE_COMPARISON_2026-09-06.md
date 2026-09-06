# Semilocal sign table — comparison of the two independent implementations (observer, 2026-09-06)

Object: the sign of E_S(k⋆k*) in the judge's split L_S = N_S − E_S (SEMILOCAL 3242ada9, SEMISIGN 59aabc18), S = {∞, 2}, λ = 1.
A: `SEMILOCAL_SIGN_TABLE_A_2026-09-06.md` (self-dual DCT-I carrier, N = 3200, Richardson in δ; two F_S variants src/pol; exact spectral route for the archimedean pair).
B: `SEMILOCAL_SIGN_TABLE_B_2026-09-06.md` (physical DCT-I carrier, N = 8192; F_S via halving operator; Sonin from subspaces; error bars from translation defect + symmetrisation).
Both implementations passed the same known-answer checks (Slepian eigenvalues, Halmos plant −3/5, ‖B_S‖ inside [a_S, b_S], Q(v_R) = 0 at machine precision, P_02 = 2|C|² − 2|S|²).

## Agreed by both (accepted as the table's result)
| statement | A | B |
|---|---|---|
| E_S > 0 on every single smooth bump inside the window (b = 0.05 … 0.5), both shifted copies, two-bump (+), and on the canonical cutoffs v_R | yes (E ≈ +0.36 at b = 0.2; +1.50 on v_R) | yes (+0.49 at b = 0.2; +1.56 on v_R) |
| E_S < 0, robust, on the antisymmetric two-bump tests h_b(x − a/2) − h_b(x + a/2) | −0.043 … −0.081 (both variants, all three λ) | −0.042 (b = 0.05), −0.056 (b = 0.1) |
| Q(v_R) − N_S(k_R) < 0 on canonical cutoffs (judge's (21)) | −4.57e−4 | −1.45e−3 |
| wide bump b = 3 (theorem control): E > N > 0 | yes | yes |
| CC20 theorem control (S = {∞}, three constraints): theorem respected by the reliable route | exact spectral E_∞ < 0 on all six | Q ≥ N_∞ with margin 0.02–0.47 on all eight |
| the DIRECT block-trace E is unreliable on rough tests | carrier flips sign on 4/6 theorem tests | direct E has +0.03…+0.10 where theorem forces ≤ −0.02…−0.47 |
| semilocal angle spectrum does not decay like the prolate one | plateau ≈ 0.4, 69–78 blocks > 1e−6 (vs 7); Σ|α_n| may diverge | 41 blocks > 1e−6, slow tail 0.65, 0.58, 0.48, … |
| N_S is tiny on narrow smooth bumps (≈ 4e−4 … 8e−4 at b = 0.2) against E_S ≈ 0.4–0.5 | yes | yes |
| irreducible semilocal model error from truncating the half-line (20 octaves of the Euler intertwiner) | ‖JFJ⁻¹ − VFV*‖ = 0.43, not decaying | ‖WᵀW − I‖ = 0.249, residual floor |

## Not agreed — UNRESOLVED
| item | A | B | observer's verdict |
|---|---|---|---|
| pole-null triple v₊, v₋, v_i (judge's falsifiers) | absolute carrier error 0.77–1.1 on this class; semilocal E marked UNRESOLVED; archimedean exact E_∞ = −0.0046 (all three) | claims resolved from Q − N_S with bar ≈ 1e−2: v₊ E = +0.022, v₋ −0.340, v_i −0.159 | UNRESOLVED. The two implementations do not even agree on L_S of the same-named test (A: 2.04/3.02/2.53; B: 2.95/3.93/3.44), so the test functions differ in construction; B's bar is not credible on a class where its own direct E was off by up to 0.5. A dedicated finer computation is needed before any sign is asserted for v₊. |
| h_b e^{i10x} | archimedean exact −0.06; semilocal +0.014…+0.021 with budget ±0.05 | E_true = −0.037, bar 1.1e−2 | UNRESOLVED |

## What the table decides
1. The inequality E_S(k⋆k*) ≤ 0 on the whole support-matched class (SEMISIGN (24)) is FALSE: it fails on every positive bump and on the canonical cutoffs, in both implementations. The bare Sonin trace N_S is neither a minorant nor a majorant of Q.
2. The sign of E_S is a property of the relative phase across the log 2 separation: antisymmetric two-bump combinations give E_S < 0 robustly, symmetric ones give E_S > 0. This is the prime-2 structure showing in the sign, and it is the one lead the table produces.
3. The judge's pole-null falsifier v₊ is not decided by either implementation at the accuracy reached; the class of rough (second-derivative) tests needs a carrier with resolved ζ_n tails.
4. Structural warning for the judge's convergence scope: both implementations see a non-decaying semilocal angle spectrum, so D_S may fail to be trace class and the trace-class realisation assumed in the split needs proof.
DIAGNOSTIC_NEVER_A_PROOF.
