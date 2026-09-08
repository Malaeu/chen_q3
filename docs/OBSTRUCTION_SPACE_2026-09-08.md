# Obstruction space of the RH problem on the verified frontier (2026-09-08)

Owner's frame (08.09): the dimension of a problem is the number of independent ways the theorem can still be false;
a good transformation T keeps P ⟺ P′ and strictly shrinks the obstruction space. Below: the basis of live obstructions
after KERNEL (K23), ALIGN (cover, near-null family), COMPENSATE (tail), SCREW/HODGE (dictionaries). Observer's map,
built from checked verdicts; each row gives object, quantifier, failure mode, RH-equivalence, dependencies.

## A. Obstructions that are DEAD on the frontier (closed, checked)
| Former obstruction | Killed by | Locator |
|---|---|---|
| Unknown radical («what is zero for free») | rad(Q) = 𝒩_pt, exact, unconditional | KERNEL (K23), check |
| Quantifier over all supports vs finite windows | fixed-width prime classes exhaust pole-null tests; RH ⟺ n₋(a)=0 ∀a | ALIGN (A17)–(A21); SCREW (S21)–(S24); SC (SC13)–(SC14) |
| Tail / high modes | mean-zero tail paid, 47/6000, 6-dim head | COMPENSATE Thm 4 + check |
| Pole plane | rank-2 (1,1) summand, removed exactly by two moment conditions; not an intrinsic Q-plane | SC (SC6)–(SC11) |
| Multiplicity of zeros as extra directions | weight, not dimension; sig(Q̄) = (∞, r) | SC (SC4), HODGE (H9) |
| «Squares are the mechanism» | a square with the right kernel exists trivially (Riesz); R ≥ 0 ⟺ RH | KERNEL (K1)–(K13) |
| Finite-S reservoir minorants; scalar compensation; lossy floors | near-null family; compact witness (K30); Thm 6; ρ_P → 1 | ALIGN, COMPENSATE, NEAR_NULL_PROBE |
| «Only infinity is missing» | a negative direction is visible on a finite window | SC (SC13); HODGE §3.2; Suzuki v1 own statement |

## B. Obstructions that are LIVE
| # | Object | Quantifier | Failure mode (how the theorem could be false) | ⟺ RH? | Depends on |
|---|---|---|---|---|---|
| O1 | Sign of Q̄ on ℋ/𝒩 = null rigidity Q[f]=0 ⇒ Af=0 = window first-touch ker A_{a*} = 0 = I − T_P ⪰ 0 = R ≥ 0 | ∀ f (equivalently ∀ a) | an isotropic non-radical vector = a hyperbolic (1,1) block = an off-line j-orbit | YES (eight equivalent records) | nothing else; this is the atom |
| O2 | Source compatibility (the Hodge–Riemann cell): a positive object compatible with the SAME pairing, or a nonnegative count with subquadratic error | ∃ construction | wrong degree / quadratic remainder / shifted metric | sufficient for O1; not known necessary | O1 |
| O3 | Identification of the canonical-system limit with ξ (SCREW/CLOSURE) | ∃ source normalisation θ(a), φ(a,z), domain | the real-zero bricks converge to a wrong real-rooted function; free gauge makes it ⟺ RH | with free gauge YES; with a fixed source gauge UNKNOWN (not proved equivalent, not proved weaker) | O5, O6 |
| O4 | Compactness (normality) of the normalised W-family on a pole-free domain | ∀ compacts | unbounded growth (control (SC22)) | NO — analytic, sufficient condition (SC21) | O6 |
| O5 | Domain/gauge repair of Cor. 1.6's meromorphic target | ∃ pole-free domain + zero-free normaliser | poles of the printed targets | NO — bookkeeping | — |
| O6 | Window form-to-operator dictionary ⟨f, A_a f⟩ = Q[f] with C_c^∞ core; reflection symmetry; deficiency columns | — | convention slip | NO — asserted, checkable | — |
| O7 | Subquadratic growth / count analogue over ℚ (CC22 has linear degree) | ∃ count | wrong growth degree | sufficient route into O2 | O2 |

## C. Rank
rank 𝔒_live = 1 essential (O1; every RH-equivalent record collapses to it) + technical rows O4–O6 (closable without RH,
no sign content) + two sufficient-supplier rows O2, O7 (constructions that would pay O1; their absence is not a failure
mode). The «enemy» is materialised: an off-line j-orbit ↔ a hyperbolic (1,1) block ↔ an isotropic non-radical vector ↔
Re c₀(ρ_max) > 0. A transformation counts as progress only if it removes a row of §B without adding one; today's
transformations removed §A rows and rewrote O1 eight times without shrinking it.

## D. Candidate transformations and their honest rank effect
| T | Keeps P ⟺ P′? | Removes | Adds | Net |
|---|---|---|---|---|
| Quotient by 𝒩 | yes | radical row | — | −1 (done) |
| Fixed-width cover | yes | quantifier row | — | −1 (done) |
| Riesz square | yes | «find X» | — | 0 on O1 (moved the sign into R) |
| Null rigidity (equality case) | yes (given the anchor) | — | — | 0 on O1; changes the TOOLS (equality case / unique continuation) |
| Canonical systems (SCREW) | only with fixed source gauge | O1 → O3+O4+O5 | O3, O4, O5 | 0 or +2 unless O3 is proved weaker than O1 |
| Hodge transplant | yes | — | O2, O7 as suppliers | 0; names what a supplier must look like |
| Zero-flow (dBN) | yes (RH ⟺ Λ = 0) | — | backward control | 0; prime ledger not preserved |
The one candidate that could give a strict decrease: proving O3 with a fixed source gauge WITHOUT proving O1 (then the
limit problem is strictly weaker than the sign, and the sign follows) — that is exactly HYPERBOLICITY (ii) and CLOSURE Q2.
