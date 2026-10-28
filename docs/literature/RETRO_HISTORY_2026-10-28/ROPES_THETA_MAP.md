# Ropes of the Goal058 roof, graded by Θ (observer, 2026-10-28)

Θ := sup Re ρ over nontrivial zeros of ζ. RH ⟺ Θ = 1/2. Unconditionally Θ ≤ 1 (zeros approach Re s = 1 at large height);
ZF78 (OpenAI, Comparator accepted for the ζ statement 2026-10-07, see `../openai_math_2026-10-07/DIRECT_Q3_THEOREM_TRANSFER.md`) gives Θ ≤ 7/8.

A rope is **Θ-graded** when its required strength is a function of Θ, so that any input that does not move Θ cannot tighten it.

## Map (state from `docs/Codex/PAPER_CHAIN.md` lines 11–26)

| Pillar / rope | Requirement | Status | Θ-graded? | Evidence |
|---|---|---|---|---|
| G5 roof (Hurwitz) | real-zero family F → Ξ locally uniformly ⇒ RH | LEAN | no (consumer) | `Goal058DirectGroundZeroEscape.lean:27` |
| hentire | each F_m entire | LEAN | no | PAPER_CHAIN:19 |
| G2 / G2b | real zeros of the row polynomial and of its transform | LEAN, G2 conditional on G1 | no | PAPER_CHAIN:17–18 |
| G4 | CCM Lemma 7.3: trial k_λ → Ξ on strips | PAPER_PUBLISHED | no | PAPER_CHAIN:24 |
| hmode, hχ/hθ, G3c | Ferrers mode rate C_n/m; projection tail O(m^-1/4) | PAPER_OWN rev | no (classical analysis) | PAPER_CHAIN:21–23 |
| G1 | simple, even ground state; cellwise gap δ_j; ‖r_j‖/δ_j → 0; odd-sector floor | OPEN (constant β KILLED) | parity/simplicity: no witness known; the ratio ‖r_j‖/δ_j feeds G3 | PAPER_CHAIN:14–16, 43–62 |
| G3 tracking | α_m = O(m^-a (log m)^A) | OPEN, "главная стена" | **yes: a > (Θ−1/2)/2** | below |
| SP floor (active CCM branch) | λ_min(K_m) ≥ −C_η m^η ∀η | OPEN | **yes: exponent = Θ − 1/2** | CHAT_DIGESTS 2026-10-28, answer3 check |
| G0, Assembly | same family F, normalization, one theorem | OPEN | no (bookkeeping on graded inputs) | PAPER_CHAIN:13, 26 |

## Why G3 is Θ-graded (both sides)

Right side (sufficiency), checked source: `CRITICAL_STRIP_PROJECTION_SOURCE_AUDIT_2026-10-06.md:206–242`:
sup_K |F_m − T_m| ≤ C m^{H/2} √log m (α_m + 4 t_m) on compacts K ⊂ {|Im z| ≤ H}, t_m superpolynomially small.
Off-real centered zeros sit at |Im z| ≤ Θ − 1/2, so α_m = O(m^-a) with a > (Θ−1/2)/2 gives hconv on a strip that contains them.
Unconditionally that is a > 1/4; with ZF78 it is a > 3/16 (`DIRECT_Q3_THEOREM_TRANSFER.md` §3).

Left side (witness), observer's derivation from the same inequality, NOT checked by Proshka:
suppose Ξ has a zero z0 with |Im z0| = δ' > 0. The F_m have only real zeros (G2) and T_m → Ξ (G4).
By Hurwitz, F_m cannot converge to Ξ uniformly on a small disc around z0, so sup_K |F_m − T_m| does not tend to 0 for K ∋ z0.
For every H > δ' this forces m^{H/2} √log m (α_m + 4 t_m) ≥ c > 0 along a subsequence, i.e. α_m ≳ m^{−H/2}/√log m infinitely often.
So the achievable tracking exponent is at most (Θ − 1/2)/2 whenever RH fails.

## Consequence

Every open rope that carries load is Θ-graded: SP floor (Θ − 1/2) and G3 tracking ((Θ − 1/2)/2).
Proving either at its RH value is proving Θ = 1/2. This is why many routes ended in "if this is proved, it is RH"
(28 RH_EQUIVALENT_FOUND rows in `RESULT.md`).
External input can tighten these ropes only by moving Θ. ZF78 moved them by exactly its gain: floor 1/2 → 3/8, tracking 1/4 → 3/16.
G1 is the open rope that is not known to be Θ-graded. External mathematics (total positivity, oscillation theory, prolate asymptotics) can serve it,
but closing G1 does not move RH by itself.

## OpenAI catalogue as supplier (scan 2026-10-28, `OAI_ROPE_SUPPLIERS.md`, catalogue abstracts only, no PDFs read)
| Target | DIRECT | PARTIAL | ANALOGY |
|---|---|---|---|
| G1 (ground parity, gap, odd floor) | 0 | 0 | 4 (#269 Laughlin gap via H² ≥ γH, #268, #369, #350) |
| prolate / Sturm–Liouville asymptotics | 0 | 0 | 1 (#262, weak) |
| Θ-moving (zero-free, density, moments, Weil positivity) | 3, all family #003 (7/8; 11/12 alternate; Landau–Siegel real-zero gap) | 0 | 2 (#182, #029) |
| Hurwitz / Laguerre–Pólya side | 0 | 0 | 0 |
| #079 local smoothing, #378 ETH | touch none of the above | | |
Lean status in formalization.yaml: "Partial progress", review "unchecked" for all candidates.
Verdict: the only OpenAI input that tightens our load-bearing ropes is Θ ≤ 7/8, and it is already used (floor 3/8, tracking 3/16).
