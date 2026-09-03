# Observer's sealed shell candidate (written BEFORE the judge's SHELLSEARCH answer)

Date: 2026-09-03 ≈23:55 CEST. Purpose: independent answer to "which shell connects the source
to the atom", sealed by commit hash so the comparison with the judge (`REQ-2026-09-03-SHELLSEARCH`)
is honest. Not sent to the judge. Owner's protocol: parallel blind answers, then a synergy check.

## Gap being shelled (after `f788d2fa`)

Atom (two-component): `W_k = Σ_{n≤N}|Δ_n|/n² = O(L⁻²)` (normality) and
`sup_{n ≤ XL/2π}|Δ_n| → 0` for each `X` (identification), `Δ_n = F_k(x_n)/F_k(0) − Ξ(x_n)/Ξ(0)`.

## SHELL_OBS_1 — Weil-energy pinning at the zeta zeros

Inputs (status):
1. The windowed Weil form is the explicit-formula quadratic form: `⟨v, K̃ v⟩ = W(g_v)` and
   `W(g) = Σ_ρ ĝ(ρ) ĝ(1−ρ̄)`-type sum over zeros minus archimedean/prime terms already inside `K̃`
   (Weil 1952; Bombieri 2000; CCM §2–3 by construction). PROVEN_IN_LITERATURE; the project's
   Lean source defines `K̃` by its entries, the zero-sum identity is NOT in the project.
2. `λ_1 ≤ Rayleigh(trial) → 0` super-exponentially (CCM §7 construction; numerics 10^{−1.9m}).
   PROVEN_IN_LITERATURE (upper bound) / OBSERVED (rate).
3. Real zeros of `F_k` and the envelope `|F_k(z)| ≤ |F_k(0)| e^{κ_k|z|²}` (Lean, `926c1865`).
   PROVEN_IN_PROJECT, conditional on bounded κ (circular for normality; usable for identification
   once normality is supplied separately).

Mechanism (5 lines): ground energy `⟨ξ,K̃ξ⟩ = λ_1` is tiny; if the zero-sum is a sum of squares
`Σ_γ F_k(γ)²` over on-line zeros, then `F_k(γ_j) ≈ 0` at all zeros `|γ_j| ≤ X`; a real-zero
function of exponential type `L/2` nearly vanishing at the `J ≈ XL/2π` zeros of `Ξ` in `[−X,X]`,
normalized at 0 and bounded by the envelope, has quotient `F_k/Ξ` analytic and bounded on
`|z| ≤ X` (envelope + minimum-modulus), hence `Δ_n` small on `n ≤ XL/2π`. Output: identification
component. Normality component NOT delivered by this shell.

Predicted first failure (observer): input 1 unconditionally is NOT a sum of squares (off-line
pairs `F(γ+iδ)F(γ−iδ)` may be negative, Yoshida/Bombieri) → "energy small ⇒ values small" needs
the ¬RH sign control → circular, same death as C2. Second failure: `J ≈ XL/2π` nodes at exact
Nyquist give no stable interpolation (Cartwright), so the quotient bound must come from the
envelope, which needs bounded κ first. Third: `λ_1` is the FULL form, its outer tail (zeros
`|γ| > m`) is not small per zero.

Registered probabilities (observer): P_SHELL_OBS_1_SURVIVES_JUDGE = 0.30;
P_SHELL_OBS_1_DELIVERS_IDENTIFICATION_GIVEN_NORMALITY = 0.45.

## SHELL_OBS_2 — (not independent) the judge's own low-mode recurrence; 0.40 by the judge.
## SHELL_OBS_3 — (not independent) common-anchor projective two-jet; judge's fallback.

## Honest count

The observer's independent proposal is ONE shell for ONE component. The count "one shell
missing" of earlier tonight was an interface count (REQUIRES − PROVIDES) and was wrong by one:
the judge split the required statement into two components.
