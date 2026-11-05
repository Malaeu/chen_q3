# PROSHKA REQUEST — PROVE RH, ROUND 5: PERELMAN'S METHOD — DESIGN THE GAUGE AND THE FUNCTIONAL (2026-11-05)

Repository: https://github.com/Malaeu/chen_q3

Branches:
- `rh_clean` holds this file; the commit is given in the owner's message.
- `proshka_inbox_2026-10-31`: write your verdict here as a NEW file. Base it on the tip that contains your Round-4 verdict.

Firmware: docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md, blob 32a5337b8b3bd431126084f250baf73f86e8f749.

Start this round only after your Round-4 verdict is pushed. If Round 4 already supplies a functional or a norm, use it as the starting point. Rounds 1–4 are not edited.

## GOAL

Prove the Riemann Hypothesis. The bottom line of your answer is RH.

## THE OWNER'S METHOD FOR THIS ROUND (explicit)

Perelman did not prove that a given quantity is monotone. He **constructed** the entropy W. He added corrections (the function f, the scale τ, constants) until the derivative along the flow became an integral of a square. He also used gauge freedom: Ricci flow corrected by diffeomorphisms becomes a gradient flow. A diffeomorphism does not change the geometry; it changes the description so that the sign becomes visible.

Do the same here, backwards from the target:

1. **Assume the target regime.** Along a flow of your choice the one-step map is non-expansive in a functional W, so errors ADD and the total is polylog(m). The natural flow is the window σ-flow from the proved side Re s = 1 down to σ_m = 1/2 + c/log m (Round-4 request, Idea 2(a), and Addendum Idea 3).
2. **Back-propagate the requirements.** For every link of the chain, write what it must satisfy for (1) to hold.
3. **Meet each requirement with a free knob, never with ζ.** Allowed knobs:
   - **(a) Gauge.** Counterterms that vanish on the admissible space 𝒦_m (built from e0 and p_m) — your representation (ii), 3d3ba2e6 §9. For each one, prove it leaves A_m unchanged on 𝒦_m.
   - **(b) The functional or norm W.** Choose the measure of error in which the σ-step contracts.
   - **(c) Further exact renormalizations**, after the pole. Candidates:
     - the smooth staircase term θ/π;
     - the pole-cancelled prime operator C_L − Z_L = M_L·Σ(log n − d(n))e_n (identity from 8e584bb8 (3.1)–(3.3)).
   - **(d) Test class.** The physical cone |f̂|² with ‖w′‖₁ ≤ 2πL‖f‖², instead of control on all frequency intervals. Your Round 3 noted that necessity of the all-frequency requirement is unknown.
   - **(e) Smoothed comparison objects** with an exactly paid difference — for example Selberg-type weights against the sharp cut n < m. The literal A_m itself stays unchanged.
   - **(f) Flow parametrization**: step size and the coupling σ_m.
4. **Build W** by adding corrections until dW/d(flow) = ∫(square) + summable remainder.
5. **Whatever no knob can achieve is the residual lemma on ζ.** State it in its cheapest form.

**Precedent inside this project.** Your pole renormalization (8.1)–(8.3) is the first successful gauge correction of exactly this kind. It is an exact identity that changes nothing on admissible vectors, yet it removed the sqrt(m) wall. Mythos DIAG, m ≤ 10⁷: the remainder after the pole echo is ≈ 1–1.6, against sqrt(m) up to 3162. Find the next correction of this kind.

## ACCEPTANCE (fixed before you start)

1. **Freeze first.** Commit the specification (flow, W, list of knobs) before construction.
2. **Gauge invariance.** For every knob used, give a proof that A_m on 𝒦_m (or the RH-export receiver) is unchanged. A knob that changes the source is a substitution and is rejected.
3. **The derivative formula.** Give the exact dW/d(flow), with the square part and the remainder separated.
4. **The residual lemma.** It must be stated exactly, and it must:
   - fail for DH, DMV and the planted quartet, each with its own source;
   - pass for the curve over 𝔽₃;
   - name the step where the arithmetic of ℚ enters.
5. **No relabelling.** All earlier kills and acceptance items of Rounds 3–4 apply. Restating N2 (Δ_m ≤ polylog) without a new inequality is NO_PROGRESS.
6. **Falsifiers.** For every strictly stronger node, give a Codex test fixed in advance: quantity, grid, precision, plant, pass/fail.
7. **Bottom of the chain**, one of:
   - (a) RH proved;
   - (b) W built, plus the exact residual lemma;
   - (c) a proof that no W of this class can make the σ-step non-expansive. Name the obstruction.
