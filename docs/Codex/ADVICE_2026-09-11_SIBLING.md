# ADVICE SIBLING — the finite function-field sibling of SL14/SL20 (owner + observer, 2026-09-11)

Owner's word: «сначала математическая модель … посмотрим, это вообще математически решаемо, а потом всё остальное»; work rule per
`ADVICE_PROTOCOL.md`: three own attempts, at most one Proshka request, answer only with a victory, else «поражение» + gains + push.

## Verified by the observer (rule 13, numbers by hand)

Object. Curve X/F_q of genus g, Z(T)=P(T)/((1−T)(1−qT)). On the critical circle T=q^{-1/2}e^{iθ}:
Xi(θ) := P(q^{-1/2}e^{iθ}) e^{-igθ} = Σ_{j=-g}^{g} φ_j e^{ijθ}, φ real and even (functional equation). Weil RH ⟺ all zeros θ real.
Discrete SL12a/SL14: V(x,y)=Σ_{t≥0}(x+y+2t)φ(x+t)φ(y+t), H_2(x,y)=q^{2(x+y)}V(x,y), x,y ∈ Z.
- genus 1, P=1−aT+qT²: V collapses to [[2, −a/√q],[−a/√q, 2]] (sympy); all other entries vanish by the odd-weight cancellation
  (the full-line sum is identically 0, exactly as in the continuous case). det = 4 − a²/q. So H_2 ⪰ 0 ⟺ |a| ≤ 2√q, the Hasse bound.
- genus 2, q=7: min eig H_2 ∈ [−5e-9, 0] for zeros on the circle, −3e-2 … −2.6 off it; 200/200 random samples: PSD ⟺ zeros on circle.
- Script: `docs/routeB_bus/sibling/ff_sibling_h2.py`. Digest: CHAT_DIGESTS 2026-09-11 «Sibling first».
Selberg zeta is NOT a sibling for this route (no Poisson duality, atomic Fourier dual, no smooth theta kernel) — do not go there.

## The question (one victory = both parts at PAPER scope)

Q1 (finite theorem). Prove: for a real even trigonometric polynomial Xi of degree g with coefficients φ, and V, H_2 as above,
    H_2 ⪰ 0 on all finitely supported complex vectors  ⟺  all zeros of Xi are real.
    Name the classical form V is congruent to (Hermite / Bezout / Schur–Cohn / de Branges reproducing kernel — the observer's
    UNVERIFIED guess: Σ_{t≥0} = geometric series 1/(1−z w̄), weight u+v = derivative, hence a Hermite–Bezout form of Xi).
Q2 (the needle). Weil proves the zeros real from geometry (Hodge index / Castelnuovo on X×X), i.e. positivity ⇒ zeros, never the
    reverse. Map that proof onto the summands of V: which intersection-theoretic quantity equals which term of
    Σ a_i ā_j V(x_i,x_j) (the 2∫t|F|² «reservoir» and the signed cross term 2Re⟨G,F⟩ of the continuous case have discrete
    analogues). The output is the property of φ (equivalently of the effective-divisor counts) that PAYS the sign, stated so that
    its number-field analogue is a checkable statement about Φ.

Negative controls to keep: any real even trigonometric polynomial with a zero off the circle (the script builds them); the
continuous controls f_c and OC1/OC2 stay in force for the port back.

IF_A: Q1+Q2 done → the port to Φ is the next request to Proshka (one request). IF_B: Q1 done, Q2 not → report the exact step of
Weil's argument that has no summand in V; that step is the wall, recorded as an object. IF_C: Q1 fails → the sibling is not SL14's
sibling; record the witness and stop.
