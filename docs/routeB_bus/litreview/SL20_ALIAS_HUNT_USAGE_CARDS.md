# SL20 under other names — alias hunt 2026-09-11 (four new shelf items)

Written by the observer after three parallel literature streams (operator theory / theta–Laguerre–Pólya /
physics–probability). Object: `V_f(x,y) = ∫₀^∞ (x+y+2t) f(x+t) f(y+t) dt`, `H₂ = e^{2(x+y)}V_f`, `f = Φ/A`;
SL14: Weil positivity on all complex compact tests ⟺ `H₂ ⪰ 0` (SL20). Source: PROSHKA_VERDICT_GOAL058_SLACK_2026-09-11.md.
Already on the shelf before the hunt and re-found by the agents: CC-WEILPOS-2020 (2006.13771), SUZUKI-SCREW-2026 (2606.09096),
MASATOSHISUZUKI-2022 (2206.03682); GEORGECSORDAS-2013 (1309.0055) and Planat–Solé (2608.19160) have their own card.

## Verified by the observer (not by the agents)

- `V_f(x,y) = 2∫_{(x+y)/2}^∞ s·f(s+τ)f(s−τ) ds`, `τ=(x−y)/2` (substitution `s=(x+y)/2+t`, exact). On the full line the
  integrand is odd in s for even f, so the untruncated integral is identically zero: **all of SL20 lives in the half-line truncation.**
  Csordas' associated kernels `K_n(t)=∫_ℝ Φ(s+t)Φ(s−t)s^{2n}ds` (1309.0055, Thm 4.5/(4.6), text line 690) use even powers for
  exactly this reason; RH ⟺ `K_n` positive definite ∀n (Thm 3.7/4.6); only n=0 is proved (Mathias 1923), n=1 is Open Problem 3.9 (line 488).
- `V_f` is not a Hankel kernel: `V_f(1,3) ≈ 4.7e-553` vs `V_f(2,2) ≈ 6.3e-141` (mpmath). Widder/Bernstein complete-monotonicity
  criteria for `k(x+y)` kernels (arXiv:2503.22189 abstract; Jorgensen–Neeb–Ólafsson 1608.04010) do not apply.
- Cross-Gram form: `Σ a_i ā_j V_f(x_i,x_j) = 2Re⟨H,F⟩`, `F=Σa_i f(x_i+·)`, `H=Σa_i ψ(x_i+·)`, `ψ(u)=u f(u)`; equivalently
  `2∫₀^∞ t|F|² + 2Re⟨G,F⟩` with `G=Σ a_i x_i f(x_i+·)` (numerically: 0.237241 − 0.229958 = 0.007283 = form, 12 digits).
  Sign stands as a difference of close numbers → not yet the rule-18 representation.

## Cards

### WOJCIECHMICHALOWSKI-2026 — arXiv:2602.20313v2, "On the Pólya Frequency Order of the de Bruijn–Newman Kernel: Certified Failure at Order Five" (preprint, Feb/Jul 2026)
VERBATIM (Thm 1.1): "The de Bruijn–Newman kernel K(u)=Φ(|u|) is not PF5. Specifically, the 5×5 Toeplitz matrix M_{ij}=K(u₀+(i−j)h), i,j=0,…,4, with u₀=0.01 and h=0.05, satisfies det(M)=−1.847236073…×10⁻⁹<0." Abstract: "does not resolve the Riemann Hypothesis."
Variables: his Φ = Φ_Csordas = our Φ(2·)/2. **Observer recomputation (mpmath, 40 digits): det = −1.847236073e-9, all printed digits match.**
Gives: total positivity / PF_r, r ≥ 5, of Φ is dead as a route to SL20. PF4 open (his Problem 1).
Does not give: anything positive. Not read: sections 2–6, the 80-digit interval certificate.

### KARLHEINZGRCHENIG-2020 — arXiv:2007.12889, Gröchenig, "Schoenberg's theory of totally positive functions and the Riemann zeta function"
VERBATIM (Thm 4): "The Riemann hypothesis holds, if and only if Λ(x) = (1/2π)∫ 1/ξ(½+τ) e^{−ixτ} dτ is a Polya frequency function." After Thm 5: "It is therefore unlikely that much is gained by Theorems 3 – 5."
Variables: his Λ = Fourier transform of **1/ξ**, not our f (our F = ξ/A by SL10). No weight.
Gives: the PF-object equivalent to RH is 1/ξ-side; Michałowski's negative result on Φ (ξ-side) is not in tension with it. Closes the Schoenberg line for SL20.
Does not give: SL20. Not read: proofs.

### PBIANEANDJPITMANANDMYOR-1999 — arXiv:math/9912170, Biane–Pitman–Yor, Bull. AMS 38 (2001) 435–465
VERBATIM (abstract): "connect Riemann's integral representations of his zeta function, involving Jacobi's theta function and its derivatives, to some particular probability laws governing sums of independent exponential variables."
Variables: their theta laws ↔ our Φ up to change of variable; no weight, no quadratic form.
Gives: Φ as an explicit density of a sum of independent exponentials (infinitely divisible). Candidate input for a rule-18 representation of `V_f` (positive mixture weights → first moment under a measure). UNTESTED.
Does not give: any PSD theorem. Not read: §2 explicit mixture representation (the thing to read next if this line is pursued).

### MASATOSHISUZUKI-2023 — arXiv:2301.00421, Suzuki, "On the Hilbert space derived from the Weil distribution", Canad. J. Math. 2025
VERBATIM (abstract): "the Hilbert space obtained by completing the space of all smooth and compactly supported functions on the real line with respect to the hermitian form arising from the Weil distribution under the Riemann hypothesis."
Variables: his hermitian form on C_c^∞ = the left side of our SL14. Result is **under RH** → circular for us (WHY_NOT_YET §4.2–4.5).
Gives: de Branges description of the completed Weil space, conditional. Does not give: SL20. Not read: body.

## Not taken as candidates
- Watson arXiv:2602.01248 (PF_∞ for a "logarithmic kernel" from Markov cycles): his Φ is a different kernel; coincides with theta only after his "Archimedean completion". No contradiction with Michałowski. Not fetched onto the shelf.
- Jorgensen–Neeb–Ólafsson 1608.04010 (reflection positivity on intervals): Hankel prototype `k(x+y)`; our kernel is not Hankel (above). Not fetched.
- "Haar Positivity: From Weil to Wightman" (philarchive): not peer-reviewed, dropped.

## Result of the hunt
No published theorem gives SL20. Closest published objects: Csordas' `K_n` (even weights, n ≥ 1 open), Suzuki's screw-function kernel
(second difference, RH ⟺ PSD ∀a), Connes–Consani Sonin compression (archimedean place, restricted tests). One branch killed with a
certificate (PF_r, r ≥ 5). Note: SL20 ⟺ RH ⟺ (K_n PSD ∀n); a single `K_1 ⪰ 0` is only necessary, so "SL20 = Csordas' L_1 inequality"
cannot hold unless K_1 ⪰ 0 already implied RH, which is not known.
