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
Update from accepted SLACK report BP1-BP5 at659f389c: the positive-variable density is r of T=sum Gamma(2,rate pi*n^2), and Phi(x)=exp(5x/2)r(exp(2x)). Phi/I is the density of the logarithmic variable only after the T^(1/4) tilt; f=Phi/A is normalized in L2. Infinite divisibility is asserted for T, not transported through the tilt/logarithm. The earlier literal Phi-is-a-sum-density/UNTESTED wording is superseded.
Gives: exact fixed source product, positive Volterra identity t*r=k*r, and mean-matched negative control showing the whole law is needed. Does not give the full-form sign SL20. Read scope: printed pages3-7,10-14 of the local recompiled math/9912170v1, SHA25604a444275e5522cef9a1ba9f7d1b9f20a752764d3548f9c48be6dbc055bb12ea; original cited sources remain relay as specified in the accepted report.

### MASATOSHISUZUKI-2023 — arXiv:2301.00421, Suzuki, "On the Hilbert space derived from the Weil distribution", Canad. J. Math. 2025
VERBATIM (abstract): "the Hilbert space obtained by completing the space of all smooth and compactly supported functions on the real line with respect to the hermitian form arising from the Weil distribution under the Riemann hypothesis."
Variables: his hermitian form on C_c^∞ = the left side of our SL14. Result is **under RH** → circular for us (WHY_NOT_YET §4.2–4.5).
Gives: de Branges description of the completed Weil space, conditional. Does not give: SL20. Not read: body.

## Not taken as candidates
- Watson arXiv:2602.01248 (PF_∞ for a "logarithmic kernel" from Markov cycles): his Φ is a different kernel; coincides with theta only after his "Archimedean completion". No contradiction with Michałowski. Not fetched onto the shelf.
- Jorgensen–Neeb–Ólafsson 1608.04010 (reflection positivity on intervals): Hankel prototype `k(x+y)`; our kernel is not Hankel (above). Not fetched.
- "Haar Positivity: From Weil to Wightman" (philarchive): not peer-reviewed, dropped.

## Result of the hunt
This bounded hunt found no verified source supplying SL20. Closest published objects: Csordas' `K_n` (even weights, n ≥ 1 open), Suzuki's screw-function kernel
(second difference, RH ⟺ PSD ∀a), Connes–Consani Sonin compression (archimedean place, restricted tests). One branch killed with a
certificate (PF_r, r ≥ 5). Note: SL20 ⟺ RH ⟺ (K_n PSD ∀n); a single `K_1 ⪰ 0` is only necessary, so "SL20 = Csordas' L_1 inequality"
cannot hold unless K_1 ⪰ 0 already implied RH, which is not known.


### SALAZAR-HCM-DEFINITION-2026 — arXiv:2606.22066v1, definition only

Source: "A Bessel-zero obstruction to hyperbolic complete monotonicity of noncentral chi-square densities", https://arxiv.org/pdf/2606.22066v1, printed/PDF page2, section1 equations(4)-(6). Media438020bytes, SHA256b3c31f2e94530f74cc034518efaf7e9c455c62f57e6f366eff97aa6ace9e4b09; intended local pdfs/q3-hcm-definition.pdf. Page2 read and rendered; only pages1-3 read. Other paper claims/proofs and original references were not audited or imported.

VERBATIM prose excerpt, page2: "is completely monotone as a function of the hyperbolic variable". The adjacent displays define r(uv)r(u/v) as a function G_u(w), w=v+v^(-1)>2, with (-1)^j G_u^(j)>=0 for all integer j>=0 and every u>0.

Mapping: our candidate input is the positive-variable density r of T=sum Gamma(2,rate pi*n^2), not Phi/I or the shifted law mu. The gamma-convolution product alone does not assert HCM. Accepted BP3's reciprocal negative control means reciprocal symmetry alone is insufficient; it is not substituted for the actual r in this test.

Root's NEW property-exclusion candidate is HC1-HC4 in DENSITY_INDEPENDENT_CHECK_2026-09-11.md: actual r at u1,v10,w101/10 has log-curvature[-0.0360085176300411560160774208455744692 +/-9.01e-38] with full derivative tails. A self-contained finite-difference argument proves the necessary log-convexity of any positive completely monotone function. Independent acceptance remains in that report's final receipt; this card alone is not acceptance.

Fit: DEFINITION_ONLY / NOT_A_POSITIVE_SUPPLIER. This reference supplies terminology, not a theorem proving SL20. The actual-source exclusion, if accepted, stops the proposed HCM shortcut; it does not disprove gamma-convolution membership or sign V/Q. Production theorem/consumer remains UNBOUND; no CLOSES/OPENS or proof admission. No further HCM source hunt is justified unless it changes this exact property test.


### MIT-SURFACES-L1-2008 / MIT-SURFACES-L2-2008 — finite SIBLING geometry

Primary teaching sources: MIT OpenCourseWare18.727, Spring2008, Algebraic Surfaces lectures1and2. Lecture1: q3-sibling-mit-lect1.pdf166197bytes/SHA2567d04b0f0bf9880cee12a3ff0332d5d64a063b4ebe694e76d6ede874af90f98d9; lecture2: q3-sibling-mit-lect2.pdf198721bytes/SHA256e279bfeed05297da7b511164668148101e3455007ebc553b9f8cc5918363d77f. Exact URLs and quotes in SIBLING_INDEPENDENT_CHECK_2026-09-11.md S7. Whole extracted text read; lecture1printedp3-4/PDFp4-5 and lecture2printedp2-3/PDFp3-4 rendered/inspected. Other cited historical foundations remain relay, not independently audited.

VERBATIM lecture2printedp2 Corollary1 (mathematical glyphs transcribed): "If D is a divisor on X and H is a hyperplane section on X s.t. (D . H) = 0 then D^2 <= 0 and D^2 = 0 iff D equiv 0." Lecture1printedp3 fixes a nonsingular projective surface over an algebraically closed field; its intersection Definition1 and printedp4 Lemma1 supply multiplicities and restriction-degree pairing. Use the correct lemma statement deg L, not the proof's printed deg L^{-1} typo. Lecture2Theorem3 signature(1,rho-1), not its last sentence's erroneous equality, fixes the primitive sign.

Mapping: Xbar x Xbar, fibers F1/F2, E_n=q^{-n/2}(Gamma_Frob^n-q^nF1-F2); H=F1+F2 ample. Hodge gives -E_m.E_n as a nonnegative Gram matrix. The local SIBLING derivation proves its equality to p_|m-n|, p_d=q^{-d/2}(1+q^d-N_d),p0=2g, and V=BMB^T; the sources are not credited with that derived dictionary. General off-circle reciprocal polynomials lack this geometric realization; nonnegative coefficients/counts alone do not pay the matrix sign.

Fit: GEOMETRIC_SIGN_SUPPLIER_FOR_FINITE_SIBLING; independent acceptance belongs only to the report receipt. No positive supplier for original Phi/SL20/DN20 is claimed. The explicit Phi-moment Hermite/Jensen interface in S6 is an unproved all-degree sign obligation, already a known criterion on the shelf, not a new research campaign. Full number-field Hodge-compatible realization remains absent from this construction. Paper intake with exact existing media is a separate owner action; candidate acceptance does not assert that it has occurred.
