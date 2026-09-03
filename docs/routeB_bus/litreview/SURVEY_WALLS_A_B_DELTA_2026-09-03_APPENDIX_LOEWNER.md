# Appendix LOEWNER — scout report on the Loewner/Cauchy-like structure of the CCM finite Weil matrix (agent C, 2026-09-03, after Probe 5)

Trigger: Probe 5 CONFIRMED (the minimal-norm dual certificate for the curvature functional
sits entirely on the second eigenpair, so attack R1 pays 1/(λ₂−λ₁)); judge's ordered rule
sends the front to R2 (Schur–Stieltjes at the central coordinate). Question to the scout:
is there a classical explicit-inverse or sign theorem that evaluates
1/12 − ⟨c,(D−λ)⁻¹b⟩ without an operator-norm bound? Verbatim agent report follows.
Extracted sources: `pdfs/survey_2026-09-03_sources/` (ccm_2511.22755, inertia_loewner_1501.01505,
silva_loewner, pole_note, herglotz_criterion, silva_operator_monotone, groskin_2607.02828).

## 1. The source lemma [VERIFIED, arXiv:2511.22755 §5.1 pp.16–17]
Lemma 5.1 verbatim: τ_{i,i}=a_i, τ_{i,j}=(b_i−b_j)/(i−j), a_{−j}=a_j, b_{−j}=−b_j. CCM do not
use the word "Loewner"; the divided-difference identification is made in follow-on work,
cited there as Connes–van Suijlekom Prop. 4.1 (CMP 406:312, 2025, arXiv:2511.23257)
[RELAY_UNVERIFIED for that attribution].

## 2. Classical Loewner inertia [VERIFIED, arXiv:1501.01505 in full]
Bhatia, Friedland, Jain, "Inertia of Loewner matrices" (2015), Thm 1.1: exact inertia of
L_r[i,j]=(p_i^r−p_j^r)/(p_i−p_j) for all real r>0; singular iff r∈{1,…,n−1}; r=2k:
In=(k,n−r,k); r=2k−1: In=(k,n−r,k−1); non-integer r with ⌊r⌋=2k or 2k−1: In=(n−k,0,k) or
(k,0,n−k); every nonzero eigenvalue simple. [RELAY] Bhatia–Sano, Math. Ann. 344 (2009):
f operator convex ⟺ all Loewner matrices conditionally negative definite. [RELAY] Fiedler,
LAA 432 (2010) 351–356 (Hilbert/Cauchy matrices); Ando, LAA 90 (1987) (total positivity).

## 3. Displacement structure [RELAY_UNVERIFIED, bibliographic]
Kailath–Sayed, SIAM Review 37(3) 1995: displacement structure survey; Schur complements of
Cauchy-like matrices remain Cauchy-like. Bertola–Gekhtman–Szmigielski, J. Approx. Theory
162 (2010), arXiv:0904.2602 (Cauchy biorthogonal polynomials, total positivity of the
Cauchy kernel).

## 4. Herglotz / secular-equation technique on THIS matrix [VERIFIED, Zenodo PDFs opened]
Silva (Breno Wilson de Andrade Silva, independent, Zenodo, June 2026, not peer-reviewed):
- 10.5281/zenodo.20694588 "A scalar Herglotz criterion for the even-simplicity hypothesis in
  the localized Weil quadratic form": pole term split as rank-2, W₀,₂ = 2|C⟩⟨C| − 2|S⟩⟨S|
  (C = cosh(x/2) even, S = sinh(x/2) odd); even-simplicity reduced via Weinstein–Aronszajn /
  Sherman–Morrison secular equations to the two Herglotz functions
  m_e(λ)=⟨C,(B_e−λ)⁻¹C⟩ = −1/2, m_o(λ)=⟨S,(B_o−λ)⁻¹S⟩ = +1/2; Thm 4: even-simplicity ⟺ one
  scalar inequality ⟨S,(B_o−λ₀^even)⁻¹S⟩ < 1/2. No operator-norm bound anywhere.
- 10.5281/zenodo.20682834 "The pole term is the only obstruction to Perron structure…",
  Remark 1: "the naive split … produces a sign-violating part whose norm equals the spectral
  gap of the sign-good part to within a percent at every cutoff … this is why no soft norm
  bound decides the sign and the nodal/oscillation route is the appropriate one."
- 10.5281/zenodo.20737111 "A Loewner/operator-monotone framework for the even-simplicity
  problem…": the full truncated Weil matrix is verbatim the Loewner matrix of an odd
  function ψ(k)=k·h(k²); the parity sectors are Loewner matrices of h and Φ(ξ)=ξh(ξ) in ξ=k².
- 10.5281/zenodo.20710075 "A Loewner divided-difference formula for the prime
  contribution…": exact identity ⟨v,Pv⟩ = −2 Σ_q Λ(q)/√q · ω_q ∫₀¹ Re[W_v(−2πω_q t) W_v(2πω_q(1−t))] dt.
Groskin, arXiv:2607.02828v3 (Aug 2026) [VERIFIED]: archimedean tail is a totally positive
Cauchy–Stieltjes increment (Karlin 1968; Simon, JAT 184 (2014)); cutoff-free interval LDLᵀ
(Sylvester inertia at high precision) certifies signs at the 10⁻⁵⁹ scale where a cutoff
alone would need T ≈ 10⁶³.

## Agent synthesis (verbatim)
1. No classical or 2020–2026 source gives a ready-made closed form or sign theorem for the
   mixed pairing ⟨c,(D−λ)⁻¹b⟩, c≠b, on this exact matrix; the question is open even in the
   specialized 2026 literature.
2. Nearest analytic tool: polarization ⟨c,(D−λ)⁻¹b⟩ = ¼[⟨c+b,(D−λ)⁻¹(c+b)⟩ − ⟨c−b,(D−λ)⁻¹(c−b)⟩],
   turning the mixed pairing into two self-pairings — exactly the Herglotz m-functions that
   Silva's secular-equation machinery handles without resolvent-norm bounds.
3. That literature diagnoses our obstruction explicitly: norm bounds fail because the bad and
   good parts are norm-matched to ~1% at every cutoff; only scalar Herglotz secular
   equations or nodal/oscillation arguments see the cancellation.
4. Bhatia–Friedland–Jain is the right template for closed-form inertia but is stated for
   f=t^r; transplanting needs the arithmetic h compared with an operator-monotone function.
5. Displacement/Cauchy-like theory suggests (D−λ)⁻¹b has an exact rational/continued-fraction
   form; nobody has carried it out for the CCM matrix.
6. Groskin's interval LDLᵀ is the concrete numerical route that avoids 1/(λ₂−λ₁).
7. The prime-block Loewner formula plus polarization could give the prime part of S(λ) exactly
   if c and b are expressed through the symbols C, S or W_v.
8. Strategy implied: do not bound ‖(D−λ₁)⁻¹‖; express S(λ₁) via a rank-one/rank-two secular
   equation against known Herglotz functions, reducing the two-order cancellation to a scalar
   identity at the energy λ₁.
9. Caveat: Silva/Groskin/Andrews are self-published (Zenodo/arXiv, June–Aug 2026), internally
   consistent and machine-verified, but not peer-reviewed: strong leads, not settled theorems.
10. Next: read Silva "Exact archimedean entries" (Zenodo 20671635) and "Quadrature
    sensitivity" (Zenodo 20650146), and Suzuki 2606.09096 in full (Krein-string / Stieltjes
    m-function framework).

Observer note: the polarization + secular-equation route is the R2 the judge asked for, in
existing words. It closes nothing yet; it names the object. Candidate for the next batch.
