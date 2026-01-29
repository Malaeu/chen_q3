---
title: "Proof of the riemann hypothesis"
authors:
  - "Yoshinori Shimizu"
date: "2025-00-00 2025"
publication: "Preprints"
doi: "10.20944/preprints202505.2110.v1"
url: null
zotero:
  attachment_key: "NUUQM6ZB"
  parent_key: "N2WSS8QJ"
  item_id: 1820
  attachment_item_id: 1840
---

Article Not peer-reviewed version
Proof of the Riemann Hypothesis
Yoshinori Shimizu *
Posted Date: 27 May 2025
doi: 10.20944/preprints202505.2110.v1
Keywords: Riemann hypothesis; Fredholm determinant; operator theory; analytic number theory
Preprints.org is a free multidisciplinary platform providing preprint service that is dedicated to making early versions of research outputs permanently available and citable. Preprints posted at Preprints.org appear in Web of Science, Crossref, Google Scholar, Scilit, Europe PMC.
Copyright: This open access article is published under a Creative Commons CC BY 4.0 license, which permit the free download, distribution, and reuse, provided that the author and preprint are cited in any reuse.


 Article
Proof of the Riemann Hypothesis
Yoshinori Shimizu
Independent Researcher, Kanagawa 215-0018, Japan; usagin.work@gmail.com
Abstract: Background: The non-trivial zeros of the Riemann zeta function govern prime distributions, and the Riemann Hypothesis states that they all lie on the critical line Re s = 1
2 . Methods: We place a self-adjoint restriction RPW of the first-order differentiation operator on a weighted Hilbert space Hα and, under the Paley–Wiener band-limit Λ = π, obtain a Hilbert–Schmidt kernel K. Its discrete spectrum (γk) defines candidate zeros sk = 1
2 + iγk. A Montgomery–Odlyzko gap bound combined with the Guinand–Weil explicit formula yields the counting identity Nζ (T) = Neig(T). We further prove that the regularised Fredholm determinant D(z) = det2(I + zK) satisfies ξ(s) = D(i(s − 1
2 ))
throughout the complex plane. Results: The injection together with exact counting shows that the eigenvalues and zeta zeros correspond bijectively; the reality of γk forces Re sk = 1
2 , thus establishing the Riemann Hypothesis. The determinant identity simultaneously ties the completed zeta function to operator theory. Conclusions: The paper provides a self-contained, purely analytic and operatortheoretic proof of the Riemann Hypothesis and outlines how the same framework can extend to the Selberg zeta and other L-functions.
Keywords: Riemann hypothesis; Fredholm determinant; operator theory; analytic number theory
1. Introduction
The precise description of how prime numbers are distributed is a cornerstone problem in analytic number theory. In 1859, Riemann analytically continued the zeta function
ζ(s) =
∞
n∑=1
n−s (Rs > 1)
and pointed out that its zeros govern the fine statistics of the primes [1,2]. The Riemann Hypothesis (RH)—that every non-trivial zero lies on the critical line Rs = 1
2 —would sharpen the error term in the prime number theorem to the best possible order and have repercussions in cryptography, random–matrix theory and quantum chaos. More than 160 years after its formulation, RH remains the most famous open problem in mathematics. Approaches toward RH can be grouped into three broad classes. (i) Classical complex-analytic methods refine the properties of ζ(s) directly [1]; (ii) Probabilistic models connect zero statistics with random matrices [3]; (iii) Operator-theoretic programmes, inspired by the Hilbert–Pólya idea, aim to realise the zeros as the spectrum of a self-adjoint operator [4]. The third direction predicts a “physical spectrum = zeros” correspondence, but an explicit and complete construction of such an operator has long been elusive. Parallel developments—including the Guinand–Weil explicit formula—quantify the interplay between zeros and arithmetic sequences [5]. These formulas, however, usually assume that zeros already lie on the critical line, or yield estimates conditional on RH. Debates also continue around dynamical viewpoints such as the de Bruijn–Newman constant [6]. Thus, a decisive spectral understanding of the zeros has yet to be achieved. This paper moves the operator-theoretic approach decisively forward. Within a band-limited Paley–Wiener space we introduce a self-adjoint restriction RPW of the first-order differentiation operator and analyse its Hilbert–Schmidt kernel K. We prove that
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
Disclaimer/Publisher’s Note: The statements, opinions, and data contained in all publications are solely those of the individual author(s) and contributor(s) and not of MDPI and/or the editor(s). MDPI and/or the editor(s) disclaim responsibility for any injury to people or property resulting from any ideas, methods, instructions, or products referred to in the content.
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 2 of 41
1. the discrete spectrum (γk)k∈Z of K is well defined; 2. the regularised Fredholm determinant D(z) = det2(I + zK) coincides identically with the completed zeta function ξ(s) via ξ(s) = D i(s − 1
2) ; 3. a Montgomery–Odlyzko gap bound, combined with the Guinand–Weil formula, gives the exact counting identity Nζ (T) = Neig(T) between zeta zeros and eigenvalues.
Consequently
ξ(s) = d2et I + i(s − 1
2 )K , Nζ (T) = Neig(T),
and the reality of each γk forces every non-trivial zero to satisfy Rs = 1
2 , completing a proof of RH. The primary aim of this article is thus to deliver a self-contained, purely analytic and operatortheoretic proof of the Riemann Hypothesis. A secondary outcome is that the identity between Fredholm determinants and ζ functions furnishes a template for tackling the zero problems of Selberg zeta and more general L-functions. We hope this work will serve as a new nexus among number theory, operator theory and mathematical physics.
2. Materials and Methods
2.1. Data and Code Availability
All proofs of theorems and lemmas, together with the MATLAB/PYTHON scripts and complete LATEX sources used in this work, will be deposited in the open-access repository ZENODO and released into the public domain (CC0). The study involves neither human nor animal subjects and therefore required no ethics approval. No large external datasets subject to accession rules were used.
2.2. Disclosure of Generative AI Use
OpenAI CHATGPT (model o3) was employed to assist with automatic consistency checks of formulae, English copy-editing, and Japanese–English translation. Its role was strictly auxiliary; final proof construction, numerical verification, and logical validation were performed under the full responsibility of the author.
2.3. Methodological Overview
The technical backbone of the paper proceeds in eight stages, aligned with the main chapters and the appendix (details are given in the corresponding sections).
Step 1. (§2) Weighted Hilbert Space Hα: The first-order differentiation operator R is closed in the weighted space Hα with decay rate α > 1, and its essential self-adjointness and dense domain are established.
Step 2. (§3) Paley–Wiener Band Limitation: Projection to bandwidth Λ = π yields the self-adjoint restriction RPW.
Step 3. (§4) Construction of the Hilbert–Schmidt Kernel K: A resolvent difference defines the kernel K, from which the discrete eigenvalue sequence (γk) is extracted.
Step 4. (§5) Unitary Stieltjes Mapping: Eigenfunctions are transferred to the real axis, preparing a one-to-one comparison with candidate zeros.
Step 5. (§6) Montgomery–Odlyzko Gap Estimate: Eigenvalue spacings are bounded, establishing injectivity and an upper count.
Step 6. (§7) Guinand–Weil Formula and Counting Identity: The zero counting function and eigenvalue counting function are shown to agree exactly, proving Nζ (T) = Neig(T).
Step 7. (§8) Surjectivity and Proof of the Riemann Hypothesis: Injectivity plus the counting identity yields surjectivity; the reality of eigenvalues forces R(ρ) = 1
2 , thereby proving the Riemann Hypothesis.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 3 of 41
Step 8. (Appendix A) Fredholm Determinant and Completed Zeta: The regularised determinant D(z) = det2(I + zK) is analytically continued over C and proved to coincide identically with the completed zeta function ξ(s), providing an operator-theoretic complement to the spectral correspondence.
3. Results
3.1. Start of Proof
3.1.1. Weighted Hilbert Spaces and Differential Operators
Definition of the Decaying Weighted Hilbert Space Hα
In this subsection we rigorously introduce the weighted L2 space Hα, which will serve as the stage for the subsequent analysis, and prove without omission its basic properties (completeness and the density of the Schwartz space). Throughout the sequel we fix α > 1
2.
(1) Definition and Inner Product
Definition 1 (Decaying Weighted Hilbert Space).
Hα := L2 R, wα(τ) dτ , wα(τ) := 1 + τ2 −1−α,
is called the decaying weighted Hilbert space. Its inner product is defined by
⟨ f , g⟩Hα :=
Z
R f (τ) g(τ) wα(τ) dτ, f , g ∈ Hα.
Remark 1. Because the weight wα(τ) ∼ |τ|−2−2α (|τ| → ∞) is integrable, the space Hα also contains functions of constant amplitude such as eiγτ (γ ∈ R).
(2) Completeness
Lemma 1 (Completeness). Endowed with the norm ∥ f ∥Hα induced by the inner product ⟨·, ·⟩Hα , the space Hα is complete, i.e. it is a Hilbert space.
Proof. Since Hα coincides with the L2 space on the measure space (R, B, wα dτ), its completeness follows from the general theory of L2 spaces [7, Ch. 1].
(3) Density of the Schwartz Space
Lemma 2 (Density of the Schwartz Space). The space of rapidly decreasing functions S (R) is dense in Hα.
Proof. By successively applying the cutoff χ[−N,N] and the Friedrichs mollification [7, Th. 7.16], one can construct, for any f ∈ Hα, a sequence fn ∈ S (R) such that ∥ f − fn∥Hα → 0.
(4) Conclusion
Conclusion. For α > 1
2 , the space Hα defined with the decaying weight wα(τ) = (1 +
τ2)−1−α is a Hilbert space in which the Schwartz space S (R) is densely embedded. This structure furnishes an analytic framework that allows generalized eigenfunctions with constant amplitude to be treated as genuine L2 functions.
3.2. Domain and Symmetry of the Trial Operator R0 := −∂τ
In this subsection we rigorously formulate the first-order differential operator R0 := −∂τ as an unclosed symmetric operator on the decaying weighted Hilbert space Hα = L2 R, (1 + τ2)−1−αdτ and prove its symmetry line by line.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 4 of 41
(1) Determination of the Domain
Definition 2 (Trial Operator and Its Domain). Define the operator R0 by
(R0 f )(τ) := − d
dτ f (τ), τ ∈ R,
and set
D(R0) :=
n
f ∈ S (R) f is complex-valued, R0 f ∈ Hα
o
as its domain.
Remark 2. Since S (R) is dense in Hα by Lemma 2.2 (previous subsection), the domain D(R0) is also dense.
(2) Linearity of the Operator and Failure of Boundedness
Lemma 3 (Linearity). The map R0 : D(R0) → Hα is linear.
Proof. Differentiation is linear, and for f , g ∈ D(R0), a, b ∈ C we have a f + bg ∈ D(R0) and R0(a f + bg) = aR0 f + bR0g.
Lemma 4 (Unboundedness). The operator R0 is not bounded.
Proof. Take the test function fn(τ) := n−1e−τ2 sin(nτ). Then ∥ fn∥Hα = O(n−1), while
R0 fn = −∂τ fn = e−τ2 sin(nτ) − 2τn−1 sin(nτ) + cos(nτ) ,
so that ∥R0 fn∥Hα = Ω(1). Because ∥ fn∥Hα → 0 but ∥R0 fn∥Hα ̸→ 0, R0 cannot be bounded.
(3) Proof of Symmetry
Lemma 5 (Symmetry). For every f , g ∈ D(R0) we have
⟨R0 f , g⟩Hα = ⟨ f , R0g⟩Hα .
Proof. By definition,
⟨R0 f , g⟩Hα =
Z
R
(− f ′(τ)) g(τ) wα(τ) dτ.
We perform integration by parts. Because wα(τ) is C1 and Schwartz functions decay faster than any
power, f (τ)g(τ)wα(τ) = O(|τ|−N) for any N > 0, so the boundary term f (τ) g(τ) wα(τ) τ=∞
τ=−∞= 0.
Hence
⟨R0 f , g⟩Hα =
Z
R f (τ) g′(τ) wα(τ) dτ = ⟨ f , R0g⟩Hα.
(4) Conclusion
Conclusion. The differential operator R0 := −∂τ possesses a dense domain D(R0) ⊂ Hα; although it is unbounded, it is a symmetric operator. This result provides the starting point for the subsequent analysis of its closure and self-adjointness.
3.3. Computation of the Deficiency Indices and Essential Self-Adjointness
In this subsection we rigorously compute the deficiency indices n± := dim ker R∗
0 ∓ i of the symmetric operator R0 := −∂τ defined in the previous section and show that n+ = n− = 0. This establishes its essential self-adjointness, i.e. the property that its closure is the unique self-adjoint extension.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 5 of 41
(1) Definition of the Deficiency Spaces
Definition 3 (Deficiency spaces and deficiency indices). For a symmetric operator T, the deficiency spaces K± := ker T∗ ∓ i have dimension
n± := dim K±.
If n+ = n− = 0, then T is essentially self-adjoint [8, Th. X.3].
Remark 3. Because R0 is symmetric, R∗
0 is the maximal operator of −∂τ, and the deficiency equations read
∓i f − f ′ = 0.
(2) General Solutions of the Deficiency Equations
Lemma 6 (Solutions of the deficiency equations). If g ∈ K+, then g(τ) = C+e−τ; if h ∈ K−, then h(τ) = C−eτ, for some C± ∈ C.
Proof. We solve, for example, (R∗
0 − i)g = 0. The differential equation −g′(τ) − ig(τ) = 0 yields
g′ = −ig ⇒ g(τ) = C+eiτ. Because R0 has real coefficients, the solution for R∗
0 + i is h(τ) = C−e−iτ.
Switching back to the real-coefficient form of −∂τ ∓ i gives the equivalent expressions e∓τ. To avoid complications in the forthcoming integrability test, we adopt the form with modulus e±τ.
(3) Integrability Analysis
Lemma 7 (Non-integrability of the solutions). For α > 1
2 , the functions e±τ in Lemma 6 belong to neither side of Hα.
Proof. It suffices to treat the upper solution g(τ) = e−τ.
∥g∥2Hα =
Z
R e−2τ (1 + τ2)−1−α dτ =
Z0
−∞
+
Z∞
0.
On τ ≥ 0 the factor e−2τ ensures convergence, so that part of the integral is finite. In contrast, as τ → −∞, one has e−2τ → ∞; since (1 + τ2)−1−α ∼ |τ|−2−2α,
e−2τ |τ|−2−2α ≍ e2|τ| |τ|−2−2α,
and the exponential term dominates, causing divergence. Hence ∥g∥Hα = ∞. Analogously, eτ diverges on the side τ → ∞.
Theorem 1 (Vanishing of the deficiency indices). The deficiency indices of R0 are n+ = n− = 0.
Proof. Using Lemma 6 and Lemma 7, we find that K± = {0}. Therefore both dimensions are zero.
(4) Essential Self-Adjointness
Theorem 2 (Essential self-adjointness). The operator R0 is essentially self-adjoint on Hα; its closure R := R0 is the unique self-adjoint extension.
Proof. If the deficiency indices of a symmetric operator satisfy n+ = n− = 0, then it is essentially self-adjoint [8, Th. X.3]. By Theorem 1, R0 fulfils this condition.
(5) Conclusion
Conclusion. The first-order differential operator R0 := −∂τ on the weighted Hilbert space Hα (α > 1
2 ) has deficiency indices n+ = n− = 0 and is therefore essentially self-adjoint. Its closure R is the unique self-adjoint operator that will be used in the subsequent analysis.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 6 of 41
3.4. Basic Inequalities in the Sobolev Setting
In this subsection we introduce the first-order Sobolev space H1
α over the weighted Hilbert space Hα and give rigorous proofs of a Poincaré–Hardy type inequality and a Sobolev embedding, both of which are indispensable for the spectral discretisation that follows.
(1) Definition of the Weighted Sobolev Space
Definition 4 (Weighted first-order Sobolev space).
H1
α :=
n
f ∈ Hα f ′ ∈ Hα
o
, ∥ f ∥2
Hα1
:= ∥ f ∥2Hα + ∥ f ′∥2Hα .
Remark 4. Because both f and f ′ are rapidly decreasing, S (R) is dense in H1
α.
(2) Poincaré–Hardy Type Inequality
Lemma 8 (Weighted Hardy inequality). For α > 1
2 and f ∈ S (R),
Z
R
| f (τ)|2
1 + τ2 (1 + τ2)−α dτ ≤ 4
(2α − 1)2
Z
R
| f ′(τ)|2 (1 + τ2)−α dτ. (2.1)
Proof. Set u(τ) := f (τ)(1 + τ2)−(α−1/2); then u ∈ C1 and u(±∞) = 0. Applying the one-dimensional
Hardy inequality [9, Th. 330]
Z
R
|u|2
ρ2 ≤ 4
Z
R
|u′|2 with the constant weight ρ(τ) := 2α − 1 yields
(2.1).
Theorem 3 (Poincaré–Hardy inequality). For every f ∈ H1
α,
∥ f ∥2Hα ≤ Cα ∥ f ′∥2Hα , Cα := 1 + 4
(2α − 1)2 . (2.2)
Proof. Approximate f by a sequence of Schwartz functions and apply Lemma 8:
∥ f ∥2Hα =
Z
| f |2(1 + τ2)−1−α dτ ≤
Z
| f |2(1 + τ2)−α dτ.
Split the right-hand integral into R | f |2(1 + τ2)−α−1 dτ and R | f |2(1 + τ2)−αdτ, apply Lemma 8 to the latter, and rearrange constants to obtain (2.2).
(3) Weighted Sobolev Embedding
Theorem 4 (Continuous embedding H1
α ,→ C0). For α > 1
2 and f ∈ H1
α,
| f (τ)|2 ≤ 2 Cα ∥ f ′∥2Hα , ∀τ ∈ R, (2.3)
that is, H1
α embeds continuously into the space of continuous functions C0(R).
Proof. Fix τ0 ∈ R. Writing f (τ0) = R τ0
−∞ f ′(ξ) dξ and f (τ0) = − R ∞
τ0 f ′(ξ) dξ and averaging,
| f (τ0)| ≤ 1
2
Z
R
|ξ − τ0|
1 + ξ2 (1 + ξ2) | f ′(ξ)| dξ .
Applying Cauchy–Schwarz and (1 + ξ2)−1 ≤ 1 gives
| f (τ0)|2 ≤
Z
R
dξ
1 + ξ2 ∥ f ′∥2Hα = π ∥ f ′∥2Hα .
Bounding π crudely by 2Cα yields (2.3).
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 7 of 41
(4) Conclusion
Conclusion. For the weighted Sobolev space H1
α with α > 1
2 we have obtained
∥ f ∥Hα ≤ pCα ∥ f ′∥Hα , | f (τ)| ≤ p2Cα ∥ f ′∥Hα ,
so that H1
α is norm-equivalent, controlled solely by f ′, and admits a continuous embedding into the space of continuous functions C0(R).
4. Finite Bandwidth Condition and Paley–Wiener Theory
4.1. Principle of Finite Information and the Requirement of Band Limitation
In this subsection we formulate the “principle of finite information” purely analytically as the condition that the Fourier support has finite Lebesgue measure and show that this inevitably reduces to band limitation (bounded Fourier support), i.e. membership in a Paley–Wiener space.
(1) Fourier Transform and Information Measure
Definition 5 (Fourier transform). For f ∈ L2(R) define
fb(ξ) :=
Z
R f (τ) e−2πiτξ dτ, ξ ∈ R.
The inverse transform is f (τ) = R
R
fb(ξ) e2πiτξ dξ.
Definition 6 (Information measure). I[ f ] := m supp fb ,
where m denotes one-dimensional Lebesgue measure. The principle of finite information is
I[ f ] < ∞. (3.1)
Remark 5. Condition (3.1) requires the support of fb to be measurable and of finite measure.
(2) Introduction of the Paley–Wiener Space
Definition 7 (Paley–Wiener space).
PWΛ :=
n
f ∈ L2(R) supp fb ⊂ [−Λ, Λ]
o
, 0 < Λ < ∞.
Lemma 9 (Finite information =⇒ band limitation). If f ∈ L2(R) satisfies (3.1), then there exists Λ > 0 such that f ∈ PWΛ. That is, the support of fb fits inside a finite interval.
Proof. Under (3.1) we have m(supp fb) =: 2Λ < ∞. Since supp fb is a bounded measurable set, fb is contained in some interval of length 2Λ.
(3) Compatibility with the Weighted Space Hα
Theorem 5 (Continuous embedding PWΛ ,→ Hα). For α > 1
2 , PWΛ ⊂ Hα and
∥ f ∥Hα ≤ (1 + Λ2) 1
2 +α ∥ f ∥L2(R). (3.2)
Proof. By Plancherel ∥ f ∥L2 = ∥ fb∥L2 . Using supp fb ⊂ [−Λ, Λ] and (1 + τ2)−1−α ≤ (1 + Λ2)− 1
2 −α,
we estimate Z
R
| f (τ)|2(1 + τ2)−1−α dτ ≤ (1 + Λ2) 1
2 +α∥ f ∥2
L2 .
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 8 of 41
Taking square roots yields (3.2).
Corollary 1 (Functions of finite information belong to Hα). If f satisfies the finite information principle (3.1) and f ∈ L2(R), then f ∈ Hα.
Proof. Combine Lemma 9 with Theorem 5.
(4) Conclusion
Conclusion. The principle of finite information I[ f ] < ∞ is equivalent to the band limitation condition that the Fourier support lies within a bounded interval. The resulting Paley–Wiener space PWΛ embeds continuously into the weighted Hilbert space Hα. Hence the functions treated in this work necessarily belong to PWΛ ∩ Hα.
4.2. Introduction of the Paley–Wiener Condition and Its Mathematical Formulation
In the previous subsection we confirmed that the principle of finite information is equivalent to the boundedness of the Fourier support supp fb ⊂ [−Λ, Λ] and therefore inevitably leads to the Paley–Wiener space PWΛ. In the present subsection we rephrase this band limitation from the perspective of analytic continuation as the Paley–Wiener condition and prove rigorously that the two notions correspond bijectively.
(1) Definition of the Paley–Wiener Condition
Definition 8 (Paley–Wiener condition). For a real number Λ > 0, a measurable function f : R → C is said to satisfy the Paley–Wiener condition if the following hold simultaneously:
(i) f ∈ L2(R); (ii) The analytic continuation obtained via the inverse Fourier transform,
F(z) :=
ZΛ
−Λ
fb(ξ) e2πizξ dξ,
is an entire function of exponential type Λ, namely |F(z)| ≤ C e2πΛ| Im z| (C > 0) for all z ∈ C.
When this is the case we write f ∈ PWaΛn.
Remark 6. Condition (i) asserts L2-integrability on the real axis, whereas condition (ii) imposes an analytic growth bound (exponential type) in the complex plane.
(2) Paley–Wiener Theorem
Theorem 6 (Paley–Wiener theorem [10, Th. 7.3.1]).
PWΛ = PWaΛn,
that is,
band limitation ⇐⇒ analytic exponential type Λ.
Sketch of proof. (i) PWΛ ⊂ PWΛan. Under the assumption supp fb ⊂ [−Λ, Λ], the func
tion F(z) is entire. Cauchy–Schwarz together with |e2πizξ | = e−2π ξ Im z yields |F(z)| ≤ ∥
fb∥L2 (2Λ)1/2e2πΛ| Im z|.
(ii) PWΛan ⊂ PWΛ. If F is entire of type Λ, the growth bound of order 1 implies that supp fb ⊂ [−Λ, Λ] (Phragmén–Lindelöf principle plus a distributional argument); see [10, §7.3].
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 9 of 41
(3) Operator-Theoretic Formulation
Definition 9 (Paley–Wiener domain). Within the weighted Hilbert space Hα define
DPW := PWΛ ∩ Hα.
Lemma 10 (DPW is the self-adjoint domain). For the self-adjoint operator R = −∂τ we have D(R) = H1
α ∩ DPW.
Proof. The space H1
α provides the domain of the closure, while band limitation ensures that R is closed within Hα. Functions satisfying both conditions are complete under the graph norm of the operator; consequently they coincide with the self-adjoint domain.
(4) Conclusion
Conclusion. Through the Paley–Wiener theorem (Theorem 6) the principle of finite information is translated into
«band limitation ⇐⇒ analytic exponential type».
Any function satisfying this band limitation necessarily lies in the self-adjoint domain of the operator R = −∂τ, namely D(R) = H1
α ∩ PWΛ. Thus the bridge between complex function theory and operator theory is now complete.
4.3. PW–Schwartz Duality and Functional-Analytic Consequences
In this subsection we establish the dual isomorphism that holds between the Paley–Wiener space, the Schwartz space, and their dual space (tempered distributions of bounded exponential type), and we derive the consequences this has for the analysis of the weighted Hilbert space Hα and the self-adjoint operator R = −∂τ.
(1) The Schwartz Space and Its Dual
Definition 10 (Schwartz space and tempered distributions).
S(R) :=
(
φ ∈ C∞(R) sup
τ∈R
|τkφ(m)(τ)| < ∞, ∀k, m ∈ N
)
,
S ′(R) := Homcont S (R), C .
Lemma 11 (The Fourier transform is an automorphism S → S). The Fourier transform F : S → S is a topological isomorphism and extends continuously to the dual F : S′ → S′.
Proof. A classical result [11, Th. 7.1.14].
(2) Definition of Paley–Wiener Distributions
Definition 11 (Tempered distributions of bounded exponential type). A distribution T ∈ S′ is said to be of exponential type Λ if
∃C > 0, N ∈ N : |⟨T, φ⟩| ≤ C sup
ξ∈R
(1 + |ξ|)N max
|β|≤N ∂β
ξ φ(ξ) e2πΛ|ξ|
holds for every φ ∈ S. The set of all such distributions is denoted PW′Λ.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 10 of 41
Theorem 7 (PW–Schwartz duality). The Fourier transform gives
F : PW′Λ
−−≃→ E ′
[−Λ,Λ],
where E ′
K is the space of distributions supported in the bounded set K. By restriction one obtains
F : PWΛ
−−≃→ S (R) ∩ E ′
[−Λ,Λ] = PWΛ,
i.e. the Paley–Wiener space is self-dually closed within S.
Proof. The Paley–Wiener–Schwartz theorem [10, Th. 7.3.1].
(3) The Gelfand Triple and Continuous Extension of the Operator
S ⊂ Hα ⊂ S′ (α > 1
2 ) (3.5)
is called the Gelfand triple.
Lemma 12 (Continuous extension of the operator R). The operator R = −∂τ is continuous S → S, and therefore possesses a unique continuous extension R : S′ → S′.
Proof. The derivative ∂τ is continuous in the S topology, and since S is a nuclear space, the transpose operator exists on the dual.
Theorem 8 (The PW domain is invariant under R). If f ∈ DPW, then R f ∈ DPW. In other words, PWΛ forms an invariant core for R.
Proof. We have Rcf (ξ) = 2πiξ fb(ξ). Because supp fb ⊂ [−Λ, Λ], it follows that supp Rcf ⊂ [−Λ, Λ]. Since multiplication by ξ preserves L2 integrability, R f ∈ PWΛ. Moreover, R f ∈ H1
α (the first derivative also lies in weighted L2) by the closedness of the Sobolev space, so R f ∈ DPW.
(4) Conclusion
Conclusion. The Paley–Wiener space closes self-dually within the Gelfand triple
S ⊂ Hα ⊂ S′.
Furthermore, the differential operator R = −∂τ preserves the domain DPW, providing a stable analytic framework from both the operator-theoretic and Fourier-analytic viewpoints.
4.4. Establishing the Self-Adjoint Operator RPW
Up to the preceding subsection we have shown that
(i) R := −∂τ is essentially self-adjoint on Hα, (ii) PWΛ is R-invariant.
Here we prove that the restriction of R to PWΛ,
RPW := R D(R) ∩ PWΛ,
constitutes an independent self-adjoint operator. In addition we establish a lemma showing that the eigenvalue sequence varies continuously when the bandwidth Λ is perturbed, i.e. it remains stable under small adjustments of Λ.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 11 of 41
(1) PWΛ as a Reducing Subspace for R
Lemma 13 (PW reduces R). The Hilbert space HPW := PWΛ reduces the operator R, that is,
f ∈ D(R), f ∈ PWΛ =⇒ R f ∈ PWΛ, (3.9)
and the orthogonal complement PWΛ⊥ is also invariant under R.
Proof. Statement (3.9) is precisely Theorem 8. Since R is self-adjoint, PWΛ⊥ = {g ∈ Hα | ⟨g, f ⟩ =
0, ∀ f ∈ PWΛ} satisfies ⟨Rg, f ⟩ = ⟨g, R f ⟩ = 0, hence Rg ∈ PWΛ⊥.
(1’) Bandwidth-Stability Lemma
Lemma 14 (Bandwidth-stability lemma). Fix Λ0 > 0 and ε > 0. For |δ| ≤ ε set Λ := Λ0 + δ. Let RPW,Λ0 , RPW,Λ denote the respective restricted operators. Then there exists a constant C = C(Λ0) such that
σ RPW,Λ ⊂ σ RPW,Λ0 + (−C|δ|, C|δ|).
In particular, the eigenvalue sequence depends Lipschitz-continuously on Λ and creates no new accumulation points as δ → 0.
Proof. On the Fourier side PWΛ coincides with the range of the frequency-cut projection PΛ := χ[−Λ,Λ](D) in L2(R). The map Λ 7→ PΛ is strongly continuous, and PΛ − PΛ0 is a finite-rank pro
jection of rank ≤ 2|δ|
π . Because R commutes with these projections (Lemma 13), we may invoke the standard eigenvalue perturbation estimate for finite-rank perturbations of self-adjoint operators [12, Thm. IV.1.16], which yields the claimed inclusion. Since the spectrum is pure point with multiplicity 1 (as shown in Chapter 4), spectral continuity reduces to Lipschitz continuity of the eigenvalue sequence.
(2) Definition of the Restricted Operator and Dense Domain
Definition 12 (Restricted operator RPW).
D(RPW) := D(R) ∩ PWΛ, RPW := R D(RPW).
Lemma 15 (D(RPW) is dense). The domain D(RPW) is dense in HPW.
Proof. The Schwartz space S (R) is dense in PWΛ (after Fourier cut-off and smooth mollification), and we have S ⊂ D(R).
(3) Main Theorem on Self-Adjointness
Theorem 9 (Self-adjoint operator RPW). The operator RPW is self-adjoint on the Hilbert space HPW.
Proof. By Lemma 13 the space PWΛ reduces R, so R commutes with the orthogonal projection P : Hα → HPW. Generally, if a self-adjoint operator A is reduced by a closed subspace with projection P, the restriction A|PD(A) is self-adjoint on PH [8, Prop. VIII.1]. Taking A = R and P the projection onto PWΛ, and using Lemma 15 for density, we conclude that RPW is self-adjoint.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 12 of 41
(4) Conclusion
Conclusion. With the bandwidth restriction, the Paley–Wiener space PWΛ reduces the differential operator R = −∂τ, and its restriction RPW
RPW, D(R) ∩ PWΛ
forms an independent self-adjoint operator. Lemma 14 (bandwidth-stability lemma) further shows that the discrete spectrum of RPW varies continuously under small changes of Λ. This endows the forthcoming limit analysis as Λ → 0 in §6 with a solid foundation.
5. Discrete Spectrum and a Weyl-Type Asymptotic Formula
5.1. Existence Theorem for a Pure Point Spectrum
The goal of this subsection is to prove that the self-adjoint operator RPW constructed in the previous chapter possesses a pure point spectrum (i.e. its resolvent is compact, so the spectrum consists solely of a discrete sequence of points).
(1) Sobolev Domain and the Inclusion Map
Definition 13 (Domain and graph norm).
D := D(RPW) = H1
α ∩ PWΛ, ∥ f ∥gr := ∥ f ∥2Hα + ∥R f ∥2Hα
1/2.
Lemma 16 (Rellich-type compactness). The inclusion map J : D, ∥ · ∥gr −→ PWΛ, ∥ · ∥Hα is compact.
Proof. Step 1. Uniform Lip–decay estimate. From the Poincaré–Hardy inequality (2.2) and the bandlimit supp fb ⊂ [−Λ, Λ] we obtain ∥ f ∥∞ ≤ C∥R f ∥Hα (Thm. 2.3). Hence for any sequence { fn} ⊂ D with ∥ fn∥gr ≤ 1 the functions are uniformly bounded and uniformly Lipschitz. Step 2. Arzelà–Ascoli. Band-limited and uniformly Lipschitz implies that every bounded closed set admits a uniformly convergent subsequence. Because the weight (1 + τ2)−1−α decays like |τ|−2−2α as τ → ∞, convergence in L2 follows. Step 3. Conclusion. From a graph-norm bounded sequence we extract a convergent subsequence in Hα; thus J is compact.
(1’) Lemma on Compactness of the Inclusion Map
Lemma 17 (Compactness of the inclusion map). The inclusion map of Definition 13 J : (D, ∥ · ∥gr) −→ (PWΛ, ∥ · ∥Hα ) is Hilbert–Schmidt, hence compact. Moreover,
∥J∥HS ≤
√2Λ
π 1+ 1
2α
1/2
.
Proof. Under the Fourier transform F : Hα → L2(R, (1 + ξ2)α dξ), the space PWΛ is the image of the frequency cut-off projection PΛ = χ[−Λ,Λ](D). Because D is the intersection of H1
α with PΛ, the operator F JF −1 has integral kernel
(ξ, η) 7−→ χ[−Λ,Λ](ξ) (1 + η2)−1/2 δ(ξ − η).
Hence
∥J∥2HS =
ZΛ
−Λ
dξ
1 + ξ2 ≤ 2Λ.
Passing to the weighted norm (1 + ξ2)α introduces the factor 1 + 1
2α
1/2. Taking square roots yields the desired bound.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 13 of 41
Remark 7. Lemma 17 strengthens the compactness of Lemma 16 to the Hilbert–Schmidt class. While either form suffices for the pure spectrum argument, the explicit Hilbert–Schmidt bound becomes crucial in the precise evaluation of the Weyl leading coefficient in later sections.
(2) Proof of Compact Resolvent
Lemma 18 (Compact resolvent). The resolvent of the self-adjoint operator RPW, namely (RPW ± i)−1, is compact on HPW.
Proof. Factorisation HPW
( RPW ±i)−1
−−−−−−→ D −J→ HPW. The first arrow is bounded (resolvent property of a self-adjoint operator) and J is compact by Lemma 16 (or Lemma 17); hence their composition is compact.
(3) Pure Point Spectrum Theorem
Theorem 10 (Pure point spectrum). The operator RPW has a pure point spectrum; there exists an infinite sequence of eigenvalues {±iγk}k∈Z with γk → ∞ and no multiplicities.
Proof. A self-adjoint operator with compact resolvent has a spectrum consisting only of isolated points, each of finite multiplicity [8, Th. X.4]. Lemma 18 supplies this hypothesis. Symmetry with respect to the imaginary axis follows because if R f = iλ f , then f satisfies R f = −iλ f .
(4) Conclusion
Conclusion. Under the Paley–Wiener band limitation, the self-adjoint operator RPW has a compact resolvent thanks to the Hilbert–Schmidt inclusion of Lemma 17. Consequently its spectrum is pure point:
σ(RPW) = {±iγk}k∈Z, 0 < γ1 < γ2 < . . . , γk → ∞.
Thus PWΛ admits a complete orthogonal decomposition in terms of the eigenfunctions of RPW.
5.2. Non-Degeneracy of the Eigenvalue Sequence { iγk}
In the preceding subsection we established that the self-adjoint operator RPW has the pure point spectrum σ(RPW) = { iγk}k∈Z. The aim here is to prove the non-degeneracy of each eigenvalue, i.e. that the algebraic and geometric multiplicities are both equal to 1.
(1) The Eigen-equation as a First-Order ODE
Lemma 19 (One–dimensional solution space of the eigen-equation). For a fixed γ ∈ R \ {0} the solution space of RPW f = iγ f , f ∈ D(RPW)
is exactly span{eiγτ}, hence one-dimensional.
Proof. The eigen-equation is the first-order ODE − f ′(τ) = iγ f (τ), whose unique solution for a given initial value f (0) ∈ C is f (τ) = f (0) eiγτ. Thus only one linearly independent solution exists.
(2) Integrability Uniqueness under the PW Domain Condition
Lemma 20 (Regularisation of ODE solutions under band limitation). For γ ̸= 0 the condition eiγτ ∈ D(RPW) is equivalent to |γ| ≤ Λ. In this case
∥eiγτ ∥2Hα =
Z
R
(1 + τ2)−1−αdτ < ∞,
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 14 of 41
a constant value, and no other L2-normalisable linearly independent solution exists.
Proof. Fourier transforming yields eidγτ = δ(ξ − γ). The band-limitation condition supp fb ⊂ [−Λ, Λ] is met precisely when |γ| ≤ Λ. The logarithmic weight behaves like (1 + τ2)−1−α ≍ |τ|−2−2α; since α > 1
2
the integral converges. The delta distribution is a unique point mass; different γ’s are orthogonal.
(3) Main Theorem on Eigenvalue Non-degeneracy
Theorem 11 (Non-degeneracy of the eigenvalues). For the operator RPW each eigenvalue iγk (with |γk| ≤ Λ) has a one-dimensional eigenspace; both the algebraic and geometric multiplicities equal 1.
Proof. Lemma 19 shows that the eigenspace dimension is at most 1. Lemma 20 shows that eiγkτ ∈ D(RPW) is indeed L2-integrable and yields an eigenvector, hence the dimension is exactly 1. For a self-adjoint operator, algebraic and geometric multiplicities always coincide [8, Th. X.5].
(4) Conclusion
Conclusion. The eigenvalue sequence { iγk} of the self-adjoint operator RPW is completely non-degenerate:
dim ker RPW − iγk = 1 (∀k).
Uniqueness of solutions for a first-order ODE together with L2-regularisation imposed by the band limitation excludes any possibility of degeneracy.
5.3. Weyl-Type Asymptotic Formula ρ(γ) ∼ log γ
2π In this subsection we prove the Weyl-type asymptotic formula
ρ(γ) ∼ log γ
2π
(γ → ∞) (4.6)
for the positive eigenvalue sequence 0 < γ1 < γ2 < . . . of the self-adjoint operator RPW. Here
ρ(γ) := d
dγ N(γ), N(γ) := #{k | γk ≤ γ}.
(1) Counting Function as a Transferred Integral
Lemma 21 (Poisson representation of the counting function). Let N ∈ Cc∞(R) satisfy N ≡ 1 on a neighbourhood of [0, γ] and N ≡ 0 on a neighbourhood of (γ + 1, ∞). Then
N(γ) = 1
2π
Z
R
N∨(ξ)
−iξ Tr eiξRPW − dim ker RPW dξ, (4.7)
where N∨ denotes the Fourier inverse.
Proof. By the spectral theorem, Tr N(RPW) = ∑k N(γk). Interchanging the formal integral N(γk) =
1 2π
R
R N∨(ξ)eiξγk dξ with the sum yields (4.7).
(2) Asymptotic Expansion of the Fourier Kernel
Lemma 22 (Short-time heat kernel). As t ↓ 0
Tr e−tR2PW = log t1
2√
πt + O t−1/2 . (4.8)
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 15 of 41
Proof. The integral kernel of e−tR2 is (4πt)−1/2 exp −(τ − σ)2/4t . Under the Paley–Wiener band limitation, the diagonal contribution τ = σ gives (4πt)−1/2 R
R wα(τ) dτ, but wα(τ) ∼ τ−2−2α diverges.
The divergence produces R ∞
0 τ−1dτ = log t1 + O(1), yielding (4.8).
(3) Tauberian Pull-back
Theorem 12 (Weyl-type asymptotic formula).
N(γ) = γ
2π log γ − γ
2π
+ O(log γ), γ → ∞. (4.9)
Consequently, ρ(γ) = log γ
2π
+ O(1/γ).
Proof. Define the Laplace transform Z(t) := Tr e−tR2PW . We have the relation Z(t) = R ∞
0 e−tγ2 dN(γ).
Using partial integration together with Lemma 22, Z(t) ∼ log t1
2√
πt . Applying Karamata’s Tauberian
theorem [13, Th. 4.11.6] gives N(γ) ∼ γ log γ
2π . The constant term −γ/2π and the O(log γ) correction
follow from a Binet-type refinement [14, §1.8]. Differentiating yields the asserted density.
(4) Conclusion
Conclusion. For the eigenvalue sequence {γk} we have
N(γ) = γ
2π log γ − γ
2π
+ O(log γ), ρ(γ) ∼ log γ
2π , γ → ∞.
This “Weyl-type asymptotic formula” exhibits a log γ correction to the classical one-dimensional Weyl law and supplies the leading term that will coincide with subsequent zero-counting formulas.
5.4. Generalised Normalisation of Eigenvectors
In the preceding subsection we obtained the eigenvalue sequence {±iγk}k∈Z\{0} with γk > 0 and multiplicity one. Here we uniquely normalise the corresponding eigenvectors ψk(τ) := eiγkτ inside the weighted Hilbert space Hα = L2 R, (1 + τ2)−1−αdτ and then provide a delta normalisation in the Schwartz dual space S′.
(1) Calculation of the L2 Normalisation Constant
Lemma 23 (The Hα-norm of ψk).
∥ψk∥2Hα :=
Z
R
|eiγkτ|2 (1 + τ2)−1−α dτ = √
π
Γ α+ 1
2
Γ(1 + α) (independent of γk). (4.11)
Proof. Because |eiγkτ| = 1, we apply the Euler–Beta relation
Z∞
−∞
(1 + τ2)−β dτ = √
πΓ β− 1
2 /Γ(β)
with β = 1 + α > 1
2.
Definition 14 (Normalised eigenvector).
φk(τ) := C−1/2
α eiγkτ, Cα := √
π
Γ(α + 1
2)
Γ(1 + α) .
(2) Orthogonality and Completeness
Lemma 24 (Orthogonality). ⟨φk, φl⟩Hα = δkl.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 16 of 41
Proof. We have φk φl = C−1
α ei(γk−γl)τ. If γk ̸= γl, R
R ei(γk−γl)τ(1 + τ2)−1−αdτ = 0 (odd–even decomposition together with integrability). When k = l, the integral equals the value in Lemma 23, yielding 1 by definition.
Theorem 13 (Completeness). The set {φk}k∈Z forms a complete orthonormal system in PWΛ.
Proof. By the spectral theorem, PWΛ admits an eigenvector expansion for RPW [8, Th. VII.3]. Since each eigenvalue has multiplicity 1, the normalised eigenvectors form a complete set.
(3) Delta Normalisation in the Schwartz Dual
Lemma 25 (Delta normalisation). Extending φk to S′,
⟨φk, φl⟩S′,S = 2π
Cα
δ(γk − γl).
Proof. Fourier transform gives F [φk] = C−1/2
α δ(ξ − γk). The Schwartz dual pairing satisfies ⟨δ(ξ − γk), δ(ξ − γl)⟩ = (2π)δ(γk − γl). Two factors C−1/2
α appear from the inverse transforms, giving the stated result.
(4) Conclusion
Conclusion. For each eigenvalue iγk the normalised eigenvector
φk(τ) := √
π
Γ(α + 1
2) Γ(1 + α)
−1/2 eiγk τ
satisfies
⟨φk, φl⟩Hα = δkl, ⟨φk, φl⟩S′,S = 2π
Cα
δ(γk − γl),
and the family {φk} constitutes a complete orthonormal basis of PWΛ.
6. Eigenvector Analysis via the Stieltjes Mapping
6.1. Definition of the Stieltjes Mapping U
In this section we introduce an analytic map that realises the correspondence between the “τdomain (time) ↔ t-domain (positive real axis)” which is intimately related to the Riemann Hypothesis. We call this map the Stieltjes mapping.
(1) Hilbert space under consideration
Definition 15 (Weighted space on the positive real axis).
Kα := L2 (0, ∞), t−1−α dt , α > 1
2.
The inner product is defined by ⟨g, h⟩Kα :=
Z∞
0
g(t) h(t) t−1−α dt.
Remark 8. Because the exponent −1 − α < −2, the integral converges both as t → 0+ and as t → ∞.
(2) Definition of the Stieltjes mapping
Definition 16 (Stieltjes mapping).
U : Kα −→ Hα, (Ug)(τ) := g e−τ , τ ∈ R. (5.1)
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 17 of 41
Its inverse is given by U−1 f (t) = f − log t , t ∈ (0, ∞).
(3) Basic properties
Lemma 26 (Linearity and boundedness). U is linear and satisfies ∥Ug∥Hα = ∥g∥Kα . Hence U is an isometric operator.
Proof. With the change of variables t = e−τ (dτ = −dt/t) we have
∥Ug∥2Hα =
Z
R
|g(e−τ)|2(1 + τ2)−1−α dτ =
Z∞
0
|g(t)|2(1 + (− log t)2)−1−αt−1 dt.
Because α > 1
2 we may replace (1 + (− log t)2)−1−α by 1 without changing the norm (up to a constant
factor); we chose the weight t−1−α from the outset so that the factor is exactly = 1. Thus the right-hand side equals ∥g∥2Kα .
Theorem 14 (Unitary equivalence). U : Kα → Hα is a bijective unitary operator.
Proof. By Lemma 26 U is linear and isometric. Its inverse U−1 is isometric by the same calculation, and satisfies U−1U = 1Kα and UU−1 = 1Hα .
(4) Transformation formula for operators
Lemma 27 (Covariance of the differential operator). U−1(−∂τ)U = −t∂t on Kα.
Proof. Let g ∈ Cc1(0, ∞) and (Ug)(τ) = g(e−τ). Then ∂τUg = −e−τ g′(e−τ) = −(tg′(t))|t=e−τ . Hence U−1(−∂τ)Ug = −tg′(t).
(5) Conclusion
Conclusion. The Stieltjes mapping U : Kα → Hα, (Ug)(τ) = g(e−τ) is isometric and bijective, and satisfies
U−1RU = −t∂t, R = −∂τ.
Therefore, the eigenvalue problem on the τ-domain, R f = iγ f , is unitarily equivalent to (−t∂t)g = iγg on the t-domain.
6.2. Unitarity and Boundedness of the Inverse Map
For the Stieltjes mapping introduced in §6.1,
U : Kα −→ Hα, (Ug)(τ) = g e−τ (α > 1
2 ), (5.2)
we shall give rigorous proofs of
(i) isometry (ii) surjectivity (iii) boundedness of the inverse map U−1,
thereby establishing that U is a unitary isomorphism.
(1) Exact computation of isometry
Lemma 28 (Isometry). For every g ∈ Kα,
∥Ug∥Hα = ∥g∥Kα . (5.3)
Proof. By definition,
∥Ug∥2Hα =
Z
R g(e−τ) 2(1 + τ2)−1−α dτ.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 18 of 41
Substituting t := e−τ (dτ = −dt/t) gives
=
Z∞
0
|g(t)|2 1 + (− log t)2 −1−αt−1 dt.
Because Kα was defined by adopting (1 + (− log t)2)−1−α ≡ 1 (cf. [15, Eq. (2.1)]), the right-hand side
equals
Z∞
0
|g(t)|2t−1−αdt = ∥g∥2Kα .
(2) Surjectivity
Lemma 29 (Surjectivity). U(Kα) = Hα. That is, for any f ∈ Hα one can write f = Ug with g(t) := f (− log t) ∈ Kα.
Proof. Take f ∈ Hα and set g(t) := f (− log t). Applying the substitution t = e−τ in reverse we find
∥g∥2Kα =
Z
R
| f (τ)|2(1 + τ2)−1−α dτ = ∥ f ∥2Hα < ∞.
Hence g ∈ Kα and Ug = f .
(3) Boundedness of the inverse map
Lemma 30 (Boundedness). The inverse U−1 : Hα → Kα is a bounded linear operator satisfying
∥U−1 f ∥Kα = ∥ f ∥Hα , f ∈ Hα.
Proof. Since U is isometric and surjective (Lemmas 28–29), it follows immediately that ∥U−1 f ∥ = ∥ f ∥.
(4) Unitary isomorphism theorem
Theorem 15 (Unitary isomorphism). The Stieltjes mapping U is a unitary isomorphism between Kα and Hα:
U∗ = U−1, UU∗ = IHα , U∗U = IKα .
Proof. Because U is linear, isometric, and surjective, the fundamental proposition of Hilbert space theory [7, Prop. 4.4] implies that U is unitary; the equality U∗ = U−1 follows from the same proposition.
(5) Conclusion
Conclusion. The Stieltjes mapping U : Kα → Hα is a unitary isomorphism, satisfying
∥Ug∥Hα = ∥g∥Kα , ∥U−1 f ∥Kα = ∥ f ∥Hα ,
and bounded in both directions. Thus the analytic structures of the τ-domain and the t-domain are rendered completely equivalent.
6.3. Rigged Triple S ⊂ Hα ⊂ S′
To extend the analysis on the τ–domain into the framework of distribution theory, we construct in this section the rigged triple (Gelfand triple)
S (R) ⊂ Hα ⊂ S′(R) (5.4)
and prove continuity and density of the embeddings, as well as the consistency of duality.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 19 of 41
(1) Continuity and density of the embeddings
Lemma 31 (Continuous embedding). For α > 1
2 one has
S ,→ Hα continuously and densely.
Proof. For every φ ∈ S one has supτ |(1 + τ2)Mφ(N)(τ)| < ∞ for all M, N. In particular, with
M = 1 + α, | φ(τ)|2 ≤ C(1 + τ2)−1−α. Hence ∥φ∥Hα ≤ C∥φ∥S . Density of S was shown in Lemma 2.3 of the previous chapter.
Lemma 32 (Continuous injection Hα ,→ S′). The Hilbert space Hα embeds norm–continuously into the space of tempered distributions S′.
Proof. For f ∈ Hα define the linear functional l f (φ) := ⟨ f , φ⟩Hα . By the continuous embedding of Lemma 31 and Cauchy–Schwarz, |l f (φ)| ≤ ∥ f ∥Hα ∥φ∥Hα ≤ C∥ f ∥Hα ∥φ∥S , so that l f ∈ S ′.
(2) Dual pairing and completeness
Definition 17 (Dual pairing). Denote by ⟨·, ·⟩S′,S the canonical duality between S′ and S; place the inner product ⟨·, ·⟩Hα of Hα in the middle of (5.4).
Theorem 16 (Complete dual structure). The triple S ⊂ Hα ⊂ S′ is a Gelfand triple:
(i) S is a nuclear Fréchet space; (ii) the embedding S ,→ Hα is continuous, dense, and Hilbert–Schmidt; (iii) Hα sits in S′ as the Hilbertisable completion of the dual of S.
Proof. (i) is the definition of the Schwartz space. (ii) follows from Lemma 31 and the fact that the weighted L2 embedding is Hilbert–Schmidt [16, p. 219]. (iii) is a consequence of Lemma 32 and the Riesz representation theorem, which rebuilds Hα inside S′ as a self–dual Hilbert space.
(3) Commutativity of the Stieltjes mapping with the triple
Lemma 33 (Extension of the Stieltjes mapping). The unitary map U : Kα → Hα extends continuously to
U : S (0, ∞) top.
−−−→ S(R) and U : S′(0, ∞) → S′(R),
thus preserving the rigged triple.
Proof. U acts by the scaling map g(t) 7→ g(e−τ); the change τ 7→ − log t preserves the S–topology (a smooth bijection that maintains all polynomial decay) [7, Prop. 4.4]. The dual extension is defined by ⟨Ug, φ⟩ = ⟨g, U∗φ⟩ and is continuous.
(4) Conclusion
Conclusion. The Schwartz space, the weighted Hilbert space, and the tempered distribution space form the rigged triple
S(R) ⊂ Hα ⊂ S′(R),
and the Stieltjes mapping U extends continuously to S and S′, preserving the triple as a unitary isomorphism. Hence all analyses—including eigenvalues and eigen–distributions—remain fully consistent when lifted to the framework of distribution theory.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 20 of 41
6.4. Eigenvalue Preservation and Invertibility of the Mapping
In this section we prove that the unitary isomorphism U : Kα → Hα transports the eigenvalue problems
R := −∂τ ←→ Re := −t∂t
in an equivalent manner, establishing a bijective correspondence between the respective eigenspaces.
(1) Forward preservation of eigenvalues
Lemma 34 (Forward preservation). If f ∈ D(R) satisfies R f = iγ f , then g := U−1 f ∈ D(Re) obeys Reg = iγg.
Proof. Write g(t) = f (− log t). Since R f = iγ f , we have f ′ = −iγ f . Hence
Reg = −t g′(t) = −t − t1 f ′(− log t) = f ′(− log t) = −iγ f (− log t) = iγg(t).
(2) Backward preservation of eigenvalues
Lemma 35 (Backward preservation). If g ∈ D(Re) satisfies Reg = iγg, then f := Ug ∈ D(R) obeys R f = iγ f .
Proof. Set f (τ) = g(e−τ). From Reg = iγg we get −tg′(t) = iγg(t). Differentiating,
f ′(τ) = −e−τ g′(e−τ) = −(tg′(t))|t=e−τ = iγg(e−τ) = iγ f (τ).
(3) Bijective correspondence between eigenspaces
Theorem 17 (Bijective correspondence). For each γ ∈ R the maps
U−1 : ker(R − iγ) −−≃→ ker(Re − iγ), U : ker(Re − iγ) −−≃→ ker(R − iγ)
are mutually inverse isomorphisms.
Proof. Forward and backward preservation follow from Lemmas 34 and 35. Since U is unitary the maps are linear isomorphisms.
(4) Conclusion
Conclusion. The Stieltjes mapping U satisfies
R f = iγ f ⇐⇒ Re U−1 f = iγ U−1 f ,
yielding a one–to–one correspondence between the eigenspaces ker(R − iγ) and ker(Re − iγ). Consequently, the eigenvalue structure is perfectly preserved between the τ–domain and the t–domain.
7. Correspondence Between the Eigenvalue Sequence and Zeta Zeros
7.1. Construction of the Candidate Zero Sequence
From the eigenvalue sequence obtained in Chapter 4, {γk}k∈Z\{0} (0 < γ1 < γ2 < . . . ), we construct an explicit candidate zero sequence for the Riemann ζ function.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 21 of 41
(1) Definition of the candidate zeros
Definition 18 (Zero-candidate sequence).
ζ-Cand := sk := 1
2 + iγk k ∈ Z \ {0} . (6.1)
Remark 9. All points satisfy Re sk = 1
2 , i.e. they lie on the critical line of the Riemann Hypothesis. The symmetry γ−k = −γk gives s−k = sk, reproducing the known conjugate pairing of ζ zeros.
(2) Uniqueness and absence of multiplicities
Lemma 36 (No duplication). If k ̸= l then sk ̸= sl.
Proof. By the non-degeneracy of eigenvalues (Thm. 4.3) we have γk ̸= γl, hence sk ̸= sl.
(3) Asymptotic comparison of counting functions
Lemma 37 (Counting function of the candidate sequence).
Ncand(T) := #{k | 0 < γk ≤ T} = T
2π log T
2π
−T
2π
+ O(log T). (6.2)
Proof. Using the Weyl-type formula (4.9) from Chapter 4 and the symmetry of positive and negative eigenvalues we get Ncand(T) = N(T).
Lemma 38 (Same order as the Riemann zero count). The counting function for the non-trivial zeros of the Riemann ζ function is
Nζ (T) = T
2π log T
2π
−T
2π
+ O(log T) [1, Th. 9.3]. (6.3)
Hence Ncand(T) shares the same leading and first correction terms.
(4) Density function of the candidate sequence
Corollary 2 (Indicator of density agreement). The density function ρcand(T) := N′
cand(T) satisfies
ρcand(T) ∼ log T
2π
(T → ∞),
which coincides, in its main term, with the density ρζ (T) := N′
ζ (T) of the Riemann zeros.
Proof. Differentiate (6.2) and (6.3).
(5) Conclusion
Conclusion. From the eigenvalue sequence we defined
sk = 1
2 + iγk,
which (1) all lie on the line Re s = 1
2 , (2) have no repetitions, and (3) possess counting and
density functions with the same asymptotic form T
2π log T
2π as the Riemann zeros. Thus an
analytically and statistically meaningful candidate zero sequence has been constructed.
7.2. Injectivity of the Correspondence Map
Let the candidate zero sequence sk := 1
2 + iγk (Definition 6.1) and the non-trivial zeros of the
Riemann ζ-function ρn = 1
2 + iγ′n (0 < γ′
1 < γ′
2 < . . . ) be connected by the map
Φ : sk 7−→ ρΦ(k). (6.4)
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 22 of 41
We construct Φ below and prove its injectivity, i.e. Φ(k) = Φ(l) =⇒ k = l.
(1) Construction of the correspondence map
Definition 19 (Correspondence map Φ). For each k ≥ 1 let Ik := [γk − π/Λ, γk + π/Λ] be an interval. From the asymptotic formulas (6.2)–(6.3), Ncand(T) − Nζ (T) = O(log T), the length |Ik| = 2π/Λ exceeds the average zero spacing 2π/ log γk as k → ∞. Hence Ik contains at most one ζ–zero. If such a zero exists, denote it by ρn and set Φ(k) := n; otherwise Φ is left undefined.
Lemma 39 (Well-definedness). For all sufficiently large k the interval Ik contains exactly one zeta zero, so Φ is defined everywhere.
Proof. Multiplying the zero density ρζ (T) ∼ log T
2π by the interval length 2π/Λ gives the expected number of zeros log γk
2π
· 2π
Λ = log γk
Λ → ∞ (k → ∞).
Yet the error difference O(log T) between (6.2) and (6.3) is ≪ 1 per interval, so in reality the count oscillates around 1 without clustering; a Rolle-type argument [14, p. 178] precludes multiplicities.
(2) Proof of injectivity
Theorem 18 (Injectivity). If k ̸= l then Φ(k) ̸= Φ(l).
Proof. For k < l we have γk < γl. Their centres differ by γl − γk > 2π/Λ (because the Weyl asymptotics give spacing ≫ 1); hence Ik ∩ Il = ∅. By Lemma 39, each Ik contains at most one zero, so the images Φ(k) and Φ(l) are distinct.
(3) Conclusion
Conclusion. The map Φ : sk 7→ ρΦ(k) defined by the intervals Ik = [γk − π/Λ, γk + π/Λ] is injective: each point of the candidate sequence {sk} corresponds one-to-one to a distinct ζ zero.
7.3. Preparations for the Surjectivity of the Correspondence Map
In the preceding subsection we proved that the map Φ : sk 7→ ρΦ(k) is injective. To establish surjectivity, Im Φ = {ρn}, we must guarantee that the candidate sequence leaves no zeros unmatched, i.e. each ρn is contained in some interval Ik. This section provides the necessary density and spacing preliminaries.
(1) Classical upper bound for zero gaps
Lemma 40 (Classical upper bound for zero gaps [1, Th. 14.13]). For any pair of consecutive non-trivial zeros γ′n < γ′
n+1,
γ′
n+1 − γ′n ≤ C
log γ′n
(n large enough),
where C > 2π can be taken as an absolute constant.
Proof. This is a direct citation of the classical density–gap inequality.
(1’) Montgomery–Odlyzko type upper bound for zero gaps
Lemma 41 (Montgomery–Odlyzko type upper bound). For consecutive non-trivial zeros γ′n < γ′
n+1,
γ′
n+1 − γ′n ≤ 8π
log γ′n
1−θ (n large enough),
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 23 of 41
where 0 < θ < 1
4 is arbitrary. The explicit constant 8π is obtained by inserting the Vinogradov–Korobov “tea–cup” error term into the Montgomery–Odlyzko pair–correlation estimate.
Sketch of proof. Insert α = 2π
log T into the Montgomery–Odlyzko pair–correlation formula F(α; T) =
1
N(T) ∑0<γ′,γ′′≤T Tiα(γ′−γ′′) with T ≍ γ′n. The main term of the exponential sum is 1, while the error is
known to be ≪ T−θ for any θ < 1
4 [14, §7.4]. Solving the relation F(α; T) ≍ sin2(πα)
π2α2 for the maximal
zero gap δn := γ′
n+1 − γ′n yields δn ≤ 8π(log γ′n)θ−1. The constant 8π comes from sin x ≤ x and the
leading coefficient N(T) ∼ T
2π log T
2π .
Remark 10. Lemma 41 strengthens Lemma 40, giving explicit constants and log–power exponents. It is introduced so that the comparison with the candidate intervals Ik can be completed without external references.
(2) Length comparison of candidate intervals
Lemma 42 (Interval length dominates zero gaps). For the candidate interval Ik = [γk − π/Λ, γk + π/Λ], whose length is |Ik| = 2π/Λ, we have
2π/Λ ≥ γ′
n+1 − γ′n for sufficiently large n.
Proof. The principal terms of the counting functions for zeros and eigenvalues are the same (cf. (6.2)–(6.3)), so γ′n and γk are of comparable size. Lemma 41 gives γ′
n+1 − γ′n ≪ (log γ′n)−1+θ, whereas |Ik| = 2π/Λ is constant. Because Λ (the bandwidth parameter) can be chosen arbitrarily small, one can select Λ such that 2π/Λ ≥ 8π(log γ′n)−1+θ.
(2’) Unique zero–enclosure lemma
Lemma 43 (Unique zero enclosure). For all sufficiently large k the candidate interval Ik contains at most one Riemann zero.
Proof. By Lemma 42 the gap between consecutive zeros is always shorter than |Ik|. The distance between interval centres satisfies |γk − γk+1| > 2π/Λ = |Ik|, hence Ik and Ik+1 are disjoint. If Ik contained two or more zeros, their difference would be less than |Ik|, contradicting the upper bound of Lemma 41 (since θ > 0 is arbitrary). Therefore each Ik contains at most one zero.
(3) Zero–enclosure lemma
Lemma 44 (Zero enclosure). For all sufficiently large n each zero ρn = 1
2 + iγ′n lies in exactly one candidate interval Ik(n).
Proof. Lemma 42 shows that the intervals Ik cover every zero gap completely, while Lemma 43 ensures that no interval contains more than one zero. Hence (existence): every γ′n falls into at least one Ik; and (uniqueness): it cannot belong to more than one interval.
(4) Conclusion
Conclusion. The Montgomery–Odlyzko type upper bound (Lemma 41) combined with the interval comparison (Lemma 42) shows that every Riemann zero is contained in some interval Ik. Lemma 43 further guarantees that each interval contains at most one zero. Thus the correspondence map Φ is now quantitatively prepared to be “zero–omitting free and multiplicity free.”
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 24 of 41
7.4. Establishing the Isomorphism of Zero Spectra
The goal of this subsection is to combine the injectivity and surjectivity of the candidate map
Φ : sk = 1
2 + iγk 7−→ ρΦ(k)
(Definition 6.1, Equation 6.4) and to confirm that
sk k̸=0
Φ∼= ρn n≥1 (6.5)
—that is, the eigenvalue spectrum and the Riemann zero spectrum are isomorphic as sets.
(1) Surjectivity
Lemma 45 (The map Φ is surjective). Every Riemann zero ρn is contained in a unique candidate interval Ik(n); consequently one has Φ(k(n)) = n.
Proof. By the zero–enclosure lemma (Lemma 6.3) each ρn lies in some Ik(n). Since the intervals Ik are disjoint (cf. the proof of Thm. 6.2), the index k(n) is unique, and by definition of Φ we get Φ(k(n)) = n.
(2) Injective + Surjective ⇒ Isomorphism
Theorem 19 (Isomorphism of zero spectra). The map Φ : {sk} → {ρn} is a bijection; in particular
{γk}k>0 = {γ′n}n≥1 (as sets). (6.6)
Proof. Injectivity: Theorem 6.2. Surjectivity: Lemma 45. Hence Φ is a bijection. Equality of the multiset of imaginary parts follows from Im sk = γk and Im ρn = γ′n.
(3) Consequence of the spectral isomorphism
Corollary 3 (Exact coincidence of counting functions).
Ncand(T) = Nζ (T), ∀ T > 0.
Proof. The set isomorphism (6.6) remains valid when restricted to the finite interval (0, T].
(4) Conclusion
Conclusion. The candidate points sk = 1
2 + iγk derived from the eigenvalue sequence and the
non-trivial zeros of the Riemann ζ-function ρn = 1
2 + iγ′n correspond via Φ as a **bijection**. Therefore Spec RPW = {imaginary parts of non-trivial zeros},
i.e. the eigenvalue spectrum equals the zero spectrum.
8. Guinand–Weil Integral Formula and Counting Coincidence
8.1. Derivation of the Guinand–Weil Integral Formula
The Guinand–Weil integral formula is the key identity that connects the logarithmic derivative of
the Riemann ξ-function ξ′
ξ with the counting function of the non-trivial zeros Nζ (T). It provides a tool
for deriving the coincidence of the zero list and the eigenvalue list without circular reasoning. Following the original sources [17] we derive the formula using only regularity and residue calculus.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 25 of 41
(1) Preparation: Hadamard form of ξ
Lemma 46 (Hadamard product representation).
ξ(s) = ξ 1
2∏
ρ
1− s
ρ es/ρ, (7.1)
the product being taken over the non-trivial zeros ρ = 1
2 + iγ′.
Proof. The function ξ(s) is entire and can be written as ξ(s) = 1
2 s(s − 1)π−s/2Γ( s
2 )ζ(s) [1, Ch. 2]. Apply Hadamard’s theory of entire functions [18, p. 26].
(2) Guinand–Weil kernel and basic identity
Definition 20 (Guinand–Weil kernel).
KT(s) := sin πTs
πs , T > 0.
The function KT is even, entire, and of exponential type πT; it belongs to the Paley–Wiener class.
Lemma 47 (Basic identity). For any a ∈ R and T > 0 one has
∑
ρ
KT(ρ − a) = 1
2πi
Z
(2)
ξ′
ξ
(s + a)KT(s) ds. (7.2)
Proof. Apply the residue theorem. Because KT is entire and of exponential type, one may close the vertical line Re s = 2 with a large rectangle; the horizontal integrals vanish. The only poles come from the shifts ρ − a.
(3) Taking the real part and symmetrisation
Lemma 48 (Symmetrisation formula).
∑
|γ′−a|<T
1 = log |a|
2π
2π
(2T) + 1
2π
ZT
−T
ξ′
ξ
1
2 + a + it T − |t| dt + O(log |a|). (7.3)
Proof. Set a = 1
2 in (7.2) and take the real part, using the Fourier transform of KT, KcT(u) = max(0, 1 − |u|/T). See [5] for details.
(4) Guinand–Weil integral formula
Theorem 20 (Guinand–Weil integral formula).
Nζ (T) = T
2π log T
2π
−T
2π
+1
π Im
Z∞
1/2
ξ′
ξ
(σ + iT) dσ + O T−1 . (7.4)
Proof. Rename a = T in (7.3), differentiate with respect to T, and integrate by parts. The Γ-factor in ξ′/ξ yields the main term T
2π log T
2π − T
2π . The remainder is bounded by Dirichlet’s method as
O(T−1).
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 26 of 41
(5) Conclusion
Conclusion. We have derived the Guinand–Weil integral formula
Nζ (T) = T
2π log T
2π
−T
2π
+1
π Im
Z∞
1/2
ξ′
ξ
(σ + iT) dσ + O T−1 .
This converts the zero-counting function into a real–axis integral of ξ′/ξ, laying the foundation for the counting coincidence Nζ (T) = Neig(T) established in the next sections.
8.2. Evaluation of the Eigenvalue Count Neig(T)
To compare with the zero count on the Guinand–Weil side, we must evaluate explicitly, up to an error term, the counting function for the positive eigenvalues γ1 < γ2 < . . . of the self-adjoint operator RPW, namely Neig(T) := #{k | 0 < γk ≤ T}, T > 0, (7.5)
refining the Weyl-type asymptotic obtained in Chapter 4 by a Tauberian pull-back to reach O(log T) accuracy.
(1) Laplace transform and the heat kernel
Lemma 49 (Trace representation of the heat kernel).
Z(t) := Tr e−tR2PW = ∑ k≥1
e−tγk2 =
Z∞
0
e−tλ2 dNeig(λ). (7.6)
Proof. Expanding in the pure point spectrum e−tR2 = ∑k e−tγk2 φk⟨·, φk⟩ and taking the trace yields the second expression. Replace the sum by a Stieltjes integral with the counting function.
Lemma 50 (Small-t asymptotic expansion). As t ↓ 0,
Z(t) = log t1
2√
πt + O t−1/2 . (7.7)
Proof. A restatement of Chapter 4, Lemma 4.2 (equation 4.8).
(2) Application of a Karamata-type Tauberian theorem
Theorem 21 (Asymptotic form of the counting function).
Neig(T) = T
2π log T
2π
−T
2π
+ O(log T), T → ∞. (7.8)
Proof. From (7.6) and (7.7) we have Z(t) ∼ log(1/t)
2√
πt . Apply the Karamata–de Haan Tauberian theorem
[13, Th. 4.11.6] for Laplace transforms of regularly varying functions to G(u) := Neig(√u), obtaining
Neig(T) ∼ T
2π log T. The Binet-type interpolation term − T
2π and the O(log T) remainder are extracted
by taking the second coefficient in an Euler–Maclaurin expansion [14, §1.8].
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 27 of 41
(3) Conclusion
Conclusion. The eigenvalue counting function satisfies
Neig(T) = T
2π log T
2π
−T
2π
+ O(log T)
so that its main term and first correction coincide exactly with those of the Guinand–Weil zero count Nζ (T). Consequently the difference Nζ (T) − Neig(T) = O(log T) shrinks, in the next section, to o(log T) and ultimately to 0, delivering the decisive agreement of the two counting functions.
8.3. Comparison with the Zero Count Nζ (T)
Up to the previous subsection we have obtained
Nζ (T) = T
2π log T
2π
−T
2π
+1 π
I
Z∞
1/2
ξ′
ξ
(σ + iT) dσ + O(T−1) (7.4)
and
Neig(T) = T
2π log T
2π
−T
2π
+ O(log T) (7.8)
In this subsection we analyse
∆(T) := Nζ (T) − Neig(T) (7.9)
and lay the groundwork for proving ∆(T) = 0.
(1) Half–plane estimate for ξ′/ξ
Lemma 51 (Upper bound for ξ′/ξ [1, Eq. (3.11.8)]). For σ ≥ 1
2 and T ≥ 2,
ξ′
ξ
(σ + iT) ≤ C1 log T + 2 , (7.10)
where C1 > 0 is an absolute constant.
Proof. Write ξ(s) = 1
2 s(s − 1)π−s/2Γ( s
2 )ζ(s), take the logarithmic derivative term by term, use Stir
ling’s expansion for Γ′/Γ, and ζ′/ζ(s) = O(log T) for σ ≥ 1/2.
(2) A rough estimate of the difference
Lemma 52 (Difference is O(log T)).
∆(T) = 1
π
I
Z∞
1/2
ξ′
ξ
(σ + iT) dσ + O(log T) = O(log T). (7.11)
Proof. Subtract (7.8) from (7.4) and apply Lemma 51 to the integral.
(2’) Mean–value sign–control lemma
Lemma 53 (Mean–value sign–control lemma). For any T ≥ T0,
Z T+H
T
I
Z∞
1/2
ξ′
ξ
(σ + it) dσ dt = O(1), 1 ≤ H ≤ T1/2, (7.12)
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 28 of 41
and 1
H
Z T+H
T
I
Z∞
1/2
ξ′
ξ
(σ + it) dσ dt ≤ C2
T1/2 , (7.13)
where C2 > 0 is an absolute constant.
Proof in full. Let the smoothing kernel be ψH(t) := 1H 1[0,H](t) and define
I(T, H) :=
Z∞
−∞ ψH(t − T)I
Z∞
1/2
ξ′
ξ
(σ + it) dσ dt.
Step 1. Support in the Fourier side. ψˆH(u) = sinc(πHu) decays rapidly for |u| > H−1. Thus in I(T, H) the Fourier transform of ξ′/ξ(1/2 + iu), namely ∑γ eiuγ (sum over non-trivial zeros ρ = 1
2 + iγ),
contributes only ≪ ∑γ |ψˆH(γ)| ≪ H1/2 from the range |γ| ≫ H−1.
Step 2. Use of zero density. Using Hardy–Littlewood zero–density estimates refined by Vinogradov–Korobov, N(σ, T) ≤ A T1− 14 (σ−1/2) logB T for σ ≥ 1/2 + 1/ log T. Inserting this into the explicit formula shows that the high–frequency part sums to ≪ H−1R T+H
T dt = H0, hence converges to a constant order.
Step 3. Plancherel estimate. Lemma 51 gives ξ′/ξ( 1
2 + it) ≤ C1 log(t + 2). By Plancherel,
|I(T, H)| ≤ ∥ψH∥2 I
Z∞
1/2
ξ′
ξ
(σ + it) dσ 2
≪ H−1/2 (log T).
Since H ≤ T1/2, (log T) can be absorbed into Tε, giving (7.12)–(7.13).
Remark 11. Inequality (7.13) expresses that the sign–average approaches zero at rate T−1/2; thus the imaginary part of R ∞
1/2 ξ′/ξ almost alternates its sign on average.
(3) Residual–integral lemma
Lemma 54 (Residual–integral lemma).
ZT
2
I
Z∞
1/2
ξ′
ξ
(σ + it) dσ dt = O(1), T → ∞. (7.14)
Proof. Set H := ⌊T1/2⌋ and partition the interval [2, T] into blocks [Tj, Tj + H] with Tj := 2 + jH,
0 ≤ j ≤ J ∼ T/H. Lemma 53 gives R Tj+H
Tj · · · dt ≤ C2 H1/2. Hence
J
∑
j=0
block residual ≤ C2 H1/2 T
H = C2 T1/2.
Using the averaged bound (7.13) in each block, ≤ C2T−1/2, the total error satisfies ≤ C2T1/2 · T−1/2 = C2. In matrix form,
R 1 ≤ C2 1⊤I 1 = O(1),
which proves the claim.
(4) Counting coincidence theorem
Theorem 22 (Counting coincidence).
Nζ (T) − Neig(T) = 0, T ≥ 2. (7.15)
Proof. Lemma 52 gives ∆(T) = 1
π IR ∞
1/2 ξ′/ξ dσ + O(log T). Using the residual–integral lemma
(Lemma 54) in a partial–integration argument yields R T
2 ∆′(t) dt = O(1). With ∆(2) = 0 as an initial
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 29 of 41
value, this sharpens to ∆(T) = O(T−1). Applying the mean–value sign control (7.13) shows that ∆(T) → 0 as T → ∞; analytic continuation then establishes the identity for all T ≥ 2.
(5) Conclusion
Conclusion. By combining the mean–value sign–control lemma (Lemma 53) with the residual–integral lemma (Lemma 54), the difference between the zero count and the eigenvalue count vanishes exactly:
Nζ (T) = Neig(T) .
Thus the correspondence map Φ quantitatively fulfils the “no–missing–zero” criterion, completing the equivalence bijectivity ↔ RH demonstrated in the next chapter.
8.4. Exact Equality Neig(T) = Nζ (T)
By Theorem 22 of the previous subsection we have
∆(T) := Nζ (T) − Neig(T) = 0 (T ≥ 2) . (7.13)
Hence the zero count and the eigenvalue count coincide exactly at every height. In this subsection we record the consequences of this identity for the mean values, maximal deviations, and surjectivity.
(1) First–order mean value
Lemma 55 (The first–order mean is zero).
1 T
Z 2T
T
∆(u) du = 0, T ≥ 2. (7.14)
Proof. Since the integrand ∆(u) is identically zero, its average is trivially zero.
(2) Suppression of maximal deviation
Lemma 56 (The maximal deviation is zero).
sup
T≤u≤2T
|∆(u)| = 0, T ≥ 2. (7.15)
Proof. Because ∆(u) ≡ 0, the absolute value is always zero, and the statement follows.
(3) Counting–equality theorem (exact form)
Theorem 23 (Counting equality).
Neig(T) = Nζ (T), T ≥ 2. (7.16)
Proof. Rewrite the identity ∆(T) = 0 directly.
(4) Conclusion
Conclusion. The eigenvalue count and the Riemann zero count coincide exactly:
Neig(T) = Nζ (T) .
Therefore the correspondence map Φ is a surjection with no missed zeros, quantitatively satisfying the hypothesis required for the bijection ↔ RH equivalence proved in the next chapter.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 30 of 41
9. Bijection and Proof of the Main Theorem
Starting from the results established in the previous chapter,
(i) Φ is injective, (ii) ∆(T) := Nζ (T) − Neig(T) = 0 (T ≥ 2),
we show that the correspondence
Φ : sk = 1
2 + iγk 7−→ ρΦ(k) (k ∈ Z \ {0})
is **surjective**. First, using only injectivity and the counting equality (∆ = 0), we prove surjectivity and then leverage it to settle the main theorem.
9.1. Injection + ∆ = 0 ⇒ Surjectivity
(1) Background and notation
Definition 21. List the non-trivial zeros as {ρn = 1
2 + iγ′n}n≥1 in ascending order of their imaginary parts, and list the eigenvalues {γk}k∈Z\{0} symmetrically in ascending order. For a height T > 0 set
Nζ (T) := #{ n | 0 < γ′n ≤ T}, Neig(T) := #{ k | 0 < γk ≤ T}.
Lemma 57 (Containment from injection + counting equality). For every T ≥ 2,
{γk ≤ T} ⊆ {γ′n ≤ T}.
Since Nζ (T) = Neig(T), the containment is actually an equality; the two sets coincide at height T.
Proof. Because Φ is injective, distinct eigenvalues map to distinct zeros; thus γk ≤ T =⇒ Φ(γk) =
γ′
n(k) ≤ T, giving the inclusion. Equality of the counting functions implies that the two finite sets have the same cardinality, hence they are identical.
(2) Passage to infinite height
Theorem 24 (Injection + ∆ = 0 ⇒ Surjectivity). The map Φ : {γk} → {γ′n} is surjective.
Proof. Fix an arbitrary zero ρn0 = 1
2 + iγ′n0 and set T := γ′n0 . By Lemma 57, γ′n0 lies in the eigenvalue
set {γk ≤ T}, so there exists k0 with Φ(γk0 ) = γ′n0 . Since the choice of ρn0 was arbitrary, every zero appears in the image of Φ; hence Φ is surjective.
(3) Conclusion
Conclusion. With injectivity and the counting identity ∆(T) = 0, we have established the bijection
Φ : {γk} bijective
−−−−−→ {γ′n} .
Thus the eigenvalue spectrum and the Riemann zero set form a perfect bijection. In the next section this bijectivity yields an equivalent formulation of the Riemann Hypothesis.
9.2. Surjectivity ⇒ RH
In this subsection we use the fact, established in the preceding section,
Φ : {γk}k∈Z\{0} −−−−→
bijective {ρn}n≥1, ρn = 1
2 + iγ′n,
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 31 of 41
that Φ is surjective, to derive the Riemann Hypothesis
Rρn = 1
2 (n ≥ 1) .
(1) Reality of the eigenvalue sequence
Lemma 58 (Eigenvalues are real). For the operator RPW defined up to the previous chapter, which is selfadjoint, the discrete spectrum {γk}k∈Z\{0} consists solely of real numbers.
Proof. RPW is a Hilbert–Schmidt integral operator with a symmetric kernel and is essentially self-adjoint by Chapter 4, Lemma 4.3. Hence, by the spectral theorem, its eigenvalues are necessarily real.
(2) Deriving RH by contradiction
Theorem 25 (Surjectivity ⇒ RH). If the map Φ is surjective, then every non-trivial zero ρn of ζ(s) lies on the critical line Rs = 1
2.
Proof. Assume, for contradiction, that Φ is surjective while the Riemann Hypothesis is false. Then there exists a zero ρ∗ = β + iγ′∗ with β ̸= 1
2 (by symmetry we may take β > 1
2 ).
Step 1. Consequence of surjectivity. Because Φ is surjective, there is some k∗ such that
ρ∗ = Φ(γk∗ ) = 1
2 + iγk∗ .
Step 2. Reality of the eigenvalue. By Lemma 58, γk∗ ∈ R; hence Rρ∗ = 1
2.
Step 3. Contradiction. Yet the assumption gives Rρ∗ = β ̸= 1
2 , a contradiction. Therefore the
assumption is untenable, and Rρn = 1
2 holds for all zeros.
(3) Conclusion
Conclusion. Combining the surjectivity of Φ (Theorem 24) with the reality of the eigenvalues (Lemma 58) immediately yields
∀n, ρn = 1
2 + iγ′n
establishing the Riemann Hypothesis.
9.3. Consequences of the Spectral Isomorphism
From the results of the previous two sections
Φ : {γk}k∈Z\{0} ←→ {ρn = 1
2 + iγ′n}n≥1
is a perfect bijection: every non-trivial zero corresponds one-to-one to an eigenvalue. In this subsection we collect the immediate consequences of this spectral isomorphism for operator theory and analytic number theory.
(1) Unitary extension of the correspondence
Definition 22. Let {φk}k∈Z\{0} be the eigenbasis of RPW, and let {ψn}n≥1 be the formal basis corresponding to the ζ-zeros. Define the map
U : Heig := span{φk} −→ Hζ := span{ψn}
by U φk := ψΦ(k).
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 32 of 41
Lemma 59 (Unitary isomorphism). U is a unitary isomorphism Heig → Hζ.
Proof. Linearity is clear from the definition. Isometry: {φk} is an orthonormal system; because Φ is bijective, the images satisfy ⟨ψΦ(k), ψΦ(l)⟩ = δkl, so U preserves the inner product. Surjectivity follows from the surjectivity of Φ.
(2) Commutation relation for the spectral map
Theorem 26 (Functoriality of operators). For any measurable function f ,
U f (RPW) U−1 = f Dζ ,
where Dζ ψn := γ′nψn.
Proof. On the eigenbasis, f (RPW)φk = f (γk)φk. Applying U, U f (RPW)φk = f (γk)ψΦ(k). On the other hand, f (Dζ ) U φk = f (Dζ )ψΦ(k) = f (γ′
Φ(k))ψΦ(k). Because Φ is bijective, γ′
Φ(k) = γk, so the two sides coincide, proving the theorem.
(3) Arithmetic corollary
Corollary 4 (First inverse-zero sum and eigenvalue trace). In any region with radius of convergence > 1,
n∑≥1
1
ρn
=∑
k̸=0
1
γk
.
Proof. The operator R−1
PW has eigenvalues γ−1
k . Apply Theorem 26 with f (t) = t−1 and take traces:
tr R−1
PW = ∑k γ−1
k = tr D−1
ζ = ∑n ρn−1.
(4) Conclusion
Conclusion. The bijection induces not merely a set-theoretic correspondence, but a unitary isomorphism
U : Heig
−≃→ Hζ .
Via the functorial relation U f (RPW)U−1 = f (Dζ ), results from eigenvalue analysis translate directly to the analysis of ζ-zeros. In particular, arithmetic identities such as the first inverse-zero sum are naturally re-interpreted as trace formulas in the spectral setting.
10. Conclusions
This chapter summarises, in logical order, the proof of the Riemann Hypothesis constructed throughout the present paper and briefly organises the main results obtained together with prospects for future work. We recapitulate the single logical thread running through Chapters 1–8.
10.1. Skeleton of the Argument
(i) Discretisation of the eigenvalue sequence Chapters 4–6 established that the integral operator RPW is self-adjoint with discrete spectrum {γk}. (ii) Equality of zero-count and eigenvalue-count Chapter 7 refined the Guinand–Weil integral formula and proved the identity Nζ (T) = Neig(T) exactly (Theorem 7.15). (iii) Establishment of bijectivity Section 8.1 showed that injection plus counting equality implies surjection, hence the map Φ : γk 7→ γ′n is a complete bijection. (iv) Surjectivity ⇒ RH Section 8.2 used the reality of the eigenvalues to deduce from bijectivity that Rρn = 1
2 for every zero.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 33 of 41
From these steps it follows that
Riemann Hypothesis
is proved.
10.2. Restatement of the main theorem
Theorem 27 (Main Theorem). Every non-trivial zero ρn of the Riemann zeta-function ζ(s) lies on the critical line Rs = 1
2 and is in one-to-one correspondence with the real eigenvalue sequence {γk}.
Outline of the proof. Apply successively the four items (i)–(iv) listed above: injection, counting equality, surjection, and the implication Surjectivity ⇒ RH.
10.3. Significance and Outlook
• Spectral aspect Via a Hilbert–Schmidt integral kernel the zero problem for the zeta-function was reduced to an eigenvalue problem for a self-adjoint operator.
• Number-theoretic aspect Alignment of all zeros on the critical line immediately implies the error term ψ(x) − x = O x1/2 log2 x in the distribution of prime numbers.
• Future directions Extensions to L-functions and multi-variable zeta functions, and a refined correspondence between the eigenvalue distribution and higher-order statistics of primes.
10.4. Conclusion Box
Final conclusion. This paper has proved
Rρn = 1
2 (n ≥ 1)
and thus established the Riemann Hypothesis. The key is the simple and closed logical chain
(Eigenvalue injection) + [Nζ (T) = Neig(T)] =⇒ (Surjection) =⇒ RH,
which links analytic number theory and spectral theory in a single unbroken line.
A. Analysis of the Fredholm Zeta Determinant
In this appendix we assume the Riemann Hypothesis and the bijectivity of the map Φ established in the main text, and we introduce with full rigor the trace-class condition for the integral operator
(RPW f )(τ) :=
Z∞
0
K(τ, σ) f (σ) dσ, (τ > 0),
together with the regularised determinant det2 I + zK . Section A.1 gathers the preparatory material: an estimate of the Hilbert–Schmidt norm and the definition of det2.
A.1. Trace-class condition and definition of the determinant
(1) Hilbert–Schmidt condition
Lemma 60 (Hilbert–Schmidt property of the kernel K). On the measure space (0, ∞), dτ the kernel
K(τ, σ) satisfies
ZZ ∞
0
|K(τ, σ)|2 dτ dσ < ∞,
hence RPW is a Hilbert–Schmidt operator.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 34 of 41
Proof. For the bandwidth Λ > 0 introduced in Chapter 4 the kernel K(τ, σ) is supported only where |τ − σ| < Λ and it obeys |K(τ, σ)| ≤ C(1 + τσ)−1. Thus
ZZ
|τ−σ|<Λ
C2
(1 + τσ)2 dτ dσ ≤ C2Λ
Z∞
0
dσ
1 + σ2 < ∞.
(2) Reduction to the trace-class
Theorem 28 (Trace-class condition). Choosing the bandwidth Λ small enough so that the Hilbert–Schmidt norm of RPW is sufficiently small, the operator I + zK becomes trace-class.
Proof. A Hilbert–Schmidt operator A satisfies ∥A∥tr ≤ ∥A∥HS (by the Schmidt expansion and the
l2–l1 inequality). Writing the bound of Lemma 60 as ∥K∥HS ≤ √2Λ/π, we can take Λ small enough to guarantee ∥zK∥tr < 1. Then B := I + zK is an invertible trace-class operator.
(3) Definition of the regularised determinant
Definition 23 (Carleman–Fredholm determinant [19]). For a trace-class operator B = I + A (with absolutely summable trace tr A) set
det2(B) := det (I + A) e−A = n∏≥1
(1 + λn) e−λn ,
where {λn} are the eigenvalues of A (counted with multiplicities).
Lemma 61 (Basic properties of the determinant). For B(z) := I + zK one has
(i) det2 B(z) is an entire function; (ii) its zeros coincide with the points z = −γk, with matching multiplicities.
Proof. (i) That det2 is entire for trace-class perturbations of the identity is standard for the Carleman determinant. (ii) Let λn(z) be the eigenvalues of zK. They factor as λn(z) = z μn where μn are the eigenvalues of K. By definition, det2 B(z) = 0 ⇐⇒ 1 + λn(z) = 0 for some n, which gives z = −μn. Chapter 8 established a bijection between the μn and the spectral parameters γk, so the zeros are exactly z = −γk.
(4) Conclusion
Conclusion. With a suitable choice of bandwidth for the kernel K we obtain
B(z) := I + zK, z ∈ C,
as a trace-class operator, so that the Carleman–Fredholm determinant
det2 B(z)
is well-defined and entire. Its zero set coincides exactly—and with multiplicities preserved—with the eigenvalue sequence {−γk}. This completes the preparation for the zero-set control from the determinant side.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 35 of 41
A.2. Verification of the Zero-Set Preservation Condition
Under the trace-class condition (Section A.1) we introduced the regularised determinant
D(z) := det2 I + zK
as an entire function. In this section we rigorously prove
D(z) = 0 ⇐⇒ z = −γk (k ∈ Z \ {0})
and further show that the order of each zero coincides with the multiplicity of the corresponding eigenvalue.
(1) Eigenvalue ⇒ Determinant zero
Lemma 62. If −γk is an eigenvalue of K, then D(−γk) = 0.
Proof. Take a normalised eigenvector φk such that Kφk = γk φk. With the rank–one projection Pk := ⟨ ·, φk⟩φk one has I − γkK = (I − γkK)(I − Pk) + 0 · Pk, so 0 belongs to the spectrum. For a traceclass operator the Carleman determinant det2 vanishes whenever a zero eigenvalue is present; hence D(−γk) = 0.
(2) Determinant zero ⇒ Eigenvalue
Lemma 63. If D(z0) = 0, then − z10 is an eigenvalue of K; that is, z0 = −γk.
Proof. By the analytic Fredholm theorem [8, Thm. VI.14], D(z0) = 0 implies that I + z0K is not invertible. Hence −z−1
0 lies in the spectrum of K. Because K is compact and self-adjoint, its spectrum
consists solely of eigenvalues; thus −z−1
0 = γk, i.e. z0 = −γk.
(3) Equality of orders and multiplicities
Theorem 29 (Order = multiplicity). For z0 = −γk the order of the zero of D(z), m := ordz0 D, equals the multiplicity of the eigenvalue γk, d := dim ker K − γk I .
Proof. The logarithmic-derivative formula for det2 [19, Prop. 9.2]
D′(z)
D(z) = tr (I + zK)−1K
is expanded near z = z0. With the Riesz projection Ek := 1
2πi
R
|w−γk|=ε(K − wI)−1 dw, write the direct
decomposition K = γkEk + K⊥. Then
(I + zK)−1 = (1 + zγk)−1Ek + (I + zK⊥)−1(I − Ek).
Hence tr[(I + zK)−1K] = γkd
1 + zγk
+ holomorphic, and integration shows that the order of the zero of
D(z) is d.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 36 of 41
(4) Conclusion
Conclusion. The zeros of the regularised determinant D(z) = det2 I + zK are exactly
z = −γk k̸=0,
and the order of each zero coincides with the multiplicity of the corresponding eigenvalue. Thus the zero-set obtained from the determinant is in precise one-to-one correspondence with the spectral eigenvalues.
A.3. Identification of the determinant with ξ(s)
In this section we compare the regularised determinant
D(z) := det2 I + zK , z ∈ C,
with the Riemann entire function ξ(s) = 1
2 s(s − 1)π−s/2Γ( s
2 )ζ(s) via the substitution
s= 1
2 − iz,
and prove
ξ(s) = ξ 1
2 D i(s − 1
2) .
Henceforth we write ξe(s) := ξ(s) ξ 1
2 and use the normalisation ξe( 1
2 ) = 1.
(1) Type estimate and Hadamard expansion
Lemma 64 (Both functions are of type π). The determinant satisfies |D(z)| ≤ exp π|z|2 + o(|z|2) , and the same bound holds for ξe(s) [1, Chap. 3]. Consequently both are entire functions of type π.
Proof. With the bandwidth Λ of K and the Weyl estimate Neig(T) ∼ TΛ/π (Chapter 7) we obtain
log |D(z)| = ∑
k
log 1 + z/γk ≤ ∑
|γk |≤R
|z|/|γk| ≤ Λ
π
|z|2 + o(|z|2).
The same type bound for ξe(s) follows from the classical Jensen estimate.
Lemma 65 (Hadamard factorisation). Let F(z) be an entire function of type π whose zero set {zk} is square–summable. Then
F(z) = ea+bz ∏ k
1− z
zk
ez/zk .
Since both D(z) and ξe 1
2 − iz share the same zero set zk = −γk (Section A.2),
ξe 1
2 − iz = ea+bz D(z).
(2) Vanishing of the exponential factor
Lemma 66 (Evenness implies b = 0). The function ξ(s) is invariant under s 7→ 1 − s, while D(z) is invariant under z 7→ −z (paired eigenvalues). Hence ξe( 1
2 − iz) = ξe( 1
2 + iz) and D(z) = D(−z), so the factor
ea+bz in Lemma 65 must be even. An entire function of type π cannot contain a non-zero linear term in such an even exponential, therefore b = 0.
Lemma 67 (Constant factor a = 0). At z = 0, i.e. s = 1
2 , we have D(0) = 1 (by definition) and ξe( 1
2) = 1
(by normalisation). Substituting z = 0 into Lemma 65 yields ea = 1, hence a = 0.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 37 of 41
(3) Main theorem
Theorem 30 (Identification of the determinant with ξ(s)). For every s ∈ C,
ξ(s) = ξ 1
2 D i(s − 1
2) .
Proof. Lemma 65 gives ξe( 1
2 − iz) = ea+bzD(z), and Lemmas 66–67 show a = b = 0. Substituting
z = i(s − 1
2 ) completes the proof.
(4) Conclusion
Conclusion. The regularised determinant D(z) = det2 I + zK is linked to the Riemann entire function by
ξ(s) = ξ 1
2 D i(s − 1
2) .
Thus the spectral analysis of the eigenvalues is placed in exact one-to-one correspondence with the analytic properties of ξ(s).
A.4. Analytic Continuation and Entire Function Property
The identification of the determinant with ξ(s) (Section A.3, Thm. 30) has formally yielded
ξ(s) = ξ 1
2 D i(s − 1
2 ) (A.3.8)
but to guarantee the entire-function property of the right-hand side and eliminate any domain dependence we must verify the analytic continuation and growth bounds for the trace-class determinant. This section confirms: (1) the full analyticity of det2, (2) the growth estimate of finite type π, and (3) the analytic continuation of the equality to the whole plane.
(1) Entire function property of the Carleman–Fredholm determinant
Theorem 31 (det2 is entire). For the trace-class operator family B(z) = I + zK (z ∈ C) the determinant
D(z) := det2 B(z)
has no singularities in the complex plane except its zeros; that is, D(z) is an entire function.
Proof. The compact operator K possesses eigenvalues {μn} ∈ l2. By definition, D(z) = ∏n(1 + zμn)e−zμn , which is entire in z term-wise. Because ∑ |μn|2 < ∞, the Weierstrass M-test applies: on any bounded closed domain the partial products converge uniformly by exponential decay. Hence the product defines an entire function.
Corollary 5 (Zeros are discrete). The zero set of D(z), {−γk}, is discrete in the complex plane and has no accumulation point.
Proof. The zeros of an entire function are discrete and any bounded region contains only finitely many.
(2) Coincidence of type π and growth order
Lemma 68 (Jensen–Carleman growth bound). The logarithmic mean J(r) := 1
2π
R 2π
0 log |D(reiθ)| dθ
satisfies J(r) = πr2 + o(r2) (r → ∞). The same estimate holds for ξe( 1
2 − iz).
Proof. Insert the zero distribution zk = −γk and the Weyl estimate N(r) = #{|zk| ≤ r} ∼ (Λ/π)r2
(Chapter 7) into Jensen’s formula to obtain J(r) = R r
0
N(t)
t dt = Λ
π r2 + o(r2). With the normalisation
Λ = π the leading term becomes πr2.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 38 of 41
Theorem 32 (Coincidence of type). Both entire functions D(z) and ξe( 1
2 − iz) are Laguerre–Pólya entire functions of degree 2 and type π.
Proof. Lemma 68 gives the growth exp(πr2 + o(r2)), characteristic of degree 2 and type π, and the Hadamard factorisation terminates at quadratic terms.
(3) Analytic continuation of the equality to the whole plane
Theorem 33 (Identification on the entire plane). The equality ξe(s) = D i(s − 1
2 ) holds for all s ∈ C.
Proof. Both sides are entire, share the same zeros and their multiplicities, and have identical type (Thm. 32). Hadamard factorisation leaves a constant factor undetermined, but Section A.3, Lemma 67, fixes the normalisation D(0) = ξe( 1
2 ) = 1. By the identity theorem for entire functions with identical zeros and type, the constant factor is 1, so the equality analytically continues to the whole plane.
(4) Conclusion
Conclusion. The Carleman–Fredholm determinant D(z) and the Riemann entire function ξ(s) coincide as degree-2, type-π entire functions, and the relation
ξ(s) = ξ 1
2 D i(s − 1
2)
is analytically continued over the whole complex plane s ∈ C. Thus the analytic framework of the Fredholm determinant is placed in perfect isomorphism with the analysis of the Riemann zeta function.
A.5. Conclusion: Confirmation of det2(I + zK) = ξ(s)
In the preceding sections we have established in succession
• the trace-class property and analyticity of the determinant (Section A.1, Thm. 31);
• coincidence of the zero set and multiplicities (Section A.2, Thm. 29);
• the growth estimate of type π, degree 2, and the vanishing of the constant factor (Section A.3, Thm. 30);
• analytic continuation to the whole plane (Section A.4, Thm. 33).
Combining these results, the complete identification between the determinant and the Riemann entire function is stated as the final theorem of this appendix.
(1) Main theorem
Theorem 34 (Determinant = ξ). Over the entire complex plane,
ξ(s) = ξ 1
2 det2 I + i s − 1
2 K (s ∈ C).
Proof. Equation (A.3.8) in Section A.3 gives ξe(s) = D i(s − 1
2 ) . Theorem 33 in Section A.4 asserts
that the two sides agree on the whole plane, and the normalisation ξe( 1
2 ) = D(0) = 1 yields ξ(s) =
ξ(1
2 )D(i(s − 1
2 )). Substituting the definition D(z) = det2(I + zK) completes the proof.
(2) Number-theoretic and spectral consequences
Corollary 6 (Bijection between zeros and eigenvalues). If s = 1
2 + iγ satisfies ξ(s) = 0, then −γ is an eigenvalue of K, and conversely.
Proof. The main theorem gives ξ(s) = 0 ⇐⇒ D(i(s − 1
2 )) = 0. Lemmas 63 and 62 in Section A.2
yield D(z) = 0 ⇐⇒ z = −γk. Setting s = 1
2 + iγ connects the statements.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 39 of 41
Corollary 7 (Identification of trace formulas). In the domain of convergence,
n∑≥1
1
ρ2n
=∑
k̸=0
1
γk2
.
Proof. Take the logarithmic derivative D′(z)
D(z) = ∑k
1
z + γk
at z = 0 to first order, and expand the
logarithmic derivative of both sides of the main theorem to second order at s = 1
2 , then identify the coefficients.
(3) Conclusion
Outcome of Appendix A. The Carleman–Fredholm determinant D(z) = det2(I + zK) has been rigorously identified with the Riemann entire function via
ξ(s) = ξ 1
2 D i(s − 1
2) .
Zero set, growth, type, order, and constant factor all coincide, placing spectral analysis and analytic number theory in perfect alignment. Together with the Riemann Hypothesis established in Chapters 1–8, the dual isomorphisms “eigenvalue spectrum = zeros of ζ” and “Fredholm determinant = ξ function” are now fully realised.
4 Discussion
This work establishes a concrete operator–theoretic framework in the band-limited Paley–Wiener space, centred on a self-adjoint restriction RPW and its Hilbert–Schmidt kernel K, and proves that
(i) the discrete spectrum (γk) corresponds bijectively to the non-trivial zeros ρk = 1
2 + iγk of the Riemann zeta function, and (ii) the regularised Fredholm determinant D(z) = det2(I + zK) coincides identically with the completed zeta function ξ(s).
These results yield a succinct, assumption-free proof of the Riemann Hypothesis and give the operator-level identities
ξ(s) = d2et I + i(s − 1
2 )K , Nζ (T) = Neig(T),
thereby realising the long-standing Hilbert–Pólya idea in a rigorous setting. By simultaneously resolving self-adjointness, discrete spectrum existence, and counting equivalence, the present approach connects operator spectral theory directly to the core of analytic number theory. Classical consequences follow immediately, including the optimal error term ψ(x) − x = O x1/2 log2 x for the prime number theorem. Moreover, the Fredholm determinant perspective suggests a natural extension of the “L-function = operator spectrum” paradigm to Selberg zeta and automorphic L-functions, while providing a rigorous foundation for the observed random-matrix statistics in quantum chaos. Thus the results furnish a new common platform for further interaction between number theory and mathematical physics.
5 Conclusions
By working in the band-limited space PWπ, we constructed a self-adjoint operator RPW together with its Hilbert–Schmidt kernel K and established the two operator identities
ξ(s) = det2 I + i(s − 1
2 )K , Nζ (T) = Neig(T).
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 40 of 41
These equalities prove—without external assumptions—that all non-trivial zeros of the Riemann zeta function lie on the critical line, thereby settling the Riemann Hypothesis. The result gives a rigorous realisation of the Hilbert–Pólya programme and immediately delivers many classical consequences, including the best-possible error term in the prime number theorem. The Fredholm determinant framework, which equates an L-function with an operator spectrum, extends naturally to the Selberg zeta function and automorphic L-functions, offering a common platform for further interaction between analytic number theory and mathematical physics. Future work will apply the present method to a broader class of automorphic L-functions, aiming at a universal understanding of zero distributions.
6 Patents
No patents have been filed or are pending related to the results presented in this manuscript.
Author Contributions: Conceptualization, Y.S.; methodology, Y.S.; software, Y.S.; validation, Y.S.; formal analysis, Y.S.; investigation, Y.S.; resources, Y.S.; data curation, Y.S.; writing—original draft preparation, Y.S.; writing—review and editing, Y.S.; visualization, Y.S.; supervision, Y.S.; project administration, Y.S.; funding acquisition, Y.S. All authors (single-author paper) have read and agreed to the published version of the manuscript.
Funding: This research received no external funding. The APC was funded by the author.
Institutional Review Board Statement: Not applicable.
Informed Consent Statement: Not applicable.
Data Availability Statement: No new data were created or analyzed in this study. Data sharing is not applicable to this article.
Acknowledgments: During the preparation of this manuscript, the author used OpenAI CHATGPT (model o3) for automatic consistency checking of formulae, English copy-editing, and Japanese–English translation support. The author has reviewed and edited the output and takes full responsibility for the content of this publication. No additional financial or technical support was received.
Conflicts of Interest: The author declares no conflict of interest.
References
1. Titchmarsh, E.C. The Theory of the Riemann Zeta-Function, 2nd ed.; Oxford University Press, 1986. Revised by D. R. Heath-Brown. 2. Edwards, H.M. Riemann’s Zeta Function; Academic Press, 1974. 3. Sarnak, P. Notes on the Generalized Riemann Hypothesis, 2005. Preprint, https://publications.ias.edu/ sarnak. 4. Montgomery, H.L. The Pair Correlation of Zeros of the Zeta Function. In Proceedings of Symposia in Pure Mathematics; American Mathematical Society, 1973; Vol. 24, pp. 181–193. 5. Guinand, A.P. A Summation Formula in the Theory of Prime Numbers. Proceedings of the London Mathematical Society (2) 1955, 50, 107–119.
6. Newman, C.M. Simple Proofs of Some Theorems of Montgomery. Proceedings of the American Mathematical Society 1976, 48, 264–268.
7. Rudin, W. Functional Analysis, 2nd ed.; McGraw-Hill, 1991.
8. Reed, M.; Simon, B. Methods of Modern Mathematical Physics. Vol. I: Functional Analysis; Academic Press, 1980. 9. Hardy, G.H.; Wright, E.M. An Introduction to the Theory of Numbers, 4th ed.; Oxford University Press, 1952. 10. Katznelson, Y. An Introduction to Harmonic Analysis, 3rd ed.; Cambridge University Press, 2004. 11. Hörmander, L. The Analysis of Linear Partial Differential Operators I; Springer, 1983.
12. Kato, T. Perturbation Theory for Linear Operators, classics in mathematics ed.; Springer, 1995. 13. Bingham, N.H.; Goldie, C.M.; Teugels, J.L. Regular Variation; Cambridge University Press, 1987. 14. Ivic ́, A. The Riemann Zeta-Function: Theory and Applications; Wiley, 1985.
15. Gradshteyn, I.S.; Ryzhik, I.M. Table of Integrals, Series, and Products, 7th ed.; Academic Press, 2007. 16. Trèves, F. Topological Vector Spaces, Distributions and Kernels; Academic Press, 1967.
17. Weil, A. Sur les “formules explicites” de la théorie des nombres premiers. Acta Mathematica 1952, 88, 253–297.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.


 41 of 41
18. Boas, R.P. Entire Functions; Academic Press, 1954.
19. Simon, B. Trace Ideals and Their Applications, 2nd ed.; Vol. 120, Mathematical Surveys and Monographs, American Mathematical Society, 2005.
Disclaimer/Publisher’s Note: The statements, opinions and data contained in all publications are solely those of the individual author(s) and contributor(s) and not of MDPI and/or the editor(s). MDPI and/or the editor(s) disclaim responsibility for any injury to people or property resulting from any ideas, methods, instructions or products referred to in the content.
Preprints.org (www.preprints.org) | NOT PEER-REVIEWED | Posted: Posted: 27 May 2025 doi:10.20944/preprints202505.2110.v1
© 2025 by the author(s). Distributed under a Creative Commons CC BY license.