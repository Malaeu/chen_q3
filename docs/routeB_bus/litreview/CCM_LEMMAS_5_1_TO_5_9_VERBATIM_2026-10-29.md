# CCM Zeta Spectral Triples (arXiv:2511.22755) — verbatim cards: Lemmas 5.1, 5.2, 5.4, Prop. 5.9 and the definitions they need
Source PDF: pdfs/2511.22755.pdf (arXiv:2511.22755v1, 27 Nov 2025). Companion of CCM_ZST_USAGE_CARDS.md (Thm 5.10, Thm 3.6, Lemma 7.2/7.3, §8).
Date of this file: 2026-10-29. Closes the gap recorded in docs/literature/RETRO_HISTORY_2026-10-28/PILLAR_PROVENANCE_2026-10-29.md line 37.

Note on locations: page numbers are the printed page numbers (they equal the PDF page index 1:1, same as in CCM_ZST_USAGE_CARDS.md).
Method: text taken with `pdftotext -layout`; every displayed formula was then compared with a 130-150 dpi rendering of the page
(pages 11, 15, 16, 17, 20, 22, 23 read as images). Where the text layer and the image disagree, the image wins.
Marks: [illegible] = could not be read (none needed). A line starting "READER NOTE" is mine, not the paper's.
Math notation is kept as printed: ∗∗ in the paper is the convolution "f* ∗ g" (adjoint-then-convolve); D is the diagonal
operator D(V_n) = nV_n (not the distribution 𝒟 = log_*(Ψ♯); the paper uses the calligraphic letter for the distribution);
Dlog is D_log; D” is the paper's double-prime.

Cards (in order): Def 5.0a  (2.6) U_n and (2.8)-(2.10) q; Def 5.0b (3.10)+(3.13) Ψ, Ψ♯; Def 5.0c (3.17)-(3.18), (3.21) κ, V_n;
Def 5.0d §5.1 QW_λ^N, 𝒟 and (5.1); Lemma 5.1; Lemma 5.2; Def 5.3 + normalisation paragraph (5.4); Lemma 5.4;
Def (5.8), Cor. 5.6 (δ_N); Prop. 5.9 with (5.25); the paper's own "even" statement (p. 2); E_N, E'_N.
Then: Crosswalk to STIELTJES.

---

## Definition: U_n and q(f,g) — pp. 3-4, §2 "The basis {U_n}" (eqs (2.4)-(2.6), (2.8)-(2.10), Lemma 2.3)
VERBATIM:
"q(f, g)(y) := (f∗ ∗ g)(y) + (f∗ ∗ g)(−y)    (2.4)
which is an even function of y depending antilinearly on f and linearly on g." [p. 3]
"A natural orthonormal basis for L²([0, L]) consists of the functions {U_n}_{n∈Z} defined by
    U_n(x) := L^{−1/2} exp(2πinx/L),   ∀x ∈ [0, L].    (2.6)" [p. 3]
"(U_m∗ ∗ U_n)(y) + (U_m∗ ∗ U_n)(−y) = 2 ℜ( (e^{2πimy/L} − e^{2πiny/L}) / (2πi(n − m)) ) = (sin(2πmy/L) − sin(2πny/L)) / (π(n − m))    (2.8)
so that the even function q(U_m, U_n) is given by
    q(U_m, U_n)(y) = (sin(2πm|y|/L) − sin(2πn|y|/L)) / (π(n − m)),  ∀y ∈ [−L, L].    (2.9)
For m = n one simply has, for y ∈ [0, L], ... We thus get
    q(U_n, U_n)(y) = 2(1 − |y|/L) cos(2πny/L),  ∀y ∈ [−L, L].    (2.10)" [p. 4]
"Lemma 2.3. The explicit expression of the even function q(U_n, U_m)(y) for y ∈ [0, L] is :
    m ≠ n :  (sin(2πmy/L) − sin(2πny/L)) / (π(n − m))
    m = n :  2(L − y) cos(2πny/L) / L" [p. 4]
Used by us for: the entry kernel q of the literal matrix (full_center_probe.py:12-14 is these two lines).

---

## Definition: Weil form QW, Ψ and Ψ♯ — pp. 6-7, §3 "The Weil quadratic form QW" (eqs (3.10), (3.12)-(3.16))
VERBATIM:
"By polarization, the Weil form gives the sesquilinear expression
    QW(f, g) = Ψ(f∗ ∗ g),   Ψ(F) := W_{0,2}(F) − W_R(F) − Σ_p W_p(F).    (3.10)
The components W_R and W_p are as above, and the functional W_{0,2} is
    W_{0,2}(F) = F̂(i/2) + F̂(−i/2).    (3.11)" [p. 6]
"Lemma 3.1. The Weil functional Ψ fulfills
    Ψ(h) = Ψ♯(h) + Ψ♯(h ◦ ι) = Ψ♯(h + h ◦ ι),    (3.12)
where Ψ♯ is the distribution on [1, ∞),
    Ψ♯ := W♯_{0,2} − W♯_R − Σ W♯_p    (3.13)
with the components given by
    W♯_{0,2}(F) = ∫_1^∞ F(x)(x^{1/2} + x^{−1/2}) d∗x,    (3.14)
    W♯_R(F) = ½(log 4π + γ)F(1) + ∫_1^∞ (x^{1/2}F(x) − F(1)) / (x − x^{−1}) d∗x,    (3.15)
    W♯_p(F) = (log p) Σ_{m=1}^∞ p^{−m/2} F(p^m).    (3.16)
Proof. This follows from the construction of Ψ. Note the factor ½ in (3.15)." [p. 7]
Used by us for: sign pattern "W_{0,2} − W_R − primes" of K (full_center_probe.py:38). The factor ½ in (3.15) is the one that turns
(log 4π + γ)·q(0)/2 into (log 4π + γ) on the diagonal (q(0) = 2 there).

---

## Definition: κ, (3.18), V_n — p. 7 (Prop. 3.2) and p. 8, eq. (3.21)
VERBATIM:
"Proposition 3.2. Let λ > 1, L = 2 log λ.
(i) The following map is an isometry κ : L²([0, L], dx) → L²([λ^{−1}, λ], d∗u),
    κ(f)(u) = f(log(λu))    (3.17)
(ii) Let f, g ∈ C^∞([0, L]). One has
    QW(κ(f), κ(g)) = Ψ♯(F),   F(u) = q(f, g)(log u).    (3.18)" [p. 7]
"Let V_n : [λ^{−1}, λ] → C be the function κ(U_n), i.e.
    V_n(u) := U_n(log(λu)),  ∀u ∈ [λ^{−1}, λ]    (3.21)" [p. 8]
"In particular, the lower bound of QW_λ is the limit, when N → ∞, of the smallest eigenvalue of the restriction of QW_λ to the
linear span E_N of the functions V_k with |k| ≤ N." [p. 8, after Prop. 3.4]
Used by us for: V_n = κ(U_n) is the orthonormal basis "modes −m..m"; the N → ∞ (fixed λ) limit is the paper's own approximation order.

---

## Definition: the truncated form QW_λ^N, the distribution 𝒟, and the matrix τ_{n,m} — pp. 15-16, §5.1 "Truncation of QW_λ" (eq. (5.1))
VERBATIM:
"Let λ > 1, L = 2 log λ, U_n as defined in (2.6) and V_n = κ(U_n) the orthonormal basis of L²([λ^{−1}, λ], d∗u) given in (3.21).
Let N ∈ N, we consider the quadratic form QW_λ^N obtained by restricting the Weil quadratic form QW_λ to the finite dimensional
space of test functions spanned by the functions V_n for |n| ≤ N.
By (3.18), the matrix elements of T = QW_λ^N in the basis V_n are given by
    τ_{n,m} = ∫_0^L q(U_n, U_m)(y) 𝒟(y)      i, j ∈ {−N, . . . , N}    (5.1)
where 𝒟 is the real distribution 𝒟 = log_*(Ψ♯) on the interval [0, L]." [p. 15 / top of p. 16]
READER NOTE: the label "i, j ∈ {−N, . . . , N}" next to a formula written with n, m is as printed (index letters not unified in the paper).
Related, p. 11, Lemma 4.1 (4.2): W♯_{0,2}(V_n, V_m) = 32 L sinh²(L/4) (L² − 16π²mn) / ((L² + 16π²m²)(L² + 16π²n²)) (no extra factor 2; the "2" that
pdftotext shows in front of the fraction is a layout artefact, image checked); (4.3): Σ W_p(V_n, V_m) = Σ_{1<k≤exp(L)} Λ(k) k^{−1/2} q(U_n, U_m)(log k);
(4.4): W_R(V_n, V_m) = (ω(0)/2)(γ + log(4π (e^L−1)/(e^L+1)))-type closed form plus ∫_0^L (exp(x/2) ω(x) − ω(0))/(exp(x) − exp(−x)) dx, ω(x) = q(U_n, U_m)(x).
Used by us for: the definition of "the literal CCM finite matrix". N is a free parameter here; nothing in the paper ties N to λ.

---

## Lemma 5.1 (structure of the matrix τ) — p. 16, §5.1/5.2 "Truncation of QW_λ"
VERBATIM:
"Lemma 5.1. The matrix τ_{n,m} is a real symmetric matrix of the form
    τ_{i,i} = a_i,  ∀i,      τ_{i,j} = (b_i − b_j)/(i − j),  ∀j ≠ i;      i, j ∈ {−N, . . . , N}    (5.2)
where the real scalars a_i fulfill a_{−j} = a_j and b_{−j} = −b_j for all j ∈ {−N, . . . , N}.
Proof. This follows from the computation of the functions q(U_n, U_m)(y) for y ∈ [0, L] in (2.8) and (2.10), which gives for n ≠ m
    τ_{n,m} = ∫_0^L (sin(2πmy/L) − sin(2πny/L)) / (π(n − m)) 𝒟(y)  ⟹
    b_n = −(1/π) ∫_0^L sin(2πny/L) 𝒟(y)
and for n = m,
    τ_{n,n} = 2 ∫_0^L (1 − y/L) cos(2πny/L) 𝒟(y) = a_n"
Used by us for: (i) the displacement structure (i − j)τ_ij = b_i − b_j, hence b_n = n·τ_{n,0} (b_0 = 0 by oddness) as in parity_residue_probe.py:23;
(ii) a even / b odd, which is what makes K commute with the reflection and puts β in the odd sector.

---

## Lemma 5.2 (grading γ and the commutator DT − TD) — p. 16, §5.2 "Properties of truncated matrices"
VERBATIM:
"In this section we let N be a positive integer, E_N be the Hilbert space with orthonormal basis {V_n, n ∈ {−N, . . . , N}} and T a
real symmetric matrix of the form (5.2). We recall the basic properties of [7] for matrices of this form.
Lemma 5.2. (i) Let γ such that γ(V_j) := V_{−j} ∀j ∈ {−N, . . . , N}. One has γ² = id and Tγ = γT.
(ii) Let D be defined by D(V_n) := n V_n for all n ∈ {−N, . . . , N}. One has Dγ = −γD and
    DT − TD = |β⟩⟨η| − |η⟩⟨β|,    β = Σ b_j V_j,   η = Σ V_j.    (5.3)
Proof. (i) One has q_{−i,−j} = q_{i,j} for all i, j ∈ {−N, . . . , N}.
(ii) The diagonal elements of the diagonal matrix D are antisymmetric which gives Dγ = −γD. Let us prove (5.3). One has
    (DT)_{i,j} = iτ_{i,j},  (TD)_{i,j} = jτ_{i,j}
so that (DT − TD)_{i,j} = (b_i − b_j) for all i, j ∈ {−N, . . . , N}. Similarly one has
    (|β⟩⟨η|)_{i,j} = |β⟩_i ⟨η|_j = b_i,  (|η⟩⟨β|)_{i,j} = |η⟩_i ⟨β|_j = b_j
which gives the required equality."
Used by us for: parity split (E = +1 eigenspace of γ, O = −1 eigenspace), η = all-ones vector = Σ V_j (unnormalised, ‖η‖² = 2N + 1), and the
rank-two commutator that is the only structural input to the even/odd Schur/Cramer identities (4.8)-(4.9) of PARITYSPLIT.
READER NOTE: the paper's proof of (i) writes q_{−i,−j} = q_{i,j} without defining q_{i,j}; read it as q(U_i, U_j) = q(U_{−i}, U_{−j}) (checked from (2.9)).

---

## Definition 5.3 and the normalisation argument — p. 16 (Def. 5.3) and p. 17 (eq. (5.4)), §5.2
VERBATIM:
"Definition 5.3. A real symmetric matrix T commuting with the Z/2-grading γ is even-simple if its smallest eigenvalue is simple and the
corresponding eigenvector ξ satisfies γξ = ξ." [p. 16]
"We now assume that T is even simple and positive and let ξ ∈ ker T, ξ ≠ 0. The real symmetric positive matrix T defines an inner product on
R^{2N+1} and its radical consists of the one dimensional subspace generated by ξ. Let us first show that we can normalize ξ by the condition
    ⟨ξ | η⟩ = 1    (5.4)
If Dξ = 0 then V_0 ∈ ker T fulfills (5.4). So we can assume that Dξ ≠ 0. One has TDξ ≠ 0 since Dξ is odd and linearly independent of ξ
while ker T is one-dimensional. By (5.3) one has
    0 ≠ (DT − TD)(ξ) = |β⟩⟨η|ξ⟩ − |η⟩⟨β|ξ⟩ = |β⟩⟨η|ξ⟩.
Thus one can normalize ξ so that ⟨η|ξ⟩ = 1." [p. 17]
Used by us for: "even-simple" = the paper's name for G1a (see crosswalk (c)); (5.4) is the paper's proof that η·ξ_0 ≠ 0 (the eta-normalisation) and
that the centre mode V_0 has ⟨V_0|η⟩ = 1.
CAVEAT: the argument assumes "ker T is one-dimensional" (simplicity is a hypothesis, not derived). It gives η·ξ ≠ 0 only; it says nothing about the SIGN
of η·ξ relative to ξ_0.

---

## Lemma 5.4 (TDξ = −β; selfadjoint D''; determinant (5.5)) — pp. 17-18, §5.2
VERBATIM:
"Lemma 5.4. Assume T ≥ 0 and Ker T = Cξ where γξ = ξ and ⟨ξ | η⟩ = 1.
(i) One has T D ξ = −β.
(ii) The operator D′ := D − |D ξ⟩⟨η| induces a selfadjoint operator D” in the Hilbert space associated to the inner product defined by T, as quotient by null vectors.
(iii) One has, denoting by ξ_j the components of ξ,
    Det(D” − s) = Det(D − s) Σ_{j=−N}^{N} (j − s)^{−1} ξ_j.    (5.5)
Proof. (i) We apply (5.3) and get, using Tξ = 0 and ⟨β|ξ⟩ = 0 since the two eigenspaces of γ are orthogonal,
    −T D ξ = (D T − T D)ξ = |β⟩⟨η|ξ⟩ − |η⟩⟨β|ξ⟩ = β."
(Proofs of (ii) and (iii) occupy pp. 17-18 and are NOT quoted here. The statement of (iii) is as above; in the proof of (ii) the paper closes with
"D” is selfadjoint by (7.3)" (p. 18) — the label (7.3) is, in this PDF, the Hermite operator H_f(u) := −f″(u) + 4π²u² f(u) on p. 28, so this cross-reference is a misprint
for (5.6); the algebra of (5.6) on p. 17 is what is used.)
Used by us for: TDξ = −β is the identity linking the ground vector to the odd vector β; (5.5) is the paper's "Stieltjes-type" function Σ ξ_j/(j − s)
for the spectrum of the diagonal D (poles at the integers j = −N..N), NOT the resolvent function g_m(t) = ⟨η,(K − t)^{-1}e_0⟩ of our request.

---

## Definition: Dirichlet kernel and δ_N — p. 19 (eq. (5.8)) and p. 20 (Cor. 5.6, eq. (5.15)), §5.3
VERBATIM:
"The Dirichlet kernel approximates the Dirac delta function as N → ∞. It is
    D_N(x) = Σ_{n=−N}^{N} exp(2πinx/L),  ∀x ∈ [0, L]    (5.8)" [p. 19]
"Corollary 5.6. Let V_n(u) := U_n(log(λu)) as in (3.21), D_log^{(λ)} be the scaling operator with periodic boundary conditions in L²([λ^{−1}, λ], d∗u)
and f ∈ Dom D_log^{(λ)}.
    lim_{N→∞} ⟨δ_N | f⟩ = f(λ),   δ_N := (1/√L) Σ_{n=−N}^{N} V_n    (5.15)
Proof. This follows from Lemma 5.5 using the isometry κ of (3.17) to pass from L²([λ^{−1}, λ], d∗u) to L²([0, L], dx), and the equality
    D_N = (1/√L) Σ_{n=−N}^{N} U_n
which follows from (5.8) and (2.6)." [p. 20]
Used by us for: δ_N = L^{−1/2} η (the paper says so itself on p. 24: "One has δ_N = L^{−1/2} η by Corollary 5.6"). The evaluation property is a LIMIT statement (N → ∞,
f ∈ Dom D_log^{(λ)}).

---

## Proposition 5.9 (Fourier transform of ξ, eq. (5.25)) — pp. 22-23, §5.6 "Spectrum and regularized determinant of D_log^{(λ,N)}"
VERBATIM:
"We first compute the Fourier transform of functions on [λ^{−1}, λ] extended by 0 to R∗_+. The Fourier transform for the duality ⟨R∗_+ | R⟩ is defined by
    F_μ(f)(s) := ∫_{R∗_+} f(u) u^{−is} d∗u.
Proposition 5.9. Let λ > 1, L = 2 log λ, N ∈ N, ξ_j ∈ C for j ∈ {−N, . . . , N},
    ξ(u) := Σ_{k∈{−N,...,N}} ξ_k V_k(u), ∀u ∈ [λ^{−1}, λ],   ξ(u) = 0, ∀u ∉ [λ^{−1}, λ].
The Fourier transform ξ̂ = F_μ(ξ) is the entire function given by
    ξ̂(z) = 2 L^{−1/2} sin(zL/2) ( Σ_{j∈{−N,...,N}} ξ_j / (z − 2πj/L) ).    (5.25)" [p. 22]
"Proof. One has for k ∈ Z, using x = log(λu), u^{−is} = λ^{is} exp(−isx), d∗u = dx,
    ∫_{λ^{−1}}^{λ} V_k(u) u^{−is} d∗u = ∫_{λ^{−1}}^{λ} U_k(log(λu)) u^{−is} d∗u =
    = L^{−1/2} λ^{is} ∫_0^L exp(2πikx/L) exp(−isx) dx = −i (1 − e^{−isL}) / (s − 2πk/L) · L^{−1/2} e^{isL/2}.
Thus the Fourier transform of ξ(u) is
    ξ̂(z) = 2 L^{−1/2} sin(zL/2) ( Σ_{{−N,...,N}} ξ_j / (z − 2πj/L) ).
The zeros z ∈ 2πZ/L of sin(sL/2) cancell the poles at 2πj/L which occur when ξ_j ≠ 0 and remain as zeros of ξ̂(z) otherwise." [p. 23]
Related (p. 23-24, proof of Thm 5.10): "the normalization of ξ given by δ_N(ξ) = 1 differs from ⟨ξ′ | η⟩ = 1. One has δ_N = L^{−1/2} η by Corollary 5.6 thus giving
ξ′ = L^{−1/2} ξ." and, with λ^{−iz} = exp(−izL/2): "det_reg(D_log^{(λ,N)} − z) = −i λ^{−iz} ξ̂(z)" (Thm 5.10 (ii), see CCM_ZST_USAGE_CARDS.md).
Used by us for: (5.25) holds for ARBITRARY complex ξ_j (no evenness, simplicity or positivity hypothesis). The only bridge to our identities is the value at z = 0:
ξ̂(0) = L^{1/2} ξ_0 (derived by the reader from (5.25), and directly from ∫ V_k d∗u = L^{1/2} δ_{k0}).

---

## The paper's own statement of "even" and of E_N — p. 2 (§1) and p. 20, p. 16
VERBATIM:
"This construction is based on the restriction QW_λ^N of the Weil quadratic form to the linear space E_N = E_N(λ) of test functions spanned by the 2N + 1 eigenfunctions
of D_log^{(λ)} associated to the 2N + 1 eigenvalues of smallest absolute value (i.e. ≤ Nπ/ log λ), extended by 0 outside the interval [λ^{−1}, λ]. We need to verify that the
smallest eigenvalue ϵ_N of QW_λ^N is simple and that the corresponding eigenfunction is "even" i.e. invariant under the symmetry u ↦ u^{−1}. We let δ_N ∈ E_N be the vector
representing the Dirichlet kernel, as an approximation to the evaluation on the boundary of the interval [λ^{−1}, λ]." [p. 2]
"Proposition 5.7. Let λ > 1 and N such that the truncated Weil quadratic form is even simple. Let ξ be the corresponding even eigenvector. There exists a unique operator
D_log^{(λ,N)} with the same domain as D_log^{(λ)} which agrees with this operator on the kernel of δ_N and such that D_log^{(λ,N)}(ξ) = 0." [p. 20]
Numerical regime of the paper (p. 25, §6): "The first case is λ = 3 and one takes N = 120." and "We then consider the first fifty zeros of zeta, use still N = 120 and the values of λ
given by λ = √12 ∼ 3.4641, λ = √13 ∼ 3.60555, λ = √14 ∼ 3.74166."
Used by us for: the paper's "even" is "invariant under u ↦ u^{−1}"; on the basis, V_n(u^{−1}) = V_{−n}(u), i.e. γ of Lemma 5.2 (checked: x = log(λu) ↦ L − x).

---
---

# Crosswalk to STIELTJES (REQ-2026-10-29-STIELTJES)

Our objects (locators at the repo state of this file):
- Request: docs/routeB_bus/proshka/PROSHKA_REQUEST_STIELTJES_2026-10-29.txt, §0 lines 22-82 (N1 29-34, N2 36-42, N3 44-51, N4 53-67, N5 69-82).
- Matrix: docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py:10-39 (`matrix_K`).
- Parity bases: docs/routeB_bus/thetagrade_2026-10-28/parity_gap_table.py:35-45 (`parity_bases`); η all-ones stated at line 6.
- Probe: docs/routeB_bus/thetagrade_2026-10-28/parity_residue_probe.py:23-24 (b, displacement), 32-33 (beta_o, d), 63-67 (h, e0, w_i).
- Lean twins: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean:51 (`ccmEtaFinite` = all ones), :56 (`ccmDeltaFinite` = L^{−1/2}·η),
  CCMFiniteWeilSourceMatrixN1.lean (`ccmQKernel`, `ccmW02Entry`, `ccmWREntry`, `ccmWeilTauN1`), CCMFiniteWeilEtaNonzero.lean (cites Lemma 5.2, Def. 5.3, p. 17 argument).

Checks I ran for this crosswalk (read-only; scripts in the session scratchpad, not in the repo; mpmath dps 40, cells m = 3, 4, 5, entries of the literal `matrix_K`):
| check | result |
|---|---|
| K symmetric; K[−i,−j] = K[i,j] (Lemma 5.2(i), Lemma 5.1 a_{−j} = a_j) | max deviation 0 (exact) on all three cells |
| b_n := n·K[n,0] is odd (b_{−n} = −b_n) | max deviation 0 |
| displacement (i − j)K_ij = b_i − b_j, i ≠ j (Lemma 5.1) and (5.3) DK − KD = |β⟩⟨η| − |η⟩⟨β|, all i, j | ≤ 2.3e-41 (m = 3, 4, 5) |
| E-O off-diagonal block Eᵀ K O | exactly 0 |
| independent recomputation of 20 entries per cell (n ∈ {−m,0,1,m}, j ∈ {−m,−1,0,2,m}) from (2.9), (2.10), (3.10), (3.13)-(3.16) with prime sum k ≤ exp(L) = m | max abs difference 2.5e-17 (m=3), 2.6e-17 (m=4), 4.2e-17 (m=5); error floor is my quadrature near y = 0 (removable singularity), not the matrix |
| h = (1, √2, …, √2) equals Eᵀη (E = `parity_bases`) | 2.3e-41 |
| g(t) := ⟨η,(K − t)^{-1}e_0⟩ = hᵀ(E_blk − t)^{-1}e_0 = det(O_blk − t)/det(E_blk − t), t = −1/7 | all three agree to 10 printed digits (m=3: 1.806446579; m=4: 2.416657651; m=5: 1.91911822) |
| Lemma 5.4 on the literal K, T = K − λ_min, ξ even, ⟨ξ\|η⟩ = 1: (i) TDξ + β; (ii) T D′ symmetric, D′ξ = 0; (iii) Det(D′ − s) = −s·Det(D − s)·Σ ξ_j/(j − s) at s = 0.37 + 0.21i | ≤ 2e-34 (m = 3, 4); λ_min = 1.0045504e-6 (m=3), 1.6995356e-9 (m=4), both even |
| sign link: m=3: η·ξ_unit = 3.166e-3, ξ'_0 (⟨ξ\|η⟩ = 1 normalisation) = +243.79; m=4: η·ξ_unit = −1.560e-4, ξ'_0 = +4603.8 | w_0 = (η·ξ_unit)ξ_unit(0) = +2.444e-3, +1.12e-4 (agrees with the request table) |

### (a) Matrix entries in our code vs Lemma 5.1 — MATCH
- Paper: Lemma 5.1 (5.2), p. 16: τ_{i,i} = a_i, τ_{i,j} = (b_i − b_j)/(i − j), a even, b odd; entries from (2.9)-(2.10), (3.10), (3.13)-(3.16), (4.2)-(4.4) (pp. 4, 6-7, 11-12).
- Ours: full_center_probe.py:12-14 (q), :28-30 (moments and diagonals, i.e. W_R integrals), :31 (constant = γ + log(4π tanh(L/2)) = the explicit tail ∫_L^∞ of (3.15) combined with ½(log 4π + γ)q(0)),
  :35 (W_{0,2} closed form = (4.2)), :36 (W_R), :37 (primes k = 2..m with Λ(k)k^{−1/2}q(log k) = (4.3)), :38 (K = W_{0,2} − W_R − primes = (3.10)).
- Checked symbol by symbol: q kernels, the sign pattern in (3.10), the factor ½ in (3.15), (4.2) without extra factor 2, prime range 1 < k ≤ exp(L), moments/diagonal in (4.4); and numerically (table above).
  The probe's b_n = n·K[n,0] (parity_residue_probe.py:23) is legitimate because Lemma 5.1 gives b_0 = 0.
- One non-paper choice built into the matrix: `L = log(m)` and N = m (full_center_probe.py:11), i.e. λ² = e^L = m = N. The paper keeps λ and N independent; see (d).

### (b) Normalisation of η / h and δ_N — MATCH for η, h, e_0 (our objects use η, not δ_N); the paper's δ_N differs from η by the explicit constant L^{−1/2}
- Paper: η = Σ V_j (5.3), p. 16, unnormalised (‖η‖² = 2N+1); ⟨ξ|η⟩ = 1 (5.4) in Lemma 5.4 (p. 17); δ_N = L^{−1/2}η (5.15) p. 20 and used with δ_N(ξ) = 1 in Thm 5.10, so ⟨η|ξ⟩ = L^{1/2} there (the paper itself flags the difference, p. 24 "differs from ⟨ξ′|η⟩ = 1"; ξ′ = L^{−1/2}ξ).
- Ours: η = all ones (CCMFiniteWeilSourceMatrix.lean:51; parity_gap_table.py:6); h = Eᵀη = (1, √2, …, √2) (parity_residue_probe.py:63; request line 25); e_0 = V_0 with η·e_0 = 1, which is exactly the paper's "⟨V_0|η⟩ = 1" (p. 17), hence Σ w_i = 1 (request N3).
- Consequences: (1) with L = log m, δ_N = (log m)^{−1/2}η; any statement quoted from Thm 5.10 under "δ_N(ξ) = 1" means Σξ_j = L^{1/2}, not 1; the factor is positive, so no sign in N1–N5 changes. (2) The request calls η the "endpoint functional" (lines 59-60, 174). That is exact at finite N for the trigonometric polynomial ξ = Σξ_kV_k: V_k(λ) = V_k(λ^{−1}) = L^{−1/2}, so η·ξ = L^{1/2}·ξ(λ) (derived from (3.21); not stated in the paper). The paper's evaluation statement (Cor. 5.6) is only the N → ∞ limit for f ∈ Dom D_log^{(λ)}.
- Our w_i uses unit-norm eigenvectors; the paper's ξ is normalised by ⟨ξ|η⟩ = 1. With c = η·ξ_unit (≠ 0 by the p. 17 argument), ξ′ = ξ_unit/c, so w_0 = c²·ξ′_0 and sign(w_0) = sign(ξ′_0) (centre coefficient in the paper's normalisation; checked on m = 3, 4 above). Via (5.25), ξ̂(0) = L^{1/2}ξ_0, hence w_0 = ξ_unit(λ)·ξ̂_unit(0) (endpoint value times integral of ξ). All this is derived here; the paper states none of it.

### (c) The paper's even/odd symmetry vs our parity split — MATCH (plus one derived equivalence)
- Paper: γ(V_j) = V_{−j}, Tγ = γT (Lemma 5.2(i), p. 16); Dγ = −γD (5.2(ii)); even = γξ = ξ (Def. 5.3, p. 16) = "invariant under u ↦ u^{−1}" (p. 2); V_n(u^{−1}) = V_{−n}(u).
- Ours: E = span{V_0, (V_n + V_{−n})/√2}, dim m + 1; O = span{(V_n − V_{−n})/√2}, dim m (parity_gap_table.py:35-45). Eᵀ K O = 0 exactly (table). β = Σ b_jV_j lies in O, β_o = (√2 b_n)_{n=1..m} (parity_residue_probe.py:32) matches b odd; D maps O → E with D(V_n − V_{−n})/√2 = n(V_n + V_{−n})/√2, consistent with Dγ = −γD; d_n = √2/n = (B^{−1}h)_n is Proshka's notation (not in the paper).
- The paper defines no blocks E/O and no dimension count; those are our decomposition of the +1/−1 eigenspaces of γ.
- Derived (not in the paper): G1a (λ_min(E) < λ_min(O)) ⟺ T = K is even-simple in the sense of Def. 5.3. (⟸) a second bottom eigenvector in O would contradict simplicity. (⟹) bottom eigenspace S ⊂ E (odd part of a bottom vector would be an odd eigenvector at the bottom, impossible if μ > λ_min(E)); if dim S ≥ 2 pick ξ ∈ S with η·ξ = 0; then (5.3) with Tξ = 0 and β·ξ = 0 (β odd, ξ even) gives TDξ = 0, so Dξ ∈ S is even and odd, Dξ = 0, ξ ∝ V_0, η·ξ = ξ_0 ≠ 0, contradiction. This agrees with PARITYSPLIT (4.5)-(4.6) (docs/routeB_bus/proshka/PROSHKA_VERDICT_PARITYSPLIT_2026-10-28.md:515-523) and goes one step beyond the paper's p. 17 argument, which assumes ker T one-dimensional.

### (d) What Prop. 5.9 / (5.25) and Thm 5.10 silently carry that N1–N5 assume or do not have — MISMATCH (regime) and NOT DETERMINABLE (content of N3–N5)
1. N1–N5 never use (5.25) (no Fourier transform, no ξ̂, no zeros of ξ̂). (5.25) is an identity for arbitrary ξ_j ∈ C and needs no hypothesis. The only bridge is ξ̂(0) = L^{1/2}ξ_0 (see (b)). Therefore nothing in Prop. 5.9 supports or contradicts N3, N4(a)-(d), N5.
2. What the chain G1a → Thm 5.10 does need is exactly the hypothesis block of Thm 5.10 (p. 23): "ϵ_N ... simple" and "ξ ... even" = Def. 5.3 = G1a by (c). The paper does not prove it for QW_λ; CCM §8 (p. 32, card in CCM_ZST_USAGE_CARDS.md) lists it as missing step 1. NOT DETERMINABLE from the paper whether it holds for any m.
3. Nothing in CCM concerns: f_m = 1/g_m with g_m(t) = ⟨η,(K − t)^{-1}e_0⟩ = det(O − t)/det(E − t) (N3); Stieltjes weights w_i = (η·ξ_i)ξ_i(0) and Σ w_i = 1 (N3); Abel sums W_k, interlacing of even/odd spectra (N4(c),(d)); the sign of w_0 or of ξ_0 (N4(b)); the alternation pattern (N5). The paper's nearest object is (5.5), Σ ξ_j/(j − s) with poles at the integers (the spectrum of D), a different function. The N3 determinant identity was re-checked numerically here (m = 3, 4, 5) but it is our algebra (Proshka (4.8)-(4.9) plus Cramer), only structurally rooted in (5.3). NOT DETERMINABLE from the paper.
4. MISMATCH of regime: the paper's identities (Lemma 5.1-5.4, Prop. 5.9, Thm 5.10) hold for every λ > 1 and every N ∈ N, with λ and N independent; its convergence/approximation statements are N → ∞ at fixed λ first (p. 8, after Prop. 3.4) and then N, λ → ∞ (abstract), and its numerics (p. 25) use N = 120 at λ = 3 and λ = √12..√14 (N/λ² between about 8.6 and 13). Our cells are the diagonal N = m, λ² = m (full_center_probe.py:11), i.e. N/λ² = 1. The matrices are exactly CCM's finite matrices at (λ, N) = (√m, m), so identities N1–N5 are legitimate cell facts, but no CCM statement about approximation of zeta zeros or about "N large" transfers to this schedule without an extra argument. The request's phrase "original schedule" is ours, not the paper's.
5. A convention trap for any future quote: Thm 5.10 normalises by δ_N(ξ) = 1 (Σξ_j = L^{1/2}), Lemma 5.4 and (5.5) by ⟨ξ|η⟩ = 1 (Σξ_j = 1), our w_i by ‖ξ‖ = 1. Mixing them changes (5.5) and (5.25) by the factor L^{±1/2} and, for the unit normalisation, by c² (c as in (b)).
Pieces I am not certain of (all in the Verbatim part): none of the displayed formulas needed [illegible]; the only text-layer vs image conflict was the spurious "2" before (4.2) (resolved by the image, p. 11), and the exact position of "L^{−1/2}e^{isL/2}" in the proof of Prop. 5.9 (read from the image: it follows the fraction).
