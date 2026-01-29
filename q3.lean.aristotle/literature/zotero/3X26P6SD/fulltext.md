---
title: "Hamiltonian for the zeros of the Riemann zeta function"
authors:
  - "Carl M. Bender"
  - "Dorje C. Brody"
  - "Markus P. M\u00fcller"
date: "2017-00-00 2017"
publication: "Physical Review Letters"
doi: "10.1103/PhysRevLett.118.130201"
url: null
zotero:
  attachment_key: "3S7TIVMP"
  parent_key: "3X26P6SD"
  item_id: 1961
  attachment_item_id: 1986
---

Hamiltonian for the Zeros of the Riemann Zeta Function
Carl M. Bender,1 Dorje C. Brody,2,3 and Markus P. Müller4,5
1Department of Physics, Washington University, St. Louis, Missouri 63130, USA 2Department of Mathematics, Brunel University London, Uxbridge UB8 3PH, United Kingdom 3Department of Optical Physics and Modern Natural Science, St. Petersburg National Research University of Information Technologies, Mechanics and Optics, St. Petersburg 197101, Russia 4Departments of Applied Mathematics and Philosophy, University of Western Ontario, Middlesex College, London, Ontario N6A 5B7, Canada 5The Perimeter Institute for Theoretical Physics, Waterloo, Ontario N2L 2Y5, Canada
(Received 23 September 2016; revised manuscript received 17 February 2017; published 30 March 2017)
A Hamiltonian operator Hˆ is constructed with the property that if the eigenfunctions obey a suitable boundary condition, then the associated eigenvalues correspond to the nontrivial zeros of the Riemann zeta function. The classical limit of Hˆ is 2xp, which is consistent with the Berry-Keating conjecture. While Hˆ is not Hermitian in the conventional sense, iHˆ is PT symmetric with a broken PT symmetry, thus allowing for the possibility that all eigenvalues of Hˆ are real. A heuristic analysis is presented for the construction of the metric operator to define an inner-product space, on which the Hamiltonian is Hermitian. If the analysis presented here can be made rigorous to show that Hˆ is manifestly self-adjoint, then this implies that the Riemann hypothesis holds true.
DOI: 10.1103/PhysRevLett.118.130201
The Riemann zeta function ζðzÞ is conventionally represented as the sum or the integral
ζðzÞ 1⁄4 ∞ X
k1⁄41
1
kz 1⁄4 1
ΓðzÞ
Z∞
0
dt tz−1
et − 1 :
(The integral reduces to the sum if the denominator of the integrand is expanded in a geometric series.) Both representations converge and define ζðzÞ as an analytic function when ReðzÞ > 1. These representations diverge when z 1⁄4 1 because the zeta function has a simple pole at z 1⁄4 1. Substituting z 1⁄4 −2n (n 1⁄4 1; 2; 3; ...) in the reflection formula
ζðzÞ 1⁄4 2zπz−1 sinðπz=2ÞΓð1 − zÞζð1 − zÞ
shows that the zeta function vanishes when z is a negativeeven integer. These zeros of ζðzÞ are called the trivial zeros. The Riemann hypothesis [1] states that the nontrivial zeros of ζðzÞ lie on the line ReðzÞ 1⁄4 1
2. This hypothesis has
attracted much attention for over a century because there is a deep connection with number theory and other branches of mathematics. However, the hypothesis has not been proved or disproved. Any advance in understanding the
zeta function would be of great interest in mathematical science, whether or not one succeeds in finally proving or falsifying the hypothesis. In this Letter, we examine the Riemann hypothesis by
constructing and studying an operator Hˆ that plays the role of a Hamiltonian. The conjectured property of Hˆ is that its eigenvalues are exactly the imaginary parts of the nontrivial zeros of the zeta function. The idea that the imaginary parts of the zeros of ζðzÞ might correspond to the eigenvalues of a Hermitian, self-adjoint operator (assuming the validity of the Riemann hypothesis) is known as the Hilbert-Pólya conjecture. Research into this connection has intensified following the observation that the spacings of the zeros of the zeta function on the line ReðzÞ 1⁄4 1
2 and the spacings of the eigenvalues of a Gaussian unitary ensemble of Hermitian random matrices have the same distribution [2–4]. Berry and Keating conjectured that the classical counterpart of such a Hamiltonian would have the form H 1⁄4 xp [5,6]. However, a Hamiltonian possessing this property has hitherto not been found (see [7] for a detailed account of the Berry-Keating program and its extensions). We propose and consider the Hamiltonian
Hˆ 1⁄4 1
1 − e−ipˆ ðˆx ˆp þ ˆp xˆÞð1 − e−i ˆpÞ: ð1Þ
Our main findings are as follows. (i) The non-Hermitian
Hamiltonian Hˆ in (1) formally satisfies the conditions of the Hilbert-Pólya conjecture. That is, if the eigenfunctions of Hˆ are required to satisfy the boundary condition ψnð0Þ 1⁄4 0 for all n, then the eigenvalues fEng have the
Published by the American Physical Society under the terms of the Creative Commons Attribution 4.0 International license. Further distribution of this work must maintain attribution to the author(s) and the published article’s title, journal citation, and DOI.
PRL 118, 130201 (2017) P H Y S I C A L R E V I E W L E T T E R S week ending
31 MARCH 2017
0031-9007=17=118(13)=130201(5) 130201-1 Published by the American Physical Society


 property that f1
2 ð1 − iEnÞg are the nontrivial zeros of the
Riemann zeta function. (ii) The Hamiltonian Hˆ reduces to the classical Hamiltonian H 1⁄4 2xp when ˆx and ˆp commute, in agreement with the Berry-Keating conjecture. We derive the corresponding boundary condition that leads to the quantization of the Berry-Keating Hamiltonian ˆhBK 1⁄4 xˆ ˆp þ ˆp ˆx. (iii) Although Hˆ is not Hermitian, iHˆ is PT symmetric; that is, iHˆ is invariant under parity-time reflection (in the sense to be defined), which means that the eigenvalues of iHˆ are either real or else occur in complex-conjugate pairs. If iHˆ has maximally broken PT symmetry—that is, if all of its eigenvalues are pureimaginary complex-conjugate pairs—then the eigenvalues of Hˆ are real and the Riemann hypothesis follows. (iv) While Hˆ is not Hermitian (symmetric) with respect to the conventional L2 inner product, we introduce an alternative inner product such that hHˆ φ; ψi 1⁄4 hφ; Hˆ ψi for all φðxÞ and ψðxÞ belonging to the linear span of the eigenstates of Hˆ . (v) If the Riemann hypothesis is correct, then the eigenvalues of Hˆ are nondegenerate, and conversely if there are nontrivial roots of ζðzÞ for which ReðzÞ ≠ 1
2, then the corresponding eigenvalues and eigenstates are both degenerate.
Preliminaries.—The Hamiltonian Hˆ in (1) is a similarity transformation of the formally Hermitian local Hamiltonian ˆx ˆp þ ˆp xˆ via the nonlocal operator ˆΔ ≔ 1 − e−i ˆp. We must therefore identify properties of the operators Δˆ and Δˆ −1. We work in units for which ħ 1⁄4 1, so the momentum operator is ˆp 1⁄4 −i∂x. Thus, e−ipˆ is a shift operator if it acts on functions fðxÞ that have a Taylor series about x with a radius of convergence greater than one. In this case, Δˆ is a difference operator:
Δˆ fðxÞ 1⁄4 fðxÞ − fðx − 1Þ: ð2Þ
Because ˆΔ annihilates unit-periodic functions, it does not have an inverse in the space of all smooth functions. However, we shall be interested in functions that vanish as x → ∞. With this in mind, by taking a series expansion of ð1 − e−ipˆ Þ−1 we may define Δˆ −1 as (cf. [8])
Δˆ −1fðxÞ 1⁄4 1
i ˆp
X ∞
n1⁄40
Bn
ð−i ˆpÞn
n! fðxÞ; ð3Þ
where fBkg are the Bernoulli numbers [9], with the convention that B1 1⁄4 − 1
2. For some functions fðxÞ this formal series diverges but it is Borel summable. The operator ði ˆpÞ−1 is interpreted as an integral operator with a boundary at infinity:
1
i ˆp gðxÞ 1⁄4
Zx
∞
dt gðtÞ:
Then Δˆ −1 defined in (3) has the property that if fðxÞ vanishes at infinity, then we have Δˆ −1 ˆΔfðxÞ 1⁄4 fðxÞ.
Eigenfunctions and eigenvalues.—The solutions to the
eigenvalue differential equation Hˆ ψ 1⁄4 Eψ are given in terms of the Hurwitz zeta function ψzðxÞ 1⁄4 −ζðz; x þ 1Þ on
the positive half line Rþ (the negative sign is our convention), with eigenvalues ið2z − 1Þ. To see this, we multiply the eigenvalue equation Hˆ ψ 1⁄4 Eψ on the left by ˆΔ. This gives a first-order linear differential equation ðˆx ˆp þ ˆp ˆxÞΔˆ ψ 1⁄4 E ˆΔψ for the function ˆΔψ, whose solution is unique and is given by ˆΔψ 1⁄4 x−z for some z ∈ C, up to a multiplicative constant. To proceed, let us calculate
Δˆ −1x−z 1⁄4 1
i ˆp
∞ X
n1⁄40
Bn
ð−i ˆpÞn
n! ði ˆpÞ x1−z
1−z
1⁄41
1−z
X ∞
n1⁄40
Bn
ð−i ˆpÞn
n! x1−z:
Since i ˆp 1⁄4 ∂x and ∂xnxμ 1⁄4 1⁄2Γðμ þ 1Þ=Γðμ − n þ 1Þ xμ−n, we set μ 1⁄4 1 − z to obtain the asymptotic series
ˆΔ−1x−z ∼ Γð2 − zÞ
1−z
X ∞
n1⁄40
Bn
ð−1Þn n!
x1−z−n
Γð2 − z − nÞ ; ð4Þ
which is valid in the limit as x → ∞. To obtain the Borel sum [10] of the series, we use the integral representation
1
Γð2 − z − nÞ 1⁄4 1
2πi
Z
C
du euunþz−2;
where C denotes a Hankel contour that encircles the negative-u axis in the positive orientation [9]. Hence,
ˆΔ−1x−z 1⁄4 Γð1 − zÞ
2πi x1−z
Z
C
du euuz−2 X ∞
n1⁄40
Bn
ð−u=xÞn n!
1⁄4 Γð1 − zÞ
2πi x−z
Z
C
du euuz−1
1 − e−u=x :
Finally, we let u=x 1⁄4 t and get
Δˆ −1x−z 1⁄4 Γð1 − zÞ
2πi
Z
C
dt exttz−1
1 − e−t ;
which we recognize as the negative of the integral representation for the Hurwitz zeta function [9]. (An analogous result was obtained in a different context in [11].) It follows that ψzðxÞ 1⁄4 −ζðz; x þ 1Þ up to an additive unit-periodic
function, but Hˆ ψ 1⁄4 Eψ implies that the periodic function must be identically zero. We thus deduce that ψzðxÞ 1⁄4 −ζðz; x þ 1Þ is the solution to the eigenvalue differential equation with eigenvalue ið2z − 1Þ:
PRL 118, 130201 (2017) P H Y S I C A L R E V I E W L E T T E R S week ending
31 MARCH 2017
130201-2


 Hˆ ψzðxÞ 1⁄4 ˆΔ−1ðˆx ˆp þ ˆp xˆÞx−z 1⁄4 ið2z − 1ÞψzðxÞ:
Next, we impose the boundary condition that ψzð0Þ 1⁄4 0 on the class of functions ψzðxÞ that satisfy the eigenvalue differential equation. This yields a countable set of eigenfunctions of Hˆ . (Since Hˆ is similar to a first-order differential operator, we impose just one boundary condition.) The choice of the boundary condition ψzð0Þ 1⁄4 0, as discussed below, is motivated by our requirement that ˆp should be symmetric. Because −ψzð0Þ 1⁄4 ζðzÞ is the Riemann zeta function, the boundary condition that we have used implies that z must belong to the discrete set of zeros of ζðzÞ. The zeros of the Riemann zeta function may be either trivial or nontrivial. It follows from (4) that for the trivial zeros z 1⁄4 −2n (n 1⁄4 1; 2; 3; ...) we have ψzðxÞ 1⁄4 −B2nþ1ðx þ 1Þ=ð2n þ 1Þ, where BnðxÞ is a Bernoulli
polynomial [9]. In this case jψ zðxÞj grows like x2nþ1 as x → ∞. For the nontrivial zeros ψzðxÞ oscillates and jψzðxÞj grows sublinearly. In particular, it follows from
(4) that for large x we have ψ zðxÞ ≈ x1−z=ð1 − zÞ. Thus, for
the trivial zeros Δˆ ψzðxÞ blows up, but for the nontrivial
zeros Δˆ ψzðxÞ goes to zero as x → ∞. The eigenstates associated with the trivial zeros violate the orthogonality relation discussed below, and the eigenstates associated with the nontrivial zeros do not. These indicate that the eigenstates associated with the trivial zeros do not belong to the domain of Hˆ . Therefore, under the boundary condition ψð0Þ 1⁄4 0, the nth eigenstate of the Hamiltonian (1) is ψnðxÞ 1⁄4 −ζðzn; x þ 1Þ; the eigenvalues En 1⁄4 ið2zn − 1Þ
are discrete and zn 1⁄4 1
2 ð1 − iEnÞ are the nontrivial zeros of the Riemann zeta function. The Riemann hypothesis is valid if and only if these eigenvalues are real. The analysis above establishes a complex extended version of the Berry-Keating conjecture [12]. We are not
able to prove that the eigenvalues of Hˆ are real; nevertheless, in what follows we present a heuristic analysis that suggests that the eigenvalues are real. Specifically, we first investigate symmetry properties of Hˆ , which shows that iHˆ is PT symmetric and Hˆ is pseudo-Hermitian. This allows us to obtain a quantization of the Berry-Keating Hamiltonian ˆhBK 1⁄4 xˆ ˆp þ ˆp ˆx that is isospectral to Hˆ . We then make use of the biorthogonality properties of the eigenstates of Hˆ to introduce an inner product which makes Hˆ Hermitian. Relation to pseudo-Hermiticity.—To gain some intuition about the reality of the eigenvalues of the Hamiltonian, we
remark first that iHˆ is PT symmetric [13,14] in the following sense. Under conventional parity-time reflection, if ˆp is a momentum and xˆ is a coordinate, we have PT ∶ðxˆ; ˆpÞ → ð−ˆx; ˆpÞ. However, we consider instead the variables where the roles of position ˆx and momentum ˆp are interchanged [15]. We then define parity-time reflection as PT ∶ðˆx; ˆpÞ → ðxˆ; − ˆpÞ. Therefore, since PT ∶i → −i, we deduce that iHˆ is invariant under this modified PT
reflection. It follows that the eigenvalues of iHˆ are either real (if the PT symmetry is unbroken in the sense that the associated eigenstates are also eigenstates of PT ), or else they form complex-conjugate pairs (if the PT symmetry is broken in the sense that the associated eigenstates are not eigenstates of PT ). If the PT symmetry is maximally broken for iHˆ , then the eigenvalues of Hˆ would be real, and the Riemann hypothesis would hold. In our case, since PT ψnðxÞ 1⁄4 ψ−nðxÞ, the PT symmetry is indeed broken for all complex values of zn. (For the trivial zeros the PT symmetry is unbroken.) Let us now assume that the momentum operator ˆp is Hermitian (symmetric); that is, the action of ˆp† agrees with that of ˆp on the domain of Hˆ . Here † denotes the adjoint with respect to the standard inner product on L2ðRþÞ. Then the Hermitian adjoint of Hˆ is
Hˆ † 1⁄4 ð1 − ei ˆpÞðˆx ˆp þ ˆp xˆÞ 1
1 − ei ˆp : ð5Þ
Therefore, if we define the operator ηˆ according to
ηˆ 1⁄4 sin2 1
2 ˆp;
which is non-negative, bounded, and Hermitian under the assumption, we get Hˆ † 1⁄4 ˆηHˆ ηˆ−1; i.e., Hˆ is pseudo-Hermitian in the sense of [16]. Assuming that ˆp is Hermitian, there exists an associated Hermitian Hamiltonian ˆh obtained by conjugating Hˆ with an operator ρˆ satisfying ˆρ† ˆρ 1⁄4 ηˆ, that is, ˆρHˆ ρˆ−1 1⁄4 ˆh. Letting ˆρ 1⁄4 sin1
2 ˆp, we obtain ˆh 1⁄4 ˆx ˆpþ ˆpxˆ þħ ˆp.
We include Planck’s constant ħ explicitly here because it indicates that the linear momentum term is a quantum anomaly; this term vanishes in the classical limit ħ → 0 [15]. Alternatively, by letting ˆρ 1⁄4 Δˆ we obtain the BerryKeating Hamiltonian hˆ BK 1⁄4 ˆx ˆp þ ˆp xˆ, whose eigenstates are φzBKðxÞ 1⁄4 x−z.
The associated Hamiltonian ˆh is unique up to unitary transformations, so there are infinitely many formally Hermitian Hamiltonians that are similar to Hˆ [12]. If both ˆη and ηˆ−1 are positive, bounded, and Hermitian, then the Hamiltonians Hˆ and ˆh are isospectral [17]. Assuming that ˆp is Hermitian, these operators are indeed Hermitian and nonnegative, but ˆη−1 is not bounded. Nevertheless, we can show by a direct calculation that Hˆ and ˆh are in fact isospectral. Furthermore, since the map from the eigenstates fψnðxÞg of
Hˆ to the eigenstates fφnðxÞg of ˆh is governed by ˆρ, we can identify the quantization condition for the eigenstates of the associated Hamiltonians explicitly by using the relation 2i sin 1
2 ˆpψ zðxÞ 1⁄4 ψzðx þ 1
2Þ − ψ zðx − 1
2Þ. For the Berry
Keating Hamiltonian, the condition ψzð0Þ 1⁄4 0 leads to
lxi→m01⁄2φzBKðxÞ − ζðz; x − 1Þ 1⁄4 0;
or, equivalently, limx→1φzBKðxÞ 1⁄4 −limx→1ζðz; x þ 1Þ.
PRL 118, 130201 (2017) P H Y S I C A L R E V I E W L E T T E R S week ending
31 MARCH 2017
130201-3


 Biorthogonal states.—Let us proceed under the
assumption that ˆp is Hermitian. Because Hˆ is not Hermitian, its eigenstates fψnðxÞg are not orthogonal. Nevertheless, by considering the eigenstates fψ~ nðxÞg of
Hˆ † we obtain a biorthogonal set of eigenstates [17], provided that Hˆ † is the Hermitian adjoint of Hˆ . Bearing in mind that ˆΔ† is the forward difference operator, a calculation shows that ψ~ nðxÞ 1⁄4 x−zn − ðx þ 1Þ−zn and that
Hˆ †ψ~ nðxÞ 1⁄4 ið2zn − 1Þψ~ nðxÞ. Using fψ~ nðxÞg, we introduce an inner product on the space of functions spanned by
fψnðxÞg as follows. For any ψðxÞ 1⁄4 P
ncnψnðxÞ we define
its associated state by ψ~ ðxÞ 1⁄4 P
ncnψ~ nðxÞ. The inner product of a pair of such functions ψðxÞ and φðxÞ is then defined
by hφ; ψi 1⁄4 h ~φjψi ≔ R0∞ ~φðxÞψðxÞdx. Alternatively stated,
since ~φðxÞ 1⁄4 ηˆφðxÞ, we have hφ; ψi 1⁄4 hφjˆηjψi; that is, the positive Hermitian operator ηˆ plays the role of the metric (or, equivalently, the CP operator [18]).
For Hˆ in (1) the inner-product space constructed above is not a Hilbert space because, as we will see, the elements of the vector space have infinite norm. However, the elements of fψnðxÞg and those of fψ~ nðxÞg are biorthogonal provided that fzng belongs to the nontrivial zeros of the Riemann zeta function. To see this, let us consider the inner product hψ~ mjψni. Observing that
ψ~ mðxÞ 1⁄4 Δˆ †Δˆ ψ nðxÞ 1⁄4 Δˆ † ˆΔΔˆ −1x−zm 1⁄4 Δˆ †x−zm ;
and recalling that ψ nðxÞ 1⁄4 ˆΔ−1x−z, we find that
hψ~ mjψni 1⁄4
Z∞
0
dx x− ̄zm Δˆ ˆΔ−1x−zn
1⁄4
Z∞
0
dx x−1þiðEn−E ̄ mÞ=2: ð6Þ
Thus, if E ̄ m 1⁄4 Em (that is, if the Riemann hypothesis is correct), then (6) is a Dirac delta function 4πδðEn − EmÞ. It follows that for m ≠ n we have
hψ~ mjψni 1⁄4 0 ð7Þ
in the distributional sense, as required by the biorthogonality condition. In contrast, for the trivial zeros, the integral (6) diverges too rapidly to be interpreted as a tempered distribution. In terms of the inner product introduced above, and assuming that ˆp is Hermitian (symmetric), we find, using ˆΔ†Δˆ 1⁄4 ηˆ, that
hHˆ φ; ψi 1⁄4
Z∞
0
dx  ̄φðxÞ ˆΔ†ðxˆ ˆp þ ˆp ˆxÞð ˆΔ†Þ−1Δˆ † ˆΔψ ðxÞ
1⁄4
Z∞
0
dx  ̄φðxÞ ˆΔ†Δˆ ˆΔ−1ðˆx ˆp þ ˆp ˆxÞΔˆ ψðxÞ
1⁄4 hφ; Hˆ ψi:
This shows that, from the assumption that ˆp is Hermitian, we may conclude that Hˆ is Hermitian (symmetric) with respect to the new inner product. As a further consequence of (6) and (7), if the Riemann
hypothesis is true, then the eigenvalues of Hˆ are nondegenerate. Conversely, if the Riemann hypothesis is false, then the eigenstates of Hˆ that correspond to nontrivial zeros for which ReðzÞ ≠ 1
2 coalesce to give rise to Jordan block structures in the Hamiltonian. This follows from the fact that at such complex degeneracies (often referred to as exceptional points), the eigenstates satisfy the so-called self-orthogonality condition hψ~ njψni 1⁄4 0. These findings may have an implication on whether the zeros of ζðzÞ are simple: It is known that if the Riemann hypothesis holds true, then at least 19=27 of the nontrivial zeros are simple [19]. However, if there exists a one-to-one correspondence between the boundary condition on the eigenstates of Hˆ and the secular equation for the eigenvalues of Hˆ , then it follows that the validity of the Riemann hypothesis implies that all roots are simple, and conversely any nontrivial zero of ζðzÞ for which ReðzÞ ≠ 1
2 cannot be simple.
Boundary condition revisited.—For finite-dimensional nondegenerate matrices, the biorthogonality relation (7)
implies that Hˆ † defined in (5) is the Hermitian adjoint of Hˆ . However, in infinite-dimensional vector spaces the completeness of the states fψnðxÞg is required to arrive at this conclusion. Nevertheless, the relation (7) suggests that our Hermiticity assumption of ˆp is valid, making ˆh manifestly Hermitian. Encouraged by this observation, we ask whether the momentum operator ˆp is Hermitian (symmetric) on the inner-product space defined above. Because 1⁄2 ˆp; ˆη 1⁄4 0, the Hermiticity of ˆp on h·; ·i follows if the boundary terms vanish under an integration by parts when the elements of fψnðxÞg and those of fψ~ nðxÞg are paired. Note that ψ~ nðxÞ diverges at x 1⁄4 0, so ψnðxÞ must vanish sufficiently fast at x 1⁄4 0 to ensure the vanishing of the boundary terms. [The divergence of fψnðxÞg at x 1⁄4 ∞ is compensated by the vanishing of fψ~ nðxÞg as x → ∞.] One can verify that imposing ψnð0Þ 1⁄4 0 is sufficient to guarantee the vanishing of the boundary term at the origin. Thus, the Hermiticity of ˆp on h·; ·i follows from the boundary condition ψnð0Þ 1⁄4 0.
Relation to quantum mechanics.—Since the operator Hˆ is a function of the canonical variables ðˆx; ˆpÞ, we have referred to it as a Hamiltonian. However, the connection of this Hamiltonian to physical systems is at best tenuous because the eigenstates of Hˆ in our inner-product space are not normalizable. This is not a concern for our analysis, but in quantum mechanics normalizability is required for a probabilistic interpretation. A possible way of making a connection to quantum theory is to introduce a regularization scheme, for example, by letting x ∈ 1⁄2Λ−1; Λ , renormalizing the states according to ψnðxÞ → ðln ΛÞ−1=2ψnðxÞ, and then taking the limit
PRL 118, 130201 (2017) P H Y S I C A L R E V I E W L E T T E R S week ending
31 MARCH 2017
130201-4


 Λ → ∞. Interestingly, the expectation value of the position operator ˆρ−1xˆ ˆρ in the state ψnðxÞ for any n in the renormalized theory is Λ= ln Λ, which for large Λ gives the leading term in the counting of prime numbers smaller than Λ. Discussion.—We have presented a formal argument
showing that the eigenvalues of the Hamiltonian Hˆ in (1), whose classical limit is 2xp, correspond to the nontrivial zeros of the Riemann zeta function. Identifying the domain of Hˆ remains a difficult and open problem. We hope that further analysis of the properties of Hˆ , such as identifying its domain and establishing its self-adjointness, will prove the reality of the eigenvalues, and thus the veracity of the Riemann hypothesis. The possibility of extending the Hilbert-Pólya program to non-Hermitian PT -symmetric operators has been noted [20]. We hope that our findings will significantly boost research in this direction. The fact that iHˆ is PT symmetric, with a broken PT symmetry, offers a fresh and optimistic outlook.
D. C. B. thanks D. Blasius and C. Hughes for comments and the Russian Science Foundation for support (Project No. 16-11-10218). M. P. M. thanks D. Schleicher for discussions. M. P. M. is supported in part by the Canada Research Chairs program. Research at Perimeter Institute is supported by the Government of Canada through Innovation, Science and Economic Development Canada and by the Province of Ontario through the Ministry of Research, Innovation and Science.
[1] B. Riemann, Ueber die Anzahl der Primzahlen unter einer gegebenen Grö sse, Monatsberichte der Berliner Akademie (Monatsberichte der Kö niglichen Preußischen Akademie der Wissenschaften zu Berlin, Berlin, 1859).
[2] H. L. Montgomery, in Analytic Number Theory. Proceedings of the Symposium on Pure Mathematics XXIV (American Mathematical Society, Providence, 1973), pp. 181–193. [3] A. M. Odlyzko, On the distribution of spacings between zeros of the zeta function, Math. Comput. 48, 273 (1987). [4] M. V. Berry, in Quantum Chaos and Statistical Nuclear Physics, edited by T. H. Seligman and H. Nishioka, Lect. Notes Phys. Vol. 263 (Springer-Verlag, New York, 1986). [5] M. V. Berry and J. P. Keating, in Supersymmetry and Trace Formulae: Chaos and Disorder, edited by I. V. Lerner et al. (Kluwer Academic/Plenum, New York, 1999) [http://link .springer.com/chapter/10.1007%2F978‐1‐4615‐4875‐1_19].
[6] A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Sel. Math. New Ser. 5, 29 (1999). [7] G. Sierra, The Riemann zeros as spectrum and the Riemann hypothesis, arXiv:1601.01797. [8] Ë. Delabaere, Ramanujan’s summation, Algorithms Sem. 2001–2002, 83 (2003) [http://algo.inria.fr/seminars/ sem01‐02/delabaere2.pdf]. [9] F. W. J. Olver, D. M. Lozier, R. F. Boisvert, and C. W. Clark, NIST Handbook of Mathematical Functions (Cambridge University Press, Cambridge, England, 2010). [10] C. M. Bender and S. A. Orszag, Advanced Mathematical Methods for Scientists and Engineers (McGraw-Hill, New York, 1978). [11] M. Müller and D. Schleicher, How to add a non-integer number of terms, and how to produce unusual infinite summations, J. Comput. Appl. Math. 178, 347 (2005); Fractional sums and Euler-like identities, Ramanujan J. 21, 123 (2010); How to add a noninteger number of terms: From axioms to new identities, Am. Math. Mon. 118, 136 (2011).
[12] One can extend Hˆ to a one-parameter family of Hamiltonians Hˆ ε by the replacement ˆΔ → ˆΔε 1⁄4 ε−1ð1 − e−iεpˆ Þ. A calcu
lation shows that the eigenstates ψεzðxÞ of Hˆ ε take the form
ψεzðxÞ ∝ −ζðz; 1 þ x=εÞ with eigenvalue ið2z − 1Þ. In the limit ε → 0 we obtain the Hamiltonian ˆp−1ðˆx pˆ þ ˆp ˆxÞpˆ with eigenstate x1−z. [13] C. M. Bender, Making sense of non-Hermitian Hamiltonians, Rep. Prog. Phys. 70, 947 (2007). [14] D. C. Brody, Consistency of PT-symmetric quantum mechanics, J. Phys. A 49, 10LT03 (2016). [15] C. M. Bender, D. C. Brody, J.-H. Chen, H. F. Jones, K. A. Milton, and M. C. Ogilvie, Equivalence of a complex PT-Symmetric quartic Hamiltonian and a Hermitian quartic Hamiltonian with an anomaly, Phys. Rev. D 74, 025016 (2006). [16] G. W. Mackey, Commutative Banach Algebras (Instituto de Matematica pura e Aplicada do Conselho Nacional de Pesquisa, Rio De Janeiro, 1959). [17] D. C. Brody, Biorthogonal quantum mechanics, J. Phys. A 47, 035305 (2014). [18] C. M. Bender, D. C. Brody, and H. F. Jones, Complex Extension of Quantum Mechanics, Phys. Rev. Lett. 89, 270401 (2002). [19] H. M. Bui and D. R. Heath-Brown, On simple zeros of the Riemann zeta-function, Bull. London Math. Soc. 45, 953 (2013). [20] Z. Ahmed and S. R. Jain, A pseudo-unitary ensemble of random matrices, PT-symmetry and the Riemann hypothesis, Mod. Phys. Lett. A 21, 331 (2006).
PRL 118, 130201 (2017) P H Y S I C A L R E V I E W L E T T E R S week ending
31 MARCH 2017
130201-5