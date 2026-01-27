---
title: "Zeta spectral triples"
authors:
  - "Alain Connes"
  - "Caterina Consani"
  - "Henri Moscovici"
date: "2025-00-00 2025"
publication: "arXiv preprint arXiv: 2511.22755"
doi: null
url: null
zotero:
  attachment_key: "6H6WHGDU"
  parent_key: "H8ULBMAL"
  item_id: 2570
  attachment_item_id: 2571
---

Zeta Spectral Triples
Alain Connes, Caterina Consani and Henri Moscovici
Abstract
We propose and investigate a strategy toward a proof of the Riemann Hypothesis based on a spectral realization of its non-trivial zeros. Our approach constructs self-adjoint operators
D(λ,N )
log obtained as rank-one perturbations of the spectral triple associated with the scaling operator on the interval [λ−1, λ]. The construction only involves the Euler products over the primes p ≤ x = λ2 and produces self-adjoint operators whose spectra coincide, with striking numerical accuracy, with the lowest non-trivial zeros of ζ( 1
2 + is), even for small values of x. The theoretical foundation rests on the framework introduced in [4] together with the extension in [7] of the classical Carathe ́odory–Feje ́r theorem for Toeplitz matrices, which guarantees the necessary self-adjointness. Numerical experiments show that the spectra of the operators D(λ,N)
log converge
towards the zeros of ζ( 1
2 + is) as the parameters N, λ → ∞. A rigorous proof of this convergence would establish the Riemann Hypothesis. We further compute the regularized determinants detreg (D(λ,N )
log − z) of these operators and discuss the analytic role they play in controlling and potentially proving the above result by showing that, suitably normalized, they converge towards the Riemann Ξ function.
Key Words. Riemann zeta, spectral triples, infrared, explicit formulas, Weil quadratic form, Prolate wave operator.
Mathematics Subject Classification 2020. 11M06, 11M55, 58B34, 33D60, 34B20.
1 Introduction
This paper is motivated by the spectral realization initiated in [4] of the low lying zeros of the Riemann zeta function, in other words as the infrared part of the spectrum of a selfadjoint operator. Another key ingredient is the generalization proved in [7] of a fundamental result on Toeplitz matrices which is a corollary of Carathe ́odory-Fejer 1911 structure theorem [2]. This generalization provides for us a large class of functions whose zeros are located on the critical line R(s) = 1/2 due to the selfadjointness of relevant matrices and the Hurwitz theorem on zeros of uniform limits of holomorphic functions. With these tools at hand one devises a process, perfectly in line with Riemann’s paper [10], which associates to the restricted Euler product involving only the primes p ≤ x a function whose zeros are on the critical line. The great surprise then, is that the zeros of this function give high-precision approximations to the first non-trivial zeros of the Riemann zeta function using remarkably few terms of the Euler product. For instance using only the primes ≤ 13 one obtains for the first 50 zeros an extraordinary accuracy,
1
arXiv:2511.22755v1 [math.NT] 27 Nov 2025


2 2. Preliminaries
with errors ranging from 2.5 × 10−55 for the first zero to approximately 10−3 for the fiftieth. The probability of achieving such precise approximations by chance is approximately 10−1235, effectively ruling out coincidence and suggesting a deep structural relationship between the restricted Euler products and the location of the zeros. The method we use is general as well as the proof that all the approximating values lie exactly on the critical line.
In fact we construct spectral triples associated to rank one perturbations D(λ,N)
log of the scaling
operator D(λ)
log on the interval [λ−1, λ] with periodic boundary conditions. This construction is based
on the restriction QW N
λ of the Weil quadratic form to the linear space EN = EN (λ) of test functions
spanned by the 2N + 1 eigenfunctions of D(λ)
log associated to the 2N + 1 eigenvalues of smallest
absolute value (i.e. ≤ N π/ log λ), extended by 0 outside the interval [λ−1, λ]. We need to verify that the smallest eigenvalue εN of QW N
λ is simple and that the corresponding eigenfunction is ”even” i.e.
invariant under the symmetry u 7→ u−1. We let δN ∈ EN be the vector representing the Dirichlet kernel, as an approximation to the evaluation on the boundary of the interval [λ−1, λ]. Our main result is the following:
Theorem 1.1. Let εN be the smallest eigenvalue of QW N
λ assumed simple and ξ the corresponding eigenvector assumed even, normalized by δN (ξ) = 1.
(i) The operator D(λ,N)
log = D(λ)
log − |D(λ)
log ξ⟩⟨δN | is selfadjoint in the direct sum E′
N ⊕ E⊥
N where on
the subspace E′
N = EN /Cξ the inner product is given by the restriction of the quadratic form
QW N
λ − εN ⟨|⟩.
(ii) The regularized determinant of D(λ,N)
log is given by detreg(D(λ,N)
log − z) = −i λ−izξb(z) where ξb is
the Fourier transform of ξ for the duality ⟨R∗+ | R⟩.
(iii) The Fourier transform ξb(z) is an entire function, all its zeros are on the real line and coincide
with the spectrum of D(λ,N)
log .
In Section 6 we show the striking numerical evidence for the convergence of the eigenvalues of
the selfadjoint operators D(λ,N)
log towards the zeros of the Riemann zeta function ζ 1
2 + is as the parameters N and λ tend to infinity. In Section 7, we explain the natural strategy to justify the above numerical convergence. It consists in taking the first steps in trying to show the convergence of the regularized determinants
detreg (D(λ,N )
log − s) towards the Riemann Ξ function. Finally Section 8 describes the missing steps in the above strategy and the perspective that it opens, based on [3], on the connections between the world of the Weil quadratic form and that of information theory, as developed through the theory of prolate wave functions by D. Slepian and his collaborators [15].
2 Preliminaries
2.1 The Banach algebra L1(R, dx)
In this section we shall explain elementary computations preparing the ground for the introduction of the Weil quadratic form QWλ and of the matrix encoding this quadratic form in a natural basis.


3 2.2 The basis {Un}n∈Z
Definition 2.1. We let L1(R, dx) be the involutive complex Banach algebra of complex valued integrable functions on R with product and involution given by
f ∗ g(y) :=
Z
f (x)g(y − x)dx (2.1)
f ∗(y) := f (−y) (2.2)
We shall use the subalgebra of compactly supported functions. Both operations yield functions with compact support. We consider the inclusion L2([0, L]) ⊂ L1(R, dx) obtained by extending functions by 0 outside the interval [0, L]. In particular, for f, g ∈ L2[0, L] the support of f ∗ ∗ g is contained in [−L, L].
We shall use inner products ⟨f, g⟩ which are antilinear in the first variable and linear in the second. The standard inner product ⟨f, g⟩2 is given by
⟨f, g⟩2 =
Z
f (x)g(x)dx = (f ∗ ∗ g)(0) (2.3)
In preparation for more involved inner products, we shall compute expressions of the form
q(f, g)(y) := (f ∗ ∗ g)(y) + (f ∗ ∗ g)(−y) (2.4)
which is an even function of y depending antilinearly on f and linearly on g. One has
(f ∗ ∗ g)(−y) = (f ∗ ∗ g)∗(y) = (g∗ ∗ f )(y),
hence q(f, g)(y) = (f ∗ ∗ g)(y) + (g∗ ∗ f )(y). (2.5)
Let a ∈ R and for any f ∈ L1(R, dx), let fa(x) := f (x − a) denote the translated of f .
Lemma 2.2. For any a ∈ R, f, g ∈ L1(R, dx), one has (fa)∗ ∗ ga = f ∗ ∗ g and q(fa, ga) = q(f, g).
Proof. One has
(fa)∗ ∗ ga(y) =
Z
(fa)∗(y − x)ga(x)dx =
=
Z
(fa)(x − y)ga(x)dx =
Z
f (x − a − y)g(x − a)dx
which is independent of a. The second equality follows from (2.4).
2.2 The basis {Un}n∈Z
A natural orthonormal basis for L2([0, L]) consists of the functions {Un}n∈Z defined by
Un(x) := L− 1
2 exp(2πinx/L), ∀x ∈ [0, L]. (2.6)


4 2.2 The basis {Un}n∈Z
Applying the above operations to the basis functions one obtains, for n ̸= m, y ∈ [0, L],
(U ∗
m ∗ Un)(y) =
Z
Um(x − y)Un(x)dx = 1
L
ZL
y
exp 2πim(y − x)/L + 2πinx/L dx
= exp(2πimy/L)
L
ZL
y
exp(2πi(n − m)x/L)dx = exp(2πimy/L)
2πi(n − m) exp(2πi(n − m)x/L) L
y
= exp(2πimy/L)
2πi(n − m) 1 − exp(2πi(n − m)y/L) = exp(2πimy/L) − exp(2πiny/L)
2πi(n − m)
so that for n ̸= m, y ∈ [0, L],
(U ∗
m ∗ Un)(y) = exp(2πimy/L) − exp(2πiny/L)
2πi(n − m) (2.7)
The result of (2.7) being symmetric in n, m, it implies using (2.5), that for y ∈ [0, L],
(U ∗
m ∗ Un)(y) + (U ∗
m ∗ Un)(−y) = 2 R e2πimy/L − e2πiny/L
2πi(n − m)
!
= sin(2πmy/L) − sin(2πny/L)
π(n − m) (2.8)
so that the even function q(Um, Un) is given by
q(Um, Un)(y) = sin(2πm|y|/L) − sin(2πn|y|/L)
π(n − m) , ∀y ∈ [−L, L]. (2.9)
For m = n one simply has, for y ∈ [0, L],
(U ∗
n ∗ Un)(y) = 1
L
ZL
y
exp(2πin(y − x)/L + 2πinx/L)dx = (1 − y/L) exp(2πiny/L),
whence (U ∗
n ∗ Un)(y) + (U ∗
n ∗ Un)(−y) = 2 R ((1 − y/L) exp(2πiny/L)) =
= 2(1 − y/L) cos(2πny/L).
We thus get q(Un, Un)(y) = 2(1 − |y|/L) cos(2πny/L), ∀y ∈ [−L, L]. (2.10)
Lemma 2.3. The explicit expression of the even function q(Un, Um)(y) for y ∈ [0, L] is :
m ̸= n sin( 2πmy
L )−sin( 2πny
L) π(n−m)
m = n 2(L−y) cos( 2πny
L) L


5 3. The Weil quadratic form QW
3 The Weil quadratic form QW
The sesquilinear form QW derives from Weil’s formulation of the explicit formula in prime numbers theory [16], which we recall below. Let us denote by W(R∗+) the Weil class of complex valued
functions f on R∗+, by which we mean the functions having continuous derivative, except at finitely
many points where both f (x) and f ′(x) may have at most a discontinuity of the first kind; at such a point the value of f (x) and f ′(x) is defined as the average of the right and left limits. In addition, the functions f ∈ W (R∗+) are assumed to satisfy the estimate
f (x) = O(xδ), for x → 0+, f (x) = O(x−1−δ), for x → +∞,
for some δ > 0. These functions admit a Mellin transform, denoted
f ̃(s) :=
Z∞
0
f (x)xs−1dx. (3.1)
With the additional notation f ♯(x) := x−1f (x−1), the Weil’s explicit formula takes the form (cf.[1])
X
ρ
f ̃(ρ) =
Z∞
0
f (x)dx +
Z∞
0
f ♯(x)dx −
X
v
Wv(f ), (3.2)
where ρ runs over all complex zeros ρ of the Riemann zeta function, v runs over all rational places of Q, the non-archimedean distributions Wp are defined as
Wp(f ) := (log p)
∞
X
m=1
f (pm) + f ♯(pm) , (3.3)
and the archimedean distribution is given by
WR(f ) := (log 4π + γ)f (1) +
Z∞
1
f (x) + f ♯(x) − 2
x f (1) dx
x − x−1 . (3.4)
It should be noted that the sum in the left hand side of (3.2), whose general term is oscillatory, is only conditionally convergent. This issue of lack of absolute convergence is an essential feature of Riemann’s formula for the function π(x) which is the number of primes less than x. In our situation this issue does not appear since we shall only apply the explicit formula to functions which are the convolution (for the group R∗+) of two square integrable functions with compact support, thus ensuring the absolute convergence of the sum over the zeros. An equivalent formulation, known as Guinand-Weil formula, uses the Fourier transform
Fb(s) :=
Z
R∗
+
F (u)u−isd∗u, d∗u = du
u (3.5)
in place of the Mellin transform (3.1). The passage from one to the other is be obtained by implementing the automorphism
f 7→ ∆1/2f = F, i .e. F (x) = x1/2f (x), (3.6)


6 3. The Weil quadratic form QW
which respects the convolution product and satisfies the equalities
(∆1/2f ♯)(x) = x1/2f ♯(x) = x−1/2f (x−1) = (∆1/2f )(x−1).
For a rational place v, denoting Wv(F ) := Wv(∆−1/2F ), the above distributions Wp take the following form:
Wp(F ) = (log p)
∞
X
m=1
p−m/2 F (pm) + F (p−m) , (3.7)
while the archimedean distribution WR becomes
WR(F ) := (log 4π + γ)F (1) +
Z∞
1
F (x) + F (x−1) − 2x−1/2F (1) x1/2
x − x−1 d∗x,
where d∗x = dx/x. The latter can also be expressed as WR = −W∞, where
W∞(F ) =
Z
R
Fb(t) 2∂tθ(t)
2π dt. (3.8)
and
θ(t) = − t
2 log π + I log Γ 1
4 +it
2 (3.9)
is the angular Riemann-Siegel function, with log Γ(s) for R(s) > 0 denoting the branch of the logarithm which is real for s real.
By polarization, the Weil form gives the sesquilinear expression
QW (f, g) = Ψ(f ∗ ∗ g), Ψ(F ) := W0,2(F ) − WR(F ) −
X
p
Wp(F ). (3.10)
The components WR and Wp are as above, and the functional W0,2 is
W0,2(F ) = Fb(i/2) + Fb(−i/2). (3.11)
There is a rather subtle invariance property of the Weil sesquilinear form, namely its symmetry under the inversion ι(u) = u−1, u ∈ R∗, which will play a significant role in its explicit description.
Lemma 3.1. The Weil functional Ψ fulfills
Ψ(h) = Ψ#(h) + Ψ#(h ◦ ι) = Ψ#(h + h ◦ ι), (3.12)
where Ψ♯ is the distribution on [1, ∞),
Ψ♯ := W #
0,2 − W #
R−
X
W#
p (3.13)


7 3. The Weil quadratic form QW
with the components given by
W#
0,2(F ) =
Z∞
1
F (x)(x1/2 + x−1/2)d∗x, (3.14)
W#
R (F ) = 1
2 (log 4π + γ)F (1) +
Z∞
1
x1/2F (x) − F (1)
x − x−1 d∗x, (3.15)
W#
p (F ) = (log p)
∞
X
m=1
p−m/2F (pm). (3.16)
Proof. This follows from the construction of Ψ. Note the factor 1
2 in (3.15).
Proposition 3.2. Let λ > 1, L = 2 log λ.
(i) The following map is an isometry κ : L2([0, L], dx) → L2([λ−1, λ], d∗u),
κ(f )(u) = f (log(λu)) (3.17)
which induces an isomorphism C∞([0, L]) → C∞([λ−1, λ]). (ii) Let f, g ∈ C∞([0, L]). One has
QW (κ(f ), κ(g)) = Ψ♯(F ), F (u) = q(f, g)(log u). (3.18)
Proof. (i) Follows since the map u 7→ log(λu) is a diffeomorphism from [λ−1, λ] to [0, L] transforming the measure d∗u into the measure dx. (ii) One has, by Lemma 3.1,
QW (κ(f ), κ(g)) = Ψ♯(h + h ◦ ι), h = κ(f )∗ ∗ κ(g).
Let us show that h + h ◦ ι = F . By Lemma 2.2, one has, with a = − L
2
q(f, g) = q(fa, ga), fa(x) := f (x + L
2 ), ga(x) := g(x + L
2)
so that fa and ga have support in [− L
2, L
2 ] and one has κ(f ) = fa ◦ log, κ(g) = ga ◦ log, where the
log is the isomorphism of locally compact groups log : R∗+ → R. This induces an isomorphism of involutive convolution algebras
◦ log : L1(R, dx) → L1(R∗
+, d∗x).
Thus one gets h = κ(f )∗ ∗ κ(g) = (fa ◦ log)∗ ∗ (ga ◦ log) = (f ∗
a ∗ ga) ◦ log
which using (2.4) gives
h + h ◦ ι = q(fa, ga) ◦ log = q(f, g) ◦ log = F.
and hence the required equality.


8 3.1 The quadratic form QWλ
3.1 The quadratic form QWλ
Let λ > 1. We denote by QWλ the restriction of the quadratic form QW to L2([λ−1, λ], d∗u), where d∗u = du
u . One has
QWλ(f, f ) =
Z
R
|
fb(t)|2 2∂tθ(t)
2π dt + 2R fb( i
2) ̄
fb(− i
2) −
X
1<n≤λ2
Λ(n)⟨f | T (n)f ⟩; (3.19)
here Λ(n) is the von Mangoldt function, and T (n) is the bounded self-adjoint operator in L2([λ−1, λ], d∗u) defined by ⟨f | T (n)g⟩ = n−1/2 (f ∗ ∗ g)(n) + (f ∗ ∗ g)(n−1) . (3.20)
Proposition 3.3. ([4, §2]) The quadratic form QWλ is lower bounded and lower semi-continuous.
Recall that a lower bounded, lower semi-continuous (lsc) quadratic form Q on a Hilbert space H is a lower semi-continuous map Q : H → (−∞, +∞], i.e. such that Q(ξ) ≤ lim inf Q(ξn) when ξn → ξ, which fulfills Q(λξ) = |λ|2Q(ξ) for all λ ∈ C, satisfies the parallelogram law
Q(ξ + η) + Q(ξ − η) = 2Q(ξ) + 2Q(η)
and also an inequality of the form Q(ξ) ≥ −c∥ξ∥2 for all ξ ∈ H reflecting the lower bound of q. The associated sesquilinear form (antilinear in the first variable) is given on the domain Dom(Q) := {ξ ∈ H | Q(ξ) < ∞} by
Q(ξ, η) := 1
4 (Q(ξ + η) − Q(ξ − η) + iQ(iξ + η) − iQ(iξ − η)) .
Let Vn : [λ−1, λ] → C be the function κ(Un), i.e.
Vn(u) := Un(log(λu)), ∀u ∈ [λ−1, λ] (3.21)
and let E ⊂ L2([λ−1, λ], d∗u) be the linear subspace generated by the Vn for n ∈ Z.
Proposition 3.4. ([4, Prop. 2.3]) The space E is a core for the quadratic form QWλ : L2([λ−1, λ], d∗u) → (−∞, +∞], which satisfies, for any f ∈ L2([λ−1, λ], d∗u),
QWλ(f, f ) = lim inf
gn→f QWλ(gn, gn), gn ∈ E. (3.22)
In particular, the lower bound of QWλ is the limit, when N → ∞, of the smallest eigenvalue of the restriction of QWλ to the linear span EN of the functions Vk with |k| ≤ N .
3.2 Discrete spectrum of the semilocal Weil quadratic form QWλ
At this juncture we appeal to a basic result from the general theory of quadratic forms. Adopting the notation in [12, Ch. 10], to a quadratic form t one associates a mapping t′ : H → R ∪ {+∞} by setting t′[x] = t[x] if x is in D(t) and t′[x] = +∞ if x is not in D(t). According to [12, Proposition 10.1] the following four conditions are equivalent:


9 3.2 Discrete spectrum of the semilocal Weil quadratic form QWλ
1. t is closed.
2. If (xn)n∈N is a sequence from D(t) such that limn→∞ xn = x in H for some x ∈ H and limn,k→∞ t [xn − xk] = 0, then x ∈ D(t) and limn→∞ t [xn − x] = 0.
3. t′ is a lower semicontinuous function on H.
4. If (xn)n∈N is a sequence from D(t) such that limn→∞ xn = x in H for some x ∈ H and the set {t [xn] : n ∈ N} is bounded, then we have x ∈ D(t) and t[x] ≤ lim infn→∞ t [xn].
By Proposition 3.3 the condition (3) is fulfilled by the semilocal Weil quadratic form QWλ, and therefore Theorem 10.7 in [12], reproduced below, applies.
Representation theorem for semibounded forms – If t is a densely defined lower semibounded closed form on H, then the operator At is self-adjoint, and t is equal to the form t(At) associated with At.
Thus, for each λ > 1, there is a canonical lower bounded unbounded selfadjoint operator Aλ in the Hilbert space L2 λ−1, λ , d∗u such that
QWλ(f, f ) = ⟨Aλf | f ⟩. (3.23)
By construction the unbounded selfadjoint operator Aλ is lower bounded. The issue is to show that it has discrete spectrum. We use the following from [12], Proposition 10.6,
Proposition 3.5. Suppose that A ≥ mA is a lower semibounded self-adjoint operator and m < mA. Then the following assertions are equivalent:
1. The embedding map ItA : (D[A], ∥ · ∥tA) → (H, ∥ · ∥) is compact.
2. The resolvent Rλ(A) is compact for one, hence for all, λ ∈ ρ(A).
3. (A − mI)−1/2 is compact.
4. A has a purely discrete spectrum.
Theorem 3.6. The selfadjoint operator Aλ has discrete lower bounded spectrum.
Proof. By the proof of the lower boundedness in [4], the contribution of the non-archimedean primes to the operator Aλ is bounded as well as the contribution of the evaluation of the Fourier transform at the poles. Thus it is enough to deal, for any λ > 1 with the contribution of the archimedean place to Aλ in the Hilbert space L2 λ−1, λ , d∗u . It is given, after Fourier transform, by the multiplication by
∂tθ(t) = 1
2 (log(|t|) − log(2) − log(π)) − 1
48t2 + O t−4 (3.24)
whose asymptotic expansion allows one to use instead the operator L of multiplication (in Fourier) by the function which is 1 for |t| ≤ e and log(|t|) otherwise. Note that the factor 1
2π is taken care of
since the unitary Fourier transform has a factor √12π .


10 3.2 Discrete spectrum of the semilocal Weil quadratic form QWλ
By Proposition 3.5, it is enough to show that the embedding map I : (D[L ], ∥ · ∥tL) → (H, ∥ · ∥) is compact. The map I is of norm ≤ 1 by construction and it is enough to show that the image of the unit ball is precompact in the following sense: Let E be a metric space. If any of the following three properties is satisfied, then all three are satisfied, and E is said to be precompact: 1. For every ε > 0, E can be covered by a finite number of balls of radius ε; 2. For every ε > 0, E can be covered by a finite number of subsets with diameter less than ε; 3. Every sequence in E has a Cauchy subsequence. We shall show that for any positive increasing function ρ : [0, ∞) → [1, ∞) such that ρ(u) → ∞ when u → ∞ the embedding Iρ of the Hilbert space Dρ in L2 λ−1, λ , d∗u is compact, where the norm square in Dρ is given by
∥f ∥2
ρ :=
Z
|fˆ(t)|2 ρ(t)
2π dt (3.25)
In fact one can use the logarithm-exponential isomorphism and replace the Hilbert space L2 λ−1, λ , d∗u by H = L2 ([−L, L] , dx) and use the ordinary Fourier transform in (3.25). It is enough to show that the image Iρ(B) of the unit ball B of Dρ is precompact in H. Let then ε > 0 and let us show that one can cover Iρ(B) by finitely many balls of radius ε for the norm of H. Since ρ(u) → ∞ when u → ∞ there exists T < ∞ such that
∥f ∥2
ρ≤1⇒
Z
|t|≥T
|fˆ(t)|2 dt
2π ≤ (ε/4)2 (3.26)
Next, the operator PcT PL is a compact operator in L2(R) and hence the image PcT PL(C) of the unit ball C of L2(R) is precompact in L2(R). By construction Iρ(B) ⊂ H = L2 ([−L, L] , dx) = PLL2(R), thus the map
PcT Iρ : Dρ → L2(R)
is compact. Thus there exists a finite set of functions {fj}j∈J ⊂ B ⊂ Dρ, such that
∀f ∈ B, ∃j | ∥PcT (f − fj)∥2 ≤ (ε/2)2.
Thus one has
∀f ∈ B, ∃j ∈ J such that
Z
|t|≤T
|fˆ(t) − fˆj(t)|2 dt
2π ≤ (ε/2)2
By (3.26) it follows that for any f ∈ B there exists j such that
∥f − fj∥2
H=
Z
|fˆ(t) − fˆj(t)|2 dt
2π =
=
Z
|t|≤T
|fˆ(t) − fˆj(t)|2 dt
2π +
Z
|t|≥T
|fˆ(t) − fˆj(t)|2 dt
2π ≤ (ε/2)2 + (ε/2)2 < ε2,
where we used (3.26) and the triangle inequality to get
Z
|t|≥T
|(fˆ(t) − fˆj)(t)|2 dt
2π
!1/2
≤ ε/4 + ε/4 = ε/2.


11 4. The matrix of QWλ in the basis Vn
Corollary 3.7. Let λ > 1. There exists an element φ ∈ L2 λ−1, λ , d∗u such that Aλ(φ) = μλ φ where μλ is the largest lower bound of the spectrum of Aλ.
Note that we cannot assert that μλ ≥ 0. One has however
λ > λ′ ⇒ μλ ≤ μλ′ (3.27)
Indeed first note that the test functions which are piecewise smooth form a core for the Weil quadratic form QWλ since the smooth ones already do by [4] and moreover the Fourier transform of piecewise smooth functions f with compact support are O(|s|−1) since the derivative f ′ is a bounded measure, so the piecewise smooth functions are in the domain of QWλ. One then uses the equivalence (with f piecewise smooth)
ν ≤ μλ ⇐⇒ QWλ(f, f ) ≥ ν∥f ∥2, ∀f | support(f ) ⊂ λ−1, λ
Corollary 3.8. If the limit when λ → ∞ of the decreasing function μλ is equal to 0 then RH holds.
4 The matrix of QWλ in the basis Vn
We now compute the matrix of the sesquilinear form QWλ(f, g) = Ψ(f ∗ ∗ g) in the basis {Vn}n∈Z. By Proposition 3.2 and the equality Vn = κ(Un) we get
QWλ(Vn, Vm) = Ψ#(F ), where F (x) = q(Un, Um)(log x) (4.1)
and Ψ♯ was defined in (3.13). Next, we proceed to describe the contribution to the matrix QWλ(Vn, Vm) of each term in (3.13).
4.1 The matrix W0,2(Vn, Vm)
The following lemma shows that the terms W0,2(Vn, Vm) contribute by a rank two matrix.
Lemma 4.1. Let n, m ∈ Z. Let F (x) = q(Un, Um)(log x), then one has :
W0,2(Vn, Vm) = W #
0,2(F ) = 32L sinh2 L
4 L2 − 16π2mn
(L2 + 16π2m2) (L2 + 16π2n2) (4.2)
Proof. This is best verified by direct computation.
4.2 The matrix Wp(Vn, Vm)
The contribution of the non archimedean primes is given by (3.16), i.e.
X
Wp(Vn, Vm) =
X
1<k≤exp(L)
Λ(k)k−1/2q(Un, Um)(log k). (4.3)


12 4.3 The matrix WR(Vn, Vm)
4.3 The matrix WR(Vn, Vm)
Let ω(x) = q(Un, Um)(x), then(3.15) gives
WR(Vn, Vm) =
ZL
0
exp x
2 ω(x) − ω(0)
exp (x) − exp (−x) dx − ω(0)
Z∞
L
dx
exp (x) − exp (−x)
+1
2 (γ + log(4π))ω(0).
Since
Z∞
L
dx
exp (x) − exp (−x) = 1
2 log eL + 1
eL − 1
one obtains
WR(Vn, Vm) = ω(0)
2 γ + log 4π eL − 1
eL + 1
+
ZL
0
exp x
2 ω(x) − ω(0)
exp (x) − exp (−x) dx. (4.4)
The explicit expression for ω(x) = q(Un, Um)(x) for x ∈ [0, L], is given by Lemma 2.3. The next step is to compute the integrals involved, they are given in terms of known functions in the following
proposition 4.2. We let ρ(x) := exp(x/2)
exp(x) − exp(−x)
We let ψ(z) = Γ′(z)/Γ(z) be the digamma function and ψ(1) be its derivative. We use the standard notation for hypergeometric functions. We use the notation Φ for the Hurwitz-Lerch function
Φ(z, 2, x) = 1
x2 + z
(x + 1)2 + z2
(x + 2)2 + z3
(x + 3)2 + z4
(x + 4)2 + . . .
An important feature of the formulas is that the parameter e−2L in the various series involved is of modulus < 1 thus ensuring the convergence and in fact fast numerical convergence for L of order 10.


13 4.3 The matrix WR(Vn, Vm)
Proposition 4.2. We use the symbols R(z) and I(z) for the real and imaginary parts of a complex number z. One has
ZL
0
sin(2πnx/L)ρ(x)dx = (4.5)
e−L/2I( 2L
L + 4πin 2F1(1, πin
L +1
4 ; πin
L +5
4 ; e−2L)) + 1
2 I(ψ( πin
L +1
4 )).
ZL
0
x cos(2πnx/L)ρ(x)dx = (4.6)
− Le−L/2I 2L
4πn − iL 2F1 1, 1
4 + inπ
L ;5
4 + inπ
L ; e−2L
− e−L/2
4 R Φ e−2L, 2, iπn
L +1
4 +1
4 R ψ(1) πin
L +1
4.
ZL
0
(cos(2πnx/L) − 1)ρ(x)dx = (4.7)
− e−L/2R 2L
L + 4πin 2F1 1, πin
L +1
4 ; πin
L +5
4 ; e−2L
+ 2e−L/2 2F1
1
4 , 1; 5
4 ; e−2L − 1
2 R ψ( πin
L +1
4) − ψ(1
4) .
Proof. In each case one first changes variables to y = 2πx/L and then expand, with a := L
2π
ρ(x) = exp ay
2
exp(ay) − exp(−ay) =
∞
X
k=0
exp(b(k)y), b(k) = −a(1 + 4k)
2
The change of variables introduces an overall factor ( L
2π )2 for the middle integral and ( L
2π ) for the others. One obtains in this way for each integral a sum of terms indexed by k ∈ N and which are
Z 2π
0
exp(bx) sin(nx) dx = n − e2πbn
b2 + n2 (4.8)
Z 2π
0
x exp(bx) cos(nx) dx = 2πe2πbb − e2πb + 1
b2 + n2 − 2n2 1 − e2πb
(b2 + n2)2 (4.9)
Z 2π
0
exp(bx)(cos(nx) − 1) dx = n2 − e2πbn2
b3 + bn2 (4.10)
All these expressions are affine in e2πb whose coefficient gives the general term of a sum over k ∈ N using
e2πb(k) = exp(− L
2 (1 + 4k)) = e−L/2zk, z = e−2L.


14 4.3 The matrix WR(Vn, Vm)
One then recognizes the series in z involved and obtains the following expressions
ZL
0
sin(2πnx/L)ρ(x)dx =
e−L/2 (iL) 2F1 1, 1
4 − inπ
L ;5
4 − inπ
L ; e−2L
L − 4iπn − (iL) 2F1 1, iπn
L +1
4 ; iπn
L +5
4 ; e−2L
L + 4iπn
!
+1
4 i ψ(0) 1
4 − inπ
L − ψ(0) iπn
L +1
4
ZL
0
x cos(2πnx/L)ρ(x)dx =
e−L/2 − 1
8 Φ e−2L, 2, iπn
L +1
4 −1
8 Φ e−2L, 2, 1
4 − iπn
L
+ e−L/2 iL2 2F1 1, iπn
L +1
4 ; iπn
L +5
4 ; e−2L
4πn − iL − iL2 2F1 1, 1
4 − iπn
L ;5
4 − iπn
L ; e−2L
4πn + iL
!
+1
8 ψ(1) iπn
L +1
4 + ψ(1) 1
4 − iπn
L
ZL
0
(cos(2πnx/L) − 1)ρ(x)dx =
e−L/2 − L 2F1 1, iπn
L +1
4 ; iπn
L +5
4 ; e−2L
L + 4iπn − L 2F1 1, 1
4 − inπ
L ;5
4 − inπ
L ; e−2L
L − 4iπn
!
+ 2e−L/2 2F1
1
4 , 1; 5
4 ; e−2L + 1
4 −ψ(0) iπn
L +1
4 − ψ(0) 1
4 − inπ
L + 2ψ(0) 1
4
Using the real and imaginary parts to simplify these expressions one obtains the required result.
For the last integral we have computed a simplified form of the required expression which is
ZL
0
(cos(2πnx/L) − exp(−x/2))ρ(x)dx =
ZL
0
(cos(2πnx/L) − 1)ρ(x)dx + c(L) (4.11)
where the correction term is
c(L) =
ZL
0
1 − exp − x
2
exp(x) − exp(−x) dx =
log eL/2 + 1 + 1
4 −2 log eL + 1 − π − log(4) + tan−1 eL/2
In fact we need to add the following to take into account the full Weil principal value
w(L) = 1
2 (γ + log(4π)) − 1
2 log eL + 1
eL − 1


15 5. The infrared spectral triples
We then obtain
c(L) + w(L) = 1
2 log eL/2 − 1
eL/2 + 1
!
+ tan−1 eL/2 − π
4+γ
2+1
2 log(8π)
To get lighter notations we let
αL(n) := 1
π
ZL
0
sin(2πnx/L)ρ(x)dx, (4.12)
βL(n) := 1
L
ZL
0
x cos(2πnx/L)ρ(x)dx, (4.13)
γL(n) :=
ZL
0
(cos(2πnx/L) − exp(−x/2))ρ(x)dx + c(L) + w(L) (4.14)
Using these notations, Proposition 4.2 and (4.4), one obtains
Proposition 4.3. The matrix WR(Vn, Vm) is given by the following table
m ̸= n αL(m)−αL(n)
n−m
m = n 2γL(n) − 2βL(n)
Proof. Follows from Lemma 2.3.
5 The infrared spectral triples
In this section we shall construct infrared spectral triples naturally associated to the scaling operator in L2([λ−1, λ], d∗u) with periodic boundary conditions. The intent is to modify the periodic boundary conditions in order to insert in the kernel of the modified scaling operator the eigenvector which realizes the minimum of the Weil quadratic form in the Hilbert space L2([λ−1, λ], d∗u). In order to obtain this perturbation we work at the truncated level and use instead of the evaluation on the boundary of the interval [λ−1, λ] an approximation to this evaluation which is given by the Dirichlet kernel. We then show the existence and uniqueness of the perturbed scaling operator, together with two fundamental facts. The first is that this operator becomes self-adjoint provided one modifies the inner product using the Weil quadratic form. The second point is that one can compute the spectrum of this operator using the Fourier transform of the minimal eigenvector.
5.1 Truncation of QWλ
Let λ > 1, L = 2 log λ, Un as defined in (2.6) and Vn = κ(Un) the orthonormal basis of L2([λ−1, λ], d∗u) given in (3.21). Let N ∈ N, we consider the quadratic form QW N
λ obtained by restricting the Weil quadratic form QWλ to the finite dimensional space of test functions spanned by the functions Vn for |n| ≤ N . By (3.18), the matrix elements of T = QW N
λ in the basis Vn are given by
τn,m =
ZL
0
q(Un, Um)(y)D(y) i, j ∈ {−N, . . . , N } (5.1)


16 5.2 Properties of truncated matrices
where D is the real distribution D = log∗(Ψ♯) on the interval [0, L].
Lemma 5.1. The matrix τn,m is a real symmetric matrix of the form
τi,i = ai, ∀i, τi,j = bi − bj
i − j , ∀j ̸= i; i, j ∈ {−N, . . . , N } (5.2)
where the real scalars ai fulfill a−j = aj and b−j = −bj for all j ∈ {−N, . . . , N }.
Proof. This follows from the computation of the functions q(Un, Um)(y) for y ∈ [0, L] in (2.8) and (2.10), which gives for n ̸= m
τn,m =
ZL
0
sin(2πmy/L) − sin(2πny/L)
π(n − m) D(y) =⇒
bn = − 1
π
ZL
0
sin(2πny/L)D(y)
and for n = m,
τn,n = 2
ZL
0
(1 − y/L) cos(2πny/L)D(y) = an
5.2 Properties of truncated matrices
In this section we let N be a positive integer, EN be the Hilbert space with orthonormal basis {Vn, n ∈ {−N, . . . , N }} and T a real symmetric matrix of the form (5.2). We recall the basic properties of [7] for matrices of this form.
Lemma 5.2. (i) Let γ such that γ(Vj) := V−j ∀j ∈ {−N, . . . , N }. One has γ2 = id and T γ = γT . (ii) Let D be defined by D(Vn) := n Vn for all n ∈ {−N, . . . , N }. One has Dγ = −γD and
D T − T D = |β⟩⟨η| − |η⟩⟨β|, β =
X
bj Vj, η =
X
Vj. (5.3)
Proof. (i) One has q−i,−j = qi,j for all i, j ∈ {−N, . . . , N }. (ii) The diagonal elements of the diagonal matrix D are antisymmetric which gives Dγ = −γD. Let us prove (5.3). One has
(DT )i,j = iτi,j, (T D)i,j = jτi,j
so that (D T − T D)i,j = (bi − bj) for all i, j ∈ {−N, . . . , N }. Similarly one has
(|β⟩⟨η|)i,j = |β⟩i⟨η|j = bi, (|η⟩⟨β|)i,j = |η⟩i⟨β|j = bj
which gives the required equality.
Definition 5.3. A real symmetric matrix T commuting with the Z/2-grading γ is even-simple if its smallest eigenvalue is simple and the corresponding eigenvector ξ satisfies γξ = ξ.


17 5.2 Properties of truncated matrices
We now assume that T is even simple and positive and let ξ ∈ ker T , ξ ̸= 0. The real symmetric positive matrix T defines an inner product on R2N+1 and its radical consists of the one dimensional subspace generated by ξ. Let us first show that we can normalize ξ by the condition
⟨ξ | η⟩ = 1 (5.4)
If Dξ = 0 then V0 ∈ ker T fulfills (5.4). So we can assume that Dξ ̸= 0. One has T Dξ ̸= 0 since Dξ is odd and linearly independent of ξ while ker T is one-dimensional. By (5.3) one has
0 ̸= (D T − T D)(ξ) = |β⟩⟨η|ξ⟩ − |η⟩⟨β|ξ⟩ = |β⟩⟨η|ξ⟩.
Thus one can normalize ξ so that ⟨η|ξ⟩ = 1.
Lemma 5.4. Assume T ≥ 0 and Ker T = Cξ where γξ = ξ and ⟨ξ | η⟩ = 1. (i) One has T D ξ = −β. (ii) The operator D′ := D − |D ξ⟩⟨η| induces a selfadjoint operator D” in the Hilbert space associated to the inner product defined by T , as quotient by null vectors. (iii) One has, denoting by ξj the components of ξ,
Det(D” − s) = Det(D − s)
N
X
j=−N
(j − s)−1ξj. (5.5)
Proof. (i) We apply (5.3) and get, using T ξ = 0 and ⟨β|ξ⟩ = 0 since the two eigenspaces of γ are orthogonal,
−T D ξ = (D T − T D)ξ = |β⟩⟨η|ξ⟩ − |η⟩⟨β|ξ⟩ = β.
(ii) The inner product defined by T is given by
⟨f | g⟩T = ⟨T f | g⟩.
We first show that
⟨D′f | g⟩T = ⟨f | D′g⟩T , ∀f, g (5.6)
One has, with R = −|D ξ⟩⟨η|
⟨D′f | g⟩T = ⟨T D′f | g⟩ = ⟨T Df | g⟩ + ⟨T Rf | g⟩.
By (i), one has T R = −|T Dξ⟩⟨η| = |β⟩⟨η|. Thus
T D′ = T D + |β⟩⟨η|
Moreover by (5.3), one has T D − DT = −|β⟩⟨η| + |η⟩⟨β|. Thus
T D′ = DT + |η⟩⟨β|,
⟨D′f | g⟩T = ⟨DT f | g⟩ + ⟨R′f | g⟩, R′ = |η⟩⟨β|.


18 5.2 Properties of truncated matrices
Moreover, using that both T and D are selfadjoint,
⟨f | D′g⟩T = ⟨T f | Dg⟩ + ⟨T f | Rg⟩ = ⟨DT f | g⟩ + ⟨f | T Rg⟩
and the required equality follows from
T Rg = (−T Dξ)⟨η|g⟩ = β⟨η|g⟩
⟨f | T Rg⟩ = ⟨f | (|β⟩⟨η|g⟩ = ⟨f | β⟩⟨η|g⟩ = ⟨R′f | g⟩.
The Hilbert space H obtained from EN using the inner product ⟨f | g⟩T is the quotient of EN by the radical Ker T = Cξ. By construction one has D′ξ = 0 so that D′ induces an operator D” in H and D” is selfadjoint by (7.3). (iii) Let vj be an orthonormal basis of H of eigenvectors for D” with eigenvalues λj. Let wj ∈ EN be lifts of the vj. One has D”(vj) = λjvj and hence D′(wj) = λjwj + sjξ for some scalars sj. Thus in the basis of EN formed by ξ and the wj, the matrix of D′ is triangular, with 0 and the λj on the diagonal. Thus one gets
Det(D′ − s) = −s
Y
(λj − s) = −s Det(D” − s) (5.7)
We now compute Det(D′ − s). We start by writing, in terms of R = −⟨Dξ⟩⟨η|:
D′ − s = D + R − s = (D − s) id + (D − s)−1R
Consequently Det(D′ − s) = Det(D − s)Det(id + (D − s)−1R).
To compute the second determinant we use the identity
Det(id + A) =
∞
X
k=0
Tr ∧kA
applied to the rank one operator A = (D − s)−1R. The higher exterior powers ∧kA vanish for k > 1 thus Det(id + (D − s)−1R) = 1 − Tr |(D − s)−1Dξ⟩⟨η| = −s⟨η|(D − s)−1ξ⟩,
using (D − s)−1Dξ = ξ + s(D − s)−1ξ and ⟨η|ξ⟩ = 1. Hence,
Det(D′ − s) = −s Det(D − s)⟨η|(D − s)−1ξ⟩ = −s Det(D − s)
N
X
j=−N
(j − s)−1ξj.
Thus one obtains (5.5) using (5.7).


19 5.3 The Dirichlet Kernel δN as an approximation of the Dirac Delta
5.3 The Dirichlet Kernel δN as an approximation of the Dirac Delta
The Dirichlet kernel approximates the Dirac delta function as N → ∞. It is
DN (x) =
N
X
n=−N
exp(2πinx/L), ∀x ∈ [0, L] (5.8)
This can be simplified using the geometric series formula:
DN (x) = sin π(2N + 1)x
L / sin πx
L (5.9)
for x ̸= 0 (mod L) while DN (0) = DN (L) = 2N + 1.
Lemma 5.5. Let D = −i∂L be the selfadjoint operator of differentiation on L2([0, L], dx) with periodic boundary conditions. Let f ∈ Dom D. Then
lim
N →∞
1
L
ZL
0
DN (x)f (x) dx = f (0) (5.10)
Proof. Let fˆ(n) = 1
L
RL
0 f (x)e−2πinx/L dx be the Fourier coefficients of f . We have by Parseval’s theorem, with a constant c > 0:
∞
X
n=−∞
|n|2|fˆ(n)|2 = c ∥f ′∥2
L2 < ∞ (5.11)
Since DN (x) = PN
n=−N e2πinx/L, we have:
1
L
ZL
0
DN (x)f (x) dx =
N
X
n=−N
fˆ(n) (5.12)
So we need to prove that the Fourier series of f converges at x = 0:
N
X
n=−N
fˆ(n) → f (0) as N → ∞ (5.13)
By the Cauchy-Schwarz inequality:
X
n̸=0
|fˆ(n)| =
X
n̸=0
1
|n| · |n||fˆ(n)|
≤


X
n̸=0
1 n2


1/2 

X
n̸=0
n2|fˆ(n)|2


1/2
<∞


20 5.4 The perturbed scaling operator
Therefore the Fourier series P∞
n=−∞ fˆ(n)e2πinx/L converges absolutely and uniformly to f (x) for all x, hence:
N
X
n=−N
fˆ(n) → f (0) as N → ∞
The scaling operator is defined as
D(λ)
log = −iu ∂
∂u = −i ∂
∂ log u (5.14)
acting on L2([λ−1, λ], d∗u) subject to periodic boundary conditions.
Corollary 5.6. Let Vn(u) := Un(log(λu)) as in (3.21), D(λ)
log be the scaling operator with periodic
boundary conditions in L2([λ−1, λ], d∗u) and f ∈ Dom D(λ)
log .
lim
N→∞⟨δN | f ⟩ = f (λ), δN := √1L
N
X
n=−N
Vn (5.15)
Proof. This follows from Lemma 5.5 using the isometry κ of (3.17) to pass from L2([λ−1, λ], d∗u) to L2([0, L], dx), and the equality
DN = √1L
N
X
n=−N
Un
which follows from (5.8) and (2.6).
5.4 The perturbed scaling operator
The perturbed scaling operator D(λ,N)
log is obtained from the following :
Proposition 5.7. Let λ > 1 and N such that the truncated Weil quadratic form is even simple.
Let ξ be the corresponding even eigenvector. There exists a unique operator D(λ,N)
log with the same
domain as D(λ)
log which agrees with this operator on the kernel of δN and such that D(λ,N)
log (ξ) = 0.
Proof. The Hilbert space L2([λ−1, λ], d∗u) is the direct sum of the finite dimensional subspace EN spanned by the Vn for |n| ≤ N and its orthogonal complement E⊥
N . Since the Vn form an
orthonormal basis of eigenvectors for D(λ)
log , this operator splits as the direct sum of its restrictions to
EN and E⊥
N . The linear form δN vanishes on E⊥
N and ξ ∈ EN by construction. Thus the existence
and uniqueness of D(λ,N)
log is reduced to the finite dimensional subspace EN . One has δN (ξ) ̸= 0 so KerδN and Cξ span EN and the equality
D(λ,N )
log (β) = D(λ)
log (α), ∀β = α + xξ, α ∈ KerδN , x ∈ C
uniquely determines the operator D(λ,N)
log .


21 5.5 Regularized Determinant
5.5 Regularized Determinant
The regularized determinant is defined by
detreg(D − s) = exp −ζ′
D(0; s) (5.16)
where ζD(z; s) := P(λ − s)−z is the spectral zeta function. There is an ambiguity in the definition of the zeta function (see [13], §7.1) since raising λ − s to the power −z implies the choice of a determination of log(λ − s). There is a clear such choice for eigenvalues λ → +∞ but in the negative direction one needs to make a choice for (−1)−z and this choice of the spectral cut affects the result in the following basic example. Note that, in this example and taking for simplicity L = 2π, one could guess the regularized determinant from the Euler product as given by the sine function sin(πs) but this would violate the spectral invariance s → s + 1. The phase factor in front of the sine function repairs this violation.
Lemma 5.8. Let L > 0. The regularized determinant for the Dirac operator D with spectrum 2π
LZ
is given, using (−1)−z := e−iπz, by
detreg(D − s) = 1 − e−iLs (5.17)
Proof. We first take L = 2π to simplify notations. The spectral zeta function is given by
ζD(z; s) =
X
n∈Z
(n − s)−z (5.18)
This converges for Re(z) > 1. One has
ζD(z; s) =
∞
X
n=1
(n − s)−z +
0
X
n=−∞
(n − s)−z (5.19)
For the second sum, substitute n → −m with m ≥ 0 and use (−1)−z := e−iπz
0
X
n=−∞
(n − s)−z =
∞
X
m=0
(−m − s)−z = e−iπz
∞
X
m=0
(m + s)−z (5.20)
So that using the Hurwitz zeta function:
ζ(z, a) =
∞
X
n=0
(n + a)−z (5.21)
one obtains
ζD(z; s) =
∞
X
n=0
(n + 1 − s)−z + e−iπz
∞
X
m=0
(m + s)−z = ζ(z, 1 − s) + e−iπzζ(z, s)


22 5.6 Spectrum and regularized determinant of D(λ,N)
log
Thus one gets the equality
ζ′
D(0; s) = ζ′(0, 1 − s) − iπζ(0, s) + ζ′(0, s) (5.22)
Moreover one has the classical expressions
ζ(0, a) = 1
2 − a, ζ′(0, a) = log Γ(a) − 1
2 log(2π) (5.23)
which give
ζ′
D(0; s) = − log(2π) + log Γ(s) + log Γ(1 − s) − iπ( 1
2 − s) (5.24)
exp −ζ′
D(0; s) = 2π
Γ(s)Γ(1 − s) exp iπ( 1
2 − s) =
= 2i sin(πs)e−iπs = 1 − e−2iπs
The general case follows using ζD(0; s) = 0. One has indeed, for a > 0
ζaD(z; as) = a−zζD(z; s) =⇒ ζ′
aD(0; as) = − log a ζD(0; s) + ζ′
D(0; s)
which gives the required result for a = 2π/L.
5.6 Spectrum and regularized determinant of D(λ,N)
log
In this section we prove the fundamental properties of D(λ,N)
log and show that its spectrum is real and that its regularized determinant is (up to a phase factor) the Fourier transform of the minimal eigenvector ξ. We first compute the Fourier transform of functions on [λ−1, λ] extended by 0 to R∗+. The Fourier
transform for the duality ⟨R∗+ | R⟩ is defined by
Fμ(f )(s) :=
Z
R∗
+
f (u)u−isd∗u.
Proposition 5.9. Let λ > 1, L = 2 log λ, N ∈ N, ξj ∈ C for j ∈ {−N, . . . , N },
ξ(u) :=
X
{−N,...,N }
ξk Vk(u), ∀u ∈ [λ−1, λ], ξ(u) = 0, ∀u ∈/ [λ−1, λ].
The Fourier transform ξb = Fμ(ξ) is the entire function given by
ξb(z) = 2 L−1/2 sin (zL/2)


X
{−N,...,N }
ξj z − 2πj/L

 . (5.25)


23 5.6 Spectrum and regularized determinant of D(λ,N)
log
Proof. One has for k ∈ Z, using x = log(λu), u−is = λis exp(−isx), d∗u = dx,
Zλ
λ−1
Vk(u)u−isd∗u =
Zλ
λ−1
Uk(log(λu))u−isd∗u =
= L−1/2λis
ZL
0
exp(2πikx/L) exp(−isx) dx = −i 1 − e−isL
s − 2πk/L L−1/2eisL/2.
Thus the Fourier transform of ξ(u) is
ξb(z) = 2 L−1/2 sin (zL/2)


X
{−N,...,N }
ξj z − 2πj/L

.
The zeros z ∈ 2πZ/L of sin (sL/2) cancell the poles at 2πj/L which occur when ξj ̸= 0 and remain
as zeros of ξb(z) otherwise.
Theorem 5.10. Let εN be the smallest eigenvalue of QW N
λ assumed simple and ξ the corresponding eigenvector assumed even, normalized by δN (ξ) = 1.
(i) The operator D(λ,N)
log is selfadjoint in the direct sum E′
N ⊕E⊥
N where on the subspace E′
N = EN /Cξ
the inner product is given by the restriction of the quadratic form QW N
λ − εN ⟨|⟩.
(ii) The regularized determinant of D(λ,N)
log is given by
detreg (D(λ,N )
log − z) = −i λ−izξb(z)
where ξb is the Fourier transform of ξ for the duality ⟨R∗+ | R⟩.
(iii) The Fourier transform ξb(z) is an entire function, all its zeros are on the real line and coincide
with the spectrum of D(λ,N)
log .
Proof. (i) We apply Lemma 5.4 to T := QW N
λ − εN id where εN is the smallest eigenvalue of QW N
λ
which is assumed to be simple and even. Let D, D′ and D” be the associated operators. One has
D(λ)
log |EN = 2π
L D, D(λ,N)
log |EN = 2π
L D′, D(λ,N)
log |E′
N = 2π
L D” (5.26)
By construction the operator D(λ,N)
log decomposes the direct sum in the direct sum E′
N ⊕ E⊥
N . Hence the result follows from Lemma 5.4, (ii). (ii) By (5.26) one has
Det(D(λ)
log |EN − 2π
L s) = ( 2π
L )2N+1Det(D − s)
Det(D(λ,N )
log |E′
N − 2π
L s) = ( 2π
L )2N Det(D” − s)


24 5.6 Spectrum and regularized determinant of D(λ,N)
log
We now apply Lemma 5.4, (iii), but note that the normalization of ξ given by δN (ξ) = 1 differs from ⟨ξ′ | η⟩ = 1. One has δN = L−1/2η by Corollary 5.6 thus giving ξ′ = L−1/2ξ. Lemma 5.4, (iii) shows that
Det(D(λ,N )
log |E′
N − 2π
L s) = L
2π Det(D(λ)
log |EN − 2π
L s)
N
X
j=−N
(j − s)−1ξ′
j
which with ξ′ = L−1/2ξ, z = 2π
L s gives
Det(D(λ,N )
log |E′
N − z) = Det(D(λ)
log |EN − z) L1/2
2π
N
X
j=−N
(j − L
2π z)−1ξj
It then follows from the multiplicativity of the regularized determinant that
detreg (D(λ,N )
log − z) = L−1/2 detreg(D(λ)
log − z)


X
{−N,...,N }
ξj 2πj/L − z

 (5.27)
By (5.25), the Fourier transform of ξ(u) is
ξb(z) = 2 L−1/2 sin (zL/2)


X
{−N,...,N }
ξj z − 2πj/L


By (5.17) one has
detreg(D(λ)
log − z) = 1 − exp(−iz L) = 2i exp(−iz L/2) sin (zL/2) ,
thus (5.27) gives
detreg (D(λ,N )
log − z) = L−1/2 (1 − exp(−iz L))


X
{−N,...,N }
ξj 2πj/L − z

=
= −i exp(−iz L/2) ξb(z) = −i λ−iz ξb(z)
(iii) The Fourier transform ξb is an entire function since ξ is an L1-function with compact support.
The regularized determinant detreg(D(λ,N)
log − z) is the product of the determinants
detreg (D(λ,N )
log − z) = Det(D(λ,N)
log |E′
N − z) detreg(D(λ)
log |E⊥
N − z)
In this factorization the first term is the characteristic polynomial of a selfadjoint matrix and hence all its zeros are real. The zeros of the second term form the set
{2πj/L | j ∈ Z, |j| > N }
which gives the required result.


25 6. Numerical results
6 Numerical results
One computes using the above formulas the matrix of the Weil quadratic form and the spectrum of
the operator D(λ,N)
log . These computations require high precision but are easily preformed using 200 digits accuracy due to the fast convergence of the special functions involved. The first case is λ = 3 and one takes N = 120.
(ρ1 )*
(ρ2 )*
(ρ3 )*
(ρ4 )* (ρ5 )*
(ρ6 )*
(ρ7 )*
(ρ8 )*
(ρ9 )*
(ρ10 )*
(ρ11 )*
(ρ12 )*
(ρ13 )*
(ρ14 )*
(ρ15 )*
(ρ16 )* (ρ17 )* (ρ18 )*
(ρ19 )*
(ρ20 )*
1.6 ×10-34
2.1 ×10-31
1.5 ×10-29
8.3 ×10-27 1.3 ×10-25
1.2 ×10-23
7.5 ×10-22
6.6 ×10-21
1.2 ×10-18
8.8 ×10-18
7.3 ×10-17
2.2 ×10-15
9.7 ×10-14
2.7 ×10-13
6.3 ×10-12
5.6 ×10-11 2.9 ×10-10 1.2 ×10-9
5.6 ×10-8
2.4 ×10-7
Figure 1: This shows the differences between the first twenty zeros of ζ 1
2 + is and the eigenvalues
of the operator D(λ,N)
log for λ = 3 and N = 120.
We then consider the first fifty zeros of zeta, use still N = 120 and the values of λ given by
λ = √12 ∼ 3.4641, λ = √13 ∼ 3.60555, λ = √14 ∼ 3.74166.
We get the following table giving an upper bound on the absolute value of the difference between the
nontrivial zeros of the Riemann zeta function ζ 1
2 + is and the eigenvalues of the operator D(λ,N)
log .


26 6. Numerical results
λ = √12 λ = √13 λ = √14 1 3.41 × 10−50 2.44 × 10−55 1.07 × 10−60 2 5.89 × 10−47 4.5 × 10−52 2.08 × 10−57 3 5.18 × 10−45 4.16 × 10−50 2. × 10−55 4 4.2 × 10−42 3.65 × 10−47 1.89 × 10−52 5 7.84 × 10−41 7.11 × 10−46 3.81 × 10−51 6 1.07 × 10−38 1.06 × 10−43 6.13 × 10−49 7 9.42 × 10−37 1. × 10−41 6.17 × 10−47 8 1.05 × 10−35 1.19 × 10−40 7.66 × 10−46 9 3.25 × 10−33 4.12 × 10−38 2.94 × 10−43 10 2.99 × 10−32 3.98 × 10−37 2.96 × 10−42 11 3.76 × 10−31 5.5 × 10−36 4.42 × 10−41 12 1.87 × 10−29 3.04 × 10−34 2.68 × 10−39 13 1.28 × 10−27 2.29 × 10−32 2.19 × 10−37 14 4.47 × 10−27 8.46 × 10−32 8.43 × 10−37 15 2.18 × 10−25 4.82 × 10−30 5.48 × 10−35 16 2.76 × 10−24 6.61 × 10−29 8.02 × 10−34 17 2.3 × 10−23 6.08 × 10−28 8.02 × 10−33 18 1.59 × 10−22 4.66 × 10−27 6.73 × 10−32 19 1.59 × 10−20 5.5 × 10−25 9.11 × 10−30 20 9.55 × 10−20 3.54 × 10−24 6.19 × 10−29 21 2.36 × 10−19 9.75 × 10−24 1.86 × 10−28 22 6.7 × 10−18 3.31 × 10−22 7.38 × 10−27 23 5.24 × 10−17 2.86 × 10−21 6.89 × 10−26 24 8.4 × 10−16 5.32 × 10−20 1.45 × 10−24 25 1.94 × 10−15 1.33 × 10−19 3.89 × 10−24 26 2.42 × 10−14 2.07 × 10−18 7.23 × 10−23 27 6.05 × 10−13 5.94 × 10−17 2.33 × 10−21 28 1.26 × 10−12 1.34 × 10−16 5.58 × 10−21 29 3.15 × 10−12 4.09 × 10−16 2.01 × 10−20 30 2.72 × 10−11 4.21 × 10−15 2.39 × 10−19 31 3.57 × 10−10 6.61 × 10−14 4.33 × 10−18 32 1.7 × 10−9 3.6 × 10−13 2.62 × 10−17 33 2.33 × 10−9 5.66 × 10−13 4.6 × 10−17 34 1.2 × 10−7 4.03 × 10−11 4.23 × 10−15 35 2.89 × 10−7 1.04 × 10−10 1.16 × 10−14 36 4.1 × 10−7 1.85 × 10−10 2.45 × 10−14 37 9.11 × 10−7 4.92 × 10−10 7.53 × 10−14 38 2.78 × 10−6 1.94 × 10−9 3.61 × 10−13 39 3.53 × 10−5 3.24 × 10−8 7.44 × 10−12 40 1.83 × 10−4 2. × 10−7 5.24 × 10−11


27 7. Outlook
40 1.83 × 10−4 2. ×10−7 5.24 × 10−11 41 1.67 × 10−4 2.12 × 10−7 6.22 × 10−11 42 2.97 × 10−4 5.66 × 10−7 2.23 × 10−10 43 2.19 × 10−3 5.49 × 10−6 2.64 × 10−9 44 4.35 × 10−3 1.35 × 10−5 7.51 × 10−9 45 1.19 × 10−2 5.3 × 10−5 3.8 × 10−8 46 1.27 × 10−2 6.88 × 10−5 5.65 × 10−8 47 2.87 × 10−2 3.01 × 10−4 3.66 × 10−7 48 1.43 × 10−1 2. × 10−3 2.98 × 10−6 49 1.98 × 10−1 3.01 × 10−3 5.34 × 10−6 50 9.02 × 10−2 2.04 × 10−3 4.78 × 10−6
7 Outlook
These numerical results provide evidence that the spectra of the operators D(λ,N)
log tend1 to the
nontrivial zeros of the Riemann zeta function ζ( 1
2 + is). Establishing this convergence rigorously would amount to a proof of the Riemann Hypothesis. One can be even more ambitious using Theorem 5.10 together with the observation of [4] that the eigenfunction associated with the lowest eigenvalue of QWλ is well approximated by prolate spheroidal wave functions. As we explain now this suggests that the regularized determinants
detreg (D(λ,N )
log − s) behave as follows
• For fixed λ, the functions detreg(D(λ,N)
log − s) converge2 when N → ∞ to the function
−i λ−izξbλ(z) where ξλ is the eigenfunction of QWλ for the smallest eigenvalue, normalized by ξ(λ) = 1.
• When λ → ∞ the functions ξbλ(z) multiplied by suitable constants, converge uniformly on closed substrips of the open strip I(z) < 1
2 towards the Ξ-function of Riemann
Ξ(s) = ξ(1/2 + is), ξ(z) = 1
2 z(z − 1)π−z/2Γ(z/2)ζ(z)
In other words the regularized determinants detreg(D(λ,N)
log − s) suitably multiplied by a factor of
the form ea+ibs converge towards Ξ(s). This convergence would entail RH using Hurwitz theorem on the zeros of limits of holomorphic functions. We now give more details to give substance to this strategy. First when reading Riemann’s paper [10] one finds that, using modern terminology, he understood his Ξ-function as the Fourier transform for the duality ⟨R∗+ | R⟩ of the function
k(u) = E(h)(u), h(u) = π
2 u2 2πu2 − 3 e−πu2 . (7.1)
1when N → ∞ and λ → ∞ 2uniformly on compact subsets of C


28 7. Outlook
where one uses the following map E:
E(f )(u) := u1/2
∞
X
1
f (nu) (7.2)
The function h(u) can be characterized as follows. One considers the Hermite operator (harmonic oscillator) Hf (u) := −f ′′(u) + 4π2u2f (u) (7.3)
and lets hn be the normalized eigenfunction for the eigenvalue 2π(1 + 2n). These functions are even for n even and, for n multiple of 4, invariant under the Fourier transform for the duality ⟨R | R⟩ which is defined by
FeR(f )(y) :=
Z
R
f (x)e2πixy dx.
Lemma 7.1. The Ξ function of Riemann is the Fourier transform of k = E(h) where h is, up to a multiplicative scalar, the only linear combination of h0, h4 with vanishing integral. More precisely one has, in terms of the normalized hn
h=
√3
211/4 h4 − 3
217/4 h0, and ∥h∥ =
√33
217/4 . (7.4)
Proof. The normalized forms of h0, h4 are
h0(x) = 21/4e−πx2 , h4(x) = 16π2x4 − 24πx2 + 3
2 4 √2√3 e−πx2
Thus
3
217/4 h0(x) = 3
16 e−πx2 ,
√3
211/4 h4(x) = π2x4 − 3πx2
2 +3
16 e−πx2
which gives the required result using (7.1).
We recall the construction of [4] of an educated guess kλ for an approximation of a scalar multiple of ξλ. It is based on the deformation of the harmonic oscillator called the prolate wave operator
P Wλ := −∂x (λ2 − x2)∂x + (2πλx)2. (7.5)
The eigenfunctions hn,λ(u) of P Wλ have the same labelling as the Hermite functions hn, they are even for n even and invariant under the Fourier transform for n multiple of 4. In agreement with Lemma 7.1, the educated guess kλ is
kλ(u) := E(hλ)(u), ∀u ∈ [λ−1, λ] (7.6)
where hλ is, up to a multiplicative scalar, the only linear combination of h0,λ, h4,λ with vanishing integral. We refer to [4], Section 3, for the motivation behind the formula for kλ and the numerical evidence showing that it gives an approximation of a scalar multiple of ξλ. Justifying rigorously this step is the main remaining obstacle to our approach to RH. We now use the educated guess (7.6) and evaluate its convergence in the next lemma 7.3. We shall first describe an estimate from [9].


29 7. Outlook
Lemma 7.2. (i) The eigenfunctions hn,λ of P Wλ, suitably normalized, fulfill for n = 0, 4 an estimate of the form (with c < ∞)
max
x∈[−λ,λ]
|hn,λ(x) − hn(x)| ≤ c λ−2 (7.7)
(ii) Let hλ be the suitably normalized linear combination of h0,λ, h4,λ with vanishing integral. One has an estimate of the form (with c < ∞)
max
x∈[−λ,λ]
|hλ(x) − h(x)| ≤ c λ−2 (7.8)
Proof. (i) This follows from [9], Satz 9, page 243, Section 3.2. entitled ”Die Sph ̈aroidfunktionen psnm z; γ2 ” which asserts that uniformly for z ∈ [−1, 1] one has the estimate
psm
n z; γ2 = (−1)m 4γ
π
1
41
(n − m)!
(n + m)!
2n + 1
1 2
1 − z2 m/2 Dn−m (2γ) 1
2 z + O γ−3
4
We need to explain carefully the notations of [9]. The differential equation defining the prolate spheroidal functions uses the operator
Fγy ≡ d
dz 1 − z2 dy
dz + −m2
1 − z2 + γ2 1 − z2 y
and we are only interested in the case when the angular parameter m = 0. In that case the operator simplifies to
Fγy ≡ d
dz 1 − z2 dy
dz + γ2 1 − z2 y
We first relate this operator (for m = 0) to the prolate wave operator of (7.5). One lets z = x/λ which gives
d
dz
2
7→ λ2 (∂x)2 , −γ2 z2 7→ −γ2/λ2 x2
Thus we need an overall minus sign and also
γ2/λ2 = 4π2λ2 =⇒ γ = 2πλ2 (7.9)
The prolate spherical functions psn := ps0n are related to those in Mathematica by
psn s; γ2 = P S(n, 0, γ, s)
The statement in [9] Satz 9 simplifies for m = 0 to the estimate, uniform for z ∈ [−1, 1],
psn z; γ2 = 4γ
π
1
41
(2n + 1)n!
1 2
Dn (2γ) 1
2 z + O γ−3
4


30 7. Outlook
which gives uniformly in the interval [−λ, λ]
4γ
π
−1
4
psn x/λ; γ2 = 1
(2n + 1)n!
1 2
Dn (2γ) 1
2 x/λ + O γ−1 (7.10)
The hermite functions Dn are defined in [9] by the equation
Dp(x) = (−1)pe x2
4 dp
dxp e− x2
2 , D0(x) = e− x2
4
In our case we have γ = 2πλ2, which gives
(2γ) 1
2 /λ = (4π) 1
2 =⇒ Dn (2γ) 1
2 x/λ = Dn (4π) 1
2x
One has in particular
D0 (4π) 1
2 x = e−πx2 , D4 (4π) 1
2 x = e−πx2 16π2x4 − 24πx2 + 3
Thus in terms of the normalized Hermite functions hn we have
D0 (4π) 1
2 x = 2−1/4h0(x), D4 (4π) 1
2 x = 25/4√3 h4(x) (7.11)
We can thus use (7.10) to normalize the products hn,λ = cnλ−1/2 psn x/λ; γ2 so that
max
x∈[−λ,λ]
|hn,λ(x) − hn(x)| ≤ c λ−2, n = 0, 4. (7.12)
(ii) By (i), we control the values hn,λ(0) for n = 0, 4. The fundamental property of the prolate wave functions is that they are eigenfunctions of the compression of the Fourier transform by the orthogonal projection Pλ of L2(R)even on the subspace of functions with support in the interval [−λ, λ]. Moreover for small values of n such as n = 0, 4 the eigenvalues χ(λ) are such that 1 − χ(λ) decays extremely fast when λ → ∞. For instance for n = 4, by [8], Theorem 1, one has
1 − χ(λ) ∼ 214
3
√2π5e−4πλ2+9 log(λ)
Moreover we have Z
hn,λ(x)dx = hn d,λ(0) = χn(λ)hn,λ(0)
By (7.12) we control the differences |hn,λ(0) − hn(0)| and hence the differences
|
Z
hn,λ(x)dx − hn(0)| = O(λ−2)
It follows that we obtain a linear combination hλ of h0,λ and h4,λ which has vanishing integral and fulfills (7.8).


31 7. Outlook
In fact we show in the following two Figures the behavior of the functions
en(λ2) := λ2 max
x∈[−λ,λ]
|hn,λ(x) − hn(x)|
Figure 2: Graph of e0(μ) for μ ≤ 36.
Figure 3: Graph of e4(μ) for μ ≤ 36.
We now show the following convergence:
Lemma 7.3. The Fourier transform of kλ converges, when λ → ∞, towards the Ξ-function of Riemann uniformly on closed substrips of the open strip |I(z)| < 1
2.
Proof. We now investigate what happens when we apply the map E while the variable is restricted to the interval [λ−1, λ]. For u in this interval, the number of integers n such that nu ≤ λ is at most λ/u, thus with
δ(λ) := max
x∈[−λ,λ]
|hλ(x) − h(x)|


32 8. The missing steps
one gets, using the definition of E which involves u1/2
|E(hλ)(u) − E(h)(u)| ≤ u1/2δ(λ) λ
u
We now evaluate the Mellin transform of kλ on the critical strip, i.e.
M(kλ)(s) =
Z∞
0
us−1kλ(u)du, R(s) ∈ [− 1
2, 1
2]
We use the following estimate, where the exponent −2 in u−2 comes from two sources, and α = R(s)
|M(kλ)(s) −
Zλ
λ−1
k(u)us−1du| ≤ λδ(λ)
Zλ
λ−1
uαu1/2u−2du
One has
Zλ
1 λ
uα+ 1
2
u2 du = 2(λ 1
2 −α − λα− 1
2)
1 − 2α
and since α ∈ (− 1
2, 1
2 ) one has 1 − 2α > 0, 1
2 −α>α− 1
2 which gives using (7.8), i.e. δ(λ) ≤ c λ−2
|M(kλ)(s) −
Zλ
λ−1
k(u)us−1du| ≤ 2cλ−1λ 1
2 −α(1 − 2α)−1 = 2cλ− 1
2 −α(1 − 2α)−1
Hence, since α ∈ (− 1
2, 1
2 ), one has 1
2 + α > 0 and one obtains, for fixed α
|M(kλ)(s) −
Zλ
λ−1
k(u)us−1du| = O(λ− 1
2 −α)
It remains to control the remainder in the Mellin transform of k. By the Poisson formula one has k(u) = k(u−1) and thus it is enough to control
Z∞
λ
k(u)us−1du
but this tends to 0 when λ → ∞ due to the convergence of the integral.
8 The missing steps
There are two essential steps still missing to justify our tentative proof of the Riemann Hypothesis. The first is that, in order to apply Theorem 5.10 to the Weil quadratic form QWλ, one must prove that its smallest eigenvalue—whose existence is ensured by Theorem 3.6—is simple and that its corresponding eigenvector ξλ is even. The second step is to establish that kλ provides a sufficiently accurate approximation to (a scalar multiple of) ξλ, in order to justify the convergence of the zeros of ξbλ towards the non-trivial zeros of ζ( 1
2 + is). There are, however, three indications supporting the feasibility of these steps. (1) The “simple-even” condition holds for all values of λ for the prolate-wave operator P Wλ.


33 8. The missing steps
(2) The extremely small numbers ελ that occur as eigenvalues of the Weil quadratic form QWλ also appear—see Figure 4—when evaluating the discrepancy for hλ to belong simultaneously to Pλ and
Pbλ.
(3) The numerical evidence for the proximity between kλ and ξλ extends to the higher eigenfunctions of the Weil quadratic form.
Figure 4: Graphs of log(ελ)) and log(1 − χ(λ))) as functions of μ = λ2.
It remains possible that our strategy for proving convergence towards the zeros of ζ( 1
2 + is) will face significant obstacles. Nevertheless, it provides a strong motivation to further develop the relationship, first uncovered in [3], between the Weil quadratic form QWλ and the prolate-wave operator P Wλ. The cornerstone of this development is the trace formula established in [3], which relates Pλ, Pbλ, and the map E to QWλ. Yet, regardless of how far one can progress along this path, the present approach naturally opens the way to a deeper exploration of the unexpected relationship between two seemingly distant mathematical worlds.
The world of the Weil quadratic form. A key discovery of Andr ́e Weil is the following remarkable fact: the Riemann Hypothesis is equivalent to the positivity of certain quadratic forms that involve only finitely many primes. This is striking, since one might expect that addressing the Riemann Hypothesis would require control over the entire infinite set of primes. Here, however, the problem acquires a local character, reducing to finite collections at a time. Moreover, in this framework, as we have seen, one can exploit our general construction of functions whose zeros lie entirely on the critical line.
The world of prolate wave functions. Developed by David Slepian and collaborators, and rooted in Claude Shannon’s work on communication theory, this theory exhibits the miraculous relationship between the orthogonal projections that define time and frequency limitations in signal analysis and a classical second-order differential operator on the real line: the prolate wave operator, itself obtained as a confluence from the Heun equation—an object entirely familiar within Riemann’s mathematical universe.
The prolate operator plays a dual role. In the infrared regime, it provides a tool for approximating


34 REFERENCES
the minimal eigenvector of the Weil quadratic form. At the opposite, ultraviolet, end it also furnishes—cf. [6]—a model of a self-adjoint operator whose spectrum reflects the high-frequency (ultraviolet) behavior of the zeros of the Riemann zeta function. This duality emphasizes how ideas from information theory, spectral analysis, and number theory converge within a unified framework, turning the relation between QWλ and P Wλ into a fertile ground for further exploration.
References
[1] E. Bombieri, The Riemann Hypothesis, in: The Millennium Prize Problems, J. Carlson, A. Jaffe, and A. Wiles (eds.), Clay Math. Inst./AMS, 2006, 107–124. 3
[2] C. Carath ́eodory und L. Fej ́er,  ̈uber den Zusammenhang der Extreme von Harmonischen Funktionen mit ihren Koeffizienten und u ̈ber den Picard-Landauschen Satz. Rend. Circ. Mat. Palermo 32 (1911)218-239. 1
[3] A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Selecta Math. (N.S.) 5 (1999), no. 1, 29–106. 1, 8
[4] A. Connes, C. Consani, Spectral triples and ζ–cycles. Enseign. Math. 69 (2023), no. 1–2, 93-148. (document), 1, 3.3, 3.4, 3.2, 3.2, 7, 7, 7
[5] A. Connes, C. Consani, H. Moscovici, Zeta zeros and prolate wave operators, ArXiv :2310.18423.
[6] A. Connes, H. Moscovici, The UV prolate spectrum matches the zeros of zeta. Proc. Natl. Acad. Sci. USA 119 (2022), no. 22. 8
[7] A. Connes and W. van Suijlekom, Quadratic Forms, Real Zeros and Echoes of the Spectral Action, Commun. Math. Phys. (2025) 406:312, volume dedicated to H. Araki. (document), 1, 5.2
[8] Fuchs, W. H. J. On the eigenvalues of an integral equation arising in the theory of band-limited signals. J. Math. Anal. Appl. 9 (1964), 317-330. 7
[9] J. Meixner and F. W. Scha ̈fke, Mathieusche Funktionen und Spha ̈roidfunktionen. Springer, Berlin, 1954. 7, 7, 7, 7
[10] B. Riemann, U ̈ber die Anzahl der Primzahlen unter einer gegebenen Gr ̈oße, Monatsberichte der K ̈oniglich Preußischen Akademie der Wissenschaften zu Berlin (1859), 671–680. 1, 7
[11] B. Riemann, U ̈ber die Darstellbarkeit einer Function durch eine trigonometrische Reihe (On the Representability of a Function by a Trigonometric Series) Abhandlungen der K ̈oniglichen Gesellschaft der Wissenschaften zu Go ̈ttingen, vol. 13 (1867), pp. 87-132.
[12] K. Schmu ̈dgen, Unbounded Self-adjoint operators on Hilbert Space, Graduate Texts in Mathematics 265. Springer. 3.2, 3.2, 3.2
[13] S. G. Scott and K. P. Wojciechowski, The ζ-Determinant and Quillen determinant for a Dirac operator on a manifold with boundary. GAFA, Geom. funct. anal. Vol. 10 (2000) 1202 – 1236. 5.5
[14] B. Simon, The classical moment problem as a self-adjoint finite difference operator, Adv. Math., 137 (1998), 82-203.
[15] D. Slepian and H. Pollack, Prolate spheroidal wave functions, Fourier analysis and uncertainty, Bell Syst. Tech. J. (1961), 43–63. 1
[16] A. Weil, Sur les formules explicites de la th ́eorie des nombres premiers, Comm. S ́em. Math. Univ. Lund, 1952, 252–265. 3
Alain Connes Caterina Consani Henri Moscovici Coll`ege de France Department of Mathematics Department of Mathematics 3 Rue d’Ulm Johns Hopkins University Ohio State University 75005 Paris Baltimore, MD 21218 Columbus, OH 43210 France USA USA alain@connes.org cconsan1@jhu.edu moscovici.1@osu.edu