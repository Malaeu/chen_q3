---
title: "Numbers as functions"
authors:
  - "Yuri I. Manin"
date: "2013-10-00 10/2013"
publication: "P-Adic Numbers, Ultrametric Analysis, and Applications"
doi: "10.1134/S2070046613040055"
url: "http://arxiv.org/abs/1312.5160"
zotero:
  attachment_key: "TV94Y7ES"
  parent_key: "5DPZBPWU"
  item_id: 1828
  attachment_item_id: 1857
---

arXiv:1312.5160v1 [math.NT] 18 Dec 2013
NUMBERS AS FUNCTIONS1
Yuri I. Manin
Max–Planck–Institut fu ̈r Mathematik, Bonn, Germany
ABSTRACT. In this survey I discuss A. Buium’s theory of “differential equations in the p–adic direction” ([Bu05]) and its interrelations with “geometry over fields with one element”, on the background of various approaches to p–adic models in theoretical physics (cf. [VlVoZe94], [ACG13]).
Introduction
One of the most beautiful (arguably, the most beautiful) mathematical formulas is Euler’s identity eπi = −1. (0.1)
It connects four numbers π = 3, 1415912 . . . , e = 2, 71828 . . . , i = √−1, and −1 itself, and has a very strong physical flavor being the base of the universal principle of “interference of probability amplitudes” in quantum mechanics and quantum field theory. The “−1” in the right hand side of (0.1) shows how two quantum states with opposite phases may annihilate each other after superposition.
On the other hand, of these four numbers π, e, i, −1, only π looks as something similar to a “physical constant” in the sense that it can be (and was) measured, with a certain approximation.
Moreover, the traditional names of the respective classes of numbers, which we nowadays tend to perceive as mathematical terms introduced by precise definitions in courses of calculus, – irrational, transcendent, imaginary, negative, – in the course of history conveyed the primeval bafflement of the rational mind, discovering these numbers but reluctant to accept them.
We may recall that at the time of their discovery these numbers had very different sources of justification: π in Euclidean geometry (which describes essentially kinematics of solids in gravitational vacuum), −1 in commerce (“debt”), e in the early history of computer science (Napier’s implementation of the discovery that a specific precomputation can facilitate everyday tasks of multiplication), i in the early history of polynomial equations.
1Based on talks at the International Workshop on p–adic methods for modelling of complex systems, Bielefeld, April 15–19, 2013, and at Journe ́es Arithme ́tiques, Grenoble, June 2–5, 2013.
1


 2
When I was asked to deliver a talk at the Workshop on p–adic Methods for Modelling of Complex Systems, I decided to present first a p–adic environment of π and e.
Probably, the earliest “arithmetic” formula involving π is due to Euler (as well as (0.1)):
π2
6 =∏
p
(1 − p−2)−1. (0.2)
However, it involves all primes p simultaneously, and in fact, can be best understood as a fact from ad`elic geometry. As such, it looks as a generalisation of the simple
minded product formula ∏
v |a|v = 1 valid for all a ∈ Q∗, where v runs over all valuations of Q, p–adic ones and archimedean one. To be more precise, (0.2) expresses the fact that the natural adelic measure of SL(2, AQ)/SL(2, Q) equals 1. For some more details, cf. [Ma89], where it was suggested that fundamental quantum physics might be related to number theory via this ad`elic philosophy, “democracy of all valuations”, and the exclusive use of real and complex numbers in our standard formalisms is the matter of tradition, which we now try to overcome by replacing “the first among equals” archimedean valuation by an arbitrary nonarchimedean one.
Now we turn to e. Here, as the discoverer of p–adic numbers Kurt Hensel himself remarked, we have a candidate for ep in each p–adic field, since the (archimedean) series for ep converges also p–adically:
ep =
∞ ∑
n=0
pn
n! . (0.3)
Since the root of degree p of the right hand side of (0.3) understood as p–adic number generates an extension of Qp of degree p, there can be no algebraic number with such local components.
This argument looks tantalisingly close to a proof of transcendence of e, although, of course, it is not one. On the other hand, I do not know any ad`elic formula involving e in such a way as (0.2) involves π.
In this survey, I proceed with discussion consisting of three main parts.
A. I will describe a class of numbers (including transcendental ones) relevant for Quantum Field Theory in the sense that they define the coefficients of perturbative


 3
series for Feynmann’s path integrals. These numbers are called (numerical) periods, they were introduced and studied in [KoZa01].
Roughly speaking, numerical periods are values at algebraic points of certain multi–valued transcendental functions, naturally defined on various moduli spaces, and also traditionally called (functions–)periods.
These functions–periods satisfy differential equations of Picard–Fuchs type, and such equations furnish main tools for studying them.
In the second part of this survey, I focus on the following program:
B. For a prime p, numerical periods also can be considered as solutions of “differential equations in the p–adic direction”.
The whole machinery of such differential equations was suggested and developed by Alexandru Buium, cf. his monograph [Bu05], and I briefly review it. I use the catchword “numbers as functions” to name this analogy.
Alexandru Buium has convincingly shown that the right analog of the p–adic derivation is (a natural generalization of) the Fermat quotient δp(a) := (a − ap)/p initially defined for a ∈ Z. Unexpectedly, this formal idea had rich consequences: Buium was able to construct analogs of classical jet spaces “in the p–adic direction”, together with a theory of functions on these jet spaces, containing an incredible amount of analogs of classical constructions traditionally requiring calculus.
Those numerical periods that were already treated by Buium include periods of abelian varieties defined over number (or even p–adic) fields. (But the reader should be aware that, in the absence of uniformization, this last statement only very crudely describes a pretty complicated picture; see more details in the main text.)
C. For Buium’s differential equations, “constants in the p–adic direction” turn out to be roots of unity and zero: Teichm ̈uller’s representatives of residue classes modulo p.
Until recently, algebraic geometry over such constants was motivated by very different insights: for a more detailed survey cf. [Ma95], [Ma08]. It is known as “theory of the field F1”.
Briefly, this last field of inquiry is focused on the following goal: to make the analogy between, say, Spec Z (or spectra of rings of algebraic integers) on the one hand, and algebraic curves over finite fields, on the other hand, so elaborated and


 4
precise that one could use a version of the technique of Andr ́e Weil, Alexander Grothendieck and Pierre Deligne in order to approach Riemann’s conjecture for Riemann’s zeta and similar arithmetic functions.
The solid bridge between F1–geometry and arithmetic differential equations was constructed by James Borger: cf. [Bor11a,b], [Bor09], [BorBu09]. Roughly speaking, in order to define the p–adic derivative δp of elements of a commutative ring A, one needs a lift of the Frobenius map, that is an endomorphism a 7→ F (a), such that F (a) ≡ ap mod p. Borger remarked that a very natural system of such lifts for all p simultaneously is encoded in the so called psi–structure or its slight modification, lambda–structure, and then suggested to consider such a structure as descent data on Spec A to F1. A related notion of “cyclotomic coordinates” in F1was independently suggested in [Ma08]. In particular, a ∈ A is a cyclotomic co–ordinate (wrt a prime p) if F (a) = ap. I will return to these ideas in the last part of this survey.
Finally, I should mention that there exists a very well developed deep theory of “p–adic periods” for algebraic varieties defined over p–adic fields that replaced the classic integration of differential forms over topological cycles with comparison of algebraic de Rham and  ́etale cohomology theories: see [Fa88] and a recent contribution and brief survey [Be11]. Periods in this setting belong to a very big Fontaine’s field BdR. The approach to periods via Buium’s p–adic geometry that we describe in this survey has a very different flavour. It would certainly be important to find connections between the two theories.
1. Periods
1.1. Numerical periods. M. Kontsevich and D. Zagier introduced an important subring P ⊂ C containing all algebraic numbers and a lot of numbers important in physics (see [KoZa01]).
1.1.1. Definition. α ∈ P if and only if the real and imaginary parts of α are values of absolutely convergent integrals of functions in Q(x1, . . . , xn) over chains in Rn given by polynomial (in)equalities with coefficients in Q.
1.1.2. Examples. a) All algebraic numbers are periods.
b) π = ∫ ∫
x2+y2≤1 dxdy.
c) Γ (p/q)q ∈ P.


 5
It is not difficult to prove that periods form a subring of C. Feynman integrals (of a certain class) are periods. But it is still not known whether π−1, e, or Euler’s constant γ are periods (probably, not). There is a close connection between periods and Grothendieck motives (see [KoZa01]), and 2πi corresponds to the Tate’s motive. Since in the motivic formalism one formally inverts the Tate motive, it is also useful to extend the period ring by (2πi)−1.
d) The multiple ζ–values (Euler)
ζ(n1, ..., nm) = ∑
0<k1 <...<km
1
k1n1 ... knmm
, ni ≥ 1, nm > 1 . (1.1)
are periods.
In order to see it, we reproduce the Leibniz and Kontsevich integral formula for them.
Let n1, . . . , nm be positive integers as in (1.1). Put n := n1 + · · · + nm, and ε := (ε1, ..., εn) where εi = 0 or 1, and εi = 1 precisely when i ∈ {1, n1 + 1, n1 + n2 + 1, . . . , n1 + · · · + nm−1 + 1}. Furthermore, put
ω(ε) := dt1
t1 − ε1
∧ ... ∧ dtn
tn − εn
and
∆0n := {(t01, . . . , t0n) ∈ Rn | 0 < t01 < · · · < t0n < 1}
Then we have
ζ(n1, . . . , nm) = ζ(ε) = (−1)m
∫
∆0n
ω(ε).
For further details, see [GoMa04], where the mixed motives associated with these periods were identified: they are constructed using moduli spaces M 0,n and their canonical stratifications.
1.2. Periods–functions. Sometimes we may introduce parameters in the description of elements of P sketched above and thus pass to the study of periods as functions. To this end, it is first convenient to rewrite the definition in a more formal algebraic–geometric framework as was already done in [KoZa01], sec. 4.1.
Consider a quadruple (V, D, ω, γ). Here V is a smooth algebraic variety of pure dimension n, endowed with divisor D with normal crossings, n–form ω regular


 6
outside D, and a homology class γ ∈ Hn(V (C), D(C); Q). Moreover, (V, D, ω)
must be defined over Q, and the integral ∫
γ ω must converge. Then the set of such integrals coincides with the period ring P defined above.
It is now clear how to relativise this definition, replacing V by a relatively smooth morphism f : V → S defined over Q, endowed with an appropriate S–family of data (D, ω, γ) having the necessary properties fiberwise.
Then we get interesting, generally transcendental functions on the base S, and eventually on moduli spaces/stacks, and these functions satisfy (versions of) classical Picard–Fuchs equations.
1.2.1. Example 1. Let S be the affine line with t–coordinate, and points t = 0, 1 deleted. Over it, we have the family E of elliptic curves Et , that are projective closures of the affine curve Et : Y 2 = X(X − 1)(X − t).
Here is the linear DE for the periods of the relative (over the base) 1–form dX/Y along the closed fiberwise 1–cycles of Et:
Ltω := 4t(1 − t) d2ω
dt2 + 4(1 − 2t) dω
dt − ω = 0. (1.2)
Example 2. Non–linear DE for the periods of dX/Y over relative 1–cycles with boundaries at sections P := (X(t), Y (t)) of finite order:
μ(P ) = 0, (1.3)
where
μ(P ) := Y (t)
2(X(t) − t)2 − d
dt
[
2t(t − 1) X′(t)
Y (t)
]
+ 2t(t − 1)X′(t) Y ′(t)
Y (t)2 . (1.4)
Notice that μ defined by (1.3) and extended to the function on the set of Lpoints of the generic fiber Et with values in any differential extension L of Q(t) is “a differential character”:
μ(P + Q) = μ(P ) + μ(Q) (1.5)
To explain (and prove) these results, it suffices to notice that
μ(P ) = Lt
∫P
∞
dX/Y


 7
because
Lt(dX/Y ) = d Y
(X − t)2 .
1.3. Perturbative Feynman integrals. Here I will briefly describe the heuristic origin of a set of numerical periods (and periods–functions) indexed by labeled graphs relevant for quantum field theory, following [Ma09], sec. 1. For a more focussed study of (some) of the integrals appearing in this way see [Mu ̈WZa12] and [W13].
A Feynman path integral is an heuristic expression of the form
∫
P eS(φ)D(φ)
∫
P eS0(φ)D(φ) (1.6)
or, more generally, a similar heuristic expression for correlation functions.
Here the integration domain P stands for a functional space of classical fields φ on a space–time manifold M . Space–time may be endowed with a fixed Minkovski or Euclidean metric. In models of quantum gravity metric is one of the fields. Fields may be scalar functions, tensors of various ranks, sections of vector bundles, connections.
S : P → C is a functional of classical action: generally S(φ) is expressed as an integral over M of a local density on M which is called Lagrangian. In
our notation (1.6) S(φ) = − ∫
M L(φ(x))dx. Lagrangian density may depend on
derivatives, include distributions etc.
Usually S(φ) is represented as the sum of a quadratic part S0(φ) (Lagrangian of free fields) and remaining terms which are interpreted as interaction and treated perturbatively.
Finally, the integration measure D(φ) and the integral itself ∫
P should be consid
ered as simply a part of the total expression (1.6) expressing the idea of “summing the quantum probability amplitudes over all classical trajectories”.
To explain the appearance and combinatorics of Feynman graphs, we consider a toy model, in which P is replaced by a finite–dimensional real space. We endow it with a basis indexed by a finite set of “colors” A, and an Euclidean metric g encoded by the symmetric tensor (gab), a, b ∈ A. We put (gab) = (gab)−1.


 8
The action functional S(φ) will be a formal series in linear coordinates on P, (φa), of the form
S(φ) = S0(φ) + S1(φ), S0(φ) := − 1
2
∑
a,b
gabφaφb,
S1(φ) :=
∑ ∞
k=1
1 k!
∑
a1 ,...,ak ∈A
Ca1,...,ak φa1 . . . φak (1.7)
where (Ca1,...,an ) are certain symmetric tensors. If these tensors vanish for all sufficiently large ranks n, S(φ) becomes a polynomial and can be considered as a genuine function on P. Below we will treat (gab) and (Ca1,...,an) as independent formal variables, “formal coordinates on the space of theories”.
Now we can express the toy version of (1.6) as a series over (isomorphism classes of) graphs.
Here a graph τ consists of two finite sets, edges Eτ and vertices Vτ , and the incidence map sending Eτ to the set of unordered pairs of vertices. Each vertex is supposed to be incident to at least one edge. There is one empty graph.
The formula for (1.6) including one more formal parameter λ (“Planck’s constant”) looks as follows:
∫
P eλ−1S(φ)D(φ)
∫
P eλ−1S0(φ)D(φ) = ∑
τ ∈Γ
λ−χ(τ )
|Aut τ | w(τ ) (1.8)
In the right hand side of (1.8), the summation is taken over (representatives of) all isomorphism classes of all finite graphs τ . The weight w(τ ) of such a graph is determined by the action functional (1.2) as follows:
w(τ ) := ∑
u: Fτ →A
∏
e∈Eτ
gu(∂e) ∏
v∈Vτ
Cu(Fτ (v)) . (1.9)
Here Fτ is the set of flags, or “half–edges” of τ . Each edge e consists of a pair of flags denoted ∂e, and each vertex v determines the set of flags incident to it denoted Fτ (v). Finally, χ(τ ) is the Euler characteristic of τ .


 9
The passage of the left hand side of (1.8) to the right hand side is by definition the result of term–wise integration of the formal series which can be obtained from the Taylor series of the exponent in the integrand. Concretely
∫
P
eλ−1S(φ)D(φ) =
∫
P
eλ−1 S0 (φ)
(
1+
∞ ∑
N =1
λ−N S1(φ)N N!
)∏
a
dφa :=
∫
P
eλ−1S0(φ) ∏
a
dφa +
∞ ∑
N =1
λ−N
N!
∞ ∑
k1,...,kN =1
1
k1! . . . kN !
∑
a(i)
j ∈A,1≤j≤ki
N ∏
i=1
Ca(i)
1 ,...,a(i)
ki
∫
P
eλ−1 S0 (φ)
N ∏
i,j
φa(i)
j
∏
a
dφa .
(1.10)
This definition makes sense if the right hand side of (1.10) is understood as a formal series of infinitely many independent weighted variables Ca1,...,ak, weight of Ca1,...,ak being k. In fact, the Gaussian integrals in the coefficients uniformly converge, and one can use the so called Wick’s lemma.
The last remark is that periods appearing in concrete models of quantum field theories are weights (1.9), in which the summation over maps u : Fτ → A is replaced by the integration over some continuous variables such as positions/momenta/colours of particles moving along the edges of the respective Feymann graph: cf. [W13], [Mu ̈WZa12] and references therein.
2. Arithmetic differential equations
2.1. Analogies between p–adic numbers and formal series. Combining the lessons of previous examples we suggest now that in order to see “p–adic properties” of numerical periods, transcendental numbers important for physics, one could try to design a theory of “derivations in p–adic direction” and interpret numerical periods as solutions of differential equations in the p–adic direction.
Below we present basics of such a theory due to A. Buium. We start with the following table of analogies. On the formal series side, we consider rings of the form k[[t]] where k is a field of characteristics zero. On the p–adic side, we consider the maximal unramified extension R of Zp.


 10
P OW ER SERIES p − ADICS
∑ aiti ∈ k[[t]] =: L ∑ εipi ∈ R := Zpun
Field of constants: ai ∈ k Monoid: εi ∈ μ∞ ∪ {0}
(Teichm ̈uller representatives)
Derivation: d/dt δp(∗) := Φ(∗)−∗p
p
(Φ := lif t of F robenius)
Polynomial Diff. Operators (PDO): p-adic PDO:
D ∈ L[T0, T1, . . . , Tn] Dp ∈ R[T0, T1, . . . , Tn]
(p–adic completion!)
—————————————————————————Action of PDO: f 7→ D(f, f ′, . . . f (n)) or Dp(f, δpf, . . . , δpnf ) —————————————————————————
The Frobenius lift Φ : R → R involved in the definition of the p–adic derivative
δp is given explicitly as Φ(∑ εipi) := ∑ εp
i pi.
2.2. Examples and applications. Here we give a sample of interesting p–adic differential operators.
2.2.1. Example 1: p–adic logarithmic derivative. It is an analog of the map
Gm(L) → Ga(L) : f 7→ f ′/f (2.1)
where a point x ∈ Gm(L) is represented by the value f ∈ L∗ at x of a fixed algebraic character t of Gm such that Gm = Spec [t, t−1]. Similarly, its p–adic version is the differential character Gm(R) → Ga(R) :
a 7→ δpa · a−p − p
2 (δpa · a−p)2 + p2
3 (δpa · a−p)3 − . . . (2.2)


 11
Example 2: Quadratic reciprocity symbol:
(a
p
)
= a p−1
2
(
1+
∞ ∑
k=1
(−1)k−1 (2k − 2)!
22k−1(k − 1)!k! (δpa)ka−pk
)
.
Example 3: a p–adic analog of the differential character μ of the group of sections of a generic elliptic curve:
μ(P ) = (4t(1 − t) d2
dt2 + 4(1 − 2t) d
dt − 1)
∫P
∞
dX Y
as a non–linear p–adic DO acting upon coordinates of P .
Such analogs were constructed in [Bu95] also for abelian varieties of arbitrary dimension and called δp–differential characters ψ(P ). More precisely, let E be an elliptic curve over R. Then there exist a differential additive map ψ : E(R) → R+ of order 2 (as in the geometric case) or 1 (as for Gm).
A character of order 2 exists if E has a good reduction and is not the canonical lift of its reduction in the sense of Serre–Tate: cf. additional discussion in 4.4 below.
A character of order 1 exists if either E has good ordinary reduction and is the canonical lift, or E has a bad multiplicative reduction.
Using these multiplicative characters, A. Buium and the author constructed in [BuMa13] “Painlev ́e VI equations with p–adic time.”
2.3. General formalism of p–derivations. In the commutative algebra, given a ring A and an A–module N , a derivation of A with values in N is any additive map ∂ : A → N such that ∂(ab) = b∂a + a∂b. Equivalently, the map A → A × N : a 7→ (a, ∂a) is a ring homomorphism, where A × N is endowed with the structure of commutative ring with componentwise addition, inheriting multiplication from A on A × {0} and having {0} × N as an ideal of square zero.
Similarly, in arithmetic geometry Buium defines a p–derivation of A with values in an A–algebra B, f : A → B, as a map δp : A → B such that the map A → B × B : a 7→ (f (a), δp(a)) is a ring homomorphism A → W2(B) where W2(B) is the ring of p–typical Witt vectors of length 2. Here Witt vectors of the form (0, b) form the ideal of square zero only if pB = {0}.


 12
Making this definition explicit, we get δp(1) = 0, and the following versions of additivety and Leibniz’s formula:
δp(x + y) = δp(x) + δp(y) + Cp(x, y), (2.3)
δp(xy) = f (x)p · δp(y) + f (y)p · δp(x) + p · δp(x) · δp(y), (2.4)
where
Cp(X, Y ) := Xp + Y p − (X + Y )p
p ∈ Z[X, Y ]. (2.5)
In particular, this implies that for any p–derivation δp : A → B the respective map φp : A → B defined by φp(a) := f (a)p + pδp(a) is a ring homomorphism satisfying φp(x) ≡ f (x)p mod p, that is “a lift of the Frobenius map applied to f ”.
Conversely, having such a lift of Frobenius, we can uniquely reconstruct the respective derivation δp under the condition that B has no p–torsion:
δp(a) := φp(a) − f (a)p
p
generalising the definition given in 2.1 for A = B = R and identical morphism.
Working with p–derivations A → A with respect to the identity map A → A and keeping p fixed, we may call (A, δ) a δ–ring. Morphisms of δ–rings are algebra morphisms compatible with their p–derivations.
2.4. p–jet spaces. Let A be an R–algebra. A prolongation sequence for A consists of a family of p–adically complete R–algebras Ai, i ≥ 0, where A0 = Â is the p–adic completion of A, and of maps φi, δi : Ai → Ai+1 satisfying the following conditions:
a) φi are ring homomorphisms, each δi is a p–derivation with respect to φi, compatible with δ on R.
b) δi ◦ φi−1 = φi ◦ δi−1 for all i ≥ 1.
Prolongation sequences form a category with evident morphisms, ring homomorphisms fi : Ai → Bi commuting with φi and δi, and in its subcategory with fixed A0 there exists an initial element, defined up to unique isomorphism (cf. [Bu05], Chapter 3). It can be called the universal prolongation sequence.


 13
In the geometric language, if X = Spec A, the formal spectrum of the i–th ring Ai in the universal prolongation sequence is denoted Ji(X) and called the i–th p–jet space of X. Conversely, Ai = O(Ji(X)), the ring of global functions.
The geometric morphisms (of formal schemes over Z) corresponding to φi are denoted φi : J i(X) → J 0(X) =: X̂ (formal p–adic completion of X).
This construction is compatible with localisation so that it can be applied to the non–necessarily affine schemes: cf. [Bu05], Chapter 3.
3. An arithmetically global version of Buium’s calculus
and lambda–rings
3.1. Introduction. p–adic numbers were considered in sec. 2 above as analogs of formal functions/local germs of functions of one variable.
In this section, we discuss the following question: does there exist a (more) global version of “arithmetic functions”, elements of a ring A, admitting p–adic derivations δp with respect to several, eventually all primes p?
An obvious example is Z:
δp(m) = m − mp
p.
Generally, we need “lifts of Frobenii”: such ring endomorphisms Φp : A → A that Φ(a) ≡ ap mod p. Then we may put
δp(a) = Φp(a) − ap
p.
A general framework for a coherent system of such lifts is given by the following definition:
3.2. Definition. A system of psi–operations on a commutative unitary ring A is a family of ring endomorphisms ψk : A → A, k ≥ 1, such that:
ψ1 = idA, ψkψr = ψkr,
ψpx ≡ xp mod pA f or all primes p.


 14
Another important structure is introduced by the following definition:
3.3. Definition. A system of lambda–operations on a commutative unitary ring A is a family of additive group endomorphisms λk : A → A, k ≥ 0, such that
λ0(x) = 1, λ1 = idA,
λn(x + y) = ∑
i+j=n
λi (x)λj (y ).
These structures are related in the following way:
3.4. Proposition. (a) If A has no additive torsion, then any system of psioperations defines a unique system of lambda–operations satisfying the compatibility relations:
(−1)k+1kλk(x) = ∑
i+j=k, j≥1
(−1)j +1 λi (x)ψ j (x).
(b) Generally, any system of lambda–operations defines a unique system of psioperations satisfying the same compatibility relations.
Briefly, such a ring, together with psi’s and lambda’s, is called a lambda–ring.
3.5. Example: a Grothendieck ring. Let R = a commutative unitary ring.
Denote by A = AR the Grothendieck K0–group of the additive category, consisting of pairs (P, φ), where P is a projective R–module of finite type, φ : P → P an endomorphism. Denote by [(P, φ)] ∈ A the class of (P, φ).
The ring structure on A is induced by the tensor product: [(P, φ)][(Q, ψ)] := [(P ⊗ Q, φ ⊗ ψ].
The lambda–operations on A are defined by λk [(P, φ)] := [(ΛkP, Λnφ)].
3.6. Example: the big Witt ring W (R). Again, let R = a commutative unitary ring.
Define the additive group of W (R) as the multiplicative group 1 + T R[[T ]].
The multiplication ∗ in W (R) is defined on elements (1 − at) as (1 − aT ) ∗ (1 − bT ) := 1 − abT , and then extended to the whole W (R) by distributivity, continuity in the (T )–adic topology, and functoriality in R.


 15
Similarly, lambda–operations in W (R) are defined by λk (1 − aT ) := 0 for k ≥ 2, and then extended by addition formulas (Def. 3.3) and continuity.
4. Roots of unity as constants:
geometries over “fields of characteristic 1”
4.1. Early history. In the paper [T57], J. Tits noticed that some basic numerical invariants related to the geometry of classical groups over finite fields Fq have well–defined values for q = 1, and these values admit suggestive combinatorial interpretations.
For example, if q = pk, p a prime, k ≥ 1, then
card Pn−1(Fq) = card (An(Fq) \ {0})
card Gm(Fq) = qn − 1
q − 1 =: [n]q,
card Gr (n, j)(Fq) = card {Pj(Fq) ⊂ Pn(Fq)} =:
(n
j
)
q
,
and the q = 1 values of the right hand sides are cardinalities of the sets
Pn−1(F1):= a finite set P of cardinality n,
Gr (n, j)(F1) := the set of subsets of P of cardinality j.
Tits suggested a program: make sense of algebraic geometry over “a field of characteristic one” so that the “projective geometry” above becomes a special case of the geometry of Chevalley groups and their homogeneous spaces.
The first implementation of Tits’ program was achieved only in 2008 by A. Connes and C. Consani, cf. [CC11], after the foundational work by C. Soul ́e [So04]. However, they required F12 as a definition field.
Earlier, in an unpublished manuscript [KaS], M. Kapranov and A. Smirnov introduced fields F1n on their own right.
They defined F1n as the monoid {0} ∪ μn, where μn is the set of roots of unity of order n. Moreover, they defined a a vector space over F1n as a pointed set (V, 0) with an action of μn free on V \ {0}. The group GL(V ), by definition, consists of permutations of V compatible with action of μn. Kapranov and Smirnov defined the determinant map det : GL(V ) → μn and proved a beautiful formula for the power residue symbol.


 16
Namely, if q = pk ≡ 1 mod n and μn is embedded in Fq∗, Fq becomes a vector space over F1n, and the power residue symbol
(a
Fq
)
n
:= a q−1
n ∈ μn
is the determinant of the multiplication by a in F1n–geometry.
Cf. also [Sm92], [Sm94].
As we noticed in sec. 2, constants with respect to Buium’s derivation δp in R := Zpun are roots of unity (of degree prime to p) completed by 0.
Therefore, in the context of the differential geometry “in the p–adic direction” an independent project of Algebraic Geometry “over roots of unity”, or “in characteristic 1”, or else “over fields F1, F1n, F1∞” acquires a new motivation. Moreover, it becomes enriched with new insights: whereas at the first stage schemes in characteristic 1 were constructed by glueing “spectra of commutative monoids”, now they could be conceived as Z–schemes endowed with lambda–structure considered as descent data: see [Bor11a,b], [Bor09]. Here is a brief survey of Borger’s philosophy, showing that his schemes form a natural habitat for p–adic differential geometries as well.
4.2. Borger’s philosophy. The category of affine F1–schemes Af f1 can be defined as the opposite category of rings endowed with lambda–structures, (A, ΛA), and compatible morphisms. The forgetful functor to the usual category of affine schemes Af f1 → Af f : (A, Λ) 7→ A is interpreted as the functor of base extension ∗ 7→ ∗ ⊗F1 Z.
Thus, a lambda–structure on a ring A is a descent data on Spec A to F1.
In particular, W (Z) must be considered as (a completion of?) Z ⊗F1 Z.
More generally, using general topos theory, Borger globalizes this construction, constructing a natural algebraic geometry of λ–schemes, which should be thought of as a lifted algebraic geometry over F1.
Just as all of usual algebraic geometry is contained in the big  ́etale topos of Z, λ–algebraic geometry is contained in a big topos, which should be thought of as the big  ́etale topos over F1. There is a map of topoi from the big etale topos over Z to the one over F1.


 17
Schemes of finite type over F1 (in this sense, as in most other approaches) are very rigid, combinatorial objects. They are essentially quotients of toric varieties by toric equivalence relations.
Non–finite–type schemes over F1 are more interesting. The big de Rham–Witt cohomology of X “is” the de Rham cohomology of X “viewed as an F1–scheme”. It should contain the full information of the motive of X and is probably a concrete universal Weil cohomology theory.
The Weil restriction of scalars from Z to F1 exists and is an arithmetically global version of Buium’s p–jet space.
In conclusion, we briefly mention some remaining challenges.
4.3. Euler factors at infinity and F1–geometry. In [Ma95], I suggested that there should exist a category of F1–motives visible through the q = 1 point count of F1–schemes. Predictions about such a point count were justified in Soul ́e’s geometry, cf. [So04]. In particular the zetas of non–negative powers of the “Lefschetz (dual Tate) motive” L must be:
Z(L×n, s) = s + n
2π .
This provides a conjectural bridge between F1–geometry and geometry of Spec Z at the archimedean infinity, that is, Arakelov geometry: a Γ–factor of classical zetas, e.g.,
ΓC(s) := [(2π)−sΓ(s)]−1 = ∏
n≥0
s+n 2π
(regularized product) looks like F1–zeta of the dualized inf–dim projective space over F1.
However, this phenomenon remains an isolated observation, and the archimedean prime still remains “first among equals” breaking the democracy of all valuations.
4.4. Other geometries “under Spec Z”. In the traditional algebraic geometry, the special role of Spec Z is related to the fact that it is the final object of the category of schemes. Since it is very far from being “a point–like object”, it seemed natural to imagine that Spec F1, being “really point–like”, will replace it. However, the belief that in an extended algebraic geometry there should necessarily exist a final object, is unfounded. Already in the simplest category of Deligne–Mumford


 18
stacks over a field k, admitting quotients with respect to the trivial action of any finite group G, there is no final object, because we have non–trivial morphisms Spec k → Spec k/G.
This led several authors to the contemplation of more general geometries lying “under Spec Z” but not necessarily at the bottom of the unfathomable abyss: cf. the To ̈en–Vaqui ́e project [TV05].
For example, in the Borger–Buium’s framework we may consider schemes for which Frobenius lifts are given only for some subsets of primes, eventually one prime p, such as the Serre–Tate canonical liftings of Abelian varieties in characteristic p: cf. [Katz81].
More precisely, for the simplest case of elliptic curves, denote by M the p–adic completion of the moduli stack of elliptic curves without supersingular locus. One can define Frobenius lift on this stack: it sends an elliptic curve to its quotient by its canonical subgroup. The latter is defined as the unique closed sub–groupscheme whose Cartier dual is the  ́etale lift to Zp of the Cartier dual of the kernel of Frobenius on the fiber modulo p. This endomorphism also lifts to a natural endomorphism of the universal elliptic curve. So James Borger suggests to say that M “descends to the p–typical F1”, and the same can be said about the universal elliptic curve over it. The p–adic elliptic curves with Frobenius lift are called canonical liftings.
Notice that if we replace the p–adic direction by the functional one, we would simply speak about families of elliptic curves with constant absolute invariants. But p–adic absolute invariants of canonical liftings are by no means “constants” in the naive sense, discussed in sec. 2, that is they are not Teichmu ̈ller representatives: cf. a recent paper by Finotti, ”Coordinates of the j–invariant of the canonical lifting”, posted at http://www.math.utk.edu/ finotti/ , and [Er13].
A better understanding of this discrepancy presents an interesting challenge for the p–adic differential geometry.
Acknowledgements. Collaboration with A. Buium on [BuMa13] helped me much in conceiving this survey. J. Borger generously explained me some of his constructions and motivations. Igor Volovich stimulated the final writing by inviting me to give a talk at the International Workshop on p–adic methods for modelling of complex systems, Bielefeld, April 15–19, 2013. I am grateful to them all.


 19
References
[ACG13] A. Abdessalam, A. Chandra, G. Guadagni. Rigorous quantum field theory functional integrals over the p–adics I: anomalous dimensions. arXiv:1302.5971
[Be11] A. Beilinson. p–adic periods and derived De Rham cohomology. Journ. AMS, vol. 25, no. 3 (2012), 319–327. arXiv:1102.1294
[Bor09] J. Borger. Lambda–rings and the field with one element. arXiv:0906.3146
[BorBu09] J. Borger, A. Buium. Differential forms on arithmetic jet spaces. Selecta Math. (N.S.) 17 (2011), no. 2, 301–335. arXiv:0908.2512
[Bor11a] J. Borger. The basic geometry of Witt vectors, I: The affine case. Algebra Number Theory 5 (2011), no. 2, 231–285.
[Bor11b] J. Borger. basic geometry of Witt vectors. II: Spaces. Math. Ann. 351 (2011), no. 4, 877–933.
[Bu95] A. Buium. Differential characters of Abelian varieties over p–adic fields. Inv. Math., vol. 122 (1995), 309–340.
[Bu05] A. Buium. Arithmetic Differential Equations. AMS Math Surveys and Monographs, vol. 118, 2005.
[BuMa13] A. Buium, Y. Manin. Arithmetic Differential Equations of Painlev ́e VI Type. arXiv:1307.3841
[CC11] A. Connes, C. Consani. On the notion of geometry over F1. J. Algebraic Geom. 20 (2011), no. 3, 525–557.
[CCMa08] A. Connes, C. Consani, M. Marcolli. Fun with F1. J. Number Theory 129 (2009), no. 6, 1532–1561. math.AG/0806.2401
[De04] A. Deitmar. Schemes over F1. In: Number Fields and Function Fields Two Parallel Worlds. Ed. by G. van der Geer, B. Moonen, R. Schoof. Progr. in Math, vol. 239, 2005. math.NT/0404185
[Er13] A. Erdogan. A universal formula for the j–invariant of the canonical lifting. arXiv:1211.1152
[GoMa04] A. Goncharov, Yu. Manin. Multiple zeta–motives and moduli spaces M 0,n. Compos. Math. 140:1 (2004), 1–14. math.AG/0204102
[Fa88] G. Faltings. p–adic Hodge theory. J. Amer. Math. Soc., 1(1988), 255–288.
[KaS] M. Kapranov, A. Smirnov. Cohomology determinants and reciprocity laws: number field case. Unpublished manuscript, 15 pp.


 20
[Katz81] Katz, N. Serre–Tate local moduli. Algebraic surfaces (Orsay, 1976–78), pp. 138–202, Lecture Notes in Math., 868, Springer, Berlin-New York, 1981.
[KoZa01] M. Kontsevich, D. Zagier. Periods. In: Mathematics unlimited—2001 and beyond, 771–808, Springer, Berlin, 2001.
[LeBr13] L. Le Bruyn. Absolute geometry and the Habiro topology. arXiv:1304.6532
[Ma89] Yu. Manin. Reflections on arithmetical physics. In: Conformal Invariance and string theory (Poiana Brasov, 1987), Academic Press, Boston, MA, 1989, 293–303. Reprinted in “Mathematics as Metaphor”, Selected Essays by Yu. I. Manin, AMS 2007, pp. 149–155.
[Ma95] Yu. Manin. Lectures on zeta functions and motives (according to Deninger and Kurokawa). Ast ́erisque 228:4 (1995), 121–163.
[Ma08] Yu. Manin. Cyclotomy and analytic geometry over F1. In: Quanta of Maths. Conference in honour of Alain Connes. Clay Math. Proceedings, vol. 11 (2010), 385–408. Preprint math.AG/0809.2716.
[Ma09] Yu. Manin. Renormalization and computation I: motivation and background. In: Proceedings OPERADS 2009, eds. J. Loday and B. Vallette, S ́eminaires et Congr`es 26, Soc. Math. de France, 2012, pp. 181–223. Preprint math.QA/0904.4921
[Mu ̈WZa12] S. Mu ̈ller–Stach, S. Weinzierl, R. Zayadeh. Picard–Fuchs equations for Feynman integrals. arXiv:1212.4389
[Sm92] A. L. Smirnov. Hurwitz inequalities for number fields. (Russian). Algebra i Analiz 4 (1992), no. 2, 186–209; translation in St. Petersburg Math. J. 4 (1993), no. 2, 357–375.
[Sm94] A. L. Smirnov. Absolute determinants and Hilbert symbols. Preprint MPI 94/72, Bonn, 1994.
[So04] C. Soul ́e. Les vari ́et ́es sur le corps `a un  ́el ́ement. Mosc. Math. J. 4:1 (2004), 217–244.
[Ti57] J. Tits. Sur les analogues alg ́ebriques des groupes semi–simples complexes. Colloque d’alg`ebre sup ́erieure, Centre Belge de Recherches Math ́ematiques,
E ́tablissement Ceuterick, Louvain, 1957, 261–289.
[TV05] B. To ̈en, M. Vaqui ́e. Au–dessous de Spec Z. J. K-Theory 3 (2009), no. 3, 437–500. math.AG/0509684
[VlVoZe94] V. S. Vladimirov, I. V. Volovich, E. I. Zelenov. p–adic analysis and mathematical physics. Series on Soviet and East European Math., 1. World Scientific, River Edge, NJ, 1994.


 21
[W13] S. Weinzierl. Periods and Hodge structures in perturbative quantum field theory. arXiv:1302.0670 [hep–th]