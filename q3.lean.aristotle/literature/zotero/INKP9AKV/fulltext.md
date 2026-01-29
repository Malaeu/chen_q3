---
title: "Variants of the Selberg sieve, and bounded intervals containing many primes"
authors:
  - "D. H. J. Polymath"
date: "2014-00-00 2014"
publication: "Research in the Mathematical Sciences"
doi: "10.1186/s40687-014-0012-7"
url: null
zotero:
  attachment_key: "WWZFBVNI"
  parent_key: "INKP9AKV"
  item_id: 2312
  attachment_item_id: 2316
---

Polymath Research in the Mathematical Sciences 2014, 1:12 http://www.resmathsci.com/content/1/1/12
RESEARCH ARTICLE Open Access
Variants of the Selberg sieve, and bounded intervals containing many primes
DHJ Polymath
Correspondence: tao@math.ucla.edu
http://michaelnielsen.org/polymath1/ index.php
Abstract
For any m ≥ 1, let Hm denote the quantity lim infn→∞(pn+m − pn). A celebrated recent result of Zhang showed the finiteness of H1, with the explicit bound H1 ≤ 70, 000, 000. This was then improved by us (the Polymath8 project) to H1 ≤ 4680, and then by Maynard to H1 ≤ 600, who also established for the first time a finiteness result for Hm for m ≥ 2, and specifically that Hm m3e4m. If one also assumes the Elliott-Halberstam conjecture, Maynard obtained the bound H1 ≤ 12, improving upon the previous bound H1 ≤ 16 of Goldston, Pintz, and Yıldırım, as well as the bound Hm m3e2m. In this paper, we extend the methods of Maynard by generalizing the Selberg sieve further and by performing more extensive numerical calculations. As a consequence, we can obtain the bound H1 ≤ 246 unconditionally and H1 ≤ 6 under the assumption of the generalized Elliott-Halberstam conjecture. Indeed, under the latter conjecture, we show the stronger statement that for any admissible triple (h1, h2, h3), there are infinitely many n for which at least two of n + h1, n + h2, n + h3 are prime, and also obtain a related disjunction asserting that either the twin prime conjecture holds or the even Goldbach conjecture is asymptotically true if one allows an additive error of at most 2, or both. We also modify the ‘parity problem’ argument of Selberg to show that the H1 ≤ 6 bound is the best possible that one can obtain from purely sieve-theoretic considerations. For larger m, we use the distributional results obtained previously by
our project to obtain the unconditional asymptotic bound Hm me
(4− 28
157
)m or
Hm me2m under the assumption of the Elliott-Halberstam conjecture. We also obtain explicit upper bounds for Hm when m = 2, 3, 4, 5.
Keywords: Selberg sieve; Elliott-Halberstam conjecture; Prime gaps
Background
For any natural number m, let Hm denote the quantity
Hm := lim inf
n→∞ ( pn+m − pn) ,
where pn denotes the nth prime. The twin prime conjecture asserts that H1 = 2; more
generally, the Hardy-Littlewood prime tuples conjecture [1] implies that Hm = H(m + 1)
for all m ≥ 1, where H(k) is the diameter of the narrowest admissible k-tuple (see the
‘Outline of the key ingredients’ section for a definition of this term). Asymptotically, one
has the bounds
(1
2 + o(1))k log k ≤ H(k) ≤ (1 + o(1)
)
k log k
© 2014 Polymath; licensee Springer. This is an Open Access article distributed under the terms of the Creative Commons Attribution License (http://creativecommons.org/licenses/by/4.0), which permits unrestricted use, distribution, and reproduction in any medium, provided the original work is properly credited.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 2 of 83 http://www.resmathsci.com/content/1/1/12
as k → ∞ (see Theorem 17 below); thus, the prime tuples conjecture implies that Hm is
comparable to m log m as m → ∞.
Until very recently, it was not known if any of the Hm were finite, even in the easi
est case m = 1. In the breakthrough work of Goldston et al. [2], several results in this
direction were established, including the following conditional result assuming the Elliott
Halberstam conjecture EH[θ] (see Claim 8 below) concerning the distribution of the
prime numbers in arithmetic progressions:
Theorem 1 (GPY theorem). Assume the Elliott-Halberstam conjecture EH[θ] for all
0 < θ < 1. Then, H1 ≤ 16.
Furthermore, it was shown in [2] that any result of the form EH [1
2 + 2 ] for some fixed
0 < < 1/4 would imply an explicit finite upper bound on H1 (with this bound equal to
16 for > 0.229855). Unfortunately, the only results of the type EH[θ] that are known
come from the Bombieri-Vinogradov theorem (Theorem 9), which only establishes EH[θ]
for 0 < θ < 1/2.
The first unconditional bound on H1 was established in a breakthrough work of Zhang
[3]:
Theorem 2 (Zhang’s theorem). H1 ≤ 70, 000, 000.
Zhang’s argument followed the general strategy from [2] on finding small gaps between
primes, with the major new ingredient being a proof of a weaker version of EH [ 1
2 + 2 ],
which we call MPZ[ , δ] (see Claim 10) below. It was quickly realized that Zhang’s
numerical bound on H1 could be improved. By optimizing many of the components
in Zhang’s argument, we were able (Polymath, DHJ: New equidistribution estimates of
Zhang type, submitted), [4] to improve Zhang’s bound to
H1 ≤ 4, 680.
Very shortly afterwards, a further breakthrough was obtained by Maynard [5] (with
related work obtained independently in an unpublished work of Tao), who developed a
more flexible ‘multidimensional’ version of the Selberg sieve to obtain stronger bounds on
Hm. This argument worked without using any equidistribution results on primes beyond
the Bombieri-Vinogradov theorem, and among other things was able to establish finite
ness of Hm for all m, not just for m = 1. More precisely, Maynard established the following
results.
Theorem 3 (Maynard’s theorem). Unconditionally, we have the following bounds:
(i) H1 ≤ 600 (ii) Hm ≤ Cm3e4m forall m ≥ 1 andanabsolute(andeffective)constantC
Assuming the Elliott-Halberstam conjecture EH[θ] for all 0 < θ < 1, we have the
following improvements:
(iii) H1 ≤ 12 (iv) H2 ≤ 600 (v) Hm ≤ Cm3e2m forall m ≥ 1 andanabsolute(andeffective)constantC


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 3 of 83 http://www.resmathsci.com/content/1/1/12
For a survey of these recent developments, see [6].
In this paper, we refine Maynard’s methods to obtain the following further
improvements.
Theorem 4. Unconditionally, we have the following bounds:
(i) H1 ≤ 246
(ii) H2 ≤ 398, 130
(iii) H3 ≤ 24, 797, 814
(iv) H4 ≤ 1, 431, 556, 072
(v) H5 ≤ 80, 550, 202, 480
(vi) Hm ≤ Cm exp ((4 − 28
157
) m) forall m ≥ 1 andanabsolute(andeffective)constantC
Assume the Elliott-Halberstam conjecture EH[θ] for all 0 < θ < 1. Then, we have the
following improvements:
(vii) H2 ≤ 270 (viii) H3 ≤ 52, 116 (ix) H4 ≤ 474, 266.
(x) H5 ≤ 4, 137, 854.
(xi) Hm ≤ Cme2m forall m ≥ 1 andanabsolute(andeffective)constantC
Finally, assume the generalized Elliott-Halberstam conjecture GEH[θ] (see Claim 12
below) for all 0 < θ < 1. Then,
(xii) H1 ≤ 6 (xiii) H2 ≤ 252
In the ‘Outline of the key ingredients’ section, we will describe the key propositions
that will be combined together to prove the various components of Theorem 4. As with
Theorem 1, the results in (vii)-(xiii) do not require EH[θ] or GEH[θ] for all 0 < θ < 1,
but only for a single explicitly computable θ that is sufficiently close to 1.
Of these results, the bound in (xii) is perhaps the most interesting, as the parity problem
[7] prohibits one from achieving any better bound on H1 than 6 from purely sieve
theoretic methods; we review this obstruction in the ‘The parity problem’ section. If
one only assumes the Elliott-Halberstam conjecture EH[θ] instead of its generalization
GEH[θ], we were unable to improve upon Maynard’s bound H1 ≤ 12; however, the par
ity obstruction does not exclude the possibility that one could achieve (xii) just assuming
EH[θ] rather than GEH[θ], by some further refinement of the sieve-theoretic arguments
(e.g. by finding a way to establish Theorem 20(ii) below using only EH[θ] instead of
GEH[θ ]).
The bounds (ii)-(vi) rely on the equidistribution results on primes established in our
previous paper. However, the bound (i) uses only the Bombieri-Vinogradov theorem, and
the remaining bounds (vii)-(xiii) of course use either the Elliott-Halberstam conjecture or
a generalization thereof.
A variant of the proof of Theorem 4(xii), which we give in ‘Additional remarks’ section,
also gives the following conditional ‘near miss’ to (a disjunction of ) the twin prime
conjecture and the even Goldbach conjecture:


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 4 of 83 http://www.resmathsci.com/content/1/1/12
Theorem 5 (Disjunction). Assume the generalized Elliott-Halberstam conjecture
GEH[θ] for all 0 < θ < 1. Then, at least one of the following statements is true:
(a) (Twinprimeconjecture) H1 = 2. (b) (near-misstoevenGoldbachconjecture)Ifnisasufficientlylargemultipleof6,then atleastoneofnand n − 2 isexpressibleasthesumoftwoprimes,similarlywith n − 2 replacedby n + 2.(Inparticular,everysufficientlylargeevennumberlies within 2 of the sum of two primes.)
We remark that a disjunction in a similar spirit was obtained in [8], which established
(prior to the appearance of Theorem 2) that either H1 was finite or that every interval
[ x, x + xε] contained the sum of two primes if x was sufficiently large depending on ε > 0.
There are two main technical innovations in this paper. The first is a further general
ization of the multidimensional Selberg sieve introduced by Maynard and Tao, in which
the support of a certain cutoff function F is permitted to extend into a larger domain than
was previously permitted (particularly under the assumption of the generalized Elliott
Halberstam conjecture). As in [5], this largely reduces the task of bounding Hm to that
of efficiently solving a certain multidimensional variational problem involving the cutoff
function F. Our second main technical innovation is to obtain efficient numerical meth
ods for solving this variational problem for small values of the dimension k, as well as
sharpened asymptotics in the case of large values of k.
The methods of Maynard and Tao have been used in a number of subsequent appli
cations [9-21]. The techniques in this paper should be able to be used to obtain slight
numerical improvements to such results, although we did not pursue these matters
here.
Organization of the paper
The paper is organized as follows. After some notational preliminaries, we recall in the
‘Distribution estimates on arithmetic functions’ section the known (or conjectured) dis
tributional estimates on primes in arithmetic progressions that we will need to prove
Theorem 4. Then, in the section ‘Outline of the key ingredients’, we give the key
propositions that will be combined together to establish this theorem. One of these
propositions, Lemma 18, is an easy application of the pigeonhole principle. Two fur
ther propositions, Theorem 19 and Theorem 20, use the prime distribution results from
the ‘Distribution estimates on arithmetic functions’ section to give asymptotics for cer
tain sums involving sieve weights and the von Mangoldt function; they are established
in the ‘Multidimensional Selberg sieves’ section. Theorems 22, 24, 26, and 28 use the
asymptotics established in Theorems 19 and 20, in combination with Lemma 18, to give
various criteria for bounding Hm, which all involve finding sufficiently strong candi
dates for a variety of multidimensional variational problems; these theorems are proven
in the ‘Reduction to a variational problem’ section. These variational problems are anal
ysed in the asymptotic regime of large k in the ‘Asymptotic analysis’ section, and for
small and medium k in the ‘The case of small and medium dimension’ section, with the
results collected in Theorems 23, 25, 27, and 29. Combining these results with the previ
ous propositions gives Theorem 16, which, when combined with the bounds on narrow
admissible tuples in Theorem 17 that are established in the ‘Narrow admissible tuples’


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 5 of 83 http://www.resmathsci.com/content/1/1/12
section, will give Theorem 4. (See also Table 1 for more details of the logical dependencies
between the key propositions.)
Finally, in the ‘The parity problem’ section, we modify an argument of Selberg to show
that the bound H1 ≤ 6 may not be improved using purely sieve-theoretic methods, and in
the ‘Additional remarks’ section, we establish Theorem 5 and make some miscellaneous
remarks.
Notation
The notation used here closely follows the notation in our previous paper.
We use |E| to denote the cardinality of a finite set E, and 1E to denote the indicator
function of a set E; thus, 1E(n) = 1 when n ∈ E and 1E(n) = 0 otherwise.
All sums and products will be over the natural numbers N := {1, 2, 3, . . .} unless other
wise specified, with the exceptions of sums and products over the variable p, which will
be understood to be over primes.
The following important asymptotic notation will be in use throughout the paper.
Definition 6 (Asymptotic notation). We use x to denote a large real parameter, which
one should think of as going off to infinity; in particular, we will implicitly assume that it is
larger than any specified fixed constant. Some mathematical objects will be independent
of x and referred to as fixed; but unless otherwise specified, we allow all mathematical
objects under consideration to depend on x (or to vary within a range that depends on x,
e.g. the summation parameter n in the sum ∑
x≤n≤2x f (n)). If X and Y are two quantities
depending on x, we say that X = O(Y ) or X Y if one has |X| ≤ CY for some fixed
C (which we refer to as the implied constant), and X = o(Y ) if one has |X| ≤ c(x)Y
for some function c(x) of x (and of any fixed parameters present) that goes to zero as
x → ∞ (for each choice of fixed parameters). We use X ≺≺ Y to denote the estimate
X ≤ xo(1)Y , X ∼ Y to denote the estimate Y X Y , and X ≈ Y to denote the
estimate Y ≺≺ X ≺≺ Y . Finally, we say that a quantity n is of polynomial size if one has
n = O (xO(1)).
If asymptotic notation such as O() or ≺≺ appears on the left-hand side of a statement,
this means that the assertion holds true for any specific interpretation of that notation. For
instance, the assertion ∑
n=O(N) |α(n)| ≺≺ N means that for each fixed constant C > 0,
one has ∑
|n|≤CN |α(n)| ≺≺ N.
If q and a are integers, we write a|q if a divides q. If q is a natural number and a ∈ Z, we
use a (q) to denote the residue class
a (q) := {a + nq : n ∈ Z}
Table 1 Results used to prove various components of Theorem 16
Theorem 16 Results used
(i) Theorems 9, 26, and 27 (ii)-(vi) Theorems 11, 24, and 25 (vii)-(xi) Theorems 22 and 23 (xii) Theorems 28 and 29 (xiii) Theorems 26 and 27
Note that Theorems 22, 24, 26, and 28 are in turn proven using Theorems 19 and 20 and Lemma 18.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 6 of 83 http://www.resmathsci.com/content/1/1/12
and let Z/qZ denote the ring of all such residue classes a(q). The notation b = a (q) is
synonymous to b ∈ a (q). We use (a, q) to denote the greatest common divisor of a and
q, and [a, q] to denote the least common multiplea. We also let
(Z/qZ)× := {a (q) : (a, q) = 1}
denote the primitive residue classes of Z/qZ.
We use the following standard arithmetic functions:
(i) φ(q) := |(Z/qZ)×| denotes the Euler totient function of q.
(ii) τ (q) := ∑
d|q 1 denotes the divisor function of q. (iii) (q) denotes the von Mangoldt function of q; thus, (q) = log p if q is a power of a prime p, and (q) = 0 otherwise. (iv) θ(q) is defined to equal log q when q is a prime, and θ(q) = 0 otherwise. (v) μ(q) denotes the Möbius function of q; thus, μ(q) = (−1)k if q is the product of k distinct primes for some k ≥ 0, and μ(q) = 0 otherwise. (vi) (q) denotes the number of prime factors of q (counting multiplicity).
We recall the elementary divisor bound
τ (n) ≺≺ 1 (1)
whenever n xO(1), as well as the related estimate
∑
nx
τ (n)C
n logO(1) x (2)
for any fixed C > 0 (see, e.g. [Lemma 1.5]).
The Dirichlet convolution α β : N → C of two arithmetic functions α, β : N → C is
defined in the usual fashion as
α β(n) := ∑
d|n
α(d)β
(n
d
)
=∑
ab=n
α (a)β (b).
Distribution estimates on arithmetic functions
As mentioned in the introduction, a key ingredient in the Goldston-Pintz-Yıldırım
approach to small gaps between primes comes from distributional estimates on the
primes, or more precisely on the von Mangoldt function , which serves as a proxy for
the primes. In this work, we will also need to consider distributional estimates on more
general arithmetic functions, although we will not prove any new such estimates in this
paper, relying instead on estimates that are already in the literature.
More precisely, we will need averaged information on the following quantity:
Definition 7 (Discrepancy). For any function α : N → C with finite support (that is, α
is non-zero only on a finite set) and any primitive residue class a (q), we define the (signed)
discrepancy (α; a (q)) to be the quantity
(α; a (q)) := ∑
n=a (q)
α(n) − 1
φ(q)
∑
(n,q)=1
α(n). (3)
For any fixed 0 < θ < 1, let EH[θ] denote the following claim:


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 7 of 83 http://www.resmathsci.com/content/1/1/12
Claim 8 (Elliott-Halberstam conjecture, EH[θ]). If Q ≺≺ xθ and A ≥ 1 is fixed, then
∑
q≤Q
sup
a∈(Z/qZ)×
∣∣ ( 1[x,2x]; a (q))∣∣ x log−A x. (4)
In [22], it was conjectured that EH[θ] held for all 0 < θ < 1. (The conjecture fails at the
endpoint case θ = 1; see [23,24] for a more precise statement.) The following classical
result of Bombieri [25] and Vinogradov [26] remains the best partial result of the form
EH[θ ]:
Theorem 9 (Bombieri-Vinogradov theorem). [25,26] EH[θ] holds for every fixed 0 < θ < 1/2.
In [2], it was shown that any estimate of the form EH[θ] with some fixed θ > 1/2 would
imply the finiteness of H1. While such an estimate remains unproven, it was observed
by Motohashi and Pintz [27] and by Zhang [3] that a certain weakened version of EH[θ]
would still suffice for this purpose. More precisely (and following the notation of our
previous paper), let , δ > 0 be fixed, and let MPZ[ , δ] be the following claim:
Claim 10 (Motohashi-Pintz-Zhang estimate, MPZ[ , δ]). Let I ⊂ [1, xδ] and Q ≺≺
x1/2+2 . Let PI denote the product of all the primes in I, and let SI denote the square-free
natural numbers whose prime factors lie in I. If the residue class a (PI) is primitive (and is
allowed to depend on x), and A ≥ 1 is fixed, then
∑
q≤Q q∈SI
∣∣ ( 1[x,2x]; a (q))∣∣ x log−A x, (5)
where the implied constant depends only on the fixed quantities (A, , δ), but not on a.
It is clear that EH [ 1
2 + 2 ] implies MPZ[ , δ] whenever , δ ≥ 0. The first non-trivial
estimate of the form MPZ[ , δ] was established by Zhang [3], who (essentially) obtained
MPZ[ , δ] whenever 0 ≤ , δ < 1
1,168 . In [Theorem 2.17], we improved this result to the
following.
Theorem 11. MPZ[ , δ] holds for every fixed , δ ≥ 0 with 600 + 180δ < 7.
In fact, a stronger result was established, in which the moduli q were assumed to be
densely divisible rather than smooth, but we will not exploit such improvements here. For
our application, the most important thing is to get as large as possible; in particular,
Theorem 11 allows one to get arbitrarily close to 7
600 ≈ 0.01167.
In this paper, we will also study the following generalization of the Elliott-Halberstam
conjecture:
Claim 12 (Generalized Elliott-Halberstam conjecture, GEH[θ]). Let ε > 0 and A ≥ 1
be fixed. Let N, M be quantities such that xε ≺≺ N, M ≺≺ x1−ε with NM x, and let


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 8 of 83 http://www.resmathsci.com/content/1/1/12
α, β : N → R be sequences supported on [N, 2N] and [M, 2M], respectively, such that one
has the pointwise bound
|α(n)| τ (n)O(1) logO(1) x; |β(m)| τ (m)O(1) logO(1) x (6)
for all natural numbers n, m. Suppose also that β obeys the Siegel-Walfisz type bound
∣∣ (β1(·,r)=1; a (q))∣∣ τ (qr)O(1)M log−A x (7)
for any q, r ≥ 1, any fixed A, and any primitive residue class a (q). Then for any Q ≺≺ xθ ,
we have ∑
q≤Q
sup
a∈(Z/qZ)×
∣∣ (α β; a (q))∣∣ x log−A x. (8)
In [28, Conjecture 1], it was essentially conjecturedb that GEH[θ] was true for all 0 <
θ < 1. This is stronger than the Elliott-Halberstam conjecture:
Proposition 13. For any fixed 0 < θ < 1, GEH[θ] implies EH[θ].
Proof. (Sketch) As this argument is standard, we give only a brief sketch. Let A > 0 be
fixed. For n ∈[x, 2x], we have Vaughan’s identityc [29]
(n) = μ< L(n) − μ< < 1(n) + μ≥ ≥ 1(n),
where L(n) := log(n) and
≥(n) := (n)1n≥x1/3 , <(n) := (n)1n<x1/3 (9)
μ≥(n) := μ(n)1n≥x1/3 , μ<(n) := μ(n)1n<x1/3 . (10)
By decomposing each of the functions μ<, μ≥, 1, <, ≥ into O
(
logA+1 x
)
func
tions supported on intervals of the form [N, (1 + log−A x)N], and discarding those
contributions which meet the boundary of [x, 2x] (cf. [3,28,30,31]), and using GEH[θ]
(with A replaced by a much larger fixed constant A′) to control all remaining contri
butions, we obtain the claim (using the Siegel-Walfisz theorem; see, e.g. [32, Satz 4] or
[33, Th. 5.29]).
By modifying the proof of the Bombieri-Vinogradov theorem, Motohashi [34] estab
lished the following generalization of that theorem:
Theorem 14 (Generalized Bombieri-Vinogradov theorem). [34] GEH[θ] holds for
every fixed 0 < θ < 1/2.
One could similarly describe a generalization of the Motohashi-Pintz-Zhang estimate
MPZ[ , δ], but unfortunately, the arguments in [3] or Theorem 11 do not extend to this
setting unless one is in the ‘Type I/Type II’ case in which N,M are constrained to be some
what close to x1/2, or if one has ‘Type III’ structure to the convolution α β, in the sense
that it can refactored as a convolution involving several ‘smooth’ sequences. In any event,
our analysis would not be able to make much use of such incremental improvements to
GEH[θ], as we only use this hypothesis effectively in the case when θ is very close to 1.
In particular, we will not directly use Theorem 14 in this paper.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 9 of 83 http://www.resmathsci.com/content/1/1/12
Outline of the key ingredients
In this section, we describe the key subtheorems used in the proof of Theorem 4, with the
proofs of these subtheorems mostly being deferred to later sections.
We begin with a weak version of the Dickson-Hardy-Littlewood prime tuples conjec
ture [1], which (following Pintz [35]) we refer to as [k, j]. Recall that for any k ∈ N, an
admissible k-tuple is a tuple H = (h1, . . . , hk) of k increasing integers h1 < . . . < hk which
avoids at least one residue class ap (p) := {ap + np : n ∈ Z} for every p. For instance,
(0, 2, 6) is an admissible 3-tuple, but (0, 2, 4) is not.
For any k ≥ j ≥ 2, we let DHL[k; j] denote the following claim:
Claim 15 (Weak Dickson-Hardy-Littlewood conjecture, DHL[k; j]). For any admissible
k-tuple H = (h1, . . . , hk), there exist infinitely many translates n+H = (n+h1, . . . , n+hk)
of H which contain at least j primes.
The full Dickson-Hardy-Littlewood conjecture is then the assertion that DHL[k; k]
holds for all k ≥ 2. In our analysis, we will focus on the case when j is much smaller than
k; in fact, j will be of the order of log k.
For any k, let H(k) denote the minimal diameter hk − h1 of an admissible k-tuple; thus
for instance, H(3) = 6. It is clear that for any natural numbers m ≥ 1 and k ≥ m + 1, the
claim DHL[ k; m + 1] implies that Hm ≤ H(k) (and the claim DHL[k; k] would imply that
Hk−1 = H(k)). We will therefore deduce Theorem 4 from a number of claims of the form
DHL[k; j]. More precisely, we have
Theorem 16. Unconditionally, we have the following claims:
(i) DHL[50; 2].
(ii) DHL[35, 410; 3].
(iii) DHL[1, 649, 821; 4].
(iv) DHL[75, 845, 707; 5].
(v) DHL[3, 473, 955, 908; 6].
(vi) DHL[k; m + 1] whenever m ≥ 1 and k ≥ C exp ((4 − 28
157
) m) forsomesufficiently large absolute (and effective) constant C.
Assume the Elliott-Halberstam conjecture EH[θ] for all 0 < θ < 1. Then, we have the
following improvements:
(vii) DHL[54; 3].
(viii) DHL[5, 511; 4].
(ix) DHL[41, 588; 5].
(x) DHL[309, 661; 6].
(xi) DHL[k; m + 1] whenever m ≥ 1 and k ≥ C exp(2m) forsomesufficientlylarge absolute (and effective) constant C.
Assume the generalized Elliott-Halberstam conjecture GEH[θ] for all 0 < θ < 1. Then
(xii) DHL[3; 2].
(xiii) DHL[51; 3].
Theorem 4 then follows from Theorem 16 and the following bounds on H(k) (ordered
by increasing value of k):


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 10 of 83 http://www.resmathsci.com/content/1/1/12
Theorem 17 (Bounds on H(k)).
(xii) H(3) = 6.
(i) H(50) = 246. (xiii) H(51) = 252. (vii) H(54) = 270.
(viii) H(5, 511) ≤ 52, 116.
(ii) H(35, 410) ≤ 398, 130.
(ix) H(41, 588) ≤ 474, 266.
(x) H(309, 661) ≤ 4, 137, 854.
(iii) H(1, 649, 821) ≤ 24, 797, 814.
(iv) H(75, 845, 707) ≤ 1, 431, 556, 072.
(v) H(3, 473, 955, 908) ≤ 80, 550, 202, 480.
(vi),(xi) Intheasymptoticlimit k → ∞,onehas H(k) ≤ k log k + k log log k − k + o(k), withtheboundsonthedecayrate o(k) beingeffective.
We prove Theorem 17 in the ‘Narrow admissible tuples’ section. In the opposite direc
tion, an application of the Brun-Titchmarsh theorem gives H(k) ≥ ( 1
2 + o(1)) k log k as
k → ∞ (see [4, §3.9] for this bound, as well as with some slight refinements).
The proof of Theorem 16 follows the Goldston-Pintz-Yıldırım strategy that was also
used in all previous progress on this problem (e.g. [2,3,5,27]), namely that of constructing
a sieve function adapted to an admissible k-tuple with good properties. More precisely,
we set
w := log log log x
and
W := ∏
p≤w
p,
and observe the crude bound
W log logO(1) x. (11)
We have the following simple ‘pigeonhole principle’ criterion for DHL[ k; m + 1] (cf.
[Lemma 4.1], though the normalization here is slightly different):
Lemma 18 (Criterion for DHL). Let k ≥ 2 and m ≥ 1 be fixed integers and define the
normalization constant
B := φ(W )
W log x. (12)
Suppose that for each fixed admissible k-tuple (h1, . . . , hk) and each residue class b (W )
such that b + hi is coprime to W for all i = 1, . . . , k, one can find a non-negative weight
function ν : N → R+ and fixed quantities α > 0 and β1, . . . , βk ≥ 0, such that one has the
asymptotic upper bound ∑
x≤n≤2x
n=b (W )
ν(n) ≤ (α + o(1)) B−k x
W , (13)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 11 of 83 http://www.resmathsci.com/content/1/1/12
the asymptotic lower bound ∑
x≤n≤2x
n=b (W )
ν(n)θ (n + hi) ≥ (βi − o(1))B1−k x
φ(W ) (14)
for all i = 1, . . . , k, and the key inequality
β1 + · · · + βk
α > m. (15)
Then, DHL[k; m + 1] holds.
Proof. Let (h1, . . . , hk) be a fixed admissible k-tuple. Since it is admissible, there is at
least one residue class b (W ) such that (b + hi, W ) = 1 for all hi ∈ H. For an arithmetic
function ν as in the lemma, we consider the quantity
N := ∑
x≤n≤2x
n=b (W )
ν(n)
⎛
⎝
k ∑
i=1
θ (n + hi) − m log 3x
⎞
⎠.
Combining (13) and (14), we obtain the lower bound
N ≥ (β1 + · · · + βk − o(1))B1−k x
φ(W ) − (mα + o(1))B−k x
W log 3x.
From (12) and the crucial condition (15), it follows that N > 0 if x is sufficiently large.
On the other hand, the sum
k ∑
i=1
θ (n + hi) − m log 3x
can be positive only if n + hi is prime for at least m + 1 indices i = 1, . . . , k. We conclude
that, for all sufficiently large x, there exists some integer n ∈[x, 2x] such that n + hi is
prime for at least m + 1 values of i = 1, . . . , k.
Since (h1, . . . , hk) is an arbitrary admissible k-tuple, DHL[k; m + 1] follows.
The objective is then to construct non-negative weights ν whose associated ratio β1 +···+βk
α has provable lower bounds that are as large as possible. Our sieve majorants will
be a variant of the multidimensional Selberg sieves used in [5]. As with all Selberg sieves,
the ν are constructed as the square of certain (signed) divisor sums. The divisor sums we
will use will be finite linear combinations of products of ‘one-dimensional’ divisor sums.
More precisely, for any fixed smooth compactly supported function F : [0, +∞) → R,
define the divisor sum λF : Z → R by the formula
λF (n) := ∑
d|n
μ(d)F(logx d) (16)
where logx denotes the base x logarithm
logx n := log n
log x . (17)
One should think of λF as a smoothed out version of the indicator function to numbers
n which are ‘almost prime’ in the sense that they have no prime factors less than xε for
some small fixed ε > 0 (see Proposition 14 for a more rigorous version of this heuristic).


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 12 of 83 http://www.resmathsci.com/content/1/1/12
The functions ν we will use will take the form
ν(n) =
⎛
⎝
J ∑
j=1
cjλFj,1 (n + h1) . . . λFj,k (n + hk)
⎞
⎠
2
(18)
for some fixed natural number J, fixed coefficients c1, . . . , cJ ∈ R and fixed smooth com
pactly supported functions Fj,i : [0, +∞) → R with j = 1, . . . , J and i = 1, . . . , k. (One
can of course absorb the constant cj into one of the Fj,i if one wishes.) Informally, ν is a
smooth restriction to those n for which n + h1, . . . , n + hk are all almost prime.
Clearly, ν is a (positive-definite) linear combination of functions of the form
n→
k ∏
i=1
λFi (n + hi)λGi (n + hi)
for various smooth functions F1, . . . , Fk, G1, . . . , Gk : [0, +∞) → R. The sum appearing
in (13) can thus be decomposed into linear combinations of sums of the form
∑
x≤n≤2x
n=b (W )
k ∏
i=1
λFi (n + hi)λGi (n + hi). (19)
Also, since from (16) we clearly have
λF (n) = F(0) (20)
when n ≥ x is prime and F is supported on [0, 1], the sum appearing in (14) can be
similarly decomposed into linear combinations of sums of the form ∑
x≤n≤2x
n=b (W )
θ (n + hi) ∏
1≤i′≤k;i′ =i
λFi′ (n + hi′ )λGi′ (n + hi′ ). (21)
To estimate the sums (21), we use the following asymptotic, proven in the
‘Multidimensional Selberg sieves’ section. For each compactly supported F : [0, +∞) →
R, let
S(F) := sup{x ≥ 0 : F(x) = 0} (22)
denote the upper range of the support of F (with the convention that S(0) = 0).
Theorem 19 (Asymptotic for prime sums). Let k ≥ 2 be fixed, let (h1, . . . , hk) be a fixed
admissible k-tuple, and let b (W ) be such that b + hi is coprime to W for each i = 1, . . . , k.
Let 1 ≤ i0 ≤ k be fixed, and for each 1 ≤ i ≤ k distinct from i0, let Fi, Gi : [0, +∞) → R
be fixed smooth compactly supported functions. Assume one of the following hypotheses:
(i) (Elliott-Halberstam)Thereexistsafixed 0 < θ < 1 suchthat EH[θ] holdsandsuch
that
∑
1≤i≤k;i=i0
(S(Fi) + S(Gi)) < θ. (23)
(ii) (Motohashi-Pintz-Zhang)Thereexistsfixed 0 ≤ < 1/4 and δ > 0 suchthat MPZ[ , δ] holdsandsuchthat ∑
1≤i≤k;i=i0
(S(Fi) + S(Gi)) < 1
2 + 2 (24)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 13 of 83 http://www.resmathsci.com/content/1/1/12
and
max
1≤i≤k;i=i0
{S(Fi), S(Gi)} < δ. (25)
Then, we have ∑
x≤n≤2x
n=b (W )
θ (n + hi0 ) ∏
1≤i≤k;i=i0
λFi (n + hi)λGi (n + hi) = (c + o(1))B1−k x
φ(W ) (26)
where
c := ∏
1≤i≤k;i=i0
(∫ 1
0
Fi′(ti)G′i(ti) dti
) .
Here of course F′ denotes the derivative of F.
To estimate the sums (19), we use the following asymptotic, also proven in the
‘Multidimensional Selberg sieves’ section.
Theorem 20 (Asymptotic for non-prime sums). Let k ≥ 1 be fixed, let (h1, . . . , hk) be
a fixed admissible k-tuple, and let b (W ) be such that b + hi is coprime to W for each
i = 1, . . . , k. For each fixed 1 ≤ i ≤ k, let Fi, Gi : [0, +∞) → R be fixed smooth compactly
supported functions. Assume one of the following hypotheses:
(i) (Trivialcase)Onehas
k ∑
i=1
(S(Fi) + S(Gi)) < 1. (27)
(ii) (GeneralizedElliott-Halberstam)Thereexistsafixed 0 < θ < 1 and i0 ∈ {1, . . . , k}
suchthat GEH[θ] holds,and ∑
1≤i≤k;i=i0
(S(Fi) + S(Gi)) < θ. (28)
Then, we have
∑
x≤n≤2x
n=b (W )
k ∏
i=1
λFi (n + hi)λGi (n + hi) = (c + o(1))B−k x
W , (29)
where
c :=
k ∏
i=1
(∫ 1
0
Fi′(ti)G′i(ti) dti
)
. (30)
A key point in (ii) is that no upper bound on S(Fi0 ) or S(Gi0 ) is required (although, as
we will see in the ‘The generalized Elliott-Halberstam case’ section, the result is a little
easier to prove when one has S(Fi0 ) + S(Gi0 ) < 1). This flexibility in the Fi0 , Gi0 functions
will be particularly crucial to obtain part (xii) of Theorem 16 and Theorem 4.
Remark 21. Theorems 19 and 20 can be viewed as probabilistic assertions of the follow
ing form: if n is chosen uniformly at random from the set {x ≤ n ≤ 2x : n = b (W )},
then the random variables θ (n + hi) and λFj (n + hj)λGj (n + hj) for i, j = 1, . . . , k have
mean (1 + o(1)) W
φ(W ) and
(∫ 1
0 Fj′(t)Gj′(t) dt + o(1)
)
B−1, respectively, and furthermore,


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 14 of 83 http://www.resmathsci.com/content/1/1/12
these random variables enjoy a limited amount of independence, except for the fact (as
can be seen from (20)) that θ (n + hi) and λFi (n + hi)λGi (n + hi) are highly correlated.
Note though that we do not have asymptotics for any sum which involves two or more
factors of θ, as such estimates are of a difficulty at least as great as that of the twin prime
conjecture (which is equivalent to the divergence of the sum ∑
n θ (n)θ (n + 2)).
Theorems 19 and 20 may be combined with Lemma 18 to reduce the task of establishing
estimates of the form DHL[k; m + 1] to that of establishing certain variational problems.
For instance, in the ‘Proof of Theorem 22’ section, we reprove the following result of
Maynard ([5, Proposition 4.2]):
Theorem 22 (Sieving on the standard simplex). Let k ≥ 2 and m ≥ 1 be fixed integers.
For any fixed compactly supported square-integrable function F : [0, +∞)k → R, define
the functionals
I(F) :=
∫
[0,+∞)k
F(t1, . . . , tk)2 dt1 . . . tk (31)
and
Ji(F) :=
∫
[0,+∞)k−1
(∫ ∞
0
F(t1, . . . , tk) dti
)2
dt1 . . . dti−1dti+1 . . . dtk (32)
for i = 1, . . . , k, and let Mk be the supremum
Mk := sup
∑k
i=1 Ji(F)
I(F) (33)
over all square integrable functions F that are supported on the simplex
Rk :=
{
(t1, . . . , tk) ∈ [0, +∞)k : t1 + · · · + tk ≤ 1
}
and are not identically zero (up to almost everywhere equivalence, of course). Suppose that
there is a fixed 0 < θ < 1 such that EH[θ] holds and such that
Mk > 2m
θ.
Then, DHL[k; m + 1] holds.
Parts (vii)-(xi) of Theorem 16 (and hence Theorem 4) are then immediate from the
following results, proven in the ‘Asymptotic analysis’ and ‘The case of small and medium
dimension’ sections, and ordered by increasing value of k:
Theorem 23 (Lower bounds on Mk).
(vii) M54 > 4.00238. (viii) M5,511 > 6. (ix) M41,588 > 8. (x) M309,661 > 10.
(xi) OnehasMk ≥ log k −C forallk ≥ C,whereCisanabsolute(andeffective)constant.
For the sake of comparison, in ([5, Proposition 4.3]), it was shown that M5 > 2,
M105 > 4, and Mk ≥ log k − 2 log log k − 2 for all sufficiently large k. As remarked in
that paper, the sieves used on the bounded gap problem prior to the work in [5] would


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 15 of 83 http://www.resmathsci.com/content/1/1/12
essentially correspond, in this notation, to the choice of functions F of the special form
F(t1, . . . , tk) := f (t1 + · · · + tk), which severely limits the size of the ratio in (33) (in
particular, the analogue of Mk in this special case cannot exceed 4, as shown in [36]).
In the converse direction, in Corollary 37, we will also show the upper bound Mk ≤
k
k−1 log k for all k ≥ 2, which shows in particular that the bounds in (vii) and (xi) of the
above theorem cannot be significantly improved. We remark that Theorem 23(vii) and the
Bombieri-Vinogradov theorem also give a weaker version DHL[54; 2] of Theorem 16(i).
We also have a variant of Theorem 22 which can accept inputs of the form MPZ[ , δ]:
Theorem 24 (Sieving on a truncated simplex). Let k ≥ 2 and m ≥ 1 be fixed integers.
Let 0 < < 1/4 and 0 < δ < 1/2 be such that MPZ[ , δ] holds. For any α > 0, let
M[α]
k be defined as in (33), but where the supremum now ranges over all square-integrable
F supported in the truncated simplex {
(t1, . . . , tk) ∈ [0, α]k : t1 + · · · + tk ≤ 1
}
(34)
and are not identically zero. If
M
[δ
1/4+
]
k >m
1/4 + ,
then DHL[k; m + 1] holds.
In the ‘Asymptotic analysis’ section, we will establish the following variant of
Theorem 23, which when combined with Theorem 11, allows one to use Theorem 24 to
establish parts (ii)-(vi) of Theorem 16 (and hence Theorem 4):
Theorem 25 (Lower bounds on M[α]
k ).
(ii) Thereexist δ, > 0 with 600 + 180δ < 7 and M
[δ
1/4+
]
35 410 > 2
1/4+ .
(iii) Thereexist δ, > 0 with 600 + 180δ < 7 and M
[δ
1/4+
]
1 649 821 > 3
1/4+ .
(iv) Thereexist δ, > 0 with 600 + 180δ < 7 and M
[δ
1/4+
]
75 845 707 > 4
1/4+ .
(v) Thereexist δ, > 0 with 600 + 180δ < 7 and M
[δ
1/4+
]
3 473 955 908 > 5
1/4+ .
(vi) Forall k ≥ C,thereexist δ, > 0 with 600 + 180δ < 7, ≥ 7
600 − C
log k ,and
M
[δ
1/4+
]
k ≥ log k − C forsomeabsolute(andeffective)constantC.
The implication is clear for (ii)-(v). For (vi), observe that from Theorem 25(vi),
Theorem 11, and Theorem 24, we see that DHL[k; m + 1] holds whenever k is sufficiently
large and
m ≤ (log k − C)
(1
4+ 7
600 − C
log k
)
which is in particular implied by
m ≤ log k
4 − 28
157
− C′
for some absolute constant C′, giving Theorem 16(vi).


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 16 of 83 http://www.resmathsci.com/content/1/1/12
Now we give a more flexible variant of Theorem 22, in which the support of F is
enlarged, at the cost of reducing the range of integration of the Ji.
Theorem 26 (Sieving on an epsilon-enlarged simplex). Let k ≥ 2 and m ≥ 1 be fixed
integers, and let 0 < ε < 1 be fixed also. For any fixed compactly supported square
integrable function F : [0, +∞)k → R, define the functionals
Ji,1−ε(F) :=
∫
(1−ε)·Rk−1
(∫ ∞
0
F(t1, . . . , tk) dti
)2
dt1 . . . dti−1dti+1 . . . dtk
for i = 1, . . . , k, and let Mk,ε be the supremum
Mk,ε := sup
∑k
i=1 Ji,1−ε(F)
I (F )
over all square-integrable functions F that are supported on the simplex
(1 + ε) · Rk =
{
(t1, . . . , tk) ∈ [0, +∞)k : t1 + · · · + tk ≤ 1 + ε
}
and are not identically zero. Suppose that there is a fixed 0 < θ < 1, such that one of the
following two hypotheses hold:
(i) EH[θ] holds,and 1 + ε < 1
θ.
(ii) GEH[θ] holds,and ε < 1
k−1 .
If
Mk,ε > 2m
θ
then DHL[k; m + 1] holds.
We prove this theorem in the ‘Proof of Theorem 26’ section. We remark that due to
the continuity of Mk,ε in ε, the strict inequalities in (i) and (ii) of this theorem may be
replaced by non-strict inequalities. Parts (i) and (xiii) of Theorem 16, and a weaker ver
sion DHL[4; 2] of part (xii), then follow from Theorem 9 and the following computations,
proven in the ‘Bounding Mk,ε for medium k’ and ‘Bounding M4,ε’ sections:
Theorem 27 (Lower bounds on Mk,ε).
(i) M50,1/25 > 4.0043. (xii’) M4,0.168 > 2.00558. (xiii) M51,1/50 > 4.00156.
We remark that computations in the proof of Theorem 27(xii’) are simple enough that
the bound may be checked by hand, without use of a computer. The computations used to
establish the full strength of Theorem 16(xii) are however significantly more complicated.
In fact, we may enlarge the support of F further. We give a version corresponding to
part (ii) of Theorem 26; there is also a version corresponding to part (i), but we will not
give it here as we will not have any use for it.
Theorem 28 (Going beyond the epsilon enlargement). Let k ≥ 2 and m ≥ 1 be
fixed integers, let 0 < θ < 1 be a fixed quantity such that GEH[θ] holds, and let 0 < ε< 1
k−1 be fixed also. Suppose that there is a fixed non-zero square-integrable function


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 17 of 83 http://www.resmathsci.com/content/1/1/12
F : [0, +∞)k → R supported in k
k−1 · Rk, such that for i = 1, . . . , k, one has the vanishing
marginal condition
∫∞
0
F(t1, . . . , tk) dti = 0 (35)
whenever t1, . . . , ti−1, ti+1, . . . , tk ≥ 0 are such that
t1 + · · · + ti−1 + ti+1 + · · · + tk > 1 + ε.
Suppose that we also have the inequality
∑k
i=1 Ji,ε(F)
I(F) > 2m
θ.
Then DHL[k; m + 1] holds.
This theorem is proven in the ‘Proof of Theorem 28’ section. Theorem 16(xii) is then
an immediate consequence of Theorem 28 and the following numerical fact, established
in the ‘Three-dimensional cutoffs’ section.
Theorem 29 (A piecewise polynomial cutoff ). Set ε := 1
4 . Then, there exists a piecewise
polynomial function F : [0, +∞)3 → R supported on the simplex
3
2 · R3 =
{
(t1, t2, t3) ∈ [0, +∞)3 : t1 + t2 + t3 ≤ 3
2
}
and symmetric in the t1, t2, t3 variables, such that F is not identically zero and obeys the
vanishing marginal condition
∫∞
0
F(t1, t2, t3) dt3 = 0
whenever t1, t2 ≥ 0 with t1 + t2 > 1 + ε and such that
3∫
t1 +t2 ≤1−ε
(∫ ∞
0 F(t1, t2, t3) dt3
)2 dt1dt2
∫
[0,∞)3 F(t1, t2, t3)2 dt1dt2dt3
> 2.
There are several other ways to combine Theorems 19 and 20 with equidistribution
theorems on the primes to obtain results of the form DHL[ k; m+1], but all of our attempts
to do so either did not improve the numerology or else were numerically infeasible to
implement.
Multidimensional Selberg sieves
In this section, we prove Theorems 19 and 20. A key asymptotic used in both theorems is
the following:
Lemma 30 (Asymptotic). Let k ≥ 1 be a fixed integer, and let N be a natural number
coprime to W with log N = O
(
logO(1) x
)
. Let F1, . . . , Fk, G1, . . . , Gk : [0, +∞) → R be
fixed smooth compactly supported functions. Then,
∑
d1,...,dk ,d′1,...,d′
k
[d1,d′1],...,[dk ,d′
k
],W ,Ncoprime
k ∏
j=1
μ (dj
)μ
(
dj′
) Fj
(logx dj
) Gj
(
logx dj′
)
[
dj, dj′
] = (c+o(1))B−k Nk
φ (N )k
(36)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 18 of 83 http://www.resmathsci.com/content/1/1/12
where B was defined in (12), and
c :=
k ∏
j=1
∫∞
0
Fj′(tj)Gj′(tj) dtj.
The same claim holds if the denominators
[
dj, dj′
]
are replaced by φ
([
dj, dj′
]) .
Such asymptotics are standard in the literature (see, e.g. [37] for some similar com
putations). In older literature, it is common to establish these asymptotics via contour
integration (e.g. via Perron’s formula), but we will use the Fourier analytic approach here.
Of course, both approaches ultimately use the same input, namely the simple pole of the
Riemann zeta function at s = 1.
Proof. We begin with the first claim. For j = 1, . . . , k, the functions t → etFj(t), t →
etGj(t) may be extended to smooth compactly supported functions on all of R, and so we
have Fourier expansions
etFj(t) =
∫
R
e−itξ fj(ξ ) dξ (37)
and
etGj(t) =
∫
R
e−itξ gj(ξ ) dξ
for some fixed functions fj, gj : R → C that are smooth and rapidly decreasing in the sense
that fj(ξ ), gj(ξ ) = O ((1 + |ξ |)−A) for any fixed A > 0 and all ξ ∈ R (here the implied
constant is independent of ξ and depends only on A).
We may thus write
Fj
(logx dj
)=
∫
R
fj(ξj)
d
1+iξj log x j
dξj
and
Gj
(
logx dj′
) =
∫
R
gj
(
ξj′
)
(
dj′
) 1+iξj′
log x
dξj′
for all dj, dj′ ≥ 1. We note that
∑
dj ,dj′
|μ (dj
)μ
(
dj′
) | [
dj, dj′
]
d1/ log x
j
(
dj′
)1/ log x = ∏ p
(
1+ 2
p1+1/ log x + 1
p1+2/ log x
)
≤ exp(O(log log x)).
Therefore, if we substitute the Fourier expansions into the left-hand side of (36), the
resulting expression is absolutely convergent. Thus, we can apply Fubini’s theorem, and
the left-hand side of (36) can thus be rewritten as ∫
R
...
∫
R
K (ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k
) k ∏
j=1
fj
(ξj
) gj
(
ξj′
)
dξjdξj′, (38)
where
K (ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k) := ∑
d1,...,dk ,d′1,...,d′
k
[d1,d′1],...,[dk ,d′
k
],W ,Ncoprime
k ∏
j=1
μ (dj
)μ
(
dj′
)
[
dj, dj′
] d
1+iξj log x j
(
dj′
) 1+iξj′
log x
.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 19 of 83 http://www.resmathsci.com/content/1/1/12
This latter expression factorizes as an Euler product
K= ∏
p WN
Kp,
where the local factors Kp are given by
Kp
(ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k
) := 1 + 1
p
∑
d1,...,dk ,d′1,...,d′
k
[d1,...,dk ,d′1,...,d′
k
]=p
[d1,d′1],...,[dk ,d′
k
]coprime
k ∏
j=1
μ (dj
)μ
(
dj′
)
d
1+iξj log x j
(
dj′
) 1+iξj′
log x
.
(39)
We can estimate each Euler factor as
Kp
(ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k
)=
(
1+O
(1
p2
)) k ∏
j=1
(
1 − p−1− 1+iξj
log x
)(
1 − p−1− 1+iξj′
log x
)
1 − p−1− 2+iξj+iξj′
log x
. (40)
Since
∏
p:p>w
(
1+O
(1
p2
))
= 1 + o(1),
we have
K (ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k
) = (1 + o(1))
k ∏
j=1
ζWN
(
1 + 2+iξj+iξj′
log x
)
ζWN
(
1 + 1+iξj
log x
)
ζWN
(
1 + 1+iξj′
log x
)
where the modified zeta function ζWN is defined by the formula
ζWN (s) := ∏
p WN
(
1− 1
ps
)−1
for (s) > 1. For (s) ≥ 1 + 1
log x , we have the crude bounds
|ζWN (s)|, |ζWN (s)|−1 ≤ ∏
p
(
1+ 1
p1+1/ log x + O
(1
p2
))
exp
⎛
⎝∑
p
1
p1+1/ log x
⎞
⎠
≤ exp(log log x + O(1))
log x.
Thus,
K (ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k
)=O
(
log3k x
) .
Combining this with the rapid decrease of fj, gj, we see that the contribution to (38)
outside of the cube
{
max (ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k
) ≤ √log x
}
(say) is negligible. Thus, it will
suffice to show that
∫ √log x
−√log x
...
∫ √log x
−√log x
K (ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k
) k ∏
j=1
fj
(ξj
) gj
(
ξj′
)
dξjdξj′ = (c + o(1))B−k Nk
φ(N)k .


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 20 of 83 http://www.resmathsci.com/content/1/1/12
When |ξj| ≤ √log x, we see from the simple pole of the Riemann zeta function ζ (s) =
∏
p
(
1− 1
ps
)−1 at s = 1 that
ζ
(
1 + 1 + iξj
log x
)
= (1 + o(1)) log x
1 + iξj
.
For −√log x ≤ ξj ≤ √log x, we see that
1− 1
p1+ 1+iξj
log x
=1− 1
p +O
(
log p
p√log x
)
.
Since log WN logO(1) x, this gives
∏
p|WN
⎛
⎝1 − 1
p1+ 1+iξj
log x
⎞
⎠ = φ(WN)
WN exp
⎛
⎝O
⎛
⎝∑
p|WN
log p
p√log x
⎞
⎠
⎞
⎠ = (1 + o(1)) φ(WN)
WN ,
since the sum is maximized when WN is composed only of primes p logO(1) x. Thus,
ζWN
(
1 + 1 + iξj
log x
)
= (1 + o(1))Bφ(N)
(1 + iξj)N ,
similarly with 1 + iξj replaced by 1 + iξj′ or 2 + iξj + iξj′. We conclude that
K (ξ1, . . . , ξk, ξ1′ , . . . , ξ ′
k
) = (1 + o(1))B−k Nk
φ (N )k
k ∏
j=1
(1 + iξj
)(
1 + iξj′
)
2 + iξj + iξj′
. (41)
Therefore, it will suffice to show that
∫
R
...
∫
R
k ∏
j=1
(1 + iξj
)(
1 + iξj′
)
2 + iξj + iξj′
fj(ξj)gj
(
ξj′
)
dξjdξj′ = c,
since the errors caused by the 1 + o(1) multiplicative factor in (41) or the truncation
|ξj|, |ξj′| ≤ √log x can be seen to be negligible using the rapid decay of fj, gj. By Fubini’s
theorem, it suffices to show that ∫
R
∫
R
(1 + iξ )(1 + iξ ′)
2 + iξ + iξ ′ fj(ξ )gj(ξ ′) dξ dξ ′ =
∫ +∞
0
Fj′(t)Gj′(t) dt
for each j = 1, . . . , k. But from dividing (37) by et and differentiating under the integral
sign, we have
Fj′(t) = −
∫
R
(1 + iξ )e−t(1+iξ)fj(ξ ) dξ ,
and the claim then follows from Fubini’s theorem.
Finally, suppose that we replace
[
dj, dj′
]
with φ
([
dj, dj′
])
. An inspection of the above
argument shows that the only change that occurs is that the 1
p term in (39) is replaced by
1
p−1 ; but this modification may be absorbed into the 1 + O
(1
p2
)
factor in (40), and the
rest of the argument continues as before.
The trivial case
We can now prove the easiest case of the two theorems, namely case (i) of Theorem 20;
a closely related estimate also appears in ([5, Lemma 6.2]). We may assume that x is suf


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 21 of 83 http://www.resmathsci.com/content/1/1/12
ficiently large depending on all fixed quantities. By (16), the left-hand side of (29) may be
expanded as
∑
d1,...,dk ,d′1,...,d′
k
⎛
⎝
k ∏
i=1
μ(di)μ (di′
) Fi
(logx di
) Gi
(logx di′
)
⎞
⎠ S (d1, . . . , dk, d′1, . . . , d′
k
)
(42)
where
S (d1, . . . , dk, d′1, . . . , d′
k
) := ∑
x≤n≤2x
n=b (W )
n+hi=0 ([di,di′]) ∀i
1.
By hypothesis, b + hi is coprime to W for all i = 1, . . . , k, and |hi − hj| < w for all distinct
i, j. Thus, S (d1, . . . , dk, d′1, . . . , d′
k
) vanishes unless the [di, di′
] are coprime to each other
and to W . In this case, S (d1, . . . , dk, d′1, . . . , d′
k
) is summing the constant function 1 over
an arithmetic progression in [x, 2x] of spacing W [d1, d′1
] . . . [dk, d′
k
], and so
S (d1, . . . , dk, d′1, . . . , d′
k
)= x
W [d1, d′1
] . . . [dk, d′
k
] + O(1).
By Lemma 30, the contribution of the main term x
W [d1,d′1]...[dk ,d′
k
] to (29) is (c +
o(1))B−k x
W ; note that the restriction of the integrals in (30) to [0, 1] instead of [0, +∞) is
harmless since S(Fi), S(Gi) < 1 for all i. Meanwhile, the contribution of the O(1) error is
then bounded by
O
⎛
⎝∑
d1,...,dk ,d′1,...,d′
k
⎛
⎝
k ∏
i=1
|Fi(logx di)||Gi(logx di′)|
⎞
⎠
⎞
⎠.
By the hypothesis in Theorem 20(i), we see that for d1, . . . , dk, d′1, . . . , d′
k contributing a
non-zero term here, one has
[d1, d′1
] . . . [dk, d′
k
] ≺≺ x1−ε
for some fixed ε > 0. From the divisor bound (1), we see that each choice of
[d1, d′1
] . . . [dk, d′
k
] arises from ≺≺ 1 choices of d1, . . . , dk, d′1, . . . , d′
k. We conclude that
the net contribution of the O(1) error to (29) is ≺≺ x1−ε, and the claim follows.
The Elliott-Halberstam case
Now we show case (i) of Theorem 19. For the sake of notation, we take i0 = k, as the other
cases are similar. We use (16) to rewrite the left-hand side of (26) as
∑
d1 ,...,dk −1 ,d′1 ,...,d′
k−1
⎛
⎝
k∏−1
i=1
μ(di)μ (di′
) Fi
(logx di
) Gi
(logx di′
)
⎞
⎠ S ̃ (d1, . . . , dk−1, d′1, . . . , d′
k−1
)
(43)
where
S ̃ (d1, . . . , dk−1, d′1, . . . , d′
k−1
) := ∑
x≤n≤2x
n=b (W )
n+hi=0 ([di,di′]) ∀i=1,...,k−1
θ (n + hk).


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 22 of 83 http://www.resmathsci.com/content/1/1/12
As in the previous case, S ̃
(
d1, . . . , dk−1, d′1, . . . , d′
k−1
)
vanishes unless the [di, di′
] are
coprime to each other and to W , and so the summand in (43) vanishes unless the modulus
qW ,d1,...,d′
k−1 defined by
qW ,d1,...,d′
k−1 := W [d1, d′1
] . . . [dk−1, d′
k−1
] (44)
is square-free. In that case, we may use the Chinese remainder theorem to concatenate
the congruence conditions on n into a single primitive congruence condition
n + hk = aW ,d1,...,d′
k−1
(
qW ,d1,...,d′
k−1
)
for some aW ,d1,...,d′
k−1 depending on W , d1, . . . , dk−1, d′1, . . . , d′
k−1, and conclude using (3)
that
S ̃ (d1, . . . , dk−1, d′1, . . . , d′
k−1
)= 1
φ
(
qW ,d1,...,d′
k−1
)∑
x+hk ≤n≤2x+hk
θ (n)
+
(
1[x+hk ,2x+hk ]θ ; aW ,d1,...,d′
k−1
(
qW ,d1,...,d′
k−1
)) .
(45)
From the prime number theorem, we have ∑
x+hk ≤n≤2x+hk
θ(n) = (1 + o(1))x
and this expression is clearly independent of d1, . . . , d′
k−1. Thus, by Lemma 30, the con
tribution of the main term in (45) is (c + o(1))B1−k x
φ(W) . By (11) and (12), it thus suffices
to show that for any fixed A we have
∑
d1 ,...,dk −1 ,d′1 ,...,d′
k−1
⎛
⎝
k∏−1
i=1
∣∣Fi
(logx di
)∣∣ ∣∣Gi
(logx di′
)∣∣
⎞
⎠ ∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ x log−A x,
(46)
where a = aW ,d1,...,d′
k−1 and q = qW ,d1,...,d′
k−1 . For future reference, we note that we may
restrict the summation here to those d1, . . . , d′
k−1 for which qW ,d1,...,d′
k−1 is square-free.
From the hypotheses of Theorem 19(i), we have
qW ,d1,...,d′
k−1 ≺≺ xθ
whenever the summand in (43) is non-zero, and each choice q of qW,d1,...,d′
k−1 is associated
to O (τ (q)O(1)) choices of d1, . . . , dk−1, d′1, . . . , d′
k−1. Thus, this contribution is
∑
q≺≺xθ
τ (q)O(1) sup
a∈(Z/qZ)×
∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ .
Using the crude bound
∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ x
q logO(1) x
and (2), we have ∑
q≺≺xθ
τ (q)C sup a∈(Z/qZ)×
∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ x logO(1) x
for any fixed C > 0. By the Cauchy-Schwarz inequality, it suffices to show that ∑
q≺≺xθ
sup
a∈(Z/qZ)×
∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ x log−A x


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 23 of 83 http://www.resmathsci.com/content/1/1/12
for any fixed A > 0. However, since θ only differs from on powers pj of primes with
j > 1, it is not difficult to show that
∣∣ (1[x+hk,2x+hk]θ ; a (q)) − (1[x+hk,2x+hk] ; a (q))∣∣ ≺≺
√x
q,
so the net error in replacing θ here by is ≺≺ x1−(1−θ)/2, which is certainly acceptable.
The claim now follows from the hypothesis EH[θ], thanks to Claim 8.
The Motohashi-Pintz-Zhang case
Now we show case (ii) of Theorem 19. We repeat the arguments from the ‘The Elliott
Halberstam case’ section, with the only difference being in the derivation of (46). As
observed previously, we may restrict qW,d1,...,d′
k−1 to be square-free. From the hypotheses
in Theorem 19(ii), we also see that
qW ,d1,...,d′
k−1 ≺≺ xθ
and that all the prime factors of qW,d1,...,d′
k−1 are at most xδ. Thus, if we set I := [1, xδ], we
see (using the notation from Claim 10) that qW,d1,...,d′
k−1 lies in SI and is thus a factor of PI .
If we then let A ⊂ Z/PI Z denote all the primitive residue classes a (PI) with the property
that a = b (W ), and such that for each prime w < p ≤ xδ, one has a + hi = 0 (p) for some
i = 1, . . . , k, then we see that aW,d1,...,d′
k−1 lies in the projection of A to Z/qW ,d1,...,d′
k−1 Z.
Each q ∈ SI is equal to qW ,d1,...,d′
k−1 for O (τ (q)O(1)) choices of d1, . . . , d′
k−1. Thus, the
left-hand side of (46) is ∑
q∈SI :q≺≺xθ
τ (q)O(1) sup
a∈A
∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ .
Note from the Chinese remainder theorem that for any given q, if one lets a range uni
formly in A, then a (q) is uniformly distributed among O (τ (q)O(1)) different moduli.
Thus, we have
sup
a∈A
∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ τ (q)O(1)
|A|
∑
a∈A
∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ ,
and so it suffices to show that ∑
q∈SI :q≺≺xθ
τ (q)O(1)
|A|
∑
a∈A
∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ x log−A x
for any fixed A > 0. We see it suffices to show that ∑
q∈SI :q≺≺xθ
τ (q)O(1) ∣∣ (1[x+hk,2x+hk]θ ; a (q))∣∣ x log−A x
for any given a ∈ A. But this follows from the hypothesis MPZ[ , δ] by repeating the
arguments of the ‘The Elliott-Halberstam case’ section.
Crude estimates on divisor sums
To proceed further, we will need some additional information on the divisor sums λF
(defined in (16)), namely that these sums are concentrated on ‘almost primes’; results of
this type have also appeared in [38].
Proposition 14 (Almost primality). Let k ≥ 1 be fixed, let (h1, . . . , hk) be a fixed admis
sible k-tuple, and let b (W ) be such that b + hi is coprime to W for each i = 1, . . . , k.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 24 of 83 http://www.resmathsci.com/content/1/1/12
Let F1, . . . , Fk : [0, +∞) → R be fixed smooth compactly supported functions, and let
m1, . . . , mk ≥ 0 and a1, . . . , ak ≥ 1 be fixed natural numbers. Then,
∑
x≤n≤2x:n=b (W )
k ∏
j=1
(|λFj (n + hj)|aj τ (n + hj)mj ) B−k x
W . (47)
Furthermore, if 1 ≤ j0 ≤ k is fixed and p0 is a prime with p0 ≤ x 1
10k , then we have the
variant
∑
x≤n≤2x:n=b (W )
k ∏
j=1
(|λFj (n + hj)|aj τ (n + hj)mj ) 1p0|n+hj0
logx p0
p0
B−k x
W . (48)
As a consequence, we have
∑
x≤n≤2x:n=b (W )
k ∏
j=1
(|λFj (n + hj)|aj τ (n + hj)mj ) 1p(n+hj0 )≤xε εB−k x
W , (49)
for any ε > 0, where p(n) denotes the least prime factor of n.
The exponent 1
10k can certainly be improved here, but for our purposes, any fixed
positive exponent depending only on k will suffice.
Proof. The strategy is to estimate the alternating divisor sums λFj (n + hj) by non
negative expressions involving prime factors of n + hj, which can then be bounded
combinatorially using standard tools.
We first prove (47). As in the proof of Proposition 30, we can use Fourier expansion to
write
Fj
(logx d) =
∫
R
fj(ξ )
d
1+iξ log x
dξ
for some rapidly decreasing fj : R → C and all natural numbers d. Thus,
λFj (n) =
∫
R
⎛
⎝∑
d|n
μ(d)
d
1+iξ log x
⎞
⎠ fj(ξ ) dξ ,
which factorizes using Euler products as
λFj (n) =
∫
R
∏
p|n
⎛
⎝1 − 1 p
1+iξ log x
⎞
⎠ fj(ξ ) dξ .
The function s → p
−s
log x has a magnitude of O(1) and a derivative of O (logx p) when
(s) > 1, and thus
1− 1 p
1+iξ log x
= O (min((1 + |ξ |) logx p, 1)) .
From the rapid decrease of fj and the triangle inequality, we conclude that
|λFj (n)|
∫
R
⎛
⎝∏
p|n
O (min((1 + |ξ |) logx p, 1))
⎞
⎠ dξ
(1 + |ξ |)A


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 25 of 83 http://www.resmathsci.com/content/1/1/12
for any fixed A > 0. Thus, noting that ∏
p|n O(1) τ (n)O(1), we have
|λFj (n)|aj τ (n)O(1)
∫
R
...
∫
R
⎛
⎝∏
p|n
a∏j
l=1
min((1 + |ξl|) logx p, 1)
⎞
⎠
dξ1 . . . dξaj
(1 + |ξ1|)A . . . (1 + |ξaj |)A
for any fixed aj, A. However, we have
a∏j
i=1
min ((1 + |ξi|) logx p, 1) min ((1 + |ξ1| + · · · + |ξaj |) logx p, 1) ,
and so
|λFj (n)|aj τ (n)O(1)
∫
R
...
∫
R
(∏
p|n min ((1 + |ξ1| + · · · + |ξaj |) logx p, 1))
dξ1 . . . dξaj
(1 + |ξ1| + · · · + |ξaj |)A .
Making the change of variables σ := 1 + |ξ1| + · · · + |ξaj |, we obtain
|λFj (n)|aj τ (n)O(1)
∫∞
1
⎛
⎝∏
p|n
min(σ logx p, 1)
⎞
⎠ dσ
σA
for any fixed A > 0. In view of this bound and the Fubini-Tonelli theorem, it suffices to
show that
∑
x≤n≤2x:n=b (W )
k ∏
j=1
⎛
⎝τ (n + hj)O(1) ∏
p|n
min(σj logx p, 1)
⎞
⎠ B−k x
W (σ1 + · · · + σk)O(1)
for all σ1, . . . , σk ≥ 1. By setting σ := σ1 + · · · + σk, it suffices to show that
∑
x≤n≤2x:n=b (W )
k ∏
j=1
⎛
⎝τ (n + hj
)O(1) ∏
p|n+hj
min (σ logx p, 1)
⎞
⎠ B−k x
W σ O(1) (50)
for any σ ≥ 1.
To proceed further, we factorize n + hj as a product
n + hj = p1 . . . pr
of primes p1 ≤ · · · ≤ pr in increasing order and then write
n + hj = djmj
where dj := p1 . . . pij and ij is the largest index for which p1 . . . pij < x 1
10k , and mj :=
pij+1 . . . pr. By construction, we see that 0 ≤ ij < r, dj ≤ x 1
10k . Also, we have
pij+1 ≥ (p1 . . . pij+1
)1
ij+1 ≥ x
1
10k(ij+1) .
Since n ≤ 2x, this implies that
r = O(ij + 1)
and so
τ (n + hj) ≤ 2O(1+ (dj)),


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 26 of 83 http://www.resmathsci.com/content/1/1/12
where we recall that (dj) = ij denotes the number of prime factors of dj, counting
multiplicity. We also see that
p(mj) ≥ x
1
10k(1+ (dj)) ≥ x
1
10k(1+ (d1...dk )) =: R,
where p(n) denotes the least prime factor of n. Finally, we have that ∏
p|n+hj
min (σ logx p, 1) ≤ ∏
p|dj
min (σ logx p, 1) ,
and we see that the d1, . . . , dk, W are coprime. We may thus estimate the left-hand side of
(50) by
∑
∗
⎛
⎝
k ∏
j=1
2O(1+ (dj) ∏
p|dj
min(σ logx p, 1)
⎞
⎠∑
∗∗
1
where the outer sum ∑
∗ is over d1, . . . , dk ≤ x 1
10k with d1, . . . , dk, W coprime, and the
inner sum ∑
∗∗ is over x ≤ n ≤ 2x with n = b (W ) and n + hj = 0 (dj) for each j, with
p
( n+hj dj
)
≥ R for each j.
We bound the inner sum ∑
∗∗ 1 using a Selberg sieve upper bound. Let G be a smooth
function supported on [0, 1] with G(0) = 1, and let d = d1 . . . dk. We see that
∑
∗∗
1≤ ∑
x≤n≤2x
n+hi≡0 (di)
n≡b (W )
k ∏
i=1
⎛
⎜⎜⎝
∑
e|n+hi
(e,dW )=1
μ(e)G(logR e)
⎞
⎟⎟⎠
2
,
since the product is G(0)2k = 1 if p
( n+hj dj
)
≥ R, and non-negative otherwise. The right
hand side may be expanded as
∑
e1,...,ek ,e′1,...,e′
k
(eie′i,dW )=1∀i
⎛
⎝
k ∏
i=1
μ(ei)μ (e′i
) G (logR ei
) G (logR e′i
)
⎞
⎠∑
x≤n≤2x
n+hi≡0 (di[ei,e′i])
n≡b (W )
1.
As in the ‘The trivial case’ section, the inner sum vanishes unless the eie′i are coprime to
each other and dW, in which case it is
x
dW [ e1, e′1] . . . [ ek, e′
k] + O(1).
The O(1) term contributes ≺≺ Rk ≺≺ x1/10, which is negligible. By Lemma 30, if (d)
log1/2 x, then the main term contributes
(d
φ(d)
)k x
dW (log R)−k 2 (d)B−k x
dW .
We see that this final bound applies trivially if (d) log1/2 x. The bound (50) thus
reduces to
∑
∗
⎛
⎝
k ∏
j=1
2O(1+ (dj))
dj
∏
p|dj
min(σ logx p, 1)
⎞
⎠ σ O(1). (51)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 27 of 83 http://www.resmathsci.com/content/1/1/12
Ignoring the coprimality conditions on the dj for an upper bound, we see this is bounded
by
∏
w<p≤x 1
10k
⎛
⎝1 + O(min(σ logx(p), 1))
p
∑
j≥0
O(1)j pj
⎞
⎠
k
exp
⎛
⎝O
⎛
⎝∑
p≤x
(min(σ logx(p), 1)) p
⎞
⎠
⎞
⎠.
But from Mertens’ theorem, we have
∑
p≤x
min(σ logx p, 1)
p =O
(
log 1
σ
) ,
and the claim (47) follows.
The proof of (48) is a minor modification of the argument above used to prove (47).
Namely, the variable dj0 is now replaced by [d0, p0] < x1/5k, which upon factoring out p0
has the effect of multiplying the upper bound for (51) by O
( σ logx p0 p0
)
(at the negligible
cost of deleting the prime p0 from the sum ∑
p≤x
)
, giving the claim; we omit the details.
Finally, (49) follows immediately from (47) when ε > 1
10k , and from (48) and Mertens’
theorem when ε ≤ 1
10k .
Remark 32. As in [38], one can use Proposition 14, together with the observation that
the quantity λF (n) is bounded whenever n = O(x) and p(n) ≥ xε, to conclude that when
ever the hypotheses of Lemma 18 are obeyed for some ν of the form (18), then there exists
a fixed ε > 0 such that for all sufficiently large x, there are x
logk x elements n of [ x, 2x]
such that n + h1, . . . , n + hk have no prime factor less than xε, and that at least m of the
n + h1, . . . , n + hk are prime.
The generalized Elliott-Halberstam case
Now we show case (ii) of Theorem 20. For the sake of notation, we shall take i0 = k, as
the other cases are similar; thus, we have
k∑ −1
i=1
(S(Fi) + S(Gi)) < θ. (52)
The basic idea is to view the sum (29) as a variant of (26), with the role of the function
θ now being played by the product divisor sum λFk λGk , and to repeat the arguments in
the ‘The Elliott-Halberstam case’ section. To do this, we rely on Proposition 14 to restrict
n + hi to the almost primes.
We turn to the details. Let ε > 0 be an arbitrary fixed quantity. From (49) and Cauchy
Schwarz, one has
∑
x≤n≤2x
n=b (W )
⎛
⎝
k ∏
i=1
λFi (n + hi)λGi (n + hi)
⎞
⎠ 1p(n+hk)≤xε = O
(
εB−k x
W
)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 28 of 83 http://www.resmathsci.com/content/1/1/12
with the implied constant uniform in ε, so by the triangle inequality and a limiting
argument as ε → 0, it suffices to show that
∑
x≤n≤2x
n=b (W )
⎛
⎝
k ∏
i=1
λFi (n + hi)λGi (n + hi)
⎞
⎠ 1p(n+hk)>xε = (cε + o(1))B−k x
W (53)
where cε is a quantity depending on ε but not on x, such that
εli→m0 cε =
k ∏
i=1
∫1
0
Fi′(t)G′i(t) dt.
We use (16) to expand out λFi , λGi for i = 1, . . . , k − 1, but not for i = k, so that the
left-hand side of (29) becomes
∑
d1 ,...,dk −1 ,d′1 ,...,d′
k−1
⎛
⎝
k ∏
i=1
μ(di)μ (di′
) Fi
(logx di
) Gi
(logx di′
)
⎞
⎠ S′ (d1, . . . , dk−1, d′1, . . . , d′
k−1
)
(54)
where
S′ (d1, . . . , dk−1, d′1, . . . , d′
k−1
) := ∑
x≤n≤2x
n=b (W )
n+hi=0 ([di,di′]) ∀i=1,...,k−1
λFk (n + hk)λGk (n + hk)1p(n+hk)>xε .
As before, the summand in (54) vanishes unless the modulusd qW,d1,...,d′
k−1 defined in
(44) is square-free, in which case we have the analogue
S′ (d1, . . . , dk−1, d′1, . . . , d′
k−1
)= 1
φ(q)
∑
x+hk ≤n≤2x+hk
(n,q)=1
λFk (n)λGk (n)1p(n)>xε
+ (1[x+hk,2x+hk]λFk λGk 1p(·)>xε ; a (q)) (55)
of (45). Here we have put q = qW,d1,...,d′
k−1 and a = aW ,d1,...,d′
k−1 for convenience. We thus
split
S′ = S′1 − S′2 + S′3,
where,
S′1
(d1, . . . , dk−1, d′1, . . . , d′
k−1
)= 1
φ(q)
∑
x+hk ≤n≤2x+hk
λFk (n)λGk (n)1p(n)>xε , (56)
S′2
(d1, . . . , dk−1, d′1, . . . , d′
k−1
)= 1
φ(q)
∑
x+hk ≤n≤2x+hk ;(n,q)>1
λFk (n)λGk (n)1p(n)>xε ,
(57)
S′3
(d1, . . . , dk−1, d′1, . . . , d′
k−1
) = (1[x+hk,2x+hk]λFk λGk 1p(·)>xε ; a (q)) , (58)
when q = qW ,d1,...,d′
k−1 is square-free, with S′1 = S′2 = S′3 = 0 otherwise.
For j ∈ {1, 2, 3}, let
j= ∑
d1 ,...,dk −1 ,d′1 ,...,d′
k−1
⎛
⎝
k ∏
i=1
μ (di) μ (di′
) Fi
(logx di
) Gi
(logx di′
)
⎞
⎠
Sj′
(d1, . . . , dk−1, d′1, . . . , d′
k−1
).
(59)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 29 of 83 http://www.resmathsci.com/content/1/1/12
To show (53), it thus suffices to show the main term estimate
1 = (cε + o(1))B−k x
W , (60)
the first error term estimate
2 ≺≺ x1−ε, (61)
and the second error term estimate
3 x log−A x (62)
for any fixed A > 0.
We begin with (61). Observe that if p(n) > xε, then the only way that
(
n, qW ,d1,...,d′
k−1
)
can exceed 1 is if there is a prime xε < p x which divides both n and one of d1, . . . , d′
k−1; in particular, this case can only occur when k > 1. For the sake of notation, we will just
consider the contribution when there is a prime that divides p and d1, as the other 2k − 3
cases are similar. By (57), this contribution to 2 can then be crudely bounded (using (1))
by
2 ≺≺ ∑
xε<p x
∑
d1 ,...,dk −1 ,d′1 ,...,d′
k −1 ≤x;p|d1
1
[d1, d′1
]...
[
dk−1, d′
k−1
]∑
n x:p|n
1
≺≺ ∑
xε<p x
x p
⎛
⎝∑
e1 ≤x2 ;p|e1
τ (e1)
e1
⎞
⎠
k∏−1
i=2
⎛
⎝∑
ei ≤x2
τ (ei)
ei
⎞
⎠
≺≺ ∑
xε<p x
x p2
≺≺ x1−ε
as required, where we have made the change of variables ei := [di, di′], using the divisor
bound to control the multiplicity.
Now we show (62). From the hypothesis (28), we have qW,d1,...,d′
k−1 ≺≺ xθ whenever
the summand in (62) is non-zero. From the divisor bound, for each q ≺≺ xθ , there are
O (τ (q)O(1)) choices of d1, . . . , d′
k−1 with qW ,d1,...,d′
k−1 = q. We see that the product in (59)
is O(1). Thus, by (58), we may bound 3 by
3
∑
q≺≺xθ
τ (q)O(1) sup
a∈(Z/qZ)×
∣∣ (1[x+hk,2x+hk]λFk λGk 1p(·)>xε ; a (q))∣∣ .
From (2), we easily obtain the bound
3
∑
q≺≺xθ
τ (q)O(1) sup
a∈(Z/qZ)×
∣∣ (1[x+hk,2x+hk]λFk λGk 1p(·)>xε ; a (q))∣∣ x logO(1) x,
so by Cauchy-Schwarz, it suffices to show that ∑
q≺≺xθ
sup
a∈(Z/qZ)×
∣∣ (1[x+hk,2x+hk]λFk λGk 1p(·)>xε ; a (q))∣∣ x log−A x (63)
for any fixed A > 0.
If we had the additional hypothesis S(Fk)+S(Gk) < 1, then this would follow easily from
the hypothesis GEH[θ] thanks to Claim 12, since one can write λFk λGk 1p(·)>xε = α β
with
α(n) := 1p(n)>xε
∑
d,d′:[d,d′]=n
μ(d)Fk
(logx d) μ (d′) Gk
(logx d′)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 30 of 83 http://www.resmathsci.com/content/1/1/12
and
β(n) := 1p(n)>xε .
But even in the absence of the hypothesis S(Fk)+S(Gk) < 1, we can still invoke GEH[θ]
after appealing to the fundamental theorem of arithmetic. Indeed, if n ∈[ x + hk, 2x + hk]
with p(·) > ε, then we have
n = p1 . . . pr
for some primes xε < p1 ≤ · · · ≤ pr ≤ 2x + hk, which forces r ≤ 1
ε + 1. If we then
partition [xε, 2x + hk] by O
(
logA+1 x
)
intervals I1, . . . , Im, with each Ij contained in an
interval of the form
[
N,
(
1 + log−A x
) N
]
, then we have pi ∈ Iji for some 1 ≤ j1 ≤
· · · ≤ jr ≤ m, with the product interval Ij1 · · · · · Ijr intersecting [x + hk, 2x + hk]. For
fixed r, there are O
(
logAr+r x
)
such tuples ( j1, . . . , jr), and a simple application of the
prime number theorem with classical error term (and crude estimates on the discrepancy
) shows that each tuple contributes O
(
x log−Ar+O(1) x
)
to (63) (here, and for the rest
of this section, implied constants will be independent of A unless stated otherwise). In
particular, the O
(
logA(r−1) x
)
tuples ( j1, . . . , jr) with one repeated ji, or for which the
interval Ij1 · · · · · Ijr meets the boundary of [ x + hk, 2x + hk], contributes O
(
log−A+O(1) x
) .
This is an acceptable error to (63), and so these tuples may be removed. Thus, it suffices
to show that ∑
q≺≺xθ
sup
a∈(Z/qZ)×
∣∣∣
(
λFk λGk 1Aj1,...,jr ; a (q)
)∣∣∣ x log−A(r+1)+O(1) x
for any 1 ≤ r ≤ 1
ε + 1 and 1 ≤ j1 < · · · < jr ≤ m with Ij1 · · · · · Ijr contained in
[x+hk, x+2hk], where Aj1,...,jr is the set of all products p1 . . . pr with pi ∈ Iji for i = 1, . . . , r,
and where we allow implied constants in the notation to depend on ε. But for n in
Aj1,...,jr , the 2r factors of n are just the products of subsets of {p1, . . . , pr}, and from the
smoothness of Fk, Gk, we see that λFk (n) is equal to some bounded constant (depending
on j1, . . . , jr, but independent of p1, . . . , pr), plus an error of O(log−A x). As before, the
contribution of this error is O
(
log−A(r+1)+O(1) x
)
, so it suffices to show that
∑
q≺≺xθ
sup
a∈(Z/qZ)×
∣∣∣
(
1Aj1,...,jr ; a (q)
)∣∣∣ x log−A(r+1)+O(1) x.
But one can write 1Aj1,...,jr as a convolution 1Aj1 · · · 1Ajr , where Aji denotes the primes
in Iji ; assigning Ajr (for instance) to be β and the remaining portion of the convolution
to be α, the claim now follows from the hypothesis GEH[θ], thanks to the Siegel-Walfisz
theorem (see, e.g. [32, Satz 4] or [33, Th. 5.29]). Finally, we show (60). By Lemma 30, we have
∑
d1 ,...,dk−1 ,d′1 ,...,d′
k−1
d1 d′1 ,...,dk−1 d′
k−1,W coprime
∏k−1
i=1 μ (di) μ (di′
) Fi
(logx di
) Gi
(logx di′
)
φ
(
qW ,d1,...,d′
k−1
) =1
φ(W )
(C′ + o(1)) B−k+1,
where
C′ :=
k∏−1
i=1
∫1
0
Fi′(t)G′i(t) dt


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 31 of 83 http://www.resmathsci.com/content/1/1/12
(note that Fi, Gi are supported on [0, 1] by hypothesis), so by (56) it suffices to show that ∑
x+hk ≤n≤2x+hk
λFk (n)λGk (n)1p(n)>xε =
(
C′′
ε + o(1)
)x
log x , (64)
where C′ε′ is a quantity depending on ε but not on x such that
εli→m0 C′ε′ =
∫1
0
F′
k (t)G′
k(t) dt.
In the case S(Fk) + S(Gk) < 1, this would follow easily from (the k = 1 case of )
Theorem 20(i) and Proposition 14. In the general case, we may appeal once more to the
fundamental theorem of arithmetic. As before, we may factor n = p1 . . . pr for some
xε ≤ p1 ≤ · · · ≤ pr ≤ 2x + hk and r ≤ 1
ε + 1. The contribution of those n with a repeated
prime factor pi = pi+1 can easily be shown to be ≺≺ x1−ε in the same manner we dealt
with 2, so we may restrict attention to the square-free n, for which the pi are strictly
increasing. In that case, one can write
λFk (n) = (−1)r∂(logx p1) . . . ∂(logx pr)Fk(0)
and
λGk (n) = (−1)r∂(logx p1) . . . ∂(logx pr)Gk(0)
where ∂(h)F(x) := F(x + h) − F(x). On the other hand, a standard application of Mertens’
theorem and the prime number theorem (and an induction on r) shows that for any fixed
r ≥ 1 and any fixed continuous function f : Rr → R, we have ∑
xε≤p1<···<pr:x+hk ≤p1≤...pr≤2x+hk
f (logx p1, . . . , logx pr
) = (cf + o(1)) x
log x
where cf is the quantity
cf :=
∫
ε≤t1 <···<tr :t1 +···+tr =1
f (t1, . . . , tr) n1 . . . dtr−1
t1 . . . tr
where we lift Lebesgue measure dt1 . . . dtr−1 up to the hyperplane t1 + · · · + tr = 1, and
thus
∫
t1 +···+tr =1
F(t1, . . . , tr) dt1 . . . dtr−1 :=
∫
Rr−1
F(t1, . . . , tr−1, 1−t1−· · ·−tr−1)dt1 . . . dtr−1.
Putting all these together, we see that we obtain an asymptotic (64) with
C′ε′ := ∑
1≤r≤ ε1 +1
∫
ε≤t1 <···<tr :t1 +···+tr =1
∂(t1) . . . ∂(tr)Fk(0)∂(t1) . . . ∂(tr)Gk(0) dt1 . . . dtr−1
t1 . . . tr
.
By Proposition 14, we have C′ε′ + O(ε) = O(1). In the case Fk = Gk, we see that this
implies ′ε converges to a limit as ε → 0, and the general case Fk = Gk then follows from
using the Cauchy-Schwarz inequality. Therefore, we have the absolute convergence ∑
r>0
∫
0<t1 <···<tr :t1 +···+tr =1
|∂t1 . . . ∂tr Fk(0)||∂t1 . . . ∂tr Gk(0)| dt1 . . . dtr−1
t1 . . . tr
< ∞, (65)
and so, by the dominated convergence theorem, it suffices to establish the identity
∑
r>0
∫
0<t1 <···<tr :t1 +···+tr =1
∂t1 . . . ∂tr Fk(0)∂t1 . . . ∂tr Gk(0) dt1 . . . dtr−1
t1 . . . tr
=
∫1
0
F′
k (t)G′
k(t) dt.
(66)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 32 of 83 http://www.resmathsci.com/content/1/1/12
It will suffice to show the identity
∑
r>0
∫
0<t1 <···<tr :t1 +···+tr =1
|∂t1 . . . ∂tr F(0)|2 dt1 . . . dtr−1
t1 . . . tr
=
∫1
0
|F′(t)|2 dt (67)
for any smooth F : [0, +∞) → R, since (66) follows by replacing F with Fk + Gk and
Fk − Gk and then subtracting.
At this point, we use the following identity:
Lemma 33. For any positive reals t1, . . . , tr with r ≥ 1, we have
1
t1 . . . tr
=∑
σ ∈Sr
1 ∏r
i=1
(∑r
j=i tσ (j)
) . (68)
Thus, for instance, when r = 2, we have
1
t1t2
=1
(t1 + t2)t1
+1
(t1 + t2)t2
.
Proof. If the right-hand side of (68) is denoted fr (t1, . . . , tr), then one easily verifies the
identity
fr(t1, . . . , tr) = 1
t1 + · · · + tr
r ∑
i=1
fr−1(t1, . . . , ti−1, ti+1, . . . , tr)
for any r > 1; but the left-hand side of (68) also obeys this identity, and the claim then
follows from induction.
From this lemma and symmetrisation, we may rewrite the left-hand side of (67) as
∑
r>0
∫
t1 ,...,tr ≥0
t1 +···+tr =1
|∂(t1) . . . ∂(tr)F(0)|2 dt1 . . . dtr−1
∏r
i=1
(∑r
j=i ti
).
Let
Ia(F) :=
∫a
0
F′(t)2 dt,
and
Ja(F) := (∂(a)F(0))2.
One can then rewrite (67) as the identity
I1(F) =
∑ ∞
r=1
K1,r(F), (69)
where
Ka,r(F) :=
∫
t1 ,...,tr ≥0
t1 +···+tr =a
Jtr
(∂(t1) . . . ∂(tr−1)F) dt1 . . . dtr−1
a (a − t1) . . . (a − t1 − · · · − tr−1) .
To prove this, we first observe the identity
Ia(F) = 1
a Ja(F) +
∫
0≤t≤a
Ia−t
(∂(t)F) dt
a


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 33 of 83 http://www.resmathsci.com/content/1/1/12
for any a > 0; indeed, we have ∫
0≤t≤a
Ia−t(∂(t)F) dt
a=
∫
0≤t≤a;0≤u≤a−t
|F′(t + u) − F′(t)|2 dudt
a
=
∫
0≤t≤s≤a
|F′(s) − F′(t)|2 dsdt
a
=1
2
∫a
0
∫a
0
|F′(s) − F′(t)|2 dsdt
a
=
∫a
0
|F′(s)|2 ds − 1
a
(∫ a
0
F′(s) ds
) (∫ a
0
F′(t) dt
)
= Ia(F) − 1
a Ja(F),
and the claim follows. Iterating this identity k times, we see that
Ia(F) =
k ∑
r=1
Ka,r(F) + La,k(F) (70)
for any k ≥ 1, where
La,k(F) :=
∫
t1,...,tk ≥0
t1+···+tk ≤a
I1−t1−···−tk
(∂(t1) . . . ∂(tk)F) dt1 . . . dtk
a(a − t1) . . . (a − t1 − · · · − tk−1) .
In particular, dropping the La,k(F) term and sending k → ∞ yields the lower bound
∑ ∞
r=1
Ka,r(F) ≤ Ia(F). (71)
On the other hand, we can expand La,k(F) as ∫
t1,...,tk ,t≥0
t1+···+tk +t≤a
|∂(t1) . . . ∂(tk)F′(t)|2 dt1 . . . dtkdt
a(a − t1) . . . (a − t1 − · · · − tk−1) .
Writing s := t1 + · · · + tk, we obtain the upper bound
La,k(F) ≤
∫
s,t≥0:s+t≤a
Ks,k(Ft′) dt,
where Ft(x) := F(x + t). Summing this and using (71) and the monotone convergence
theorem, we conclude that
∑ ∞
k=1
La,k(F) ≤
∫
s,t≥0:s+t≤a
Is(Ft) dt < ∞,
and in particular La,k(F) → 0 as k → ∞. Sending k → ∞ in (70), we obtain (69) as
desired.
Reduction to a variational problem
Now that we have proven Theorems 19 and 20, we can now establish Theorems 22, 24,
26 and 28. The main technical difficulty is to take the multidimensional measurable func
tions F appearing in these functions and approximate them by tensor products of smooth
functions, for which Theorems 19 and 20 may be applied.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 34 of 83 http://www.resmathsci.com/content/1/1/12
Proof of Theorem 22
We now prove Theorem 22. Let k, m, θ obey the hypotheses of that theorem, and thus we
may find a fixed square-integrable function F : [0, +∞)k → R supported on the simplex
Rk :=
{
(t1, . . . , tk) ∈[0, +∞)k : t1 + · · · + tk ≤ 1
}
and not identically zero and with
∑k
i=1 Ji(F)
I(F) > 2m
θ . (72)
We now perform a number of technical steps to further improve the structure of F. Our
arguments here will be somewhat convoluted and are not the most efficient way to prove
Theorem 22 (which in any event was already established in [5]), but they will motivate
the similar arguments given below to prove the more difficult results in Theorems 24, 26
and 28. In particular, we will use regularisation techniques which are compatible with the
vanishing marginal condition (35) that is a key hypothesis in Theorem 28.
We first need to rescale and retreat a little bit from the slanted boundary of the simplex
Rk. Let δ1 > 0 be a sufficiently small fixed quantity, and write F1 : [0, +∞)k → R to be
the rescaled function
F1(t1, . . . , tk) := F
( t1
θ/2 − δ1
, . . . , tk
θ/2 − δ1
) .
Thus, F1 is a fixed square-integrable measurable function supported on the rescaled
simplex
(θ/2 − δ1) · Rk =
{
(t1, . . . , tk) ∈[0, +∞)k : t1 + · · · + tk ≤ θ/2 − δ1
} .
From (72), we see that if δ1 is small enough, then F1 is not identically zero and
∑k
i=1 Ji(F1)
I(F1) > m. (73)
Let δ1 and F1 be as above. Next, let δ2 > 0 be a sufficiently small fixed quantity (smaller
than δ1), and write F2 : [0, +∞)k → R to be the shifted function, defined by setting
F2(t1, . . . , tk) := F1(t1 − δ2, . . . , tk − δ2)
when t1, . . . , tk ≥ δ2, and F2(t1, . . . , tk) = 0 otherwise. As F1 was square-integrable, com
pactly supported, and not identically zero, and because spatial translation is continuous
in the strong operator topology on L2, it is easy to see that we will have F2 not identically
zero and that
∑k
i=1 Ji(F2)
I(F2) > m (74)
for δ2 small enough (after restricting F2 back to [0, +∞)k, of course). For δ2 small enough,
this function will be supported on the region {
(t1, . . . , tk) ∈ Rk : t1 · · · + tk ≤ θ/2 − δ2; t1, . . . , tk ≥ δ2
} ,
and thus F2 stays away from all the boundary faces of Rk.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 35 of 83 http://www.resmathsci.com/content/1/1/12
By convolving F2 with a smooth approximation to the identity that is supported suf
ficiently close to the origin, one may then find a smooth function F3 : [0, +∞)k → R,
supported on {
(t1, . . . , tk) ∈ Rk : t1 · · · + tk ≤ θ/2 − δ2/2; t1, . . . , tk ≥ δ2/2
} ,
which is not identically zero and such that
∑k
i=1 Ji(F3)
I(F3) > m. (75)
We extend F3 by zero to all of Rk and then define the function f3 : Rk → R by
f3(t1, . . . , tk) :=
∫
s1≥t1,...,sk ≥tk
F3(s1, . . . , sk) ds1 . . . dsk,
and thus f3 is smooth, not identically zero and supported on the region
⎧⎨
⎩(t1, . . . , tk) ∈ Rk :
k ∑
i=1
max(ti, δ2/2) ≤ θ/2 − δ2/2
⎫⎬
⎭ . (76)
From the fundamental theorem of calculus, we have
F3(t1, . . . , tk) := (−1)k ∂k
∂t1 . . . ∂tk
f3(t1, . . . , tk), (77)
and so I(F3) = I ̃( f3) and Ji(F3) = J ̃i( f3) for i = 1, . . . , k, where
I ̃(f3) :=
∫
[0,+∞)k
∣∣∣∣∣
∂k
∂t1 . . . ∂tk
f3(t1, . . . , tk)
∣∣∣∣∣
2
dt1 . . . dtk (78)
and
J ̃i( f3) :=
∫
[0,+∞)k−1
∣∣∣∣∣
∂ k−1
∂t1 . . . ∂ti−1∂ti+1 . . . ∂tk
f3(t1, . . . , ti−1, 0, ti+1, . . . , tk)
∣∣∣∣∣
2
dt1 . . . dti−1dti+1 . . . dtk.
(79)
In particular,
∑k
i=1 J ̃i( f3)
I ̃( f3) > m. (80)
Now we approximate f3 by linear combinations of tensor products. By the Stone
Weierstrass theorem, we may express f3 as the uniform limit of functions of the form
(t1, . . . , tk) →
J ∑
j=1
cjf1,j(t1) . . . fk,j(tk) (81)
where c1, . . . , cJ are real scalars, and fi,j : R → R are smooth compactly supported func
tions. Since f3 is supported in (76), we can ensure that all the components f1,j(t1) . . . fk,j(tk)
are supported in the slightly larger region
⎧⎨
⎩(t1, . . . , tk) ∈ Rk :
k ∑
i=1
max(ti, δ2/4) ≤ θ/2 − δ2/4
⎫⎬
⎭.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 36 of 83 http://www.resmathsci.com/content/1/1/12
Observe that if one convolves a function of the form (81) by a smooth approxima
tion to the identity which is of tensor product form (t1, . . . , tk) → φ1(t1) . . . φ1(tk), one
obtains another function of this form. Such a convolution converts a uniformly conver
gent sequence of functions to a uniformly smoothly convergent sequence of functions
(that is to say, all derivatives of the functions converge uniformly). From this, we con
clude that f3 can be expressed as the smooth limit of functions of the form (81), with each
component f1,j(t1) . . . fk,j(tk) supported in the region
⎧⎨
⎩(t1, . . . , tk) ∈ Rk :
k ∑
i=1
max(ti, δ2/8) ≤ θ/2 − δ2/8
⎫⎬
⎭.
Thus, we may find such a linear combination
f4(t1, . . . , tk) =
J ∑
j=1
cjf1,j(t1) . . . fk,j(tk) (82)
with J, cj, fi,j fixed and f4 not identically zero, with
∑k
i=1 J ̃i( f4)
I ̃( f4) > m. (83)
Furthermore, by construction we have
S( f1,j) + · · · + S( fk,j) < θ
2 ≤1
2 (84)
for all j = 1, . . . , J, where S() was defined in (22).
Now we construct the sieve weight ν : N → R by the formula
ν(n) :=
⎛
⎝
J ∑
j=1
cjλf1,j (n + h1) . . . λfk,j (n + hk)
⎞
⎠
2
, (85)
where the divisor sums λf were defined in (16).
Clearly ν is non-negative. Expanding out the square and using Theorem 20(i) and (84),
we see that ∑
x≤n≤2x
n=b (W )
ν(n) = (α + o(1))B−k x
log x
where
α :=
J ∑
j=1
J ∑
j′ =1
cjcj′
k ∏
i=1
∫∞
0
fi′,j(ti)f ′
i,j′ (ti) dti
which factorizes using (82) and (78) as
α=
∫
[0,+∞)k
∣∣∣∣∣
∂k
∂t1 . . . ∂tk
f4(t1, . . . , tk)
∣∣∣∣∣
2
dt1 . . . dtk
= I ̃( f4).


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 37 of 83 http://www.resmathsci.com/content/1/1/12
Now consider the sum
∑
x≤n≤2x
n=b (W )
ν(n)θ (n + hk).
By (20), one has
λfk,j (n + hk) = fk,j(0)
whenever n gives a non-zero contribution to the above sum. Expanding out the square in
(85) again and using Theorem 19(i) and (84) (and the hypothesis EH[θ]), we thus see that
∑
x≤n≤2x
n=b (W )
ν(n)θ (n + hk) = (βk + o(1)) B1−k x
φ(W )
where
βk :=
J ∑
j=1
J ∑
j′ =1
cjcj′ fi,j(0)fi,j′ (0)
k∏−1
i=1
∫∞
0
fi′,j(ti)f ′
i,j′ (ti) dti
which factorizes using (82) and (79) as
βk =
∫
[0,+∞)k
∣∣∣∣∣
∂k
∂t1 . . . ∂tk−1
f4(t1, . . . , tk−1, 0)
∣∣∣∣∣
2
dt1 . . . dtk−1
= J ̃k(f4).
More generally, we see that
∑
x≤n≤2x
n=b (W )
ν(n)θ (n + hk) = (βi + o(1)) B1−k x
φ(W )
for i = 1, . . . , k, with βi := J ̃i( f4). Applying Lemma 18 and (75), we obtain DHL[k; m + 1]
as required.
Proof of Theorem 24
Now we prove Theorem 24, which uses a very similar argument to that of the previous
section. Let k, m, , δ, F be as in Theorem 24. By performing the same rescaling as in the
previous section (but with 1/2 + 2 playing the role of θ), we see that we can find a fixed
square-integrable measurable function F1 supported on the rescaled truncated simplex
{
(t1, . . . , tk) ∈[0, +∞)k : t1 + · · · + tk ≤ 1
4 + − δ1; t1, . . . , tk < δ − δ1
}


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 38 of 83 http://www.resmathsci.com/content/1/1/12
for some sufficiently small fixed δ1 > 0, such that (73) holds. By repeating the arguments
of the previous section, we may eventually arrive at a smooth function f4 : Rk → R of
the form (82), which is not identically zero and obeys (83) and such that each component
f1,j(t1) . . . fk,j(tk) is supported in the region
⎧⎨
⎩(t1, . . . , tk) ∈ Rk :
k ∑
i=1
max(ti, δ2/8) ≤ 1
4 + − δ2/8; t1, . . . , tk < δ − δ2/8
⎫⎬
⎭
for some sufficiently small δ2 > 0. In particular, one has
S( f1,j) + · · · + S( fk,j) < 1
4+ ≤1
2
and
S( f1,j), . . . , S( fk,j) < δ
for all j = 1, . . . , J. If we then define ν by (85) as before, and repeat all of the above
arguments (but use Theorem 19(ii) and MPZ[ , δ] in place of Theorem 19(i) and EH[θ]),
we obtain the claim; we leave the details to the interested reader.
Proof of Theorem 26
Now we prove Theorem 26. Let k, m, ε, θ be as in that theorem. Then, one may find a
square-integrable function F : [0, +∞)k → R supported on (1 + ε) · Rk which is not
identically zero, and with
∑k
i=1 Ji,1−ε(F)
I(F) > 2m
θ.
By truncating and rescaling as in the ‘Proof of Theorem 22’ section, we may find a fixed
bounded measurable function F1 : [0, +∞)k → R on the simplex (1 + ε) ( θ
2 − δ1
) · Rk such that
∑k
i=1 Ji,(1−ε) θ
2 (F1)
I(F1) > m.
By repeating the arguments in the ‘Proof of Theorem 22’ section, we may eventually
arrive at a smooth function f4 : Rk → R of the form (82), which is not identically zero
and obeys
∑k
i=1 J ̃i,(1−ε) θ
2 ( f4)
I ̃( f4) > m (86)
with
J ̃i,(1−ε) θ
2 (f4) :=
∫
(1−ε) θ
2 ·Rk−1
∣∣∣∣∣
∂ k−1
∂t1 . . . ∂ti−1∂ti+1 . . . ∂tk
f4(t1, . . . , ti−1, 0, ti+1, . . . , tk)
∣∣∣∣∣
2
dt1 . . . dti−1dti+1 . . . dtk,


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 39 of 83 http://www.resmathsci.com/content/1/1/12
and such that each component f1,j(t1) . . . fk,j(tk) is supported in the region
⎧⎨
⎩(t1, . . . , tk) ∈ Rk :
k ∑
i=1
max(ti, δ2/8) ≤ (1 + ε) θ
2 − δ2
8
⎫⎬
⎭
for some sufficiently small δ2 > 0. In particular, we have
S( f1,j) + · · · + S( fk,j) ≤ (1 + ε) θ
2 − δ2
8 (87)
for all 1 ≤ j ≤ J.
Let δ3 > 0 be a sufficiently small fixed quantity (smaller than δ1 or δ2). By a smooth
partitioning, we may assume that all of the fi,j are supported in intervals of length at most
δ3, while keeping the sum
J ∑
j=1
|cj|| f1,j(t1)| . . . | fk,j(tk)| (88)
bounded uniformly in t1, . . . , tk and in δ3.
Now let ν be as in (85), and consider the expression ∑
x≤n≤2x
n=b (W )
ν(n).
This expression expands as a linear combination of the expressions
∑
x≤n≤2x
n=b (W )
k ∏
i=1
λfi,j (n + hi)λfi,j′ (n + hi)
for various 1 ≤ j, j′ ≤ J. We claim that this sum is equal to ⎛
⎝
k ∏
i=1
∫1
0
fi′,j(ti)f ′
i,j′ (ti) dti + o(1)
⎞
⎠ B−k x
W.
To see this, we divide into two cases. First, suppose that hypothesis (i) from Theorem 26
holds, then from (87) we have
k ∑
i=1
S( fi,j) + S( fi,j′ ) < (1 + ε)θ < 1
and the claim follows from Theorem 20(i). Now suppose instead that hypothesis (ii) from
Theorem 26 holds, then from (87) one has
k ∑
i=1
S( fi,j) + S( fi,j′ ) < (1 + ε)θ < k
k − 1θ,
and so from the pigeonhole principle, we have ∑
1≤i≤k:i=i0
S( fi,j) + S( fi,j′ ) < θ
for some i0 = 1, . . . , k. The claim now follows from Theorem 20(ii).


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 40 of 83 http://www.resmathsci.com/content/1/1/12
Putting these together as in the ‘Proof of Theorem 22’ section, we conclude that ∑
x≤n≤2x
n=b (W )
ν(n) = (α + o(1))B−k x
W
where
α := I ̃(f4).
Now we consider the sum ∑
x≤n≤2x
n=b (W )
ν(n)θ (n + hk). (89)
From Proposition 13, we see that we have EH[θ] as a consequence of the hypotheses of
Theorem 26. However, this and Theorem 19 are not strong enough to obtain an asymp
totic for the sum (89), as there is an epsilon loss in (87). But observe that Lemma 18 only
requires a lower bound on the sum (89), rather than an asymptotic.
To obtain this lower bound, we partition {1, . . . , J} into J1 ∪ J2, where J1 consists of
those indices j ∈ {1, . . . , J} with
S( f1,j) + · · · + S( fk−1,j) < (1 − ε) θ
2 (90)
and J2 is the complement. From the elementary inequality
(x1 + x2)2 = x21 + 2x1x2 + x22 ≥ (x1 + 2x2)x1,
we obtain the pointwise lower bound
ν(n) ≥
⎛
⎝
⎛
⎝∑
j∈J1
+2
∑
j∈J2
⎞
⎠ cjλf1,j (n + h1) . . . λfk,j (n + hk)
⎞
⎠
×
⎛
⎝∑
j′ ∈J1
cj′ λf1,j′ (n + h1) . . . λfk,j′ (n + hk )
⎞
⎠.
The point of performing this lower bound is that if j ∈ J1 ∪ J2 and j′ ∈ J1, then from
(87) and (90) one has
k∑ −1
i=1
S ( fi,j
) + S ( fi,j′
)<θ
which makes Theorem 19(i) available for use. Indeed, for any j ∈ {1, . . . , J} and i =
1, . . . , k, we have from (87) that
S ( fi,j
) ≤ (1 + ε) θ
2 < θ < 1,
and so by (20), we have
ν(n)θ (n + hk) ≥
⎛
⎝
⎛
⎝∑
j∈J1
+2
∑
j∈J2
⎞
⎠ cjλf1,j (n + h1) . . . λfk−1,j
(n + hk−1
) fk,j(0)
⎞
⎠
×
⎛
⎝∑
j′ ∈J1
cj′ λf1,j′ (n + h1) . . . λfk−1,j′
(n + hk−1
) fk,j′ (0)
⎞
⎠ θ (n + hk)
(91)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 41 of 83 http://www.resmathsci.com/content/1/1/12
for x ≤ n ≤ 2x. If we then apply Theorem 19(i) and the hypothesis EH[θ], we obtain the
lower bound ∑
x≤n≤2x
n=b (W )
ν(n)θ (n + hk) ≥ (βk − o(1))B1−k x
φ(W )
with
βk :=
⎛
⎝∑
j∈J1
+2
∑
j∈J2
⎞
⎠∑
j′ ∈J1
cjcj′ fk,j(0)fk,j′ (0)
k∏−1
i=1
∫∞
0
fi′,j(ti)f ′
i,j′ (ti) dti
which we can rearrange as
βk =
∫
[0,+∞)k−1
(
∂ k−1
∂t1 . . . ∂tk−1
f4,1(t1, . . . , tk−1, 0) + 2 ∂k−1
∂t1 . . . ∂tk−1
f4,2(t1, . . . , tk−1, 0)
)
∂ k−1
∂t1 . . . ∂tk−1
f4,1(t1, . . . , tk−1, 0) dt1 . . . dtk−1
where
f4,l(t1, . . . , tk) := ∑
j∈Jl
cjf1,j(t1) . . . fk,j(tk)
for l = 1, 2. Note that f4,1, f4,2 are both bounded pointwise by (88), and their supports only
overlap on a set of measure O(δ3). We conclude that
βk = J ̃k( f4,1) + O(δ3)
with the implied constant independent of δ3, and thus
βk = J ̃k,(1−ε) θ
2 ( f4) + O(δ3).
A similar argument gives ∑
x≤n≤2x
n=b (W )
ν(n)θ (n + hi) ≥ (βi − o(1))B1−k x
φ(W )
for i = 1, . . . , k with
βi = J ̃i,(1−ε) θ
2 ( f4) + O(δ3).
If we choose δ3 small enough, then the claim DHL[k; m+1] now follows from Lemma 18
and (86).
Proof of Theorem 28
Finally, we prove Theorem 28. Let k, m, ε, F be as in that theorem. By rescaling as in previ
ous sections, we may find a square-integrable function F1 : [0, +∞)k → R supported on
(k k−1
θ
2 − δ1
)
· Rk for some sufficiently small fixed δ1 > 0, which is not identically zero,
which obeys the bound
∑k
i=1 Ji,(1−ε) θ
2 (F1)
I(F1) > m


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 42 of 83 http://www.resmathsci.com/content/1/1/12
and also obeys the vanishing marginal condition (35) whenever t1, . . . , ti−1, ti+1, . . . , tk ≥
0 are such that
t1 + · · · + ti−1 + ti+1 + · · · + tk > (1 + ε) θ
2 − δ1.
As before, we pass from F1 to F2 by a spatial translation, and from F2 to F3 by a regu
larisation; crucially, we note that both of these operations interact well with the vanishing
marginal condition (35), with the end product being that we obtain a smooth function
F3 : [0, +∞)k → R, supported on the region {
(t1, . . . , tk) ∈ Rk : t1 · · · + tk ≤ k
k−1
θ
2 − δ2
2 ; t1, . . . , tk ≥ δ2
2
}
for some sufficiently small δ2 > 0, which is not identically zero, obeying the bound
∑k
i=1 Ji,(1−ε) θ
2 (F3)
I(F3) > m
and also obeying the vanishing marginal condition (35) whenever t1, . . . , ti−1,
ti+1, . . . , tk ≥ 0 are such that
t1 + · · · + ti−1 + ti+1 + · · · + tk > (1 + ε) θ
2 − δ2
2.
As before, we now define the function f3 : Rk → R by
f3(t1, . . . , tk) :=
∫
s1≥t1,...,sk ≥tk
F3(s1, . . . , sk) ds1 . . . dsk,
and thus, f3 is smooth, not identically zero and supported on the region
⎧⎨
⎩(t1, . . . , tk) ∈ Rk :
k ∑
i=1
max(ti, δ2/2) ≤ k
k−1
θ
2 − δ2
2
⎫⎬
⎭.
Furthermore, from the vanishing marginal condition, we see that we also have
f3(t1, . . . , tk) = 0
whenever we have some 1 ≤ i ≤ k for which ti ≤ δ2/2 and
t1 + · · · + ti−1 + ti+1 + · · · + tk ≥ (1 + ε) θ
2 − δ2
2.
From the fundamental theorem of calculus as before, we have
∑k
i=1 J ̃i,(1−ε) θ
2 ( f3)
I ̃( f3) > m.
Using the Stone-Weierstrass theorem as before, we can then find a function f4 of the
form
(t1, . . . , tk) →
J ∑
j=1
cjf1,j(t1) . . . fk,j(tk) (92)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 43 of 83 http://www.resmathsci.com/content/1/1/12
where c1, . . . , cJ are real scalars, and fi,j : R → R are smooth functions supported of
intervals of length at most δ3 > 0 for some sufficiently small δ3 > 0, with the support of
each component f1,j(t1) . . . fk,j(tk) supported in the region
⎧⎨
⎩(t1, . . . , tk) ∈ Rk :
k ∑
i=1
max(ti, δ2/8) ≤ k
k−1
θ
2 − δ2/8
⎫⎬
⎭
and avoiding the regions {
(t1, . . . , tk) ∈ Rk : ti ≤ δ2/8; t1 + · · · + ti−1 + ti+1 + · · · + tk ≥ (1 + ε) θ
2 − δ2/8
}
for each i = 1, . . . , k, and such that
∑k
i=1 J ̃i,(1−ε) θ
2
( f4
)
I ̃( f4) > m.
In particular, for any j = 1, . . . , J we have
S ( f1,j
) + · · · + S ( fk,j
)< k
k−1
θ
2 <1
2
k
k − 1 ≤ 1 (93)
and for any i = 1, . . . , k with fk,i not vanishing at zero, we have
S ( f1,j
) + · · · + S ( fk,i−1
) + S ( fk,i+1
) + · · · + S ( fk,j
) < (1 + ε) θ
2 . (94)
Let ν be defined by (85). From (93), the hypothesis GEH[θ], and the argument from the
previous section used to prove Theorem 26(ii), we have ∑
x≤n≤2x
n=b (W )
ν(n) = (α + o(1)) B−k x
W
where
α := I ̃ ( f4
).
Similarly, from (94) (and the upper bound S ( fi,j
) < 1 from (93)), the hypothesis EH[θ]
(which is available by Proposition 13), and the argument from the previous section, we
have
∑
x≤n≤2x
n=b (W )
ν(n)θ (n + hi) ≥ (βi − o(1)) B1−k x
φ(W )
for i = 1, . . . , k with
βi = J ̃i,(1−ε) θ
2 ( f4) + O(δ3).
Setting δ3 small enough, the claim DHL[k; m + 1] now follows from Lemma 18.
Asymptotic analysis
We now establish upper and lower bounds on the quantity Mk defined in (33), as well as
for the related quantities appearing in Theorem 24.
To obtain an upper bound on Mk, we use the following consequence of the Cauchy
Schwarz inequality.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 44 of 83 http://www.resmathsci.com/content/1/1/12
Lemma 34 (Cauchy-Schwarz). Let k ≥ 2, and suppose that there exist positive
measurable functions Gi : Rk → (0, +∞) for i = 1, . . . , k such that ∫∞
0
Gi(t1, . . . , tk) dti ≤ 1 (95)
for all t1, . . . , ti−1, ti+1, . . . , tk ≥ 0, where we extend Gi by zero to all of [0, +∞)k. Then, we
have
Mk ≤ ess sup
(t1,...,tk )∈Rk
k ∑
i=1
1
Gi(t1, . . . , tk) . (96)
Here ess sup refers to essential supremum (thus, we may ignore a subset of Rk of measure
zero in the supremum).
Proof. Let F : [0, +∞)k → R be a square-integrable function supported on Rk. From
the Cauchy-Schwarz inequality and (95), we have (∫ ∞
0
F(t1, . . . , tk) dti
)2
≤
∫∞
0
F(t1, . . . , tk)2
Gi(t1, . . . , tk) dti
for any t1, . . . , ti−1, ti+1, . . . , tk ≥ 0. Inserting this into (32) and integrating, we conclude
that
Ji(F) ≤
∫
Rk
F(t1, . . . , tk)2
Gi(t1, . . . , tk) dt1 . . . dtk.
Summing in i and using (31), (33), and (96), we obtain the claim.
As a corollary, we can compute Mk exactly if we can locate a positive eigenfunction:
Corollary 35. Let k ≥ 2, and suppose that there exists a positive function F : Rk →
(0, +∞) obeying the eigenfunction equation
λF(t1, . . . , tk) =
k ∑
i=1
∫∞
0
F(t1, . . . , ti−1, ti′, ti+1, . . . , tk) dti′ (97)
for some λ > 0 and all (t1, . . . , tk) ∈ Rk, where we extend F by zero to all of [0, +∞)k.
Then, λ = Mk.
Proof. On the one hand, if we integrate (97) against F and use (31) and (32), we see that
λI(F) =
k ∑
i=1
Ji (F ),
and thus by (33), we see that Mk ≥ λ. On the other hand, if we apply Lemma 34 with
Gi(t1, . . . , tk) := F(t1, . . . , tk)
∫∞
0 F(t1, . . . , ti−1, ti′, ti+1, . . . , tk) dti′
,
we see that Mk ≤ λ, and the claim follows.
This allows for an exact calculation of M2:


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 45 of 83 http://www.resmathsci.com/content/1/1/12
Corollary 36 (Computation of M2). We have
M2 = 1
1 − W (1/e) = 1.38593 . . .
where the Lambert W -function W (x) is defined for positive x as the unique positive
solution to x = W (x)eW(x).
Proof. If we set λ := 1
1−W(1/e) = 1.38593 . . . , then a brief calculation shows that
2λ − 1 = λ log λ − λ log(λ − 1). (98)
Now if we define the function f : [0, 1] →[0, +∞) by the formula
f (x) := 1
λ−1+x + 1
2λ − 1 log λ − x
λ − 1 + x,
then a further brief calculation shows that
∫ 1−x
0
f (y) dy = λ − 1 + x
2λ − 1 log λ − x
λ − 1 + x + λ log λ − λ log(λ − 1)
2λ − 1
for any 0 ≤ x ≤ 1, and hence by (98) that
∫ 1−x
0
f (y) dy = (λ − 1 + x)f (x).
If we then define the function F : R2 → (0, +∞) by F(x, y) := f (x) + f (y), we conclude
that
∫ 1−x
0
F(x′, y) dx′ +
∫ 1−y
0
F(x, y′) dy′ = λF(x, y)
for all (x, y) ∈ R2, and the claim now follows from Corollary 35.
We conjecture that a positive eigenfunction for Mk exists for all k ≥ 2, not just for k = 2;
however, we were unable to produce any such eigenfunctions for k > 2. Nevertheless,
Lemma 34 still gives us a general upper bound:
Corollary 37. We have Mk ≤ k
k−1 log k for any k ≥ 2.
Thus, for instance, one has M2 ≤ 2 log 2 = 1.38629 . . . , which compares well with
Corollary 36. On the other hand, Corollary 37 also gives
M4 ≤ 4
3 log 4 = 1.8454 . . . ,
so that one cannot hope to establish DHL[4; 2] (or DHL[3; 2]) solely through Theorem 22
even when assuming GEH, and must rely instead on more sophisticated criteria for
DHL[k; m] such as Theorem 26 or Theorem 28.
Proof. If we set Gi : Rk → (0, +∞) for i = 1, . . . , k to be the functions
Gi(t1, . . . , tk) := k − 1
log k
1
1 − t1 − · · · − tk + kti


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 46 of 83 http://www.resmathsci.com/content/1/1/12
then direct calculation shows that
∫∞
0
Gi(t1, . . . , tk) dti ≤ 1
for all t1, . . . , ti−1, ti+1, . . . , tk ≥ 0, where we extend Gi by zero to all of [0, +∞)k. On the
other hand, we have
k ∑
i=1
1
Gi(t1, . . . , tk) = k
k − 1 log k
for all (t1, . . . , tk) ∈ Rk. The claim now follows from Lemma 34.
The upper bound arguments for Mk can be extended to other quantities such as Mk,ε,
although the bounds do not appear to be as sharp in that case. For instance, we have the
following variant of Lemma 37, which shows that the improvement in constants when
moving from Mk to Mk,ε is asymptotically modest:
Proposition 38. For any k ≥ 2 and ε ≥ 0, we have
Mk,ε ≤ k
k − 1 log(2k − 1).
Proof. Let F : [0, +∞)k → R be a square-integrable function supported on (1 + ε) · Rk.
If i = 1, . . . , k and (t1, . . . , ti−1, ti+1, . . . , tk) ∈ (1 − ε) · Rk, then if we write s := 1 − t1 −
· · · − ti−1 − ti+1 − · · · − tk, we have s ≥ ε and hence
∫ 1−t1−···−ti−1−ti+1−···−tk +ε
0
1
1 − t1 − · · · − tk + kti
dti =
∫ s+ε
0
1
s + (k − 1)ti
dti
=1
k − 1 log ks + (k − 1)ε
s
≤1
k − 1 log(2k − 1).
By Cauchy-Schwarz, we conclude that
(∫ ∞
0
F(t1, . . . , tk) dti
)2
≤1
k − 1 log(2k−1)
∫∞
0
(1−t1−· · ·−tk +kti)F(t1, . . . , tk)2 dti.
Integrating in t1, . . . , ti−1, ti+1, . . . , tk and summing in i, we obtain the claim.
Remark 39. The same argument, using the weight 1 + a(−t1 − · · · − tk + kti), gives the
more general inequality
Mk,ε ≤ k
a(k − 1) log
(
k + (a(1 + ε) − 1)(k − 1)
1 − a(1 − ε)
)
whenever 1
1+ε < a < 1
1−ε ; the case a = 1 is Proposition 38, and the limiting case a = 1
1+ε recovers Lemma 37 when one sends ε to zero.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 47 of 83 http://www.resmathsci.com/content/1/1/12
One can also adapt the computations in Corollary 36 to obtain exact expressions for
M2,ε, although the calculations are rather lengthy and will only be summarized here. For
fixed 0 < ε < 1, the eigenfunctions F one seeks should take the form
F(x, y) := f (x) + f (y)
for x, y ≥ 0 and x + y ≤ 1 + ε, where
f (x) := 1x≤1−ε
∫ 1+ε−x
0
F(x, t) dt.
In the regime 0 < ε < 1/3, one can calculate that f will (up to scalar multiples) take the
form
f (x) = 1x≤2ε
C1
λ−1−ε+x
+ 12ε≤x≤1−ε
( log(λ − x) − log(λ − 1 − ε + x)
2λ − 1 − ε + 1
λ−1−ε+x
)
where
C1 := log(λ − 2ε) − log(λ − 1 + ε)
1 − log(λ − 1 + ε) + log(λ − 1 − ε)
and λ is the largest root of the equation
1 = C1(log(λ − 1 + ε) − log(λ − 1 − ε)) − log(λ − 1 + ε)
+ (λ − 1 + ε) log(λ − 1 + ε) − (λ − 2ε) log(λ − 2ε)
2λ − 1 − ε .
In the regime 1/3 ≤ ε < 1, the situation is significantly simpler, and one has the exact
expressions
f (x) = 1x≤1−ε
λ−1−ε+x
and
λ = e(1 + ε) − 2ε
e−1 .
In both cases, a variant of Corollary 35 can be used to show that M2,ε will be equal to λ;
thus, for instance,
M2,ε = e(1 + ε) − 2ε
e−1
for 1/3 ≤ ε < 1. In particular, M2,ε increases to 2 in the limit ε → 1; the lower
bound lim infε→1 M2,ε ≥ 2 can also be established by testing with the function F(x, y) :=
1x≤δ,y≤1+ε−δ + 1y≤δ,x≤1+ε−δ for some sufficiently small δ > 0.
Now we turn to lower bounds on Mk, which are of more relevance for the purpose
of establishing results such as Theorem 23. If one restricts attention to those functions
F : Rk → R of the special form F(t1, . . . , tk) = f (t1 + · · · + tk) for some function
f : [0, 1] → R, then the resulting variational problem has been optimized in previous
works [39] (and originally in an unpublished work of Conrey), giving rise to the lower
bound
Mk ≥ 4k(k − 1)
j2
k−2


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 48 of 83 http://www.resmathsci.com/content/1/1/12
where jk−2 is the first positive zero of the Bessel function Jk−2. This lower bound is
reasonably strong for small k; for instance, when k = 2 it shows that
M2 ≥ 1.383 . . .
which compares well with Corollary 36, and also shows that M6 > 2, recovering the result
of Goldston, Pintz, and Yıldırım that DHL[6; 2] (and hence H1 ≤ 16) was true on the
Elliott-Halberstam conjecture. However, one can show that 4k(k−1)
j2
k−2
< 4 for all k (see [36]),
so this lower bound cannot be used to force Mk to be larger than 4.
In [5], the lower bound
Mk ≥ log k − 2 log log k − 2 (99)
was established for all sufficiently large k. In fact, the arguments in [5] can be used to show
this bound for all k ≥ 200 (for k < 200, the right-hand side of (99) is either negative or
undefined). Indeed, if we use the bound ([5], (7.19)) with A chosen so that A2eA = k, then
3 < A < log k when k ≥ 200, hence eA = k/A2 > k/ log2 k and so A ≥ log k − 2 log log k.
By using the bounds A
eA−1 < 1
6 (since A > 3) and eA/k = 1/A2 < 1/9, we see that the
right-hand side of ([5], (8.17)) exceeds A − 1
(1−1/6−1/9)2 ≥ A − 2, which gives (99).
We will remove the log log k term in (99) via the following explicit estimate.
Theorem 40. Let k ≥ 2, and let c, T, τ > 0 be parameters. Define the function g :
[ 0, T] → R by
g(t) := 1
c + (k − 1)t (100)
and the quantities
m2 :=
∫T
0
g(t)2 dt (101)
μ := 1
m2
∫T
0
tg(t)2 dt (102)
σ 2 := 1
m2
∫T
0
t2g(t)2 dt − μ2. (103)
Assume the inequalities
kμ ≤ 1 − τ (104)
kμ < 1 − T (105)
kσ 2 < (1 + τ − kμ)2. (106)
Then, one has
k
k − 1 log k − M[T]
k≤ k
k−1
Z + Z3 + WX + VU
(1 + τ/2)
(
1 − kσ2
(1+τ −kμ)2
) (107)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 49 of 83 http://www.resmathsci.com/content/1/1/12
where Z, Z3, W , X, V , U are the explicitly computable quantities
Z := 1
τ
∫ 1+τ
1
(
r
(
log r − kμ
T + kσ2
4(r − kμ)2 log r−kμ
T
)
+ r2
4kT
)
dr (108)
Z3 := 1
m2
∫T
0
kt log
(
1+ t
T
)
g(t)2 dt (109)
W := 1
m2
∫T
0
log
(
1+ τ
kt
)
g(t)2 dt (110)
X := log k
τ c2 (111)
V := c
m2
∫T
0
1
2c + (k − 1)t g(t)2 dt (112)
U := log k
c
∫1
0
((1 + uτ − (k − 1)μ − c)2 + (k − 1)σ 2) du. (113)
Of course, since M[T]
k ≤ Mk, the bound (107) also holds with M[T]
k replaced by Mk.
Proof. From (33), we have
k ∑
i=1
Ji(F) ≤ M[T]
k I(F)
whenever F : [0, +∞)k → R is square-integrable and supported on [0, T]k ∩Rk. By
rescaling, we conclude that
k ∑
i=1
Ji(F) ≤ rM[T]
k I(F)
whenever r > 0 and F : [0, +∞)k → R is square-integrable and supported on [0, rT]k ∩r ·
Rk. We apply this inequality with the function
F(t1, . . . , tk) := 1t1+···+tk≤rg(t1) . . . g(tk)
where r > 1 is a parameter which we will eventually average over, and g is extended by
zero to [0, +∞). We thus have
I(F) = mk2
∫∞
0
...
∫∞
0
1t1+···+tk ≤r
k ∏
i=1
g(ti)2 dti
m2
.
We can interpret this probabilistically as
I(F) = mk2P(X1 + · · · + Xk r)
where X1, . . . , Xk are independent random variables taking values in [0, T] with probabil
ity distribution 1
m2 g(t)2 dt. In a similar fashion, we have
Jk(F) = mk−1
2
∫∞
0
...
∫∞
0
(∫
[0,r−t1−···−tk−1]
g(t) dt
)2 k∏−1
i=1
g(ti)2 dti
m2
,


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 50 of 83 http://www.resmathsci.com/content/1/1/12
where we adopt the convention that ∫
[a,b] vanishes when b < a. In probabilistic language,
we thus have
Jk(F) = mk−1
2E
(∫
[0,r−X1−···−Xk−1]
g(t) dt
)2
.
Also by symmetry, we see that Ji(F) = Jk(F) for all i = 1, . . . , k. Putting all these
together, we conclude that
E
(∫ r−X1−···−Xk−1
0
g(t) dt
)2
≤ m2M[T]
kr
k P(X1 + · · · + Xk ≥ r)
for all r > 1. Writing Si := X1 + · · · + Xi, we abbreviate this as
E
(∫
[0,r−Sk −1 ]
g(t) dt
)2
≤ m2M[T]
kr
k P(Sk ≥ r). (114)
Now we run a variant of the Cauchy-Schwarz argument used to prove Corollary 37. If,
for fixed r > 0, we introduce the random function h : (0, +∞) → R by the formula
h(t) := 1
r − Sk−1 + (k − 1)t 1Sk−1<r (115)
and observe that whenever Sk−1 < r, we have
∫
[0,r−Sk −1 ]
h(t) dt = log k
k − 1 (116)
and thus by the Legendre identity, we have
(∫
[0,r−Sk −1 ]
g(t) dt
)2
= log k
k−1
∫
[0,r−Sk −1 ]
g(t)2
h(t) dt − 1
2
∫
[0,r−Sk −1 ]
∫
[0,r−Sk −1 ]
(g(s)h(t) − g(t)h(s))2
h(s)h(t) dsdt
for Sk−1 < r; but the claim also holds when r ≤ Sk−1 since all integrals vanish in that case.
On the other hand, we have
E
∫
[0,r−Sk −1 ]
g(t)2
h(t) dt = m2E(r − Sk−1 + (k − 1)Xk
) 1Xk ≤r−Sk−1
= m2E(r − Sk + kXk) 1Sk≤r
= m2Er1Sk≤r
= m2rP(Sk ≤ r)
where we have used symmetry to get the third equality. We conclude that
E
(∫
[0,r−Sk −1 ]
g(t) dt
)2
= log k
k − 1 m2rP(Sk ≤ r) − 1
2E
∫
[0,r−Sk −1 ]
∫
[0,r−Sk −1 ]
(g(s)h(t) − g(t)h(s))2
h(s)h(t) dsdt.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 51 of 83 http://www.resmathsci.com/content/1/1/12
Combining this with (114), we conclude that
rP(Sk ≤ r) ≤ k
2m2
E
∫
[0,r−Sk −1 ]
∫
[0,r−Sk −1 ]
(g(s)h(t) − g(t)h(s))2
h(s)h(t) dsdt
where
:= k
k − 1 log k − M[T]
k.
Splitting into regions where s, t are less than T or greater than T, and noting that g(s)
vanishes for s > T, we conclude that
rP(Sk ≤ r) ≤ Y1(r) + Y2(r)
where
Y1(r) := k
m2
E
∫
[0,T ]
∫
[T ,r−Sk−1 ]
g(t)2
h(t) h(s) dsdt
and
Y2(r) := k
2m2
E
∫
[0,min(T ,r−Sk−1 )]
∫
[0,min(T ,r−Sk−1 )]
(g(s)h(t) − g(t)h(s))2
h(s)h(t) dsdt.
We average this from r = 1 to r = 1 + τ , to conclude that
(1
τ
∫ 1+τ
1
rP(Sk ≤ r) dr
)
≤1
τ
∫ 1+τ
1
Y1(r) dr + 1
τ
∫ 1+τ
1
Y2(r) dr.
Thus, to prove (107), it suffices (by (106)) to establish the bounds
1 τ
∫ 1+τ
1
rP(Sk ≤ r) dr ≥ (1 + τ/2)
(
1 − kσ2
(1 + τ − kμ)2
)
, (117)
k
k − 1 Y1(r) ≤ Z + Z3 (118)
for all 1 < r ≤ 1 + τ , and
1 τ
∫ 1+τ
1
Y2(r) dr ≤ k
k − 1 (WX + VU). (119)
We begin with (117). Since
1 τ
∫ 1+τ
1
r dr = 1 + τ
2,
it suffices to show that
P(Sk > 1 + τ ) ≤ kσ 2
(1 + τ − kμ)2 .
But from (102) and (103), we see that each Xi has mean μ and variance σ 2, so Sk has
mean kμ and variance kσ 2. The claim now follows from Chebyshev’s inequality and (104).


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 52 of 83 http://www.resmathsci.com/content/1/1/12
Now we show (118). The quantity Y1(r) is vanishing unless r − Sk−1 ≥ T. Using the
crude bound h(s) ≤ 1
(k−1)s from (115), we see that
∫
[T ,r−Sk−1 ]
h(s) ds ≤ 1
k − 1 log+
r − Sk−1 T
where log+(x) := max(log x, 0). We conclude that
Y1(r) ≤ k
k−1
1
m2
E
∫
[0,T ]
g(t)2
h(t) dt log+
r − Sk−1
T.
We can rewrite this as
Y1(r) ≤ k
k − 1 E 1Sk≤r
h(Xk) log+
r − Sk−1
T.
By (115), we have
1Sk ≤r
h(Xk) = (r − Sk + kXk) 1Sk≤r.
Also, from the elementary bound log+(x + y) ≤ log+ x + log(1 + y) for any x, y ≥ 0, we
see that
log+
r − Sk−1
T ≤ log+
r − Sk
T + log
(
1 + Xk
T
) .
We conclude that
Y1(r) ≤ k
k − 1 E (r − Sk + kXk)
(
log+
r − Sk
T + log
(
1 + Xk
T
))
1Sk ≤r
≤k
k−1
(
E(r − Sk + kXk) log+
r − Sk
T + max(r − Sk, 0) Xk
T + kXk log
(
1 + Xk
T
))
using the elementary bound log(1 + y) ≤ y. Symmetrizing in the X1, . . . , Xk, we conclude
that
Y1(r) ≤ k
k − 1 (Z1(r) + Z2(r) + Z3) (120)
where
Z1(r) := Er log+
r − Sk T
Z2(r) := E(r − Sk)1Sk≤r
Sk kT
and Z3 was defined in (109).
For the minor error term Z2, we use the crude bound (r − Sk)1Sk≤rSk ≤ r2
4 , so
Z2(r) ≤ r2
4kT . (121)
For Z1, we upper bound log+ x by a quadratic expression in x. More precisely, we
observe the inequality
log+ x ≤
(x − 2a log a − a)2
4a2 log a


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 53 of 83 http://www.resmathsci.com/content/1/1/12
for any a > 1 and x ∈ R, since the left-hand side is concave in x for x ≥ 1, while the
right-hand side is convex in x, non-negative, and tangent to the left-hand side at x = a.
We conclude that
log+
r − Sk
T≤
(r − Sk − 2aT log a − aT)2
4a2T2 log a .
On the other hand, from (102) and (103), we see that each Xi has mean μ and variance
σ 2, so Sk has mean kμ and variance kσ 2. We conclude that
Z1(r) ≤ r
(r − kμ − 2aT log a − aT)2 + kσ 2
4a2T2 log a
for any a > 1.
From (105) and the assumption r > 1, we may choose a := r−kμ
T here, leading to the
simplified formula
Z1(r) ≤ r
(
log r − kμ
T + kσ2
4(r − kμ)2 log r−kμ
T
)
. (122)
From (120), (121), (122), and (108) we conclude (118).
Finally, we prove (119). Here, we finally use the specific form (100) of the function g.
Indeed, from (100) and (115), we observe the identity
g(t) − h(t) = (r − Sk−1 − c)g(t)h(t)
for t ∈[ 0, min(r − Sk−1, T)]. Thus,
Y2(r) = k
2m2
E
∫
[0,min(r−Sk−1 ,T )]
∫
[0,min(r−Sk−1 ,T )]
((g − h)(s)h(t) − (g − h)(t)h(s))2
h(s)h(t) dsdt
=k
2m2
E(r − Sk−1 − c)2
∫
[0,min(r−Sk−1 ,T )]
∫
[0,min(r−Sk−1 ,T )]
(g(s) − g(t))2 h(s)h(t) dsdt.
Using the crude bound (g(s) − g(t))2 ≤ g(s)2 + g(t)2 and using symmetry, we conclude
Y2(r) ≤ k
m2
E (r − Sk−1 − c)2
∫
[0,min(r−Sk−1 ,T )]
∫
[0,min(r−Sk−1 ,T )]
g(s)2h(s)h(t) dsdt.
From (116) and (115), we conclude that
Y2(r) ≤ k
k − 1 Z4(r)
where
Z4(r) := log k
m2
E
((r − Sk−1 − c)2
∫
[0,min(r−Sk−1 ,T )]
g(s)2
r − Sk−1 + (k − 1)s ds
)
.
To prove (119), it thus suffices (after making the change of variables r = 1 + uτ ) to show
that
∫1
0
Z4(1 + uτ ) du ≤ WX + VU. (123)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 54 of 83 http://www.resmathsci.com/content/1/1/12
We will exploit the averaging in u to deal with the singular nature of the factor
1
r−Sk−1+(k−1)s . By Fubini’s theorem, the left-hand side of (123) may be written as
log k
m2
E
∫1
0
Q(u) du
where Q(u) is the random variable
Q(u) := (1 + uτ − Sk−1 − c)2
∫
[0,min(1+uτ −Sk−1,T)]
g(s)2
1 + uτ − Sk−1 + (k − 1)s ds.
Note that Q(u) vanishes unless 1 + uτ − Sk−1 > 0. Consider first the contribution of
those Q(u) for which
0 < 1 + uτ − Sk−1 ≤ 2c.
In this regime, we may bound
(1 + uτ − Sk−1 − c)2 ≤ c2,
so this contribution to (123) may be bounded by
log k
m2
c2E
∫
[0,T ]
g(s)2
(∫ 1
0
11+uτ −Sk−1≥s
1 + uτ − Sk−1 + (k − 1)s du
)
ds.
Observe on making the change of variables v := 1 + uτ − Sk−1 + (k − 1)s that ∫1
0
11+uτ −Sk−1≥s
1 + uτ − Sk−1 + (k − 1)s du = 1
τ
∫
[max(ks,1−Sk−1+(k−1)s),1−Sk−1+τ +(k−1)s]
dv v
≤1
τ log ks + τ
ks
and so this contribution to (123) is bounded by WX, where W , X are defined in (110) and
(111).
Now we consider the contribution to (123) whene
1 + uτ − Sk−1 > 2c.
In this regime, we bound
1
1 + uτ − Sk−1 + (k − 1)s ≤ 1
2c + (k − 1)t ,
and so this portion of ∫ 1
0 Z4[ 1 + uτ ] du may be bounded by
∫1
0
log k
c E (1 + uτ − Sk−1 − c)2 V du = VU
where V , U are defined in (112) and (113). The proof of the theorem is now complete.
We can now perform an asymptotic analysis in the limit k → ∞ to establish
Theorem 23(xi) and Theorem 25(vi). For k sufficiently large, we select the parameters
c := 1
log k + α
log2 k
T := β
log k
τ := γ
log k


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 55 of 83 http://www.resmathsci.com/content/1/1/12
for some real parameters α ∈ R and β, γ > 0 independent of k to be optimized in later.
From (100) and (101), we have
m2 = 1
k−1
(1
c− 1
c + (k − 1)T
)
= log k
k
(
1− α
log k + o
(1
log k
))
where we use o ( f (k)) to denote a function g(k) of k with g(k)/f (k) → 0 as k → ∞. On
the other hand, we have from (100) and (102) that
m2(c + (k − 1)μ) =
∫T
0
(c + (k − 1)t) g(t)2 dt
=1
k − 1 log c + (k − 1)T
c = log k
k
(
1 + log β
log k + o
(1
log k
))
and thus
kμ = k
k−1
(
1 + log β + α
log k + o
(1
log k
))
− kc
k−1 = 1 + log β + α
log k + o
(1
log k
) −
(1
log k + o
(1
log k
))
= 1 + log β + α − 1
log k + o
(1
log k
) .
Similarly, from (100), (102), and (103), we have
m2
(c2 + 2c(k − 1)μ + (k − 1)2 (μ2 + σ 2)) =
∫T
0
(c + (k − 1)t)2 g(t)2 dt
=T
and thus
kσ2 = k
(k − 1)2
(T
m2
− c2 − 2c(k − 1)μ
)
− kμ2
=β
log2 k + o
(1
log2 k
) .
We conclude that the hypotheses (104), (105), and (106) will be obeyed for sufficiently
large k if we have
log β + α + γ < 1
log β + α + β < 1
β < (1 + γ − α − log β)2 .
These conditions can be simultaneously obeyed, for instance by setting β = γ = 1 and α = −1.
Now we crudely estimate the quantities Z, Z3, W , X, V , U in (108)-(113). For 1 ≤ r ≤
1 + τ , we have r − kμ ∼ 1/ log k, and so
r − kμ
T 1; kσ 2
(r − kμ)2 1; r2
4kT = o(1)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 56 of 83 http://www.resmathsci.com/content/1/1/12
and so by (108) Z = O(1). Using the crude bound log (1 + t
T
) = O(1) for 0 ≤ t ≤ T, we
see from (109) and (102) that Z3 = O(kμ) = O(1). It is clear that X = O(1), and using the
crude bound 1
2c+(k−1)t ≤ 1
c we see from (112) and (101) that V = O(1). For 0 ≤ u ≤ 1 we
have 1 + uτ − (k − 1)μ − c = O(1/ log k), so from (113) we have U = O(1). Finally, from
(110) and the change of variables t = s
k log k , we have
W = log k
km2
∫ kT log k
0
log
(
1+ γ
s
) ds
(
1+ α
log k + k−1
ks
)2
=O
(∫ ∞
0
log
(
1+ γ
s
) ds
(1 + o(1))(1 + s)2
)
= O(1).
Finally, we have
1 − kσ2
(1 + τ − kμ)2 ∼ 1.
Putting all these together, we see from (107) that
Mk ≥ M[T]
k≥ k
k − 1 log k − O(1)
giving Theorem 23(xi). Furthermore, if we set
:= 7
600 − C
log k
and
δ :=
(1
4+ 7
600
)β
log k ,
then we will have 600 + 180δ < 7 for C large enough, and Theorem 25(vi) also follows
(as one can verify from inspection that all implied constants here are effective).
Finally, Theorem 23(viii), (ix), and (x) follow by setting
c := θ
log k
T := β
log k
τ = 1 − kμ
with θ , β given by Table 2, with (107) then giving the bound M[T]
k > M with M as given by
the table, after verifying of course that the conditions (104), (105), and (106) are obeyed.
Similarly, Theorem 25 (ii), (iii), (iv), and (v) follows with θ, β given by the same table, with
chosen so that
M= m
1
4+
with m = 2, 3, 4, 5 for (ii), (iii), (iv), (v), respectively, and δ chosen by the formula
δ := T
(1
4+
) .


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 57 of 83 http://www.resmathsci.com/content/1/1/12
Table 2 Parameter choices for Theorems 23 and 25
k θ βM
5,511 0.965 0.973 6.000048609 35,410 0.99479 0.85213 7.829849259 41,588 0.97878 0.94319 8.000001401 309,661 0.98627 0.92091 10.00000032 1,649,821 1.00422 0.80148 11.65752556 75,845,707 1.00712 0.77003 15.48125090 3,473,955,908 1.0079318 0.7490925 19.30374872
The case of small and medium dimension
In this section, we establish lower bounds for Mk (and related quantities, such as Mk,ε)
both for small values of k (in particular, k = 3 and k = 4) and medium values of k (in par
ticular, k = 50 and k = 54). Specifically, we will establish Theorem 23(vii), Theorem 27,
and Theorem 29.
Bounding Mk for medium k
We begin with the problem of lower bounding Mk. We first formalize an observationf of
Maynard [5] that one may restrict without loss of generality to symmetric functions:
Lemma 41. For any k ≥ 2, one has
Mk := sup kJ1(F)
I (F )
where F ranges over symmetric square-integrable functions on Rk that are not identically
zero.
Proof. Firstly, observe that if one replaces a square-integrable function F : [0, +∞)k →
R with its absolute value |F|, then I(|F|) = I(F) and Ji(|F|) ≥ Ji(F). Thus, one may restrict
the supremum in (33) to non-negative functions without loss of generality. We may thus
find a sequence Fn of square-integrable non-negative functions on Rk, normalized so that
I(Fn) = 1, and such that ∑k
i=1 Ji(Fn) → Mk as n → ∞. Now let
Fn(t1, . . . , tk) := 1
k!
∑
σ ∈Sk
Fn(tσ (1), . . . , tσ (k))
be the symmetrisation of Fn. Since the Fn are non-negative with I(Fn) = 1, we see that
I(Fn) ≥ I
(1
k! Fn
)
=1
(k! )2
and so I(Fn) is bounded away from zero. Also, from (33), we know that the quadratic form
Q(F) := MkI(F) −
k ∑
i=1
Ji (F )


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 58 of 83 http://www.resmathsci.com/content/1/1/12
is positive semi-definite and is also invariant with respect to symmetries, and so from the
triangle inequality for inner product spaces, we conclude that
Q (Fn
) ≤ Q (Fn) .
By construction, Q(Fn) goes to zero as n → ∞, and thus Q(Fn) also goes to zero. We
conclude that
kJ1
(Fn
)
I (Fn
)=
∑k
i=1 Ji
(Fn
)
I (Fn
) → Mk
as n → ∞, and so
Mk ≥ sup kJ1(F)
I(F) .
The reverse inequality is immediate from (33), and the claim follows.
To establish a lower bound of the form Mk > C for some C > 0, one thus seeks to
locate a symmetric function F : [0, +∞)k → R supported on Rk such that
kJ1(F) > CI(F). (124)
To do this numerically, we follow [5] (see also [2] for some related ideas) and can restrict
attention to functions F that are linear combinations
F=
n ∑
i=1
aibi
of some explicit finite set b1, . . . , bn : [0, +∞)k → R supported on Rk and some real
scalars a1, . . . , an that we may optimize in. The condition (124) then may be rewritten as
aT M2a − CaT M1a > 0 (125)
where a is the vector
a :=
⎛
⎜⎜⎝
a1
...
an
⎞
⎟⎟⎠
and M1, M2 are the real symmetric and positive semi-definite n × n matrices
M1 =
(∫
Rk
bi(t1, . . . , tk)bj(t1, . . . , tk) dt1 . . . dtk
)
1≤i,j≤n
(126)
M2 =
( k
∫
Rk+1
bi(t1, . . . , tk)bj(t1, . . . , tk−1, t′
k) dt1 . . . dtkdt′
k
)
1≤i,j≤n
. (127)
If the b1, . . . , bn are linearly independent in L2(Rk), then M1 is strictly positive definite,
and (as observed in [5, Lemma 8.3]), one can find a obeying (125) if and only if the largest
eigenvalue of M2M−1
1 exceeds C. This is a criterion that can be numerically verified for
medium-sized values of n, if the b1, . . . , bn are chosen so that the matrix coefficients of
M1, M2 are explicitly computable.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 59 of 83 http://www.resmathsci.com/content/1/1/12
In order to facilitate computations, it is natural to work with bases b1, . . . , bn of
symmetric polynomials. We have the following basic integration identity:
Lemma 42 (Beta function identity). For any non-negative a, a1, . . . , ak, we have
∫
Rk
(1 − t1 − · · · − tk)ata1
1 . . . tak
k dt1 . . . dtk = (a + 1) (a1 + 1) . . . (ak + 1)
(a1 + · · · + ak + k + a + 1)
where (s) := ∫ ∞
0 ts−1e−t dt is the Gamma function. In particular, if a1, . . . , ak are natural
numbers, then
∫
Rk
(1 − t1 − · · · − tk)ata1
1 . . . tak
k dt1 . . . dtk = a! a1! . . . ak!
(a1 + · · · + ak + k + a)! .
Proof. Since
∫
Rk
(1 − t1 − · · · − tk)ata1
1 . . . tak
k dt1 . . . dtk = a
∫
Rk+1
ta1
1 . . . tak
k ta−1
k+1 dt1 . . . dtk+1,
we see that to establish the lemma, it suffices to do so in the case a = 0.
If we write
X :=
∫
t1+···+tk =1
ta1
1 . . . tak
k dt1 . . . dtk−1,
then by homogeneity we have
ra1+···+ak+k−1X =
∫
t1+···+tk =r
ta1
1 . . . tak
k dt1 . . . dtk−1
for any r > 0, and hence on integrating r from 0 to 1, we conclude that
X
a1 + · · · + ak + k =
∫
Rk
ta1
1 . . . tak
k dt1 . . . dtk.
On the other hand, if we multiply by e−r and integrate r from 0 to ∞, we obtain instead
∫∞
0
ra1+···+ak+k−1Xe−r dr =
∫
[0,+∞)k
ta1
1 . . . tak
k e−t1−···−tk dt1 . . . dtk.
Using the definition of the Gamma function, this becomes
(a1 + · · · + ak + k)X = (a1 + 1) . . . (ak + 1)
and the claim follows.
Define a signature to be a non-increasing sequence α = (α1, α2, . . . , αk) of natural num
bers; for brevity, we omit zeroes; thus, for instance if k = 6, then (2, 2, 1, 1, 0, 0) will be


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 60 of 83 http://www.resmathsci.com/content/1/1/12
abbreviated as (2, 2, 1, 1). The number of non-zero elements of α will be called the length
of the signature α, and as usual the degree of α with be α1 + · · · + αk. For each signature
α, we then define the symmetric polynomials Pα = P(αk) by the formula
Pα(t1, . . . , tk) = ∑ a:s(a)=α
ta1
1 . . . tak
k
where the summation is over all tuples a = (a1, . . . , ak) whose non-increasing rearrange
ment s(a) is equal to α. Thus, for instance
P(1)(t1, . . . , tk) = t1 + · · · + tk
P(2)(t1, . . . , tk) = t12 + · · · + t2
k
P(1,1)(t1, . . . , tk) = ∑
1≤i<j≤k
titj
P(2,1)(t1, . . . , tk) = ∑
1≤i<j≤k
ti2tj + titj2
and so forth. Clearly, the Pα form a linear basis for the symmetric polynomials of t1, . . . , tk.
Observe that if α = (α′, 1) is a signature containing 1, then one can express Pα as P(1)Pα′
minus a linear combination of polynomials Pβ with the length of β less than that of α.
This implies that the functions P(a1)Pα, with a ≥ 0 and α avoiding 1, are also a basis for
the symmetric polynomials. Equivalently, the functions (1 − P(1))aPα with a ≥ 0 and α
avoiding 1 form a basis.
After extensive experimentation, we have discovered that a good basis b1, . . . , bn to use
for the above problem comes by setting the bi to be all the symmetric polynomials of the
form (1 − P(1))aPα, where a ≥ 0 and α consists entirely of even numbers, whose total
degree a + α1 + · · · + αk is less than or equal to some chosen threshold d. For such
functions, the coefficients of M1, M2 can be computed exactly using Lemma 42.
More explicitly, first we quickly compute a look-up table for the structure constants
cα,β,γ ∈ Z derived from simple products of the form
PαPβ = ∑ γ
cα,β,γ Pγ
where deg(α) + deg(β) ≤ d. Using this look-up table, we rewrite the integrands of the
entries of the matrices in (126) and (127) as integer linear combinations of nearly ‘pure’
monomials of the form (1 − P(1))ata1
1 . . . tak
k . We then calculate the entries of M1 and M2,
as exact rational numbers, using Lemma 42.
We next run a generalized eigenvector routine on (real approximations to) M1 and M2
to find a vector a′ which nearly maximize the quantityC in (125). Taking a rational approx
imation a to a′, we then do the quick (and exact) arithmetic to verify that (125) holds for
some constant C > 4. This generalized eigenvector routine is time-intensive when the
sizes of M1 and M2 are large (say, bigger than 1, 500 × 1, 500) and in practice is the most
computationally intensive step of our calculation. When one does not care about an exact
arithmetic proof that C > 4, instead one can run a test for positive-definiteness for the
matrix CM1 − M2, which is usually much faster and less RAM intensive.
Using this method, we were able to demonstrate M54 > 4.00238, thus establishing
Theorem 23(vii). We took d = 23 and imposing the restriction on signatures α that they
be composed only of even numbers. It is likely that d = 22 would suffice in the absence of


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 61 of 83 http://www.resmathsci.com/content/1/1/12
this restriction on signatures, but we found that the gain in M54 from lifting this restric
tion is typically only in the region of 0.005, whereas the execution time is increased by a
large factor. We do not have a good understanding of why this particular restriction on
signatures is so inexpensive in terms of the trade-off between the accuracy of M-values
and computational complexity. The total run-time for this computation was under 1 h.
We now describe a second choice for the basis elements b1, . . . , bn, which uses the
Krylov subspace method; it gives faster and more efficient numerical results than the pre
vious basis, but does not seem to extend as well to more complicated variational problems
such as Mk,ε. We introduce the linear operator L : L2(Rk) → L2(Rk) defined by
Lf (t1, . . . , tk) :=
k ∑
i=1
∫ 1−t1−···−ti−1−ti+1−···−tk
0
f (t1, . . . , ti−1, ti′, ti+1, . . . , tk) dti′.
This is a self-adjoint and positive semi-definite operator on L2(Rk). For symmetric
b1, . . . , bn ∈ L2(Rk), one can then write
M1 = (〈bi, bj〉)
1≤i,j≤n
M2 = (〈Lbi, bj〉)
1≤i,j≤n .
If we then choose
bi := Li−11
where 1 is the unit constant function on Rk, then the matrices M1, M2 take the Hankel
form
M1 = (〈Li+j−21, 1〉)
1≤i,j≤n
M2 = (〈Li+j−11, 1〉)
1≤i,j≤n ,
and so can be computed entirely in terms of the 2n numbers 〈Li1, 1〉 for i = 0, . . . , 2n − 1.
The operator L maps symmetric polynomials to symmetric polynomials; for instance,
one has
L1 = k − (k − 1)P(1)
LP(1) = k
2 − k−1
2 P(2) − (k − 2)P(1,1)
and so forth. From this and Lemma 42, the quantities 〈Li1, 1〉 are explicitly computable
rational numbers; for instance, one can calculate
〈1, 1〉 = 1
k!
〈L1, 1〉 = 2k
(k + 1)!
〈L21, 1〉 = k(5k + 1)
(k + 2)!
〈L31, 1〉 = 2k2(7k + 5)
(k + 3)!
and so forth.
With Maple, we were able to compute 〈Li1, 1〉 for i ≤ 50 and k ≤ 100, leading to lower
bounds on Mk for these values of k, a selection of which is given in Table 3.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 62 of 83 http://www.resmathsci.com/content/1/1/12
Table 3 Selected lower bounds on Mk obtained from the Krylov subspace method, with
k
k−1 log k upper bound displayed for comparison
k Lower bound on Mk k
k−1 log k
2 1.38593 1.38629 3 1.64644 1.64791 4 1.84540 1.84839 5 2.00714 2.01179 10 2.54547 2.55842 20 3.12756 3.15340 30 3.48313 3.51848 40 3.73919 3.78346 50 3.93586 3.99186 53 3.98621 4.04664 54 4.00223 4.06424 60 4.09101 4.16374 100 4.46424 4.65168
Bounding Mk,ε for medium k
When bounding Mk,ε, we have not been able to implement the Krylov method because
the analogue of Li1 in this context is piecewise polynomial instead of polynomial, and we
were only able to compute it explicitly for very small values of i, such as i = 1, 2, 3, which
are insufficient for good numerics. Thus, we rely on the previously discussed approach,
in which symmetric polynomials are used for the basis functions. Instead of computing
integrals over the region Rk, we pass to the regions (1±ε)Rk. In order to apply Lemma 42
over these regions, this necessitates working with a slightly different basis of polynomials.
We chose to work with those polynomials of the form (1 + ε − P(1))aPα, where α is a
signature with no 1’s. Over the region (1 + ε)Rk, a single change of variables converts
the needed integrals into those of the form in Lemma 42, and we can then compute the
entries of M1.
On the other hand, over the region (1−ε)Rk, we instead want to work with polynomials
of the form (1 − ε − P(1))aPα. Since (1 + ε − P(1))a = (2ε + (1 − ε − P(1)))a, an expansion
using the binomial theorem allows us to convert from our given basis to polynomials of
the needed form.
With these modifications, and calculating as in the previous section, we find that
M50,1/25 > 4.00124 if d = 25 and M50,1/25 > 4.0043 if d = 27, thus establishing
Theorem 27(i). As before, we found it optimal to restrict signatures to contain only
even entries, which greatly reduced execution time while only reducing M by a few
thousandths.
One surprising additional computational difficulty introduced by allowing ε > 0 is that
the ‘complexity’ of ε as a rational number affects the run-time of the calculations. We
found that choosing ε = 1/m (where m ∈ Z has only small prime factors) reduces this
effect.
A similar argument gives M51,1/50 > 4.00156, thus establishing Theorem 27(xiii). In this
case, our polynomials were of maximum degree d = 22.
Code and data for these calculations may be found at http://www.dropbox.com/sh/
0xb4xrsx4qmua7u/WOhuo2Gx7f/Polymath8b.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 63 of 83 http://www.resmathsci.com/content/1/1/12
Bounding M4,ε
We now prove Theorem 27(xii’), which can be established by a direct numerical calcula
tion. We introduce the explicit function F : [0, +∞)4 → R defined by
F(t1, t2, t3, t4) := (1 − α(t1 + t2 + t3 + t4))1t1+t2+t3+t4≤1+ε
with ε := 0.168 and α := 0.784. As F is symmetric in t1, t2, t3, t4, we have Ji,1−ε(F) =
J1,1−ε(F), so to show Theorem 27(xii’) it will suffice to show that
4J1,1−ε (F )
I(F) > 2.00558. (128)
By making the change of variables s = t1 + t2 + t3 + t4, we see that
I(F) =
∫
t1 +t2 +t3 +t4 ≤1+ε
(1 − α(t1 + t2 + t3 + t4))2 dt1dt2dt3dt4
=
∫ 1+ε
0
(1 − αs)2 s3
3! ds
= α2 (1 + ε)6
36 − α (1 + ε)5
15 + (1 + ε)4
24 = 0.00728001347 . . .
and similarly by making the change of variables u = t1 + t2 + t3
J1,1−ε(F) =
∫
t1 +t2 +t3 ≤1−ε
(∫ 1+ε−t1−t2−t3
0
(1 − α(t1 + t2 + t3 + t4)) dt4
)2
dt1dt2dt3
=
∫ 1−ε
0
(∫ 1+ε−u
0
(1 − α(u + t4)) dt4
)2 u2
2! du
=
∫ 1−ε
0
(1 + ε − u)2
(
1 − α1 + ε + u
2
)2 u2
2 du
= 0.003650160667 . . .
and so (128) follows.
Remark 43. If we use the truncated function
F ̃ (t1, t2, t3, t4) := F(t1, t2, t3, t4)1t1,t2,t3,t4≤1
in place of F and set ε to 0.18 instead of 0.168, one can compute that
4J1,1−ε(F ̃ )
I(F ̃ ) > 2.00235.
Thus, it is possible to establish Theorem 27(xii’) using a cutoff function F′ that is also
supported in the unit cube [0, 1]4. This allows for a slight simplification to the proof of
DHL[4; 2] assuming GEH, as one can add the additional hypothesis S(Fi0 ) + S(Gi0 ) < 1
to Theorem 20(ii) in that case.
Remark 44. By optimizing in ε and taking F to be a symmetric polynomial of degree
higher than 1, one can get slightly better lower bounds for M4,ε; for instance, setting
ε = 5/21 and choosing F to be a cubic polynomial, we were able to obtain the bound
M4,ε ≥ 2.05411. On the other hand, the best lower bound for M3,ε that we were able
to obtain was 1.91726 (taking ε = 56/113 and optimizing over cubic polynomials).


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 64 of 83 http://www.resmathsci.com/content/1/1/12
Again, see www.dropbox.com/sh/0xb4xrsx4qmua7u/WOhuo2Gx7f/Polymath8b for the
relevant code and data.
Three-dimensional cutoffs
In this section, we establish Theorem 29. We relabel the variables (t1, t2, t3) as (x, y, z);
thus, our task is to locate a piecewise polynomial function F : [0, +∞)3 → R supported
on the simplex
R :=
{
(x, y, z) ∈[0, +∞)3 : x + y + z ≤ 3
2
}
and symmetric in the x, y, z variables, obeying the vanishing marginal condition ∫∞
0
F(x, y, z) dz = 0 (129)
whenever x, y ≥ 0 with x + y > 1 + ε, and such that
J(F) > 2I(F) (130)
where
J(F) := 3
∫
x+y≤1−ε
(∫ ∞
0
F(x, y, z) dz
)2
dxdy (131)
and
I(F) :=
∫
R
F(x, y, z)2 dxdydz (132)
and
ε := 1/4.
Our strategy will be as follows. We will decompose the simplex R (up to null sets) into
a carefully selected set of disjoint open polyhedra P1, . . . , Pm (in fact m will be 60), and
on each Pi we will take F(x, y, z) to be a low-degree polynomial Fi(x, y, z) (indeed, the
degree will never exceed 3). The left-hand and right-hand sides of (130) become quadratic
functions in the coefficients of the Fi. Meanwhile, the requirement of symmetry, as well as
the marginal requirement (129), imposes some linear constraints on these coefficients. In
principle, this creates a finite-dimensional quadratic program, which one can try to solve
numerically. However, to make this strategy practical, one needs to keep the number of
linear constraints imposed on the coefficients to be fairly small, as compared with the
total number of coefficients. To achieve this, the following properties on the polynomials
Pi are desirable:
• (Symmetry) If Pi is a polytope in the partition, then every reflection of Pi formed by permuting the x, y, z coordinates should also lie in the partition. • (Graph structure) Each polytope Pi should be of the form
{(x, y, z) : z ∈ Qi; ai(x, y) < z < bi(x, y)} , (133)
where ai(x, y), bi(x, y) are linear forms and Qi is a polygon.
• (Epsilon splitting) Each Qi is contained in one of the regions {(x, y) : x + y < 1 − ε},
{(x, y) : 1 − ε < x + y < 1 + ε}, or {(x, y) : 1 + ε < x + y < 3/2}.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 65 of 83 http://www.resmathsci.com/content/1/1/12
Observe that the vanishing marginal condition (129) now takes the form
∑
i:(x,y)∈Qi
∫ bi(x,y)
ai(x,y)
Fi(x, y, z) dz = 0 (134)
for every x, y > 0 with x + y > 1 + ε. If the set {i : (x, y) ∈ Qi} is fixed, then the left-hand
side of (134) is a polynomial in x, y whose coefficients depend linearly on the coefficients
on the Fi, and thus (134) imposes a set of linear conditions on these coefficients for each
possible set {i : (x, y) ∈ Qi} with x + y > 1 + ε.
Now we describe the partition we will use. This partition can in fact be used for all ε in
the interval [1/4, 1/3], but the endpoint ε = 1/4 has some simplifications which allowed
for reasonably good numerical results. To obtain the symmetry property, it is natural to
split R (modulo null sets) into six polyhedra Rxyz, Rxzy, Ryxz, Ryzx, Rzxy, Rzyx, where
Rxyz := {(x, y, z) ∈ R : x + y < y + z < z + x}
= {(x, y, z) : 0 < y < x < z; x + y + z ≤ 3/2}
and the other polyhedra are obtained by permuting the indices x, y, z, thus for instance
Ryxz := {(x, y, z) ∈ R : y + x < x + z < z + y}
= {(x, y, z) : 0 < x < y < z; x + y + z ≤ 3/2} .
To obtain the epsilon splitting property, we decompose Rxyz (modulo null sets) into
eight sub-polytopes
Axyz = {(x, y, z) ∈ R : x + y < y + z < z + x < 1 − ε} ,
Bxyz = {(x, y, z) ∈ R : x + y < y + z < 1 − ε < z + x < 1 + ε} ,
Cxyz = {(x, y, z) ∈ R : x + y < 1 − ε < y + z < z + x < 1 + ε} ,
Dxyz = {(x, y, z) ∈ R : 1 − ε < x + y < y + z < z + x < 1 + ε} ,
Exyz = {(x, y, z) ∈ R : x + y < y + z < 1 − ε < 1 + ε < z + x} ,
Fxyz = {(x, y, z) ∈ R : x + y < 1 − ε < y + z < 1 + ε < z + x} ,
Gxyz = {(x, y, z) ∈ R : x + y < 1 − ε < 1 + ε < y + z < z + x} ,
Hxyz = {(x, y, z) ∈ R : 1 − ε < x + y < y + z < 1 + ε < z + x} ;
the other five polytopes Rxzy, Ryxz, Ryzx, Rzxy, Rzyx are decomposed similarly, leading to a
partition of R into 6 × 8 = 48 polytopes. This is almost the partition we will use; however,
there is a technical difficulty arising from the fact that some of the permutations of Fxyz
do not obey the graph structure property. So we will split Fxyz further into the three pieces
Sxyz = {(x, y, z) ∈ Fxyz : z < 1/2 + ε} ,
Txyz = {(x, y, z) ∈ Fxyz : z > 1/2 + ε; x > 1/2 − ε} ,
Uxyz = {(x, y, z) ∈ Fxyz : x < 1/2 − ε} .
Thus, Rxyz is now partitioned into ten polytopes Axyz, Bxyz, Cxyz, Dxyz, Exyz, Sxyz, Txyz,
Uxyz, Gxyz, Hxyz, and similarly for permutations of Rxyz, leading to a decomposition of R
into 6 × 10 = 60 polytopes.
A symmetric piecewise polynomial function F supported on R can now be described
(almost everywhere) by specifying a polynomial function F P: P → R for the ten


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 66 of 83 http://www.resmathsci.com/content/1/1/12
polytopes P = Axyz, Bxyz, Cxyz, Dxyz, Exyz, Sxyz, Txyz, Uxyz, Gxyz, Hxyz, and then extending by
symmetry, thus for instance
F Ayzx (x, y, z) = F Axyz (z, x, y).
As discussed earlier, the expressions I(F), J(F) can now be written as quadratic forms
in the coefficients of the F P, and the vanishing marginal condition (129) imposes some
linear constraints on these coefficients.
Observe that the polytope Dxyz and all of its permutations make no contribution to
either the functional J(F) or to the marginal condition (129), and give a non-negative
contribution to I(F). Thus, without loss of generality we may assume that
F Dxyz = 0.
However, the other nine polytopes Axyz, Bxyz, Cxyz, Exyz, Sxyz, Txyz, Uxyz, Gxyz, Hxyz have
at least one permutation which gives a non-trivial contribution to either J(F) or to (129),
and cannot be easily eliminated.
Now we compute I(F). By symmetry, we have
I(F) = 3! I(F Rxyz ) = 6
∑
P
I(F P)
where P ranges over the nine polytopes Axyz, Bxyz, Cxyz, Exyz, Sxyz, Txyz, Uxyz, Gxyz, Hxyz. A
tedious but straightforward computation shows that
I(F Axyz ) =
∫ 1/2−ε/2
x=0
∫x
y=0
∫ 1−ε−x
z=x
F2
Axyz dz dy dx
I(F Bxyz ) =
(∫ 1/2+ε/2
z=1/2−ε/2
∫z
x=1−ε−z
+
∫ 1−ε
z=1/2+ε/2
∫ 1+ε−z
x=1−ε−z
) ∫ 1−ε−z
y=0
F 2Bxyz dy dx dz
I(F Cxyz ) =
(∫ 1/2−3ε/2
y=0
∫ y+2ε
x=y
+
∫ 1/2−ε
y=1/2−3ε/2
∫ 1−ε−y
x=y
) ∫ 1+ε−x
z=1−ε−y
+
∫ 1/2−ε/2
y=1/2−ε
∫ 1−ε−y
x=y
∫ 3/2−x−y
z=1−ε−y
F2
Cxyz dz dx dy
I(F Exyz ) =
∫ 1−ε
z=1/2+ε/2
∫z
x=1+ε−z
∫ 1−ε−z
y=0
F2
Exyz dy dx dz
I(F Sxyz ) =
(∫ 1/2−3ε/2
y=0
∫ 1/2+ε
z=1−ε−y
+
∫ 1/2−ε
y=1/2−3ε/2
∫ 1/2+ε
z=y+2ε
) ∫ 1−ε−y
x=1+ε−z
F Sxyz dx dz dy
I(F Txyz ) =
(∫ 1/2+2ε
z=1/2+ε
∫ 3/2−z
x=1+ε−z
+
∫ 1+ε
z=1/2+2ε
∫ 3/2−z
x=1/2−ε
) ∫ 3/2−x−z
y=0
F2
Txyz dy dz dx
I(F Uxyz ) =
∫ 1/2−ε
x=0
∫x
y=0
∫ 1+ε−y
z=1+ε−x
F Uxyz dz dy dx
I(F Gxyz ) =
∫ 1/2−ε
x=0
∫x
y=0
∫ 3/2−x−y
z=1+ε−y
F2
Gxyz dx dz dy
and
I(F Hxyz ) =
(∫ 1−ε
x=1/2+ε/2
∫ 3/2−2x
y=1−ε−x
+
∫ 3/4
x=1−ε
∫ 3/2−2x
y=0
) ∫ 3/2−x−y
z=x
+
∫ 1/2+ε/2
x=1/2
∫ 1/2−ε
y=1−ε−x
∫ 3/2−x−y
z=1+ε−x
F 2Hxyz dz dy dx.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 67 of 83 http://www.resmathsci.com/content/1/1/12
Now we consider the quantity J(F). Here we only have the symmetry of swapping x and
y, so that
J(F) = 6
∫
0<y<x;x+y<1−ε
(∫ 3/2−x−y
0
F(x, y, z) dz
)2
dxdy.
The region of integration meets the polytopes Axyz, Ayzx, Azyx, Bxyz, Bzyx, Cxyz, Exyz, Ezyx,
Sxyz, Txyz, Uxyz, and Gxyz.
Projecting these regions to the (x, y)-plane, we have the diagram:
This diagram is drawn to scale in the case when ε = 1/4; otherwise, there is a sep
aration between the J5 and J7 regions. For each of these eight regions, there are eight
corresponding integrals J1, J2, . . . , J8, and thus
J = 2 (J1 + · · · + J8) .
We have
J1 =
∫ 1/2−ε
x=0
∫x
y=0
(∫ y
z=0
F Ayzx +
∫x
z=y
F Azyx +
∫ 1−ε−x
z=x
F Axyz +
∫ 1−ε−y
z=1−ε−x
F Bxyz
+
∫ 1+ε−x
z=1−ε−y
F Cxyz +
∫ 1+ε−y
z=1+ε−x
F Uxyz +
∫ 3/2−x−y
z=1+ε−y
F Gxyz dz
)2
dy dx.
Next comes
J2 =
∫ 1/2−ε/2
x=1/2−ε
∫x
y=1/2−ε
(∫ y
z=0
F Ayzx +
∫x
z=y
F Azyx +
∫ 1−ε−x
z=x
F Axyz +
∫ 1−ε−y
z=1−ε−x
F Bxyz
+
∫ 3/2−x−y
z=1−ε−y
F Cxyz dz
)2
dy dx.
Third is the piece
J3 =
∫ 1/2−ε/2
x=1/2−ε
∫ 1/2−ε
y=0
(∫ y
z=0
F Ayzx +
∫x
z=y
F Azyx +
∫ 1−ε−x
z=x
F Axyz +
∫ 1−ε−y
z=1−ε−x
F Bxyz
+
∫ 1+ε−x
z=1−ε−y
F Cxyz +
∫ 3/2−x−y
z=1+ε−x
F Txyz dz
)2
dy dx.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 68 of 83 http://www.resmathsci.com/content/1/1/12
We now have dealt with all integrals involving Axyz, and all remaining integrals pass
through Bzyx. Continuing, we have
J4 =
∫ 1/2
x=1/2−ε/2
∫ 1−ε−x
y=1/2−ε
(∫ y
z=0
F Ayzx +
∫ 1−ε−x
z=y
F Azyx +
∫x
z=1−ε−x
F Bzyx
+
∫ 1−ε−y
z=x
F Bxyz +
∫ 3/2−x−y
z=1−ε−y
F Cxyz dz
)2
dy dx.
Another component is
J5 =
∫ 1/2
x=1/2−ε/2
∫ 1/2−ε
y=0
(∫ y
z=0
F Ayzx +
∫ 1−ε−x
z=y
F Azyx
+
∫x
z=1−ε−x
F Bzyx +
∫ 1−ε−y
z=x
F Bxyz +
∫ 1+ε−x
z=1−ε−y
F Cxyz
+
∫ 3/2−x−y
z=1+ε−x
F Txyz dz
)2
dy dx.
The most complicated piece is
J6 =
(∫ 2ε
x=1/2
∫ 1−ε−x
y=0
+
∫ 1/2+ε/2
x=2ε
∫ 1−ε−x
y=x−2ε
) (∫ y
z=0
F Ayzx +
∫ 1−ε−x
z=y
F Azyx
+
∫x
z=1−ε−x
F Bzyx +
∫ 1−ε−y
z=x
F Bxyz +
∫ 1+ε−x
z=1−ε−y
F Cxyz +
∫ 1/2+ε
z=1+ε−x
F Sxyz
+
∫ 3/2−x−y
z=1/2+ε
F Txyz dz
)2
dy dx.
Here we use
(∫ 2ε
x=1/2
∫ 1−ε−x
y=0 + ∫ 1/2+ε/2
x=2ε
∫ 1−ε−x y=x−2ε
)
f (x, y) dydx as an abbreviation for
∫ 2ε
x=1/2
∫ 1−ε−x
y=0
f (x, y) dydx +
∫ 1/2+ε/2
x=2ε
∫ 1−ε−x
y=x−2ε
f (x, y) dydx.
We have now exhausted Cxyz. The seventh piece is
J7 =
∫ 1/2+ε/2
x=2ε
∫ x−2ε
y=0
(∫ y
z=0
F Ayzx +
∫ 1−ε−x
z=y
F Azyx +
∫x
z=1−ε−x
F Bzyx
+
∫ 1+ε−x
z=x
F Bxyz +
∫ 1−ε−y
z=1+ε−x
F Exyz +
∫ 1/2+ε
1−ε−y
F Sxyz
+
∫ 3/2−x−y
1/2+ε
F Txyz dz
)2
dy dx.
Finally, we have
J8 =
∫ 1−ε
x=1/2+ε/2
∫ 1−ε−x
y=0
(∫ y
z=0
F Ayzx +
∫ 1−ε−x
z=y
F Azyx +
∫ 1+ε−x
z=1−ε−x
F Bzyx
+
∫x
z=1+ε−x
F Ezyx +
∫ 1−ε−y
z=x
F Exyz +
∫ 1/2+ε
1−ε−y
F Sxyz
+
∫ 3/2−x−y
1/2+ε
F Txyz dz
)2
dy dx.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 69 of 83 http://www.resmathsci.com/content/1/1/12
In the case ε = 1/4, the marginal conditions (129) reduce to requiring
∫ 3/2−x−y
z=0
F Gyzx dz = 0 (135)
∫y
z=0
F Gyzx +
∫ 3/2−x−y
z=y
F Gzyx dz = 0 (136)
∫ 1+ε−x
z=0
F Uyzx +
∫y
z=1+ε−x
F Gyzx +
∫ 3/2−x−y
z=y
F Gzyx dz = 0 (137)
∫ 1+ε−x
z=0
F Uyzx +
∫ 3/2−x−y
z=1+ε−x
F Gyzx dz = 0 (138)
∫ 3/2−x−y
z=0
F Tyzx dz = 0 (139)
∫ 1−ε−x
z=0
F Eyzx +
∫ 1−ε−y
z=1−ε−x
F Syzx +
∫ 3/2−x−y
z=1−ε−y
F Hyzx dz = 0. (140)
Each of these constraints is only required to hold for some portion of the parameter
space {(x, y) : 1 + ε ≤ x + y ≤ 3/2}, but as the left-hand sides are all polynomial functions
in x, y (using the signed definite integral ∫ a
b = −∫ b
a ), it is equivalent to require that all
coefficients of these polynomial functions vanish.
Now we specify F. After some numerical experimentation, we have found that the sim
plest choice of F which still achieves the desired goal comes by taking F(x, y, z) to be a
polynomial of degree 1 on each of Exyz, Sxyz, and Hxyz; degree 2 on Txyz, vanishing on
Dxyz; and degree 3 on the remaining five relevant components of Rxyz. After solving the
quadratic program, rounding, and clearing denominators, we arrive at the choice
F Axyz := −66 + 96x − 147x2 + 125x3 + 128y − 122xy + 104x2y − 275y2 + 394y3
+ 99z − 58xz + 63x2z − 98yz + 51xyz + 41y2z − 112z2 + 24xz2 + 72yz2
+ 50z3
F Bxyz := −41 + 52x − 73x2 + 25x3 + 108y − 66xy + 71x2y − 294y2 + 56xy2
+ 363y3 + 33z + 15xz + 22x2z − 40yz − 42xyz + 75y2z − 36z2 − 24xz2
+ 26yz2 + 20z3
F Cxyz := −22 + 45x − 35x2 + 63y − 99xy + 82x2y − 140y2 + 54xy2 + 179y3
F Exyz := −12 + 8x + 32y
F Sxyz := −6 + 8x + 16y
F Txyz := 18 − 30x + 12x2 + 42y − 20xy − 66y2 − 45z + 34xz + 22z2
F Uxyz := 94 − 1, 823x + 5, 760x2 − 5, 128x3 + 54y − 168x2y + 105y2 + 1, 422xz
− 2, 340x2z − 192y2z − 128z2 − 268xz2 + 64z3
F Gxyz := 5, 274 − 19, 833x + 18, 570x2 − 5, 128x3 − 18, 024y + 44, 696xy
− 20, 664x2y + 16, 158y2 − 19, 056xy2 − 4, 592y3 − 10, 704z
+ 26, 860xz − 12, 588x2z + 24, 448yz − 30, 352xyz − 10, 980y2z + 7, 240z2
− 9, 092xz2 − 8, 288yz2 − 1, 632z3
F Hxyz := 8z.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 70 of 83 http://www.resmathsci.com/content/1/1/12
One may compute that
I(F) = 62, 082, 439, 864, 241
507, 343, 011, 840
and
J(F) = 9, 933, 190, 664, 926, 733
40, 587, 440, 947, 200
with all the marginal conditions (135)-(140) obeyed, and thus
J (F )
I(F) = 2 + 286, 648, 173
4, 966, 595, 189, 139, 280
and (130) follows.
The parity problem
In this section, we argue why the ‘parity barrier’ of Selberg [7] prohibits sieve-theoretic
methods, such as the ones in this paper, from obtaining any bound on H1 that is stronger
than H1 ≤ 6, even on the assumption of strong distributional conjectures such as the
generalized Elliott-Halberstam conjecture GEH[θ] and even if one uses sieves other than
the Selberg sieve. Our discussion will be somewhat informal and heuristic in nature.
We begin by briefly recalling how the bound H1 ≤ 6 on GEH (i.e., Theorem 4(xii)) was
proven. This was deduced from the claim DHL[3; 2], or more specifically from the claim
that the set
A := {n ∈ N : at least two ofn, n + 2, n + 6 are prime} (141)
was infinite.
To do this, we (implicitly) established a lower bound ∑
n
ν(n)1A(n) > 0
for some non-negative weight ν : N → R+ supported on [x, 2x] for a sufficiently large
x. This bound was in turn established (after a lengthy sieve-theoretic analysis, and with a
carefully chosen weight ν) from upper bounds on various discrepancies. More precisely,
one required good upper bounds (on average) for the expressions
∣∣∣∣∣∣
∑
x≤n≤2x:x=a (q)
f (n + h) − 1
φ(q)
∑
x≤n≤2x:(n+h,q)=1
f (n + h)
∣∣∣∣∣∣ (142)
for all h ∈ {0, 2, 6} and various residue classes a (q) with q ≤ x1−ε and arithmetic functions
f , such as the constant function f = 1, the von Mangoldt function f = , or Dirichlet
convolutions f = α β of the type considered in Claim 12. (In the presentation of this
argument in previous sections, the shift by h was eliminated using the change of variables
n′ = n + h, but for the current discussion, it is important that we do not use this shift.)
One also required good asymptotic control on the main terms ∑
x≤n≤2x:(n+h,q)=1
f (n + h). (143)
An inspection of these arguments (which no longer exploit change of variables such as
n′ = n + h in the n variable) shows that they would be equally valid if one inserted a


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 71 of 83 http://www.resmathsci.com/content/1/1/12
further non-negative weight ω : N → R+ in the summation over n. More precisely, the
above sieve-theoretic argument would also deduce the lower bound ∑
n
ν(n)1A(n)ω(n) > 0
if one had control on the weighted discrepancies
∣∣∣∣∣∣
∑
x≤n≤2x:x=a (q)
f (n + h)ω(n) − 1
φ(q)
∑
x≤n≤2x:(n+h,q)=1
f (n + h)ω(n)
∣∣∣∣∣∣ (144)
and on the weighted main terms ∑
x≤n≤2x:(n+h,q)=1
f (n + h)ω(n) (145)
that were of the same form as in the unweighted case ω = 1.
Now suppose for instance that one was trying to prove the bound H1 ≤ 4. A natural
way to proceed here would be to replace the set A in (141) with the smaller set
A′ := {n ∈ N : n, n + 2are both prime} ∪ {n ∈ N : n + 2, n + 6are both prime} (146)
and hope to establish a bound of the form ∑
n
ν(n)1A′ (n) > 0
for a well-chosen function ν : N → R+ supported on [x, 2x], by deriving this bound from
suitable (averaged) upper bounds on the discrepancies (142) and control on the main
terms (143). If the arguments were sieve-theoretic in nature, then (as in the H1 ≤ 6 case)
one could then also deduce the lower bound ∑
n
ν(n)1A′ (n)ω(n) > 0 (147)
for any non-negative weight ω : N → R+, provided that one had the same control on the
weighted discrepancies (144) and weighted main terms (145) that one did on (142) and
(143).
We apply this observation to the weight
ω(n) := (1 − λ(n)λ(n + 2))(1 − λ(n + 2)λ(n + 6))
= 1 − λ(n)λ(n + 2) − λ(n + 2)λ(n + 6) + λ(n)λ(n + 6)
where λ(n) := (−1) (n) is the Liouville function. Observe that ω vanishes for any n ∈ A′,
and hence ∑
n
ν(n)1A′ (n)ω(n) = 0 (148)
for any ν. On the other hand, the ‘Möbius randomness law’ (see, e.g. [33]) predicts a
significant amount of cancellation for any non-trivial sum involving the Möbius function
μ or the closely related Liouville function λ. For instance, the expression ∑
x≤n≤2x:n=a (q)
λ(n + h)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 72 of 83 http://www.resmathsci.com/content/1/1/12
is expected to be very small (of sizeg O
(x
q log−A x
)
for any fixed A) for any residue class a
(q) with q ≤ x1−ε, and any h ∈ {0, 2, 6}; similarly for more complicated expressions such
as
∑
x≤n≤2x:n=a (q)
λ(n + 2)λ(n + 6)
or
∑
x≤n≤2x:n=a (q)
(n)λ(n + 2)λ(n + 6)
or more generally ∑
x≤n≤2x:n=a (q)
f (n)λ(n + 2)λ(n + 6)
where f is a Dirichlet convolution α β of the form considered in Claim 12. Similarly for
expressions such as ∑
x≤n≤2x:n=a (q)
f (n)λ(n)λ(n + 2);
note from the complete multiplicativity of λ that (α β)λ = (αλ) (βλ), so if f is of the
form in Claim 12, then f λ is also. In view of these observations (and similar observations
arising from permutations of {0, 2, 6}), we conclude (heuristically, at least) that all the
bounds that are believed to hold for (142) and (143) should also hold (up to minor changes
in the implied constants) for (144) and (145). Thus, if the bound H1 ≤ 4 could be proven
in a sieve-theoretic fashion, one should be able to conclude the bound (147), which is in
direct contradiction to (148).
Remark 45. Similar arguments work for any set of the form
AH := {n ∈ N : ∃n ≤ p1 < p2 ≤ n + H; p1, p2 both prime, p2 − p1 ≤ 4}
and any fixed H > 0, to prohibit any non-trivial lower bound on ∑
n ν(n)1AH (n) from sieve-theoretic methods. Indeed, one uses the weight
ω(n) := ∏
0≤i≤i′ ≤H ;(n+i,3)=(n+i′ ,3)=1;i′ −i≤4
(1 − λ(n + i)λ(n + i′));
we leave the details to the interested reader. This seems to block any attempt to use any
argument based only on the distribution of the prime numbers and related expressions in
arithmetic progressions to prove H1 ≤ 4.
The same arguments of course also prohibit a sieve-theoretic proof of the twin prime
conjecture H1 = 2. In this case, one can use the simpler weight ω(n) = 1 − λ(n)λ(n + 2)
to rule out such a proof, and the argument is essentially due to Selberg [7].
Of course, the parity barrier could be circumvented if one were able to introduce
stronger sieve-theoretic axioms than the ‘linear’ axioms currently available (which only
control sums of the form (142) or (143)). For instance, if one were able to obtain
non-trivial bounds for ‘bilinear’ expressions such as ∑
x≤n≤2x
f (n) (n + 2) = ∑
d
∑
m
α(d)β(m)1[x,2x](dm) (dm + 2)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 73 of 83 http://www.resmathsci.com/content/1/1/12
for functions f = α β of the form in Claim 12, then (by a modification of the proof of
Proposition 13) one would very likely obtain non-trivial bounds on
∑
x≤n≤2x
(n) (n + 2)
which would soon lead to a proof of the twin prime conjecture. Unfortunately, we do not
know of any plausible way to control such bilinear expressions. (Note however that there
are some other situations in which bilinear sieve axioms may be established, for instance
in the argument of Friedlander and Iwaniec [40] establishing an infinitude of primes of
the form a2 + b4.)
Additional remarks
The proof of Theorem 16(xii) may be modified to establish the following variant:
Proposition 46. Assume the generalized Elliott-Halberstam conjecture GEH[ θ] for all
0 < θ < 1. Let 0 < ε < 1/2 be fixed. Then, if x is a sufficiently large multiple of 6, there
exists a natural number n with εx ≤ n ≤ (1 − ε)x such that at least two of n, n − 2, x − n
are prime, and similarly if n − 2 is replaced by n + 2.
Note that if at least two of n, n − 2, x − n are prime, then either n, n + 2 are twin primes
or else at least one of x, x − 2 is expressible as the sum of two primes, and Theorem 5
easily follows.
Proof. (Sketch) We just discuss the case of n − 2, as the n + 2 case is similar. Observe
from the Chinese remainder theorem (and the hypothesis that x is divisible by 6) that one
can find a residue class b (W ) such that b, b − 2, x − b are all coprime to W (in particular,
one has b = 1 (6)). By a routine modification of the proof of Lemma 18, it suffices to find
a non-negative weight function ν : N → R+ and fixed quantities α > 0 and β1, β2, β3 ≥ 0,
such that one has the asymptotic upper bound
∑
εx≤n≤(1−ε)x n=b (W )
ν(n) ≤ S(α + o(1))B−k (1 − 2ε)x
W,
the asymptotic lower bounds
∑
εx≤n≤(1−ε)x n=b (W )
ν(n)θ (n) ≥ S(β1 − o(1))B1−k (1 − 2ε)x
φ(W )
∑
εx≤n≤(1−ε)x n=b (W )
ν(n)θ (n + 2) ≥ S(β2 − o(1))B1−k (1 − 2ε)x
φ(W )
∑
εx≤n≤(1−ε)x n=b (W )
ν(n)θ (x − n) ≥ S(β3 − o(1))B1−k (1 − 2ε)x
φ(W )
and the inequality
β1 + β2 + β3 > 2α,


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 74 of 83 http://www.resmathsci.com/content/1/1/12
where S is the singular series
S := ∏
p|x(x−2);p>w
p
p − 1.
We select ν to be of the form
ν(n) =
⎛
⎝
J ∑
j=1
cjλFj,1 (n)λFj,2 (n + 2)λFj,3 (x − n)
⎞
⎠
2
for various fixed coefficients c1, . . . , cJ ∈ R and fixed smooth compactly supported func
tions Fj,i : [0, +∞) → R with j = 1, . . . , J and i = 1, . . . , 3. It is then routineh to verify that
analogues of Theorem 19 and Theorem 20 hold for the various components of ν, with
the role of x in the right-hand side replaced by (1 − 2ε)x, and the claim then follows by a
suitable modification of Theorem 28, taking advantage of the function F constructed in
Theorem 29.
It is likely that the bounds in Theorem 4 can be improved further by refining the sieve
theoretic methods employed in this paper, with the exception of part (xii) for which the
parity problem prevents further improvement, as discussed in the ‘The parity problem’
section. We list some possible avenues to such improvements as follows:
1. In Theorem 27, the bound Mk,ε > 4 was obtained for some ε > 0 and k = 50. It is possible that k could be lowered slightly, for instance to k = 49, by further numerical computations, but we were only barely able to establish the k = 50 bound after 2 weeks of computation. However, there may be a more efficient way to solve the required variational problem (e.g. by selecting a more efficient basis than the symmetric monomial basis) that would allow one to advance in this direction; this would improve the bound H1 ≤ 246 slightly. Extrapolation of existing numerics also raises the possibility that M53 exceeds 4, in which case the bound of 270 in Theorem 4(vii) could be lowered to 264. 2. To reduce k (and thus H1) further, one could try to solve another variational problem, such as the one arising in Theorem 24 or in Theorem 28, rather than trying to lower bound Mk or Mk,ε. It is also possible to use the more complicated versions of MPZ[ , δ] established (in which the modulus q is assumed to be densely divisible rather than smooth) to replace the truncated simplex appearing in Theorem 24 with a more complicated region (such regions also appear implicitly in [§4.5]). However, in the medium-dimensional setting k ≈ 50, we were not able to accurately and rapidly evaluate the various integrals associated to these variational problems when applied to a suitable basis of functions. One key difficulty here is that whereas polynomials appear to be an adequate choice of basis for the Mk, an analysis of the Euler-Lagrange equation reveals that one should use piecewise polynomial basis functions instead for more complicated variational problems such as the Mk,ε problem (as was done in the three-dimensional case in the ‘Three-dimensional cutoffs’ section), and these are difficult to work with in medium dimensions. From our experience with the low k problems, it looks like one should allow these piecewise polynomials to have relatively high degree on


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 75 of 83 http://www.resmathsci.com/content/1/1/12
some polytopes and low degree on other polytopes, and vanish completely on yet further polytopesi, but we do not have a systematic understanding of what the optimal placement of degrees should be.
3. In Theorem 28, the function F was required to be supported in the simplex
k
k−1 · Rk. However, one can consider functions F supported in other regions R, subject to the constraint that all elements of the sumset R + R lie in a region treatable by one of the cases of Theorem 20. This could potentially lead to other optimization problems that lead to superior numerology, although again it appears difficult to perform efficient numerics for such problems in the medium k regime k ≈ 50. One possibility would be to adopt a ‘free boundary’ perspective, in which the support of F is not fixed in advance, but is allowed to evolve by some iterative numerical scheme. 4. To improve the bounds on Hm for m = 2, 3, 4, 5, one could seek a better lower bound on Mk than the one provided by Theorem 40; one could also try to lower bound more complicated quantities such as Mk,ε. 5. One could attempt to improve the range of , δ for which estimates of the form MPZ[ , δ] are known to hold, which would improve the results of Theorem 4(ii)-(vi). For instance, we believe that the condition 600 + 180δ < 7 in Theorem 11 could be improved slightly to 1, 080 + 330δ < 13 by refining the arguments, but this requires a hypothesis of square root cancellation in a certain four-dimensional exponential sum over finite fields, which we have thus far been unable to establish rigorously. Another direction to pursue would be to improve the δ parameter, or to otherwise relax the requirement of smoothness in the moduli, in order to reduce the need to pass to a truncation of the simplex Rk, which is the primary reason why the m = 1 results are currently unable to use the existing estimates of the form MPZ[ , δ]. Another speculative possibility is to seek MPZ[ , δ] type estimates which only control distribution for a positive proportion of smooth moduli, rather than for all moduli, and then to design a sieve ν adapted to just that proportion of moduli (cf. [41]). Finally, there may be a way to combine the arguments currently used to prove MPZ[ , δ] with the automorphic forms (or ‘Kloostermania’) methods used to prove nontrivial equidistribution results with respect to a fixed modulus, although we do not have any ideas on how to actually achieve such a combination. 6. It is also possible that one could tighten the argument in Lemma 18, for instance by
establishing a non-trivial lower bound on the portion of the sum ∑
n ν(n) when n + h1, . . . , n + hk are all composite, or a sufficiently strong upper bound on the
pair correlations ∑
n θ (n + hi)θ (n + hj) (see [9, §6] for a recent implementation of this latter idea). However, our preliminary attempts to exploit these adjustements suggested that the gain from the former idea would be exponentially small in k, whereas the gain from the latter would also be very slight (perhaps reducing k by O(1) in large k regimes, e.g. k ≥ 5, 000). 7. All of our sieves used are essentially of Selberg type, being the square of a divisor sum. We have experimented with a number of non-Selberg type sieves (for instance
trying to exploit the obvious positivity of 1 − ∑
p≤x:p|n
log p
log x when n ≤ x); however, none of these variants offered a numerical improvement over the Selberg sieve. Indeed it appears that after optimizing the cutoff function F, the Selberg sieve is in


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 76 of 83 http://www.resmathsci.com/content/1/1/12
some sense a ‘local maximum’ in the space of non-negative sieve functions, and one would need a radically different sieve to obtain numerically superior results. 8. Our numerical bounds for the diameter H(k) of the narrowest admissible k-tuple are known to be exact for k ≤ 342, but there is scope for some slight improvement for larger values of k, which would lead to some improvements in the bounds on Hm for m = 2, 3, 4, 5. However, we believe that our bounds on Hm are already fairly close (e.g. within 10%) of optimal, so there is only a limited amount of gain to be obtained solely from this component of the argument.
Narrow admissible tuples
In this section, we outline the methods used to obtain the numerical bounds on H(k)
given by Theorem 17, which are reproduced below:
1. H(3) = 6,
2. H(50) = 246, 3. H(51) = 252, 4. H(54) = 270, 5. H(5, 511) ≤ 52, 116,
6. H(35, 410) ≤ 398, 130,
7. H(41, 588) ≤ 474, 266,
8. H(309, 661) ≤ 4, 137, 854,
9. H(1, 649, 821) ≤ 24, 797, 814,
10. H(75, 845, 707) ≤ 1, 431, 556, 072,
11. H(3, 473, 955, 908) ≤ 80, 550, 202, 480.
H(k) values for small k
The equalities in the first four bounds (1)-(4) were previously known. The case H(3) = 6
is obvious: the admissible 3-tuples (0, 2, 6) and (0, 4, 6) have diameter 6 and no 3-tuple of
smaller diameter is admissible. The cases H(50) = 246, H(51) = 252, and H(54) = 270
follow from results of Clark and Jarvis [42]. They define ∗(x) to be the largest integer k
for which there exists an admissible k-tuple that lies in a half-open interval (y, y + x] of
length x. For each integer k > 1, the largest x for which ∗(x) = k is precisely H(k + 1).
Table 1 of [42] lists these largest x values for 2 ≤ k ≤ 170, and we find that H(50) = 246,
H(51) = 252, and H(54) = 270. Admissible tuples that realize these bounds are shown
in Subsubsections “Admissible 50-tuple realizing H(50) = 246”, “Admissible 51-tuple
realizing H(51) = 252” and “Admissible 54-tuple realizing H(54) = 270”.
Admissible 50-tuple realizing H(50) = 246
Admissible 51-tuple realizing H(51) = 252


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 77 of 83 http://www.resmathsci.com/content/1/1/12
Admissible 54-tuple realizing H(54) = 270
H(k) bounds for mid-range k
As previously noted, exact values for H(k) are known only for k ≤ 342. The upper bounds
on H(k) for the five cases (5)-(9) were obtained by constructing admissible k-tuples using
techniques developed during the first part of the Polymath8 project. These are described
in detail in section 3 of [4], but for the sake of completeness, we summarize the most
relevant methods here.
Fast admissibility testing
A key component of all our constructions is the ability to efficiently determine whether a
given k-tuple H = (h1, . . . , hk) is admissible. We say that H is admissible modulo p if its
elements do not form a complete set of residues modulo p. Any k-tuple H is automatically
admissible modulo all primes p > k, since a k-tuple cannot occupy more than k residue
classes; thus, we only need to test admissibility modulo primes p < k.
A simple way to test admissibility modulo p is to enumerate the elements of H mod
ulo p and keep track of which residue classes have been encountered in a table with p
boolean-valued entries. Assuming the elements of H have absolute value bounded by
O(k log k) (true of all the tuples we consider), this approach yields a total bit-complexity
of O(k2/ log k M(log k)), where M(n) denotes the complexity of multiplying two n
bit integers, which, up to a constant factor, also bounds the complexity of division
with remainder. Applying the Schönhage-Strassen bound M(n) = O(n log n log log n)
from [43], this is O(k2 log log k log log log k), essentially quadratic in k.
This approach can be improved by observing that for most of the primes p < k, there
are likely to be many unoccupied residue classes modulo p. In order to verify admissibil
ity at p, it is enough to find one of them, and we typically do not need to check them all
in order to do so. Using a heuristic model that assumes the elements of H are approxi
mately equidistributed modulo p, one can determine a bound m < p such that k random
elements of Z/pZ are unlikely to occupy all of the residue classes in [0, m]. By represent
ing the k-tuple H as a boolean vector B = (b0, . . . , bhk−h1 ) in which bi = 1 if and only
if i = hj − h1 for some hj ∈ H, we can efficiently test whether H occupies every residue
class in [0, m] by examining the the entries
b0, . . . , bm, bp, . . . , bp+m, b2p, . . . , b2p+m, . . .
of B. The key point is that when p < k is large, say p > (1+ )k/ log k, we can choose m so
that we only need to examine a small subset of the entries in B. Indeed, for primes p > k/c
(for any constant c), we can take m = O(1) and only need to examine O(log k) elements
of B (assuming its total size is O(k log k), which applies to all the tuples we consider here).
Of course it may happen that H occupies every residue class in [0, m] modulo p. In this
case, we revert to our original approach of enumerating the elements of H modulo p,
but we expect this to happen for only a small proportion of the primes p < k. Heuristi
cally, this reduces the complexity of admissibility testing by a factor of O(log k), making


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 78 of 83 http://www.resmathsci.com/content/1/1/12
it sub-quadratic. In practice, we find this approach to be much more efficient than the
straightforward method when k is large (see [§3.1] for further details.
Sieving methods
Our techniques for constructing admissible k-tuples all involve sieving an integer interval
[s, t] of residue classes modulo primes p < k and then selecting an admissible k-tuple
from the survivors. There are various approaches one can take, depending on the choice
of interval and the residue classes to sieve. We list four of these below, starting with the
classical sieve of Eratosthenes and proceeding to more modern variations.
• SieveofEratosthenes. We sieve an interval [2, x] to obtain admissible k-tuples
pm+1, . . . , pm+k.
with m as small as possible. If we sieve the the residue class 0(p) for all primes p ≤ k, we have m = π(k) and pm+1 > k. In this case, no admissibility testing is required, since the residue class 0(p) is unoccupied for all p ≤ k. Applying the Prime Number Theorem in the forms
pk = k log k + k log log k − k + O
(
k log log k
log k
) ,
π(x) = x
log x + O
(x
log2 x
) ,
this construction yields the upper bound
H(k) ≤ k log k + k log log k − k + o(k). (149)
As an optimization, rather than sieving modulo every prime p ≤ k, we instead sieve modulo increasing primes p and as soon as the first k survivors form an admissible tuple. This will typically happen for for some pm < k. • Hensley-Richardssieve. The bound in (149) was improved by Hensley and Richards [44-46], who observed that rather than sieving [2, x] it is better to sieve the interval [−x/2, x/2] to obtain admissible k-tuples of the form
−pm+ k/2 −1, . . . , pm+1, . . . , −1, 1, . . . , pm+1, . . . , pm+ (k+1)/2 −1,
where we again wish to make m as small as possible. It follows from Lemma 5 of [45] that one can take m = o(k/ log k), leading to the improved upper bound
H(k) ≤ k log k + k log log k − (1 + log 2)k + o(k). (150)
• ShiftedSchinzelsieve. As noted by Schinzel in [47], in the Hensley-Richards sieve, it is slightly better to sieve 1(2) rather than 0(2); this leaves unsieved powers of 2 near the center of the interval [−x/2, x/2] that would otherwise be removed (more generally, one can sieve 1(p) for many small primes p, but we did not). Additionally, we find that shifting the interval [−x/2, x/2] can yield significant improvements (one can also view this as changing the choices of residue classes). This leads to the following approach: we sieve an interval [s, s + x] of odd integers and multiples of odd primes p ≤ pm, where x is large enough to ensure at least k survivors, and m is large enough to ensure that the survivors form an admissible tuple, with x and m minimal subject to these constraints. A tuple of exactly k survivors is then chosen to minimize the diameter. By varying s and comparing the results, we can choose a starting point s ∈[−x/2, x/2] that yields the smallest final


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 79 of 83 http://www.resmathsci.com/content/1/1/12
diameter. For large k, we typically find s ≈ k is optimal, as opposed to s ≈ −(k/2) log k in the Hensley-Richards sieve. • Shiftedgreedysieve. As a further optimization, we can allow greater freedom in the choice of residue class to sieve. We begin as in the shifted Schinzel sieve, but for
primes p ≤ pm that exceed 2√k log k, rather than sieving 0(p), we choose a minimally occupied residue class a(p). As above, we sieve the interval [s, s + x] for varying values of s ∈[−x/2, x/2] and select the best result, but unlike the shifted Schinzel sieve, for large k, we typically choose s ≈ −(k/ log k − k)/2. We remark that while one might suppose that it would be better to choose a minimally occupied residue class at all primes, not just the larger ones, we find that this is generally not the case. Fixing a structured choice of residue classes for the small primes avoids the erratic behavior that can result from making greedy choices to soon (see [48, Fig. 1] for an illustration of this).
Table 4 lists the bounds obtained by applying each of these techniques (in the online
version of this paper, each table entry includes a link to the constructed tuple). To the
admissible tuples obtained using the shifted greedy sieve, we additionally applied various
local optimizations that are detailed in ([§3.6]). As can be seen in the table, the additional
improvement due to these local optimizations is quite small compared to that gained by
using better sieving algorithms, especially when k is large.
Table 4 also lists the value k log k + k that we conjecture as an upper bound on H(k)
for all sufficiently large k.
H(k) bounds for large k
The upper bounds on H(k) for the last two cases (10) and (11) were obtained using mod
ified versions of the techniques described above that are better suited for handling very
large values of k. These entail three types of optimizations that are summarized in the
subsections below.
Improved time complexity
As noted above, the complexity of admissibility testing is quasi-quadratic in k. Each of the
techniques listed in the ‘H(k) bounds for mid-range k’ section involves optimizing over a
parameter space whose size is at least quasi-linear in k, leading to an overall quasi-cubic
time complexity for constructing a narrow admissible k-tuple; this makes it impractical
to handle k > 109. We can reduce this complexity in a number of ways.
First, we can combine parameter optimization and admissibility testing. In both
the sieve of Eratosthenes and Hensley-Richards sieves, taking m = k guarantees an
Table 4 Upper bounds on H(k) for selected values of k
k 5,511 35,410 41,588 309,661 1,649,821
k primes past k 56,538 433,992 516,586 4,505,700 26,916,060 Eratosthenes 55,160 424,636 505,734 4,430,212 26,540,720 Hensley-Richards 54,480 415,642 494,866 4,312,612 25,841,884 Shifted Schinzel 53,774 411,060 489,056 4,261,858 25,541,910 Shifted greedy 52,296 399,936 476,028 4,142,780 24,798,306 Best known 52,116 398,130 474,266 4,137,854 24,797,814
k log k + k 52,985 406,320 483,899 4,224,777 25,268,951


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 80 of 83 http://www.resmathsci.com/content/1/1/12
admissible k-tuple. For m < k, if the corresponding k-tuple is inadmissible, it is typ
ically because it is inadmissible modulo the smallest prime pm+1 that appears in the
tuple. This suggests a heuristic approach in which we start with m = k, and then
iteratively reduce m, testing the admissibility of each k-tuple modulo pm+1 as we go,
until we can proceed no further. We then verify that the last k-tuple that was admis
sible modulo pm+1 is also admissible modulo all primes p > pm+1 (we know it is
admissible at all primes p ≤ pm because we have sieved a residue class for each of
these primes). We expect this to be the case, but if not we can increase m as required.
Heuristically, this yields a quasi-quadratic running time, and in practice, it takes less
time to find the minimal m than it does to verify the admissibility of the resulting
k-tuple.
Second, we can avoid a complete search of the parameter space. In the case of the shifted
Schinzel sieve, for example, we find empirically that taking s = k typically yields an admis
sible k-tuple whose diameter is not much larger than that achieved by an optimal choice
of s; we can then simply focus on optimizing m using the strategy described above. Similar
comments apply to the shifted greedy sieve.
Improved space complexity
We expect a narrow admissible k-tuple to have diameter d = (1 + o(1))k log k. Whether
we encode this tuple as a sequence of k integers, or as a bitmap of d + 1 bits, as in the fast
admissibility testing algorithm, we will need approximately k log k bits. For k > 109, this
may be too large to conveniently fit in memory. We can reduce the space to O(k log log k)
bits by encoding the k-tuple as a sequence of k − 1 gaps; the average gap between consec
utive entries has size log k and can be encoded in O(log log k) bits. In practical terms, for
the sequences we constructed, almost all gaps can be encoded using a single 8-bit byte for
each gap.
One can further reduce space by partitioning the sieving interval into windows. For the
construction of our largest tuples, we used windows of size O(√d) and converted to a
gap-sequence representation only after sieving at all primes up to an O(√d) bound.
Parallelization
With the exception of the greedy sieve, all the techniques described above are easily paral
lelized. The greedy sieve is more difficult to parallelize because the choice of a minimally
occupied residue class modulo p depends on the set of survivors obtained after sieving
modulo primes less than p. To address this issue, we modified the greedy approach to
work with batches of consecutive primes of size n, where n is a multiple of the number of
parallel threads of execution. After sieving fixed residue classes modulo all small primes
p < 2√k log k, we determine minimally occupied residue classes for the next n primes in
parallel, sieve these residue classes, and then proceed to the next batch of n primes.
In addition to the techniques described above, we also considered a modified Schinzel
sieve in which we check admissibility modulo each successive prime p before sieving mul
tiples of p, in order to verify that sieving modulo p is actually necessary. For values of p
close to but slightly less than pm, it will often be the case that the set of survivors is already
admissibility modulo p, even though it does contain multiples of p (because some other
residue class is unoccupied). As with the greedy sieve, when using this approach, we sieve
residue classes in batches of size n to facilitate parallelization.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 81 of 83 http://www.resmathsci.com/content/1/1/12
Table 5 Upper bounds on H(k) for selected values of k
k 75,845,707 3,473,955,908
k primes past k 1,541,858,666 84,449,123,072
Eratosthenes 1,526,698,470 83,833,839,848
Hensley-Richards 1,488,227,220 81,912,638,914
Shifted Schinzel 1,467,584,468 80,761,835,464
Shifted greedy 1,431,556,072 Not available
Best known 1,431,556,072 80,550,202,480
k log k + k 1,452,006,268 79,791,764,059
Results for large k
Table 5 lists the bounds obtained for the two largest values of k. For k = 75, 845, 707, the
best results were obtained with a shifted greedy sieve that was modified for parallel execu
tion as described above, using the fixed shift parameter s = −(k log k − k)/2. A list of the
sieved residue classes is available at math.mit.edu/∼drew/n75845707_1431556072.txt.
This file contains values of k, s, d, and m, along with a list of prime indices ni > m and
residue classes ri such that sieving the interval [s, s + d] of odd integers, multiples of pn
for 1 < n ≤ m, and at ri modulo pni yields an admissible k-tuple.
For k = 3, 473, 955, 908, we did not attempt any form of greedy sieving due to practical
limits on the time and computational resources available. The best results were obtained
using a modified Schinzel sieve that avoids unnecessary sieving, as described above,
using the fixed shift parameter s = k0. A list of the sieved residue classes is available at
math.mit.edu/∼drew/n75845707_1431556072.txt.
This file contains values of k, s, d, and m, along with a list of prime indices ni > m such
that sieving the interval [s, s + d] of odd integers, multiples of pn for 1 < n ≤ m, and
multiples of pni yields an admissible k-tuple.
Source code for our implementation is available at http://math.mit.edu/~drew/
ompadm_v0.5.tar; this code can be used to verify the admissibility of both the tuples listed
above.
Endnotes
aWhen a, b are real numbers, we will also need to use (a, b) and [a, b] to denote the open and closed intervals, respectively, with endpoints a, b. Unfortunately, this notation conflicts with the notation given above, but it should be clear from the context which notation is in use. bActually, there are some differences between Conjecture 1 of [28] and the claim here. Firstly, we need an estimate that is uniform for all a, whereas in [28] only the case of a fixed modulus a was asserted. On the other hand, α, β were assumed to be controlled in 2 instead of via the pointwise bounds (6), and Q was allowed to be as large as x log−C x for some fixed C (although, in view of the negative results in [23,24], this latter strengthening may be too ambitious). cOne could also use the Heath-Brown identity [49] here if desired. dIn the k = 1 case, we of course just have qW,d1,...,d′
k−1 = W .
eOne could obtain a small improvement to the bounds here by replacing the threshold 2c with a parameter to be optimized over. fThe arguments in [5] are rigorous under the assumption of a positive eigenfunction as in Corollary 35, but the existence of such an eigenfunction remains open for k ≥ 3.


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 82 of 83 http://www.resmathsci.com/content/1/1/12
gIndeed, one might be even more ambitious and conjecture a square-root cancellation
≺≺ √x/q for such sums (see [50] for some similar conjectures), although such stronger cancellations generally do not play an essential role in sieve-theoretic computations. hOne new technical difficulty here is that some of the various moduli [dj, dj′] arising in
these arguments are not required to be coprime at primes p > w dividing x or x − 2; this requires some modification to Lemma 30 that ultimately leads to the appearance of the singular series S. However, these modifications are quite standard, and we do not give the details here. iIn particular, the optimal choice F for Mk,ε should vanish on the polytope
{(t1, . . . , tk) ∈ (1 + ε) · Rk : ∑
i=i0 ti ≥ 1 − ε for all i0 = 1, . . . , k}.
Acknowledgements
This paper is part of the Polymath project, which was launched by Timothy Gowers in February 2009 as an experiment to see if research mathematics could be conducted by a massive online collaboration. The current project (which was administered by Terence Tao) is the eighth project in this series, and this is the second paper arising from that project. Further information on the Polymath project can be found on the web site michaelnielsen.org/polymath1. Information about this specific project may be found at http://michaelnielsen.org/polymath1/index.php?title=Bounded_gaps_ between_primes, and a full list of participants and their grant acknowledgments may be found at http://michaelnielsen. org/polymath1/index.php?title=Polymath8_grant_acknowledgments. We thank Thomas Engelsma for supplying us with his data on narrow admissible tuples and Henryk Iwaniec for useful suggestions. We also thank the anonymous referees for some suggestions in improving the content and exposition of the paper.
Received: 18 July 2014 Accepted: 19 July 2014
References
1. Hardy, GH, Littlewood, JE: Some problems of “Partitio Numerorum”, III: on the expression of a number as a sum of primes. Acta Math. 44, 1–70 (1923) 2. Goldston, D, Pintz, J, Yıldırım, C: Primes in tuples. I. Ann. Math. 170(2), 819–862 (2009) 3. Zhang, Y: Bounded gaps between primes. Annals Math. 179, 1121–1174 (2014) 4. Polymath, DHJ: New equidistribution estimates of Zhang type, and bounded gaps between primes. arxiv.org/abs/1402.0811v2 5. Maynard, J: Small gaps between primes. Annals Math. to appear. 6. Granville, A: Bounded gaps between primes, preprint. 7. Selberg, A: On elementary methods in prime number-theory and their limitations. In: Proc. 11th Scand. Math. Cong. Trondheim (1949), Collected Works, vol. I, pp. 388–397. Springer-Verlag, Berlin-Göttingen-Heidelberg, (1989) 8. Pintz, J: The bounded gap conjecture and bounds between consecutive Goldbach numbers. Acta Arith. 155(4), 397–405 (2012) 9. Banks, WD, Freiberg, T, Maynard, J: On limit points of the sequence of normalized prime gaps, preprint. 10. Banks, WD, Freiberg, T, Turnage-Butterbaugh, CL: Consecutive primes in tuples, preprint. 11. Benatar, J: The existence of small prime gaps in subsets of the integers, preprint. 12. Castillo, A, Hall, C, Lemke Oliver, RJ, Pollack, P, Thompson, L: Bounded gaps between primes in number fields and function fields, preprint. 13. Chua, L, Park, S, Smith, G. D: Bounded gaps between primes in special sequences, preprint. 14. Freiberg, T: A note on the theorem of Maynard and Tao, preprint. 15. Li, H, Pan, H: Bounded gaps between primes of the special form, preprint. 16. Maynard, J: Dense clusters of primes in subsets, preprint. 17. Pintz, J: On the ratio of consecutive gaps between primes, preprint. 18. Pintz, J: On the distribution of gaps between consecutive primes, preprint. 19. Pollack, P: Bounded gaps between primes with a given primitive root, preprint. 20. Pollack, P, Thompson, L: Arithmetic functions at consecutive shifted primes, preprint. 21. Thorner, J: Bounded Gaps Between Primes in Chebotarev Sets, preprint. 22. Elliott, PDTA, Halberstam, H: A conjecture in prime number theory. Symp. Math. 4, 59–72 (1968) 23. Friedlander, J, Granville, A: Relevance of the residue class to the abundance of primes. In: Proceedings of the Amalfi Conference on Analytic Number Theory (Maiori, 1989), pp. 95–103. Univ. Salerno, Salerno, (1992) 24. Friedlander, J, Granville, A, Hildebrand, A, Maier, H: Oscillation theorems for primes in arithmetic progressions and for sifting functions. J. Amer. Math. Soc. 4(1), 25–86 (1991) 25. Bombieri, E: Le Grand Crible dans la Théorie Analytique des Nombres (Seconde ed.) Astérisque. 18 (1987) 26. Vinogradov, AI: The density hypothesis for Dirichlet L-series. Izv. Akad. Nauk SSSR Ser. Mat. (in Russian). 29, 903–934 (1956) 27. Motohashi, Y, Pintz, J: A smoothed GPY sieve. Bull. Lond. Math. Soc. 40(2), 298–310 (2008) 28. Bombieri, E, Friedlander, J, Iwaniec, H: Primes in arithmetic progressions to large moduli. Acta Math. 156(3–4), 203–251 (1986) 29. Vaughan, RC: Sommes trigonométriques sur les nombres premiers. C. R. Acad. Sci. Paris Sér. A. 285, 981–983 (1977) 30. Fouvry É: Autour du théorème de Bombieri-Vinogradov. Acta Math. 152(3–4), 219–244 (1984) 31. Fouvry, É, Iwaniec, H: Primes in arithmetic progressions. Acta Arith. 42(2), 197–218 (1983)


 Polymath Research in the Mathematical Sciences 2014, 1:12 Page 83 of 83 http://www.resmathsci.com/content/1/1/12
32. Siebert, H: Einige Analoga zum Satz von Siegel-Walfisz. In: Zahlentheorie (Tagung, Math. Forschungsinst., Oberwolfach, 1970), pp. 173–184. Bibliographisches Inst., Mannheim (1971) 33. Iwaniec, H, Kowalski, E: Analytic number theory, Vol. 53. American Mathematical Society Colloquium Publications (2004) 34. Motohashi, Y: An induction principle for the generalization of Bombieri’s prime number theorem. Proc. Japan Acad. 52, 273–275 (1976) 35. Pintz, J: Polignac Numbers, Conjectures of Erdo ̋ s on Gaps between Primes, Arithmetic Progressions in Primes, and the Bounded Gap Conjecture, preprint. 36. Soundararajan, K: Small gaps between prime numbers: the work of Goldston-Pintz-Yıldırım. Bull. Amer. Math. Soc. (N.S.) 44(1), 1–18 (2007) 37. Goldston, D, Yıldırım, C: Higher correlations of divisor sums related to primes. I. Triple correlations. Integers. 3(A5), 66 (2003) 38. Pintz, J: Are there arbitrarily long arithmetic progressions in the sequence of twin primes? An irregular mind. Szemerédi is 70. Bolyai Soc. Math. Stud. Springer. 21, 525–559 (2010) 39. Farkas, B, Pintz, J, Révész, S: On the optimal weight function in the Goldston-Pintz-Yıldırım method for finding small gaps between consecutive primes. In: Paul Turán Memorial Volume: Number Theory, Analysis and Combinatorics. de Gruyter, Berlin, (2013) 40. Friedlander, J, Iwaniec, H: The polynomial X2 + Y 4 captures its primes. Ann. Math. 148(3), 945–1040 (1998) 41. Fouvry, E: Théor  ́me de Brun-Titchmarsh: application au théorème de Fermat. Invent. Math. 79(2), 383–407 (1985) 42. Clark, D, Jarvis, N: Dense admissible sequences. Math. Comp. 70(236), 1713–1718 (2001) 43. Schönhage, A, Strassen, V: Schnelle Multiplikation großer Zahlen. Comput. Arch. Elektron. Rechnen. 7, 281–292 (1971) 44. Hensley, D, Richards, I: On the incompatibility of two conjectures concerning primes. In: Analytic Number Theory (Proc. Sympos. Pure Math., Vol. XXIV, St. Louis Univ., St. Louis, Mo. 1972), pp. 123–127. Amer. Math. Soc., Providence, R.I. (1973) 45. Hensley, D, Richards, I: Primes in intervals. Acta Arith. 25(1973/74), 375–391 46. Richards, I: On the incompatibility of two conjectures concerning primes; a discussion of the use of computers in attacking a theoretical problem. Bull. Amer. Math. Soc. 80, 419–438 (1974) 47. Schinzel, A: Remarks on the paper “Sur certaines hypothèses concernant les nombres premiers”. Acta Arith. 7, 1–8 (1961/1962) 48. Gordon, D, Rodemich, G: Dense admissible sets. In: Algorithmic Number Theory (Portland, OR, 1998), Lecture Notes in Comput. Sci, pp. 216–225. Springer, Berlin, (1998) 49. Heath-Brown, DR: Prime numbers in short intervals and a generalized Vaughan identity. Canad. J. Math. 34(6), 1365–1377 (1982) 50. Montgomery, HL: Topics in Multiplicative Number Theory, volume 227. Lecture Notes in Math. Springer, New York (1971)
doi:10.1186/s40687-014-0012-7 Cite this article as: Polymath: Variants of the Selberg sieve, and bounded intervals containing many primes. Research in the Mathematical Sciences 2014 1:12.
Submit your manuscript to a journal and benefit from:
7 Convenient online submission 7 Rigorous peer review 7 Immediate publication on acceptance 7 Open access: articles freely available online 7 High visibility within the field 7 Retaining the copyright to your article
Submit your next manuscript at 7 springeropen.com