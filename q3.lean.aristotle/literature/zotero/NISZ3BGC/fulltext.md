---
title: "Small gaps between primes"
authors:
  - "James Maynard"
date: "2015-00-00 2015"
publication: "Annals of Mathematics"
doi: "10.4007/annals.2015.181.1.7"
url: null
zotero:
  attachment_key: "4N27844N"
  parent_key: "NISZ3BGC"
  item_id: 2313
  attachment_item_id: 2318
---

arXiv:1311.4600v3 [math.NT] 28 Oct 2019
SMALL GAPS BETWEEN PRIMES
JAMES MAYNARD
Abstract. We introduce a refinement of the GPY sieve method for studying prime k-tuples and small gaps between primes. This refinement avoids previous limitations of the method, and allows us to show that for each k, the prime k-tuples conjecture holds for a positive proportion of admissible k-tuples. In particular, lim infn(pn+m − pn) < ∞ for every integer m. We also show that lim inf(pn+1 − pn) ≤ 600, and, if we assume the Elliott-Halberstam conjecture, that lim infn(pn+1 − pn) ≤ 12 and lim infn(pn+2 − pn) ≤ 600.
1. Introduction
We say that a set H = {h1, . . . , hk} of distinct non-negative integers is ‘admissible’ if, for every prime p, there is an integer ap such that ap . h (mod p) for all h ∈ H. We are interested in the following conjecture.
Conjecture (Prime k-tuples conjecture). Let H = {h1, . . . , hk} be admissible. Then there are infinitely many integers n such that all of n + h1, . . . , n + hk are prime.
When k > 1 no case of the prime k-tuples conjecture is currently known. Work on approximations to the prime k-tuples conjecture has been very successful in showing the existence of small gaps between primes, however. In their celebrated paper [5], Goldston, Pintz and Yıldırım introduced a new method for counting tuples of primes, and this allowed them to show that
(1.1) lim inf
n
pn+1 − pn
log pn
= 0.
The recent breakthrough of Zhang [9] managed to extend this work to prove
(1.2) lim inf
n (pn+1 − pn) ≤ 70 000 000,
thereby establishing for the first time the existence of infinitely many bounded gaps between primes. Moreover, it follows from Zhang’s theorem the that number of admissible sets of size 2 contained in [1, x]2 which satisfy the prime 2-tuples conjecture is ≫ x2 for large x. Thus, in this sense, a positive proportion of admissible sets of size 2 satisfy the prime 2-tuples conjecture. The recent polymath project [7] has succeeded in reducing the bound (1.2) to 4680, by optimizing Zhang’s arguments and introducing several new refinements. The above results have used the ‘GPY method’ to study prime tuples and small gaps between primes, and this method relies heavily on the distribution of primes in arithmetic progressions. Given θ > 0, we say the primes have ‘level of distribution θ’1 if, for every A > 0, we have
(1.3)
∑
q≤xθ
max
(a,q)=1
∣ ∣ ∣
∣π(x; q, a) − π(x)
φ(q)
∣ ∣ ∣
∣ ≪A
x
(log x)A .
1We note that different authors have given slightly different names or definitions to this concept. For the purposes of this paper, (1.3) will be our definition of the primes having level of distribution θ. 1


 2 JAMES MAYNARD
The Bombieri-Vinogradov theorem establishes that the primes have level of distribution θ for every θ < 1/2, and Elliott and Halberstam [1] conjectured that this could be extended to every θ < 1. Friedlander and Granville [2] have shown that (1.3) cannot hold with xθ replaced with x/(log x)B for any fixed B, and so the Elliott-Halberstam conjecture is essentially the strongest possible result of this type. The original work of Goldston, Pintz and Yıldırım showed the existence of bounded gaps between primes if (1.3) holds for some θ > 1/2. Moreover, under the Elliott-Halberstam conjecture one had lim infn(pn+1 − pn) ≤ 16. The key breakthrough of Zhang’s work was in establishing that a slightly weakened form of (1.3) holds for some θ > 1/2. If one looks for bounded length intervals containing two or more primes, then the GPY method fails to prove such strong results. Unconditionally we are only able to improve upon the trivial bound from the prime number theorem by a constant factor [4], and even assuming the Elliott-Halberstam conjecture, the best available result [5] is
(1.4) lim inf
n
pn+2 − pn
log pn
= 0.
The aim of this paper is to introduce a refinement of the GPY method which removes the barrier of θ = 1/2 to establishing bounded gaps between primes, and allows us to show the existence of arbitrarily many primes in bounded length intervals. This answers the second and third questions posed in [5] on extensions of the GPY method (the first having been answered by Zhang’s result). Our new method also has the benefit that it produces numerically superior results to previous approaches.
Theorem 1.1. Let m ∈ N. We have
lim inf
n (pn+m − pn) ≪ m3e4m.
Terence Tao (private communication) has independently proven Theorem 1.1 (with a slightly weaker bound) at much the same time. He uses a similar method; the steps are more-or-less the same but the calculations are done differently. We will indicate some of the differences in our proofs as we go along. We see that the bound in Theorem 1.1 is quite far from the conjectural bound of approximately m log m predicted by the prime m-tuples conjecture. Our proof naturally generalizes (but with a weaker upper bound) to many subsequences of the primes which have a level of distribution θ > 0. For example, we can show corresponding results where the primes are contained in short intervals [N, N + N7/12+ǫ ] for any ǫ > 0 or in an arithmetic progression modulo q ≪ (log N)A. In particular, our method gives results for simultaneously prime values of linear functions, which might have specific interest. Given k distinct linear functions Li(n) = ain + bi (1 ≤ i ≤ k) with positive integer coefficients such that the product function Π(n) = ∏k
i=1 Li(n) has no fixed prime divisor, the method presented here shows that there are infinitely many integers n such that at least (1/4 + ok→∞(1)) log k of the Li(n) are prime.
Theorem 1.2. Let m ∈ N. Let r ∈ N be sufficiently large depending on m, and let A = {a1, a2, . . . , ar} be a set of r distinct integers. Then we have
#{{h1, . . . , hm} ⊆ A : for infinitely many n all of n + h1, . . . , n + hm are prime}
#{{h1, . . . , hm} ⊆ A} ≫m 1.
Thus a positive proportion of admissible m-tuples satisfy the prime m-tuples conjecture for every m, in an appropriate sense.


 SMALL GAPS BETWEEN PRIMES 3
Theorem 1.3. We have
lim inf
n (pn+1 − pn) ≤ 600.
We emphasize that the above result does not incorporate any of the technology used by Zhang to establish the existence of bounded gaps between primes. The proof is essentially elementary, relying only on the Bombieri-Vinogradov theorem. Naturally, if we assume that the primes have a higher level of distribution, then we can obtain stronger results.
Theorem 1.4. Assume that the primes have level of distribution θ for every θ < 1. Then
lim inf
n (pn+1 − pn) ≤ 12,
lim inf
n (pn+2 − pn) ≤ 600.
Although the constant 12 of Theorem 1.4 appears to be optimal with our method in its current form, the constant 600 appearing in Theorem 1.3 and Theorem 1.4 is certainly not optimal. By performing further numerical calculations our method could produce a better bound, and also most of the ideas of Zhang’s work (and the refinements produced by the polymath project) should be able to be combined with this method to reduce the constant further. We comment that the assumption of the Elliott-Halberstam conjecture allows us to improve the bound on Theorem 1.1 to O(m3e2m).
2. An improved GPY sieve method
We first give an explanation of the key idea behind our new approach. The basic idea of the GPY method is, for a fixed admissible set H = {h1, . . . , hk}, to consider the sum
S (N, ρ) =
∑
N≤n<2N
(
k
∑
i=1
χP(n + hi) − ρ)
(2.1) wn.
Here χP is the characteristic function of the primes, ρ > 0 and wn are non-negative weights. If we can show that S (N, ρ) > 0 then at least one term in the sum over n must have a positive contribution. By the non-negativity of wn, this means that there must be some integer n ∈ [N, 2N] such that at least ⌊ρ + 1⌋ of the n + hi are prime. (Here ⌊x⌋ denotes the largest integer less than or equal to x.) Thus if S (N, ρ) > 0 for all large N, there are infinitely many integers n for which at least ⌊ρ + 1⌋ of the n + hi are prime (and so there are infinitely many bounded length intervals containing ⌊ρ + 1⌋ primes). The weights wn are typically chosen to mimic Selberg sieve weights. Estimating (2.1) can be interpreted as a ‘k-dimensional’ sieve problem. The standard Selberg k-dimensional weights (which can be shown to be essentially optimal in other contexts) are
(2.2) wn = ( ∑
d| ∏k
i=1 (n+hi )
d<R
λd
)2, λd = μ(d)(log R/d)k.
With this choice we find that we just fail to prove the existence of bounded gaps between primes if we assume the Elliott-Halberstam conjecture. The key new idea in the paper of Goldston, Pintz and Yıldırım [5] was to consider more general sieve weights of the form
(2.3) λd = μ(d)F(log R/d),
for a suitable smooth function F. Goldston, Pintz and Yıldırım chose F(x) = xk+l for suitable l ∈ N, which has been shown to be essentially optimal when k is large. This allows us to gain a factor of approximately 2 for large k over the previous choice of sieve weights. As a result we


 4 JAMES MAYNARD
just fail to prove bounded gaps using the fact that the primes have exponent of distribution θ for any θ < 1/2, but succeed in doing so if we assume they have level of distribution θ > 1/2. The new ingredient in our method is to consider a more general form of the sieve weights
(2.4) wn =
(∑
di |n+hi ∀i
λd1,...,dk
)2.
Using such weights with λd1,...,dk is the key feature of our method. It allows us to improve on the previous choice of sieve weights by an arbitrarily large factor, provided that k is sufficiently large. It is the extra flexibility gained by allowing the weights to depend on the divisors of each factor individually which gives this improvement. The idea to use such weights is not entirely new. Selberg [8, Page 245] suggested the possible use of similar weights in his work on approximations to the twin prime problem, and Goldston and Yıldırım [6] considered similar weights in earlier work on the GPY method, but with the support restricted to di < R1/k for all i. We comment that our choice of λd1,...,dk will look like
(2.5) λd1,...,dk ≈ (
k
∏
i=1
μ(di)
)
f (d1, . . . , dk),
for a suitable smooth function f . For our precise choice of λd1,...,dk (given in Proposition 4.1) we find it convenient to give a slightly different form of λd1,...,dk , but weights of the form (2.5) should produce essentially the same results.
3. Notation
We shall view k as a fixed integer, and H = {h1, . . . , hk} as a fixed admissible set. In particular, any constants implied by the asymptotic notation o, O or ≪ may depend on k and H. We will let N denote a large integer, and all asymptotic notation should be interpreted as referring to the limit N → ∞. All sums, products and suprema will be assumed to be taken over variables lying in the natural numbers N = {1, 2, . . . } unless specified otherwise. The exception to this is when sums or products are over a variable p, which instead will be assumed to lie in the prime numbers P = {2, 3, . . . , }. Throughout the paper, φ will denote the Euler totient function, τr(n) the number of ways of writing n as a product of r natural numbers and μ the Moebius function. We will let ǫ be a fixed positive real number, and we may assume without further comment that ǫ is sufficiently small at various stages of our argument. We let pn denote the nth prime, and #A denote the number of elements of a finite set A. We use ⌊x⌋ to denote the largest integer n ≤ x, and ⌈x⌉ the smallest integer n ≥ x. We let (a, b) be the greatest common divisor of integers a and b. Finally, [a, b] will denote the closed interval on the real line with endpoints a and b, except for in Section 5 where it will denote the least common multiple of integers a and b instead.
4. Outline of the proof
We will find it convenient to choose our weights wn to be zero unless n lies in a fixed residue class v0 (mod W), where W = ∏
p≤D0 p. This is a technical modification which removes some minor complications in dealing with the effect of small prime factors. The precise choice of D0 is unimportant, but it will suffice to choose
(4.1) D0 = log log log N,


 SMALL GAPS BETWEEN PRIMES 5
so certainly W ≪ (log log N)2 by the prime number theorem. By the Chinese remainder theorem, we can choose v0 such that v0 + hi is coprime to W for each i since H is admissible. When n ≡ v0 (mod W), we choose our weights wn of the form (2.4). We now wish to estimate the sums
S1 =
∑
N≤n<2N
n≡v0 (mod W)


∑
di |n+hi ∀i
λd1,...,dk


2
(4.2) ,
S2 =
∑
N≤n<2N
n≡v0 (mod W)
(
k
∑
i=1
χP(n + hi))


∑
di |n+hi ∀i
λd1,...,dk


2
(4.3) .
We evaluate these sums using the following proposition.
Proposition 4.1. Let the primes have exponent of distribution θ > 0, and let R = Nθ/2−δ for some small fixed δ > 0. Let λd1,...,dk be defined in terms of a fixed smooth function F by
λd1,...,dk =
(
k
∏
i=1
μ(di)di
)∑
r1,...,rk
di|ri∀i
(ri ,W )=1∀i
μ(∏k
i=1 ri)2
∏k
i=1 φ(ri) F
( log r1
log R , . . . , log rk
log R
)
,
whenever (∏k
i=1 di, W) = 1, and let λd1,...,dk = 0 otherwise. Moreover, let F be supported on
Rk = {(x1, . . . , xk) ∈ [0, 1]k : ∑k
i=1 xi ≤ 1}. Then we have
S 1 = (1 + o(1))φ(W)kN(log R)k
Wk+1 Ik(F),
S 2 = (1 + o(1))φ(W)kN(log R)k+1
Wk+1 log N
k
∑
m=1
J(m)
k (F),
provided Ik(F) , 0 and J(m)
k (F) , 0 for each m, where
Ik(F) =
∫1
0
···
∫1
0
F(t1, . . . , tk)2dt1 . . . dtk,
J(m)
k (F) =
∫1
0
···
∫1
0
(∫ 1
0
F(t1, . . . , tk)dtm
)2
dt1 . . . dtm−1dtm+1 . . . dtk.
We recall that if S 2 is large compared to S 1, then using the GPY method we can show that there are infinitely many integers n such that several of the n + hi are prime. The following proposition makes this precise.
Proposition 4.2. Let the primes have level of distribution θ > 0. Let δ > 0 and H = {h1, . . . , hk} be an admissible set. Let Ik(F) and J(m)
k (F) be given as in Proposition 4.1,
and let Sk denote the set of Riemann-integrable functions F : [0, 1]k → R supported on Rk = {(x1, . . . , xk) ∈ [0, 1]k : ∑k
i=1 xi ≤ 1} with Ik(F) , 0 and J(m)
k (F) , 0 for each m. Let
Mk = sup
F∈Sk
∑k
m=1 J(m)
k (F)
Ik(F) , rk = ⌈ θMk
2
⌉.
Then there are infinitely many integers n such that at least rk of the n + hi (1 ≤ i ≤ k) are prime. In particular, lim infn(pn+rk−1 − pn) ≤ max1≤i, j≤k(hi − h j).


 6 JAMES MAYNARD
Proof of Proposition 4.2. We let S = S 2 − ρS 1, and recall that from Section 2 that if we can show S > 0 for all large N, then there are infinitely many integers n such that at least ⌊ρ + 1⌋ of the n + hi are prime. We put R = Nθ/2−δ for a small δ > 0. By the definition of Mk, we can choose F0 ∈ Sk such that ∑k
m=1 J(m)
k (F0) > (Mk − δ)Ik(F0) > 0. Since F0 is Riemann-integrable, there is a smooth
function F1 such that ∑k
m=1 J(m)
k (F1) > (Mk − 2δ)Ik(F1) > 0. Using Proposition 4.1, we can then choose λd1,...,dk such that
S = φ(W)kN(log R)k
W k+1
( log R
log N
k
∑
j=1
J(m)
k (F1) − ρIk(F1) + o(1)
)
≥ φ(W)kN(log R)kIk(F1)
W k+1
(( θ
2 − δ)(
(4.4) Mk − 2δ) − ρ + o(1)).
If ρ = θMk/2 − ǫ then, by choosing δ suitably small (depending on ǫ), we see that S > 0 for all large N. Thus there are infinitely many integers n for which at least ⌊ρ + 1⌋ of the n + hi are prime. Since ⌊ρ + 1⌋ = ⌈θMk/2⌉ if ǫ is suitably small, we obtain Proposition 4.2.
Thus, if the primes have a fixed level of distribution θ, to show the existence of many of the n + hi being prime for infinitely many n ∈ N we only require a suitable lower bound for Mk. The following proposition establishes such a bound for different values of k.
Proposition 4.3. Let k ∈ N, and Mk be as given by Proposition 4.2. Then
(1) We have M5 > 2. (2) We have M105 > 4.
(3) If k is sufficiently large, we have Mk > log k − 2 log log k − 2.
We now prove Theorems 1.1, 1.2, 1.3 and 1.4 from Propositions 4.2 and 4.3. First we consider Theorem 1.3. We take k = 105. By Proposition 4.3, we have M105 > 4. By the Bombieri-Vinogradov theorem, the primes have level of distribution θ = 1/2 − ǫ for every ǫ > 0. Thus, if we take ǫ sufficiently small, we have θM105/2 > 1. Therefore, by Proposition 4.2, we have lim inf(pn+1 − pn) ≤ max1≤i, j≤105(hi − h j) for any admissible set H = {h1, . . . , h105}. By computations performed by Thomas Engelsma (unpublished), we can choose2 H such that 0 ≤ h1 < . . . < h105 and h105 − h1 = 600. This gives Theorem 1.3. If we assume the Elliott-Halberstam conjecture then the primes have level of distribution θ = 1 − ǫ. First we take k = 105, and see that θM105/2 > 2 for ǫ sufficiently small (since M105 > 4). Therefore, by Proposition 4.2, lim infn(pn+2 − pn) ≤ max1≤i, j≤105(hi − h j). Thus, choosing the same admissible set H as above, we see lim infn(pn+2 − pn) ≤ 600 under the Elliott-Halberstam conjecture. Next we take k = 5 and H = {0, 2, 6, 8, 12}, with θ = 1 − ǫ again. By Proposition 4.3 we have M5 > 2, and so θM5/2 > 1 for ǫ sufficiently small. Thus, by Proposition 4.2, lim infn(pn+1 − pn) ≤ 12 under the Elliott-Halberstam conjecture. This completes the proof of Theorem 1.4.
2Explicitly, we can take H = {0, 10, 12, 24, 28, 30, 34, 42, 48, 52, 54, 64, 70, 72, 78, 82, 90, 94, 100, 112, 114, 118, 120, 124, 132, 138, 148, 154, 168, 174, 178, 180, 184, 190, 192, 202, 204, 208, 220, 222, 232, 234, 250, 252, 258, 262, 264, 268, 280, 288, 294, 300, 310, 322, 324, 328, 330, 334, 342, 352, 358, 360, 364, 372, 378, 384, 390, 394, 400, 402, 408, 412, 418, 420, 430, 432, 442, 444, 450, 454, 462, 468, 472, 478, 484, 490, 492, 498, 504, 510, 528, 532, 534, 538, 544, 558, 562, 570, 574, 580, 582, 588, 594, 598, 600}. This set was obtained from the website http://math.mit.edu/ ̃primegaps/ maintained by Andrew Sutherland.


 SMALL GAPS BETWEEN PRIMES 7
Finally, we consider the case when k is large. For the rest of this section, any constants implied by asymptotic notation will be independent of k. By the Bombieri-Vinogradov theorem, we can take θ = 1/2 − ǫ. Thus, by Proposition 4.3, we have for k sufficiently large
(4.5) θMk
2 ≥ (1
4−ǫ
2
)(log k − 2 log log k − 2).
We choose ǫ = 1/k, and see that θMk/2 > m if k ≥ Cm2e4m for some absolute constant C (independent of m and k). Thus, for any admissible set H = {h1, . . . , hk} with k ≥ Cm2e4m, at least m + 1 of the n + hi must be prime for infinitely many integers n. We can choose our set H to be the set {pπ(k)+1, . . . , pπ(k)+k} of the first k primes which are greater than k. This is admissible, since no element is a multiple of a prime less than k (and there are k elements, so it cannot cover all residue classes modulo any prime greater than k.) This set has diameter pπ(k)+k − pπ(k)+1 ≪ k log k. Thus lim infn(pn+m − pn) ≪ k log k ≪ m3e4m if we take k = ⌈Cm2e4m⌉. This gives Theorem 1.1. We can now establish Theorem 1.2 by a simple counting argument. Given m, we let k = ⌈Cm2e4m⌉ as above. Therefore if {h1, . . . , hk} is admissible, then there exists a subset {h′
1, . . . , h′
m} ⊆ {h1, . . . , hk} with the property that there are infinitely many integers n for which
all of the n + h′
i are prime (1 ≤ i ≤ m). We let A2 denote the set formed by starting with the given set A = {a1, . . . , ar}, and for each prime p ≤ k in turn removing all elements of the residue class modulo p which contains the fewest integers. We see that #A2 ≥ r ∏
p≤k(1 − 1/p) ≫m r. Moreover, any subset of A2 of size k must be admissible, since it cannot cover all residue classes modulo p for any prime p ≤ k. We let s = #A2, and since r is taken sufficiently large in terms of m, we may assume that s > k.
We see there are (s
k
) sets H ⊆ A2 of size k. Each of these is admissible, and so contains at least one subset {h′
1, . . . , h′
m} ⊆ A2 which satisfies the prime m-tuples conjecture. Any
admissible set B ⊆ A2 of size m is contained in (s−m
k−m
) sets H ⊆ A2 of size k. Thus there are
at least (s
k
)(s−m k−m
)−1 ≫m sm ≫m rm admissible sets B ⊆ A2 of size m which satisfy the prime
m-tuples conjecture. Since there are ( r
m
) ≤ rm sets {h1, . . . , hm} ⊆ A, Theorem 1.2 holds. We are left to establish Propositions 4.1 and 4.3.
5. Selberg sieve manipulations
In this section we perform initial manipulations towards establishing Proposition 4.1. These arguments are multidimensional generalizations of the sieve arguments of [3]. In particular, our approach is based on the elementary combinatorial ideas of Selberg. The aim is to introduce a change of variables to rewrite our sums S 1 and S 2 in a simpler form. Throughout the rest of the paper we assume that the primes have a fixed level of distribution θ, and R = Nθ/2−δ. We restrict the support of λd1,...,dk to tuples for which the product d = ∏k
i=1 di
is less than R and also satisfies (d, W) = 1 and μ(d)2 = 1. We note that the condition μ(d)2 = 1 implies that (di, d j) = 1 for all i , j.
Lemma 5.1. Let
yr1,...,rk = (
k
∏
i=1
μ(ri)φ(ri)) ∑
d1,...,dk
ri |di ∀i
λd1,...,dk
∏k
i=1 di
.


 8 JAMES MAYNARD
Let ymax = supr1,...,rk |yr1,...,rk |. Then
S1 = N
W
∑
r1,...,rk
y2
r1,...,rk
∏k
i=1 φ(ri) + O
( y2
maxφ(W)kN(log R)k
W k+1 D0
).
Proof. We expand out the square, and swap the order of summation to give
(5.1) S 1 =
∑
N≤n<2N
n≡v0 (mod W)
(∑
di |n+hi ∀i
λd1,...,dk
)2 =
∑
d1 ,...,dk
e1 ,...,ek
λd1,...,dk λe1,...,ek
∑
N≤n<2N
n≡v0 (mod W)
[di ,ei ]|n+hi ∀i
1.
We recall that here, and throughout this section, we are using [a, b] to denote the least common multiple of a and b. By the Chinese remainder theorem, the inner sum can be written as a sum over a single residue class modulo q = W ∏k
i=1[di, ei], provided that the integers W, [d1, e1], . . . , [dk, ek] are pairwise coprime. In this case the inner sum is N/q + O(1). If the integers are not pairwise coprime then the inner sum is empty. This gives
S1 = N
W
∑′
d1,...,dk
e1 ,...,ek
λd1,...,dk λe1,...,ek
∏k
i=1[di, ei] + O
( ∑′
d1,...,dk
e1,...,ek
(5.2) |λd1,...,dk λe1,...,ek |),
where ∑′ is used to denote the restriction that we require W, [d1, e1], . . . , [dk, ek] to be pairwise coprime. To ease notation we will put λmax = supd1,...,dk |λd1,...,dk |. We now see that since λd1,...,dk
is non-zero only when ∏k
i=1 di < R, the error term contributes
(5.3) ≪ λ2
max
(∑
d<R
τk(d)
)2 ≪ λ2
maxR2(log R)2k,
which will be negligible. In the main sum we wish to remove the dependencies between the di and the ej variables. We use the identity
(5.4) 1
[di, ei] = 1
diei
∑
ui |di ,ei
φ(ui)
to rewrite the main term as
(5.5) N
W
∑
u1 ,...,uk
(
k
∏
i=1
φ(ui)) ∑′
d1,...,dk
e1,...,ek
ui |di ,ei ∀i
λd1,...,dk λe1,...,ek
(
∏k
i=1 di)(∏k
i=1 ei) .
We recall that λd1,...,dk is supported on integers d1, . . . , dk with (di, W) = 1 for each i and (di, d j) = 1 for all i , j. Thus we may drop the requirement that W is coprime to each of the [di, ei] from the summation, since these terms have no contribution. Similarly, we may drop the requirement that the di variables are all pairwise coprime, and the requirement that the ei variables are all pairwise coprime. Thus the only remaining restriction coming from the pairwise coprimality of W, [d1, e1], . . . , [dk, ek] is that (di, e j) = 1 for all i , j.


 SMALL GAPS BETWEEN PRIMES 9
We can remove the requirement that (di, ej) = 1 by multiplying our expression by ∑
si,j|di,ej μ(si, j).
We do this for all i, j with i , j. This transforms the main term to
(5.6) N
W
∑
u1,...,uk
(
k
∏
i=1
φ(ui)
)∑
s1,2 ,..., sk,k−1
(∏
1≤i, j≤k i, j
μ(si, j)
)∑
d1,...,dk
e1 ,...,ek
ui |di ,ei ∀i
si, j|di,e j∀i, j
λd1,...,dk λe1,...,ek
(
∏k
i=1 di)(∏k
i=1 ei) .
We can restrict the si, j to be coprime to ui and u j, because terms with si, j not coprime to ui or u j make no contribution to our sum. This is because λd1,...,dk = 0 unless (di, d j) = 1. Similarly we can further restrict our sum so that si, j is coprime to si,a and sb, j for all a , j and b , i. We
denote the summation over s1,2, . . . , sk,k−1 with these restrictions by ∑∗. We now introduce a change of variables to make the estimation of the sum more straightforward. We let
(5.7) yr1,...,rk = (
k ∏
i=1
μ(ri)φ(ri)) ∑
d1,...,dk
ri |di ∀i
λd1,...,dk
∏k
i=1 di
.
This change is invertible. For d1, . . . , dk with ∏k
i=1 di square-free we find that
∑
r1,...,rk
di|ri∀i
yr1,...,rk
∏k
i=1 φ(ri) =
∑
r1,...,rk
di |ri ∀i
(
k
∏
i=1
μ(ri)) ∑
e1 ,...,ek
ri |ei ∀i
λe1,...,ek
∏k
i=1 ei
=
∑
e1,...,ek
λe1,...,ek
∏k
i=1 ei
∑
r1,...,rk
di |ri ∀i
ri |ei ∀i
k
∏
i=1
μ(ri) = λd1,...,dk
∏k
i=1 μi(di)di
(5.8) .
Thus any choice of yr1,...,rk supported on r1, . . . , rk, with the product r = ∏k
i=1 ri square-free and satisfying r < R and (r, W) = 1, will give a suitable choice of λd1,...,dk. We let ymax = supr1,...,rk |yr1,...,rk |. Now, since d/φ(d) = ∑
e|d 1/φ(e) for square-free d, we find by taking r′ =
∏k
i=1 ri/di that
λmax ≤ sup
d1 ,...,dk
∏k
i=1 di square-free
ymax
(
k
∏
i=1
di
)∑
r1,...,rk
di|ri∀i
∏k
i=1 ri<R ∏k
i=1 ri square-free
(
k
∏
i=1
μ(ri)2
φ(ri)
)
≤ ymax sup
d1 ,...,dk
∏k
i=1 di square-free
(
k
∏
i=1
di
φ(di)
)∑
r′<R/ ∏k
i=1 di (r′,∏k
i=1 di)=1
μ(r′)2τk(r′)
φ(r′)
≤ ymax sup
d1,...,dk
∑
d| ∏k
i=1 di
μ(d)2
φ(d)
∑
r′<R/ ∏k
i=1 di (r′,∏k
i=1 di)=1
μ(r′)2τk(r′)
φ(r′)
≤ ymax
∑
u<R
μ(u)2τk(u)
(5.9) φ(u) ≪ ymax(log R)k.


 10 JAMES MAYNARD
In the last line we have taken u = dr′, and used the fact τk(dr′) ≥ τk(r′). Hence the error term O(λ2
maxR2(log N)2k) is of size O(y2
maxR2(log N)4k). Substituting our change of variables (5.7) into the main term (5.6), and using the above estimate for the error term, we obtain
S1 = N
W
∑
u1,...,uk
(
k
∏
i=1
φ(ui)
) ∑∗
s1,2 ,..., sk,k−1
(∏
1≤i, j≤k i, j
μ(si, j)
)(
k
∏
i=1
μ(ai)μ(bi)
φ(ai)φ(bi)
)
ya1,...,ak yb1,...,bk
+O
(
y2
(5.10) maxR2(log R)4k),
where a j = u j
∏
i, j s j,i and b j = u j
∏
i, j si, j. In these expressions we have used the fact that we have restricted si, j to be coprime to the other terms in the expression for ai and b j. For the same reason we may rewrite μ(a j) as μ(u j) ∏
i, j μ(si, j), and similarly for φ(a j), μ(b j) and φ(b j). This gives us
S1 = N
W
∑
u1,...,uk
(
k
∏
i=1
μ(ui)2
φ(ui)
) ∑∗
s1,2 ,..., sk,k−1
(∏
1≤i, j≤k i, j
μ(si, j)
φ(si, j)2
)
ya1,...,ak yb1,...,bk + O
(
y2
(5.11) maxR2(log R)4k).
We see that there is no contribution from si, j with (si, j, W) , 1 because of the restricted support of y. Thus we only need to consider si, j = 1 or si, j > D0. The contribution when si, j > D0 is
≪ y2
max N
W
(∑
u<R
(u,W )=1
μ(u)2
φ(u)
)k( ∑
si, j>D0
μ(si, j)2
φ(si, j)2
)(∑
s≥1
μ(s)2
φ(s)2
)k2−k−1 ≪ y2
maxφ(W)kN(log R)k
W k+1 D0
(5.12) .
Thus we may restrict our attention to the case when si, j = 1 ∀i , j. This gives
(5.13) S 1 = N
W
∑
u1,...,uk
y2
u1 ,...,uk
∏k
i=1 φ(ui) + O
( y2
maxφ(W)kN(log R)k
Wk+1 D0
+ y2
maxR2(log R)4k
)
.
We recall that R2 = Nθ−2δ ≤ N1−2δ and W ≪ Nδ, and so the first error term dominates. This gives the result.
We now consider S 2. We write S 2 = ∑k
m=1 S (m)
2 , where
(5.14) S (m)
2=
∑
N≤n<2N
n≡v0 (mod W)
χP(n + hm)
(∑
d1,...,dk
di |n+hi ∀i
λd1,...,dk
)2.
We now estimate S (m)
2 in a similar way to our treatment of S 1.
Lemma 5.2. Let
y(m)
r1,...,rk =
(
k
∏
i=1
μ(ri)g(ri)
)∑
d1,...,dk
ri |di ∀i dm=1
λd1,...,dk
∏k
i=1 φ(di) ,
where g is the totally multiplicative function defined on primes by g(p) = p − 2. Let y(m)
max =
supr1,...,rk |y(m)
r1,...,rk|. Then for any fixed A > 0 we have
S (m)
2= N
φ(W) log N
∑
r1,...,rk
(y(m)
r1,...,rk )2
∏k
i=1 g(ri) + O
( (y(m)
max)2φ(W)k−2N(log N)k−2
W k−1 D0
)+O
( y2
max N
(log N)A
).


 SMALL GAPS BETWEEN PRIMES 11
Proof. We first expand out the square and swap the order of summation to give
(5.15) S (m)
2=
∑
d1 ,...,dk
e1 ,...,ek
λd1,...,dk λe1,...,ek
∑
N≤n<2N
n≡v0 (mod W)
[di ,ei ]|n+hi ∀i
χP(n + hm).
As with S 1, the inner sum can be written as a sum over a single residue class modulo q = W
∏k
i=1[di, ei], provided that W, [d1, e1], . . . , [dk, ek] are pairwise coprime. The integer n + hm will lie in a residue class coprime to the modulus if and only if dm = em = 1. In this case the inner sum will contribute XN/φ(q) + O(E(N, q)), where
E(N, q) = 1 + sup
(a,q)=1
∣ ∣ ∣ ∣
∑
N≤n<2N
n≡a (mod q)
χP(n) − 1
φ(q)
∑
N≤n<2N
χP(n)
∣ ∣ ∣
(5.16) ∣,
XN =
∑
N≤n<2N
(5.17) χP(n).
If either one pair of W, [d1, e1], . . . , [dk, ek] share a common factor, or if either dm or em are not 1, then the contribution of the inner sum is zero. Thus we obtain
(5.18) S (m)
2 = XN
φ(W )
∑′
d1 ,...,dk
e1 ,...,ek
em =dm =1
λd1,...,dk λe1,...,ek
∏k
i=1 φ([di, ei]) + O
(∑
d1,...,dk
e1,...,ek
|λd1,...,dk λe1,...,ek |E(N, q)),
where we have written q = W ∏k
i=1[di, ei].
We first deal with the contribution from the error terms. From the support of λd1,...,dk, we see that we only need to consider square-free q with q < R2W. Given a square-free integer r, there are at most τ3k(r) choices of d1, . . . , dk, e1, . . . , ek for which W ∏k
i=1[di, ei] = r. We also
recall from (5.9) that λmax ≪ ymax(log R)k. Thus the error term contributes
(5.19) ≪ y2
max(log R)2k ∑
r<R2W
μ(r)2τ3k(r)E(N, r).
By Cauchy-Schwarz, the trivial bound E(N, q) ≪ N/φ(q), and our hypothesis that the primes have level of distribution θ, this contributes for any fixed A > 0
(5.20) ≪ y2
max(log R)2k( ∑
r<R2W
μ(r)2τ2
3k(r) N
φ(r)
)1/2( ∑
r<R2W
μ(r)2E(N, r))1/2 ≪ y2
max N
(log N)A .
We now concentrate on the main sum. As in the treatment of S 1 in the proof of Lemma 5.1, we rewrite the conditions (di, ej) = 1 by multiplying our expression by ∑
si,j|di,ej μ(si, j). Again
we may restrict si, j to be coprime to ui, u j, si,a and sb, j for all a , j and b , i. We denote the
summation subject to these restrictions by ∑∗. We also split the φ([di, ei]) terms by using the equation (valid for square-free di, ei)
(5.21) 1
φ([di, ei]) = 1
φ(di)φ(ei)
∑
ui |di ,ei
g(ui),


 12 JAMES MAYNARD
where g is the totally multiplicative function defined on primes by g(p) = p − 2. This gives us a main term of
(5.22) XN
φ(W )
∑
u1 ,...,uk
(
k
∏
i=1
g(ui)) ∑∗
s1,2 ,..., sk,k−1
(∏
1≤i, j≤k i, j
μ(si, j)) ∑
d1,...,dk
e1 ,...,ek
ui |di ,ei ∀i
si, j|di,e j∀i, j dm =em =1
λd1,...,dk λe1,...,ek
∏k
i=1 φ(di)φ(ei) .
We have now separated the dependencies between the e and d variables, so again we make a substitution. We let
(5.23) y(m)
r1,...,rk =
(
k
∏
i=1
μ(ri)g(ri)
)∑
d1,...,dk
ri |di ∀i dm=1
λd1,...,dk
∏k
i=1 φ(di) .
We note y(m)
r1,...,rk = 0 unless rm = 1. Substituting this into (5.22), we obtain a main term of
(5.24) XN
φ(W )
∑
u1,...,uk
(
k
∏
i=1
μ(ui)2
g(ui)
) ∑∗
s1,2 ,..., sk,k−1
(∏
1≤i, j≤k i, j
μ(si, j)
g(si, j)2
)
y(m)
a1,...,ak y(m)
b1,...,bk ,
where a j = u j
∏
i, j s j,i and b j = u j
∏
i, j si, j for each 1 ≤ j ≤ k. As before, we have replaced μ(a j) with μ(u j) ∏
i, j μ(s j,i) (and similarly for g(a j), μ(b j) and g(b j)). This is valid since terms with a j or b j not square-free make no contribution. We see the contribution from si, j , 1 is of size
≪ (y(m)
max )2 N
φ(W) log N
(∑
u<R
(u,W )=1
μ(u)2
g(u)
)k−1(∑
s
μ(s)2
g(s)2
)k(k−1)−1 ∑
si, j>D0
μ(si, j)2
g(si, j)2
≪ (y(m)
max)2φ(W)k−2N(log R)k−1
(5.25) Wk−1D0 log N .
Thus we find that
(5.26) S (m)
2 = XN
φ(W )
∑
u1 ,...,uk
(y(m)
u1,...,uk )2
∏k
i=1 g(ui) + O
( (y(m)
max)2φ(W)k−2N(log R)k−2
D0 W k−1
)+O
( y2
max N
(log N)A
).
Finally, by the prime number theorem, XN = N/ log N + O(N/(log N)2). This error term contributes
(5.27) ≪ (y(m)
max )2 N
φ(W)(log N)2
(∑
u<R
(u,W )=1
μ(u)2
g(u)
)k−1 ≪ (y(m)
max)2φ(W)k−2N(log R)k−3
Wk−1 ,
which can be absorbed into the first error term of (5.26). This completes the proof.
Remark. In our proof of Lemma 5.2 we only really require λd1,...,dk to be supported on d1, . . . , dk satisfying ∏
i, j di < R for all j instead of ∏k
i=1 di < R. For k ≥ 3, the numerical benefit of this extension is small and so we do not consider it further.
Remark. As our result relies on the Bombieri-Vinogradov theorem, the implied constant in the error term is not effectively computable. However, if we restrict the λd1,...,dk to be supported on di which are coprime to the largest prime factor of a possible exceptional modulus of a


 SMALL GAPS BETWEEN PRIMES 13
primitive character then we can make this error term (and all others in this paper) effective at the cost of a negligible error.
We now relate our new variables y(m)
r1,...,rk to the yr1,...,rk variables from S 1.
Lemma 5.3. If rm = 1 then
y(m)
r1,...,rk =
∑
am
yr1,...,rm−1,am,rm+1,...,rk
φ(am) + O
( ymaxφ(W) log R
W D0
).
Proof. We assume throughout the proof that rm = 1. We first substitute our expression (5.8) into the definition (5.23). This gives
(5.28) y(m)
r1,...,rk = (
k
∏
i=1
μ(ri)g(ri)) ∑
d1,...,dk
ri|di∀i dm=1
(
k
∏
i=1
μ(di)di
φ(di)
)∑
a1 ,...,ak
di|ai∀i
ya1,...,ak
∏k
i=1 φ(ai) .
We swap the summation of the d and a variables to give
(5.29) y(m)
r1,...,rk = (
k
∏
i=1
μ(ri)g(ri)) ∑
a1,...,ak
ri|ai∀i
ya1 ,...,ak
∏k
i=1 φ(ai)
∑
d1 ,...,dk
di |ai ,ri |di ∀i dm=1
k
∏
i=1
μ(di)di
φ(di) .
We can now evaluate the sum over d1, . . . , dk explicitly. This gives
y(m)
r1,...,rk = (
k
∏
i=1
μ(ri)g(ri)) ∑
a1,...,ak
ri|ai∀i
ya1 ,...,ak
∏k
i=1 φ(ai)
∏
i,m
μ(ai)ri
(5.30) φ(ai) .
We see that from the support of ya1,...,ak that we may restrict the summation over a j to (a j, W) = 1. Thus either a j = r j or a j > D0r j. For j , m, the total contribution from a j , r j is
≪ ymax
(
k
∏
i=1
g(ri)ri
)( ∑
a j>D0r j r j|a j
μ(a j)2
φ(a j)2
)( ∑
am<R
(am ,W )=1
μ(am)2
φ(am)
)∏
1≤i≤k
i, j,m
(∑
ri|ai
μ(ai)2
φ(ai)2
)
≪
(
k
∏
i=1
g(ri)ri
φ(ri)2
) ymaxφ(W) log R
W D0
≪ ymaxφ(W) log R
W D0
(5.31) .
Thus we find that the main contribution is when a j = r j for all j , m. We have
y(m)
r1,...,rk = (
k
∏
i=1
g(ri)ri
φ(ri)2
)∑
am
yr1 ,...,rm−1 ,am ,rm+1 ,...,rk
φ(am) + O
( ymaxφ(W) log R
W D0
(5.32) ).
We note that g(p)p/φ(p)2 = 1 + O(p−2). Thus, since the contribution is zero unless ∏k
i=1 ri is
coprime to W, we see that the product in the above expression may be replaced by 1 +O(D−1
0 ). This gives the result.


 14 JAMES MAYNARD
6. Smooth choice of y
We now choose suitable values for our y variables, and complete the proof of Proposition 4.1. We first give some comments to motivate our choice of the y variables, which we believe should be close to optimal. We wish to choose y so as to maximize the ratio of the main terms of S 2 and S 1. If we use Lagrangian multipliers to maximize this ratio (treating all error terms as zero) we arrive at the condition that
(6.1) λyr1,...,rk =
(
k
∏
i=1
φ(ri)
g(ri)
)
k
∑
m=1
g(rm)
φ(rm) y(m)
r1,...,rm−1,1,rm+1,...,rk
for some fixed constant λ. The y terms are supported on integers free of small prime factors, and for most integers r free of small prime factors we have g(r) ≈ φ(r) ≈ r, and so the above condition reduces to
(6.2) λyr1,...,rk ≈
k
∑
m=1
y(m)
r1,...,rm−1,1,rm+1,...,rk .
This condition looks smooth (it has no dependence on the prime factorization of the ri), and should be able to be satisfied if yr1,...,rk is a smooth function of the ri variables. Motivated by
the above, when the product r = ∏k
i=1 ri satisfies (r, W) = 1 and μ(r)2 = 1 we choose
(6.3) yr1,...,rk = F
(log r1
log R , . . . , log rk
log R
),
for some smooth function F : Rk → R, supported on Rk = {(x1, . . . , xk) ∈ [0, 1]k : ∑k
i=1 xi ≤
1}. As previously required, we set yr1,...,rk = 0 if the product r is either not coprime to W or is not square-free. With this choice of y, we can obtain suitable asymptotic estimates for S 1 and S 2.
We will use the following Lemma to estimate our sums S 1 and S 2 with this choice of y.
Lemma 6.1. Let A1, A2, L > 0. Let γ be a multiplicative function satisfying
0 ≤ γ(p)
p ≤ 1 − A1,
and
−L ≤
∑
w≤ p≤z
γ(p) log p
p − log z/w ≤ A2
for any 2 ≤ w ≤ z. Let g be the totally multiplicative function defined on primes by g(p) = γ(p)/(p−γ(p)). Finally, let G : [0, 1] → R be smooth, and let Gmax = supt∈[0,1](|G(t)|+|G′(t)|). Then
∑
d<z
μ(d)2g(d)G
(log d
log z
) = S log z
∫1
0
G(x)dx + OA1,A2(SLGmax),
where
S=
∏
p
(
1 − γ(p)
p
)−1(
1− 1
p
).
Here the constant implied by the ‘O’ term is independent of G and L.
Proof. This is [3, Lemma 4], with κ = 1 and slight changes to the notation.


 SMALL GAPS BETWEEN PRIMES 15
We now finish our estimations of S 1 and S (m)
2 , completing the proof of Proposition 4.1. We first estimate S 1.
Lemma 6.2. Let yr1,...,rk be given in terms of a smooth function F by (6.3), with F supported
on Rk = {(x1, . . . , xk) ∈ [0, 1]k : ∑k
i=1 xi ≤ 1}. Let
Fmax = sup
(t1 ,...,tk )∈[0,1]k
|F(t1, . . . , tk)| +
k
∑
i=1
| ∂F
∂ti
(t1, . . . , tk)|.
Then we have
S 1 = φ(W)kN(log R)k
Wk+1 Ik(F) + O
(F2
maxφ(W)kN(log R)k
W k+1 D0
),
where
Ik(F) =
∫1
0
···
∫1
0
F(t1, . . . , tk)2dt1 . . . dtk.
Proof. We substitute our choice (6.3) of y into our expression of S 1 in terms of yr1,...,rk given by Lemma 5.1. This gives
(6.4) S 1 = N
W
∑
u1,...,uk
(ui,u j)=1∀i, j (ui ,W )=1∀i
(
k
∏
i=1
μ(ui)2
φ(ui)
)
F
( log u1
log R , . . . , log uk
log R
)2 + O
(F2
maxφ(W)kN(log R)k
Wk+1 D0
).
We note that two integers a and b with (a, W) = (b, W) = 1 but (a, b) , 1 must have a common prime factor which is greater than D0. Thus we can drop the requirement that (ui, u j) = 1, at the cost of an error of size
≪ F2
max N
W
∑
p>D0
∑
u1 ,...,uk <R
p|ui,u j (ui ,W )=1∀i
k
∏
i=1
μ(ui)2
φ(ui)
≪ F2
max N
W
∑
p>D0
1
(p − 1)2
(∑
u<R
(u,W )=1
μ(u)2
φ(u)
)k ≪ F2
maxφ(W)kN(log R)k
W k+1 D0
(6.5) .
Thus we are left to evaluate the sum
(6.6)
∑
u1 ,...,uk
(ui ,W )=1∀i
(
k
∏
i=1
μ(ui)2
φ(ui)
)
F
(log u1
log R , . . . , log uk
log R
)2.
We can now estimate this sum by k applications of Lemma 6.1, dealing with the sum over each ui in turn. For each application we take
γ(p) =



1, p ∤ W,
0, otherwise,
(6.7)
L≪1+
∑
p|W
log p
(6.8) p ≪ log D0,


 16 JAMES MAYNARD
and A1 and A2 fixed constants of suitable size. This gives
∑
u1 ,...,uk
(ui ,W )=1∀i
(
k
∏
i=1
μ(ui)2
φ(ui)
)
F
(log u1
log R , . . . , log uk
log R
)2 = φ(W)k(log R)k
Wk Ik(F)
+O
(F2
maxφ(W)k(log D0)(log R)k−1
Wk
(6.9) ).
We now combine (6.9) with (6.4) and (6.5) to obtain the result.
Lemma 6.3. Let yr1,...,rk, F and Fmax be as described in Lemma 6.2. Then we have
S (m)
2 = φ(W)kN(log R)k+1
Wk+1 log N J(m)
k (F) + O
( F2
maxφ(W)kN(log R)k
Wk+1 D0
),
where
J(m)
k (F) =
∫1
0
···
∫1
0
(
∫1
0
F(t1, . . . , tk)dtm
)2dt1 . . . dtm−1dtm+1 . . . dtk.
Proof. The estimation of S (m)
2 is similar to the estimation of S 1. We first estimate y(m)
r1,...,rk . We
recall that y(m)
r1,...,rk = 0 unless rm = 1 and r = ∏k
i=1 ri satisfies (r, W) = 1 and μ(r)2 = 1, in
which case y(m)
r1,...,rk is given in terms of yr1,...,rk by Lemma 5.3. We first concentrate on this case
when y(m)
r1,...,rk , 0. We substitute our choice (6.3) of y into our expression from Lemma 5.3. This gives
y(m)
r1,...,rk =
∑
(u,W ∏k
i=1 ri)=1
μ(u)2
φ(u) F
( log r1
log R , . . . , log rm−1
log R , log u
log R , log rm+1
log R , . . . , log rk
log R
)
+O
( Fmaxφ(W) log R
W D0
(6.10) ).
We can see from this that y(m)
max ≪ φ(W)Fmax(log R)/W. We now estimate the sum over u in (6.10). We apply Lemma 6.1 with
γ(p) =



1, p ∤ W ∏k
i=1 ri,
0, otherwise,
(6.11)
L≪1+
∑
p|W ∏k
i=1 ri
log p
p≪
∑
p<log R
log p
p+
∑
p|W ∏k
i=1 ri
p>log R
log log R
(6.12) log R ≪ log log N,
and with A1, A2 suitable fixed constants. This gives us
y(m)
r1,...,rk = (log R) φ(W)
W
(
k
∏
i=1
φ(ri)
ri
)F (m)
r1,...,rk + O
( Fmaxφ(W) log R
W D0
(6.13) ),
where
(6.14) F(m)
r1,...,rk =
∫1
0
F
( log r1
log R , . . . , log rm−1
log R , tm, log rm+1
log R , . . . , log rk
log R
)
dtm.
Thus we have shown that if rm = 1 and r = ∏k
i=1 ri satisfies (r, W) = 1 and μ(r)2 = 1 then
y(m)
r1,...,rk is given by (6.13), and otherwise y(m)
r1,...,rk = 0. We now substitute this into our expression


 SMALL GAPS BETWEEN PRIMES 17
from Lemma 5.2, namely
(6.15) S (m)
2= N
φ(W) log N
∑
r1,...,rk
(y(m)
r1,...,rk )2
∏k
i=1 g(ri) + O
( (y(m)
max)2φ(W)k−2N(log N)k−2
W k−1 D0
)
+O
( y2
max N
(log N)A
).
We obtain
S (m)
2 = φ(W)N(log R)2
W2 log N
∑
r1,...,rk
(ri ,W )=1∀i
(ri,r j)=1∀i, j rm=1
(
k
∏
i=1
μ(ri)2φ(ri)2
g(ri)r2
i
)(F (m)
r1,...,rk )2 + O
( F2
maxφ(W)kN(log R)k
Wk+1 D0
).
(6.16)
We remove the condition that (ri, r j) = 1 in the same way we did when considering S 1. Instead of (6.5), this introduces an error which is of size
≪ φ(W)N(log R)2F2
max
W2 log N
(∑
p>D0
φ( p)4
g(p)2 p4
)( ∑
r<R
(r,W )=1
μ(r)2φ(r)2
g(r)r2
)k−1 ≪ F2
maxφ(W)kN(log N)k
W k+1 D0
.
(6.17)
Thus we are left to evaluate the sum
(6.18)
∑
r1,...,rm−1,rm+1,...,rk
(ri ,W )=1∀i
(∏
1≤i≤k
i, j
μ(ri)2φ(ri)2
g(ri)r2
i
)(F (m)
r1,...,rk )2.
We estimate this by applying Lemma 6.1 to each summation variable in turn. In each case we take
γ(p) =



1 − p2−3p+1
p3−p2−2p+1 , p ∤ W
0, otherwise,
(6.19)
L≪1+
∑
p|W
log p
(6.20) p ≪ log D0,
and A1, A2 suitable fixed constants. This gives
(6.21) S (m)
2 = φ(W)kN(log R)k+1
Wk+1 log N J(m)
k +O
(F2
maxφ(W)kN(log N)k
Wk+1 D0
),
where
(6.22) J(m)
k=
∫1
0
···
∫1
0
(
∫1
0
F(t1, . . . , tk)dtm
)2dt1 . . . dtm−1dtm+1 . . . dtk,
as required.
Remark. If F(t1, . . . , tk) = G(∑k
i=1 ti) for some function G, then Ik(F) and J(m)
k (F) simplify to
Ik(F) = ∫ 1
0 G(t)2tk−1dt/(k − 1)! and J(m)
k (F) = ∫ 1
0 (∫ 1
t G(v)dv)2tk−2dt/(k − 2)! for each m, which
is equivalent to the results obtained using the original GPY method using weights given by (2.3).
Remark. Tao gives an alternative approach to arrive at his equivalent of Proposition 4.1. His approach is to define λd1,...,dk in terms of a suitable smooth function f (t1, . . . , tk) as in (2.5). He then estimates the corresponding sums directly using Fourier integrals. This is somewhat


 18 JAMES MAYNARD
similar to the original paper of Goldston, Pintz and Yıldırım [5]. Our function F corresponds to f (t1, . . . , tk) differentiated with respect to each coordinate.
7. Choice of smooth weight for large k
In this section we establish part (3) of Proposition 4.3. Our argument here is closely related to that of Tao, who uses a probability theory proof. We let Sk denote the set of Riemann-integrable functions F : [0, 1]k → R supported on Rk = {(x1, . . . , xk) ∈ [0, 1]k : ∑k
i=1 xi ≤ 1} with Ik(F) , 0 and J(m)
k (F) , 0 for each m. We would like to obtain a lower bound for
(7.1) Mk = sup
F∈Sk
∑k
m=1 J(m)
k (F)
Ik(F) .
Remark. Let Lk denote the linear operator defined by
(7.2) LkF(u1, . . . , uk) =
k
∑
m=1
∫ 1−∑
i,m ui
0
F(u1, . . . , um−1, tm, um+1, . . . , uk)dtm
whenever (u1, . . . , uk) ∈ Rk, and zero otherwise. We expect that if F maximizes the ratio
∑k
m=1 J(m)
k (F)/Ik(F), then F is an eigenfunction for Lk, and the corresponding eigenvalue is the value of ratio at F. Unfortunately the author has not been able to solve the eigenvalue equation for Lk when k > 2.
We obtain a lower bound for Mk by constructing a function F = Fk which makes the ratio
∑k
m=1 J(m)
k (F)/Ik(F) large provided k is large. We choose F to be of the form
(7.3) F(t1, . . . , tk) =



∏k
i=1 g(kti), if ∑k
i=1 ti ≤ 1,
0, otherwise,
for some smooth function g : [0, ∞] → R, supported on [0, T ]. We see that with this choice F is symmetric, and so J(m)
k (F) is independent of m. Thus we only need to consider Jk = J(1)
k (F). Similarly we write Ik = Ik(F).
The key observation is that if the center of mass ∫ ∞
0 ug(u)2du/ ∫ ∞
0 g(u)2du of g2 is strictly
less than 1, then for large k we expect that the constraints ∑k
i=1 ti ≤ 1 to be able to be dropped at the cost of only a small error. This is because (by concentration of measure) the main contribution to the unrestricted integrals I′
k = ∫∞
0 ···∫ ∞
0
∏k
i=1 g(kti)2dt1 . . . dtk and
J′
k =∫∞
0 ···∫ ∞
0 (∫ ∞
0
∏k
i=1 g(kti)dt1)2dt2 . . . dtk should come primarily from when ∑k
i=1 ti is close
to the center of mass. Therefore we would expect the contribution when ∑k
i=1 ti > 1 to be
small if the center of mass is less than 1, and so Ik and Jk are well approximated by I′
k and J′
k
in this case. To ease notation we let γ = ∫
u≥0 g(u)2du, and restrict our attention to g such that γ > 0. We
have
(7.4) Ik =
(
Rk
F(t1, . . . , tk)2dt1 . . . dtk ≤ (
∫∞
0
g(kt)2dt
)k = k−kγk.
We now consider Jk. Since squares are non-negative, we obtain a lower bound for Jk if we restrict the outer integral to ∑k
i=2 ti < 1 − T/k. This has the advantage that, by the support of


 SMALL GAPS BETWEEN PRIMES 19
g, there are no further restrictions on the inner integral. Thus
(7.5) Jk ≥
(
t2 ,...,tk ≥0
∑k
i=2 ti≤1−T /k
(
∫ T/k
0
(
k
∏
i=1
g(kti)
)
dt1
)2dt2 . . . dtk.
We write the right hand side of (7.5) as J′
k − Ek, where
J′
k=
(
t2 ,...,tk ≥0
(
∫ T/k
0
(
k
∏
i=1
g(kti)
)
dt1
)2dt2 . . . dtk
=
(
∫∞
0
g(kt1)dt1
)2(
∫∞
0
g(kt)2dt
)k−1 = k−k−1γk−1(
∫∞
0
g(u)du
(7.6) )2,
Ek =
(
t2 ,...,tk ≥0
∑k
i=2 ti>1−T /k
(
∫ T/k
0
(
k
∏
i=1
g(kti))
dt1
)2dt2 . . . dtk
= k−k−1(
∫∞
0
g(u)du
)2 (
u2 ,...,uk ≥0
∑k
i=2 ui>k−T
(
k
∏
i=2
g(ui)2)
(7.7) du2 . . . duk.
First we wish to show the error integral Ek is small. We do this by comparison with a second moment. We expect the bound (7.13) for Ek to be small if the center of mass of g2 is strictly less than (k − T )/(k − 1). Therefore we introduce the restriction on g that
(7.8) μ =
∫∞
0 ug(u)2du
∫∞
0 g(u)2du < 1 − T
k.
To simplify notation, we put η = (k − T )/(k − 1) − μ > 0. If ∑k
i=2 ui > k − T then ∑k
i=2 ui >
(k − 1)(μ + η), and so we have
(7.9) 1 ≤ η−2( 1
k−1
k ∑
i=2
ui − μ)2.
Since the right hand side of (7.9) is non-negative for all ui, we obtain an upper bound for Ek if we multiply the integrand by η−2(∑k
i=2 ui/(k − 1) − μ)2, and then drop the requirement that
∑k
i=1 ui > k − T . This gives us
Ek ≤ η−2k−k−1(
∫∞
0
g(u)du
)2 ∫ ∞
0
···
∫∞
0
(
∑k
i=2 ui
k − 1 − μ)2(
k
∏
i=2
g(ui)2)
(7.10) du2 . . . duk.
We expand out the inner square. All the terms which are not of the form u2
j we can calculate explicitly as an expression in μ and γ. We find
∫∞
0
···
∫∞
0
(2 ∑
2≤i< j≤k uiu j
(k − 1)2 − 2μ ∑k
i=2 ui
k − 1 + μ2)(
k
∏
i=2
g(ui)2)
du2 . . . duk = −μ2γk−1
(7.11) k − 1 .


 20 JAMES MAYNARD
For the u2
j terms we see that u2
jg(u j)2 ≤ T u jg(u j)2 from the support of g. Thus
∫∞
0
···
∫∞
0
u2
j
(
k
∏
i=2
g(ui)2)
du2 . . . duk ≤ T γk−2
∫∞
0
(7.12) u jg(u j)2du j = μT γk−1.
This gives
Ek ≤ η−2k−k−1(
∫∞
0
g(u)du
)2( μT γk−1
k − 1 − μ2γk−1
k−1
) ≤ η−2μT k−k−1γk−1
k−1
(
∫∞
0
g(u)du
(7.13) )2.
Since (k − 1)η2 ≥ k(1 − T/k − μ)2 and μ ≤ 1, we find that putting together (7.4), (7.5), (7.6) and (7.13), we obtain
(7.14) kJk
Ik
≥ (∫ ∞
0 g(u)du)2
∫∞
0 g(u)2du
(1 − T
k(1 − T/k − μ)2
).
To maximize our lower bound (7.14), we wish to maximize ∫ T
0 g(u)du subject to the con
straints that ∫ T
0 g(u)2du = γ and ∫ T
0 ug(u)2du = μγ. Thus we wish to maximize the expression
(7.15)
∫T
0
g(u)du − α(
∫T
0
g(u)2du − γ) − β(
∫T
0
ug(u)2du − μγ)
with respect to α, β and the function g. By the Euler-Lagrange equation, this occurs when
∂
∂g (g(t) − αg(t)2 − βtg(t)2) = 0 for all t ∈ [0, T ]. Thus we see that
(7.16) g(t) = 1
2α + 2βt for 0 ≤ t ≤ T .
Since the ratio we wish to maximize is unaffected if we multiply g by a positive constant, we restrict our attention to functions g is of the form 1/(1 + At) for t ∈ [0, T ] and for some constant A > 0. With this choice of g we find that
∫T
0
g(u)du = log(1 + AT )
A,
∫T
0
g(u)2du = 1
A
(1 − 1
1 + AT
(7.17) ),
∫T
0
ug(u)2du = 1
A2
(
log(1 + AT ) − 1 + 1
1 + AT
(7.18) ).
We choose T such that 1 + AT = eA (which is close to optimal). With this choice we find that μ = 1/(1 − e−A) − A−1 and T ≤ eA/A. Thus 1 − T/k − μ ≥ A−1(1 − A/(eA − 1) − eA/k). Substituting (7.17) into (7.14), and then using these expressions, we find that
(7.19) kJk
Ik
≥A
1 − e−A
(
1− T
k(1 − T/k − μ)2
)≥A
(
1 − AeA
k(1 − A/(eA − 1) − eA/k)2
),
provided the right hand side is positive. Finally, we choose A = log k − 2 log log k > 0. For k sufficiently large we have
(7.20) 1 − T
k − μ ≥ A−1(1 − (log k)3
k−1
(log k)2
) > 0,
and so μ < 1 − T/k, as required by our constraint (7.8). This choice of A gives
(7.21) Mk ≥ kJk
Ik
≥ (log k − 2 log log k)(1 − log k
(log k)2 + O(1)
) ≥ log k − 2 log log k − 2
when k is sufficiently large.


 SMALL GAPS BETWEEN PRIMES 21
8. Choice of weight for small k
In this section we establish parts (1) and (2) of Proposition 4.3. In order to get a suitable lower bound for Mk when k is small, we will consider approximations to the optimal function F of the form
(8.1) F(t1, . . . , tk) =



P(t1, . . . , tk), if (t1, . . . , tk) ∈ Rk
0, otherwise,
for polynomials P. By the symmetry of ∑k
m=1 J(m)
k (F) and Ik(F), we restrict our attention
to polynomials which are symmetric functions of t1, . . . , tk. (If F satisfies LkF = λF then Fσ = F(σ(t1), . . . , σ(tk)) also satisfies this for every permutation σ of t1, . . . , tk. Thus the symmetric function which is the average of Fσ over all such permutations would satisfy this eigenfunction equation, and so we expect there to be an optimal function which is symmetric.) Any such polynomial can be written as a polynomial expression in the power sum polynomials P j = ∑k
i=1 t j
i.
Lemma 8.1. Let P j = ∑k
i=1 t j
i denote the jth symmetric power sum polynomial. Then we have
(
Rk
(1 − P1)aPb
jdt1 . . . dtk = a!
(k + jb + a)!Gb, j(k),
where
Gb, j(x) = b!
b
∑
r=1
(x
r
) ∑
b1 ,...,br ≥1
∑r
i=1 bi=b
r
∏
i=1
( jbi)!
bi!
is a polynomial of degree b which depends only on b and j.
Proof. We first show by induction on k that
(8.2)
(
Rk
(
1−
k
∑
i=1
ti
)a k
∏
i=1
tai
i dt1 . . . dtk = a! ∏k
i=1 ai!
(k + a + ∑k
i=1 ai)! .
We consider the integration with respect to t1. The limits of integration are 0 and 1 − ∑k
i=2 ti
for (t2, . . . , tk) ∈ Rk−1. By substituting v = t1/(1 − ∑k
i=2 ti) we find
∫ 1−∑k
i=2 ti
0
(1 −
k
∑
i=1
ti
)a(
k
∏
i=1
tai
i
)
dt1 = (
k
∏
i=2
tai
i
)(1 −
k
∑
i=2
ti
)a+a1+1 ∫ 1
0
(1 − v)ava1 dv
= a!a1!
(a + a1 + 1)!
(
k
∏
i=2
tai
i
)(1 −
k
∑
i=2
ti
(8.3) )a+a1+1.
Here we used the beta function identity ∫ 1
0 ta(1 − t)bdt = a!b!/(a + b + 1)! in the last line. We
now see (8.2) follows by induction. By the binomial theorem,
(8.4) Pb
j=
∑
b1,...,bk
∑k
i=1 bi=b
b!
∏k
i=1 bi!
k
∏
i=1
t jbi
i.


 22 JAMES MAYNARD
Thus, applying (8.2), we obtain
(8.5)
(
Rk
(1 − P1)aPb
jdt1 . . . dtk = b!a!
(k + a + jb)!
∑
b1,...,bk
∑k
i=1 bi=b
k
∏
i=1
( jbi)!
bi! .
For computations b will be small, and so we find it convenient to split the summation depending on how many of the bi are non-zero. Given an integer r, there are
(k r
)
ways of choosing r of b1, . . . , bk to be non-zero. Thus
(8.6)
∑
b1,...,bk
∑k
i=1 bi=b
k
∏
i=1
( jbi)!
bi! =
b
∑
r=1
(k
r
) ∑
b1 ,...,br ≥1
∑r
i=1 bi=b
r
∏
i=1
( jbi)!
bi! .
This gives the result.
It is straightforward to extend Lemma 8.1 to more general combinations of the symmetric power polynomials. In this paper we will concentrate on the case when P is a polynomial expression in only P1 and P2 for simplicity. We comment the polynomials Gb, j are not problematic to calculate numerically for small values of b. We now use Lemma 8.1 to obtain a manageable expression for Ik(F) and J(m)
k (F) with this choice of P.
Lemma 8.2. Let F be given in terms of a polynomial P by (8.1). Let P be given in terms of a polynomial expression in the symmetric power polynomials P1 = ∑k
i=1 ti and P2 = ∑k
i=1 t2
i by
P = ∑d
i=1 ai(1 − P1)bi Pci
2 for constants ai ∈ R and non-negative integers bi, ci. Then for each
1 ≤ m ≤ k we have
Ik(F) =
∑
1≤i, j≤d
aia j
(bi + b j)!Gci+cj,2(k)
(k + bi + b j + 2ci + 2c j)! ,
J(m)
k (F) =
∑
1≤i, j≤d
aia j
c ∑i
c′
1 =0
cj
∑
c′
2 =0
( ci
c′
1
)(c j
c′
2
) γbi,b j,ci,cj,c′
1 ,c′
2 Gc′
1 +c′
2,2(k − 1)
(k + bi + b j + 2ci + 2c j + 1)! ,
where
γbi,b j,ci,c j,c′
1 ,c′
2 = bi!b j!(2ci − 2c′
1)!(2c j − 2c′
2)!(bi + b j + 2ci + 2c j − 2c′
1 − 2c′
2 + 2)!
(bi + 2ci − 2c′
1 + 1)!(b j + 2c j − 2c′
2 + 1)! ,
and where G is the polynomial given by Lemma 8.1.
Proof. We first consider Ik(F). We have, using Lemma 8.1,
Ik(F) =
(
Rk
P2dt1 . . . dtk =
∑
1≤i, j≤d
aia j
(
Rk
(1 − P1)bi+bj Pci+cj
2 dt1 . . . dtk
=
∑
1≤i, j≤d
aia j
(bi + b j)!Gci+cj,2(k)
(8.7) (k + bi + b j + 2ci + 2c j)! .


 SMALL GAPS BETWEEN PRIMES 23
We now consider J(m)
k (F). Since F is symmetric in t1, . . . , tk we see that J(m)
k (F) is independent
of m, and so it suffices to only consider J(1)
k (F). We have
∫ 1−∑k
i=2 ti
0
(1 − P1)bPc
2dt1 =
c
∑
c′ =0
(c
c′
) (
k
∑
i=2
t2
i
)c′ ∫ 1−∑k
i=2 ti
0
(
1−
k
∑
i=1
ti
)bt2c−2c′
1 dt1
=
c
∑
c′ =0
(c
c′
)
(P′
2)c′ (1 − P′
1 )b+2c−2c′ +1
∫1
0
(1 − u)bu2c−2c′ du
=
c
∑
c′ =0
(c
c′
)
(P′
2)c′ (1 − P′
1)b+2c−2c′+1 b!(2c − 2c′)!
(8.8) (b + 2c − 2c′ + 1)! ,
where P′
1 = ∑k
i=2 ti and P′
2 = ∑k
i=2 t2
i . Thus
(
∫1
0
Fdt1
)2 = (
d
∑
i=1
ai
∫ 1−∑k
j=2 t j
0
(1 − P1)bi Pci
2 dt1
)2
=
∑
1≤i, j≤d
aia j
c ∑i
c′
1 =0
cj
∑
c′
2=0
( ci
c′
1
)(c j
c′
2
)
(P′
2)c′
1 +c′
2(1 − P′
1)bi+b j+2ci+2c j−2c′
1 −2c′
2 +2
× bi!b j!(2ci − 2c′
1)!(2c j − 2c′
2)!
(bi + 2ci − 2c′
1 + 1)!(b j + 2c j − 2c′
(8.9) 2 + 1)! .
Applying Lemma 8.1 again, we see that
(8.10)
(
Rk−1
(1 − P′
1)b(P′
2)c′ dt2 . . . dtk = b!
(k + b + c − 1)!Gc,2(k − 1).
Combining (8.9) and (8.10) gives the result.
We see from Lemma 8.2 that Ik(F) and ∑k
m=1 J(m)
k (F) can both be expressed as quadratic forms in the coefficients a = (a1, . . . , ad) of P. Moreover, these will be positive definite real quadratic forms. Thus in particular we find that
(8.11)
∑k
m=1 J(m)
k (F)
Ik(F) = aT A2a
aT A1a ,
for two rational symmetric positive definite matrices A1, A2, which can be calculated explicitly in terms of k for any choice of the exponents bi, ci. Maximizing expressions of this form has a known solution.
Lemma 8.3. Let A1, A2 be real, symmetric positive definite matrices. Then
aT A2a
aT A1a
is maximized when a is an eigenvector of A−1
1 A2 corresponding to the largest eigenvalue of
A−1
1 A2. The value of the ratio at its maximum is this largest eigenvalue.
Proof. We see that multiplying a by a non-zero scalar doesn’t change the ratio, so we may assume without loss of generality that aT A1a = 1. By the theory of Lagrangian multipliers, aT A2a is maximized subject to aT A1a = 1 when
(8.12) L(a, λ) = aT A2a − λ(aT A1a − 1)


 24 JAMES MAYNARD
is stationary. This occurs when (using the symmetricity of A1, A2)
(8.13) 0 = ∂L
∂ai
= ((2A2 − 2λA1)a)i,
for each i. This implies that (recalling that A1 is positive definite so invertible)
(8.14) A−1
1 A2a = λa.
It then is clear that aT A1a = λ−1aT A2a.
Proof of parts (1) and (2) of Proposition 4.3. To establish Proposition 4.3 we rely on some computer calculation to calculate a lower bound for Mk. We let F be given in terms of a polynomial P by (8.1). We let P be given by a polynomial expression in P1 = ∑k
i=1 ti and
P2 = ∑k
i=1 t2
i which is a linear combination of all monomials (1 − P1)bPc
2 with b + 2c ≤
11. There are 42 such monomials, and with k = 105 we can calculate the 42 × 42 rational symmetric matrices A1 and A2 corresponding to the coefficients of the quadratic forms Ik(F) and ∑k
m=1 J(m)
k (F). We then find3 that the largest eigenvalue of A−1
1 A2 is
(8.15) λ ≈ 4.0020697 . . . > 4.
Thus M105 > 4. This verifies part (2) of Proposition 4.3. We comment that by taking a rational approximation to the corresponding eigenvector, we can verify this lower bound by calculating the ratio ∑k
m=1 J(m)
k (F)/Ik(F) using only exact arithmetic. For part (1) of Proposition 4.3, we take k = 5 and
(8.16) P = (1 − P1)P2 + 7
10 (1 − P1)2 + 1
14 P2 − 3
14 (1 − P1).
With this choice we find that
(8.17) M5 ≥
∑k
m=1 J(m)
k (F)
Ik(F) = 1 417 255
708 216 > 2.
This completes the proof of Proposition 4.3.
9. Acknowledgements
The author would like to thank Andrew Granville, Roger Heath-Brown, Dimitris Koukoulopoulos and Terence Tao for many useful conversations and suggestions. The work leading to this paper was started whilst the author was a D.Phil student at Oxford and funded by the EPSRC (Doctoral Training Grant EP/P505216/1), and was finished when the author was a CRM-ISM postdoctoral fellow at the Universite ́ de Montre ́al.
References
[1] P. D. T. A. Elliott and H. Halberstam. A conjecture in prime number theory. In Symposia Mathematica, Vol. IV (INDAM, Rome, 1968/69), pages 59–72. Academic Press, London, 1970. [2] J. Friedlander and A. Granville. Limitations to the equi-distribution of primes. I. Ann. of Math. (2), 129(2):363–382, 1989. [3] D. A. Goldston, S. W. Graham, J. Pintz, and C. Y. Yıldırım. Small gaps between products of two primes. Proc. Lond. Math. Soc. (3), 98(3):741–774, 2009.
[4] D. A. Goldston, J. Pintz, and C. Y. Yıldırım. Primes in tuples. III. On the difference pn+ν − pn. Funct. Approx. Comment. Math., 35:79–89, 2006. [5] D. A. Goldston, J. Pintz, and C. Y. Yıldırım. Primes in tuples. I. Ann. of Math. (2), 170(2):819–862, 2009.
3An ancillary Mathematica R© file detailing these computations is available alongside this paper at www.arxiv.org.


 SMALL GAPS BETWEEN PRIMES 25
[6] D. A. Goldston and C. Y. Yıldırım. Higher correlations of divisor sums related to primes. III. Small gaps between primes. Proc. Lond. Math. Soc. (3), 95(3):653–686, 2007. [7] D. H. J. Polymath. A new bound for gaps between primes. Preprint. [8] A. Selberg. Collected papers. Vol. II. Springer-Verlag, Berlin, 1991. With a foreword by K. Chandrasekharan. [9] Y. Zhang. Bounded gaps between primes. Ann. of Math.(2), to appear.
Centre de recherches mathe ́matiques, Universite ́ de Montre ́al, Pavillon Andre ́-Aisenstadt, 2920 Chemin
de la tour, Room 5357, Montre ́al (Que ́bec) H3T 1J4
E-mail address: maynardj@dms.umontreal.ca