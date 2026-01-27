---
title: "THE DE BRUIJN\u2013NEWMAN CONSTANT IS NON-NEGATIVE"
authors:
  - "BRAD RODGERS"
  - "TERENCE TAO"
date: "2020-00-00 2020"
publication: "Forum of Mathematics, Pi"
doi: "10.1017/fmp.2020.6"
url: null
zotero:
  attachment_key: "C4TWKY7F"
  parent_key: "N9GCWPSB"
  item_id: 1818
  attachment_item_id: 1841
---

Forum of Mathematics, Pi (2020), Vol. 8, e6, 62 pages
doi:10.1017/fmp.2020.6 1
THE DE BRUIJN–NEWMAN CONSTANT IS NON-NEGATIVE
BRAD RODGERS1 and TERENCE TAO 2 1 Department of Mathematics and Statistics, Queen’s University, Kingston, ON K7L 3N6, Canada; email: brad.rodgers@queensu.ca 2 Department of Mathematics, UCLA, Los Angeles, CA 90095, USA; email: tao@math.ucla.edu
Received 25 January 2018; accepted 9 March 2020
Abstract
For each t ∈ R, we define the entire function
Ht (z) :=
∫∞
0
etu2 Φ(u) cos(zu) du,
where Φ is the super-exponentially decaying function
Φ(u) :=
∞ ∑
n=1
(2π 2n4e9u − 3π n2e5u ) exp(−π n2e4u ).
Newman showed that there exists a finite constant Λ (the de Bruijn–Newman constant) such that the zeros of Ht are all real precisely when t > Λ. The Riemann hypothesis is equivalent to the assertion Λ 6 0, and Newman conjectured the complementary bound Λ > 0. In this paper, we establish Newman’s conjecture. The argument proceeds by assuming for contradiction that Λ < 0 and then analyzing the dynamics of zeros of Ht (building on the work of Csordas, Smith and Varga) to obtain increasingly strong control on the zeros of Ht in the range Λ < t 6 0, until one establishes that the zeros of H0 are in local equilibrium, in the sense that they locally behave (on average) as if they were equally spaced in an arithmetic progression, with gaps staying close to the global average gap size. But this latter claim is inconsistent with the known results about the local distribution of zeros of the Riemann zeta function, such as the pair correlation estimates of Montgomery.
2010 Mathematics Subject Classification: 11M06 (primary)
c© The Author(s) 2020. This is an Open Access article, distributed under the terms of the Creative Commons Attribution licence (http://creativecommons.org/licenses/by/4.0/), which permits unrestricted re-use, distribution, and reproduction in any medium, provided the original work is properly cited.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 2
1. Introduction
Let H0 : C → C denote the function
H0(z) :=
1
8ξ
(1
2+
iz
2
)
, (1)
where ξ denotes the Riemann xi function
ξ(s) :=
s(s − 1)
2 π −s/2Γ
(s
2
)
ζ (s) (2)
and ζ is the Riemann zeta function. Then H0 is an entire even function with functional equation H0(z) = H0(z), and the Riemann hypothesis is equivalent to the assertion that all the zeros of H0 are real. It is a classical fact (see [29, page 255]) that H0 has the Fourier representation
H0(z) =
∫∞
0
Φ(u) cos(zu) du,
where Φ is the super-exponentially decaying function
Φ(u) :=
∞ ∑
n=1
(2π 2n4e9u − 3π n2e5u) exp(−π n2e4u). (3)
The sum defining Φ(u) converges absolutely for negative u also. From Poisson summation, one can verify that Φ satisfies the functional equation Φ(u) = Φ(−u) (that is, Φ is even). De Bruijn [4] introduced the more general family of functions Ht : C → C for t ∈ R by the formula
Ht (z) :=
∫∞
0
etu2 Φ(u) cos(zu) du. (4)
As noted in [11, page 114], one can view Ht as the evolution of H0 under the backward heat equation ∂t Ht (z) = −∂zz Ht (z). As with H0, each of the Ht is an entire even function with functional equation Ht (z) = Ht (z). From results of P ́olya [20], it is known that if Ht has purely real zeros for some t, then Ht′ has purely real zeros for all t′ > t. De Bruijn showed that the zeros of Ht are purely real for t > 1/2. Strengthening these results, Newman [17] showed that there is an absolute constant −∞ < Λ 6 1/2, now known as the De Bruijn–Newman constant, with the property that Ht has purely real zeros if and only if t > Λ. The Riemann hypothesis is then clearly equivalent to the upper bound Λ 6 0. Newman conjectured the complementary lower bound Λ > 0 and noted that this
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 3
conjecture asserts that if the Riemann hypothesis is true, it is only ‘barely so’. As progress towards this conjecture, several lower bounds on Λ were established; see Table 1.
Table 1. Previous lower bounds on Λ. Dates listed are publication dates. The final four results use the method of Csordas, Smith and Varga [11].
Lower bound on Λ References −∞ Newman 1976 [17] −50 Csordas–Norfolk–Varga 1988 [8] −5 te Riele 1991 [22] −0.385 Norfolk–Ruttan–Varga 1992 [18] −0.0991 Csordas–Ruttan–Varga 1991 [10] −4.379 × 10−6 Csordas–Smith–Varga 1994 [11] −5.895 × 10−9 Csordas–Odlyzko–Smith–Varga 1993 [9] −2.63 × 10−9 Odlyzko 2000 [19] −1.15 × 10−11 Saouter–Gourdon–Demichel 2011 [23]
We also mention that the upper bound Λ 6 1/2 of de Bruijn [4] was sharpened slightly by Ki, Kim and Lee [13] to Λ < 1/2. (In press: this bound has recently been improved to Λ 6 0.22 in [21].) See also [5, 25] on work on variants of Newman’s conjecture and [3, Ch. 5] for a survey. The main result of this paper is to affirmatively settle Newman’s conjecture:
THEOREM 1. One has Λ > 0.
We now discuss the methods of the proof. Starting from the work of CsordasSmith–Varga [11], the best lower bounds on Λ were obtained by exploiting the following repulsion phenomenon: if Λ was significantly less than zero, then adjacent zeros of H0 (or of the Riemann ξ function) cannot be too close to each other (as compared with the other nearby zeros). See [11, Theorem 1] for a precise statement. In particular, a negative value of Λ gives limitations on the quality of ‘Lehmer pairs’ [14], which roughly speaking refer to pairs of adjacent zeros of the Riemann zeta function that are significantly closer to each other than the average spacing of zeros at that level. The lower bounds on Λ in [9, 11, 19, 23] then follow from numerically locating Lehmer pairs of increasingly high quality. (See also [26] for a refinement of the Lehmer pair concept used in the above papers.) In principle, one could settle Newman’s conjecture by producing an infinite sequence of Lehmer pairs of arbitrarily high quality. As suggested
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 4
in [19], we were able to achieve this under the Gaussian Unitary Ensemble (GUE) hypothesis on the asymptotic distribution of zeros of the Riemann zeta function; we do not detail this computation here as it is superseded by our main result. (A sketch of the argument may be found at terrytao.wordpress.com/2018/01/20.) However, without the GUE hypothesis, the known upper bounds on narrow gaps between zeros (for example, [7]) do not appear to be sufficient to make this strategy work, even if one assumes the Riemann hypothesis (which one can do for Theorem 1 without loss of generality). Instead, we return to the analysis in [11] and strengthen the repulsion phenomenon to a relaxation to local equilibrium phenomenon: if Λ is negative, then the zeros of H0 are not only repelled from each other but will nearly always be arranged locally as an approximate arithmetic progression, with the gaps between zero mostly staying very close to the global average gap that is given by the Riemann–von Mangoldt formula. (To illustrate the equilibrium nature of arithmetic progressions under backward heat flow, consider the entire functions Ft (z) := etu2 cos(zu) for some fixed real u > 0. These functions
all have zeros on the arithmetic progression {
2π (k +
1
2)
u : k ∈ Z} and solve the
backward heat equation ∂t Ft = −∂zz F.) To obtain the local relaxation to equilibrium under the hypothesis that Λ < 0 requires a sequence of steps in which we obtain increasingly strong control on the distribution of zeros of Ht for Λ < t 6 0 (actually for technical reasons, we will need to move t away from Λ as the argument progresses, restricting instead to ranges such as Λ/2 6 t 6 0 or Λ/4 6 t 6 0). The first step is to obtain Riemann–von Mangoldt type formulae for the number of zeros of Ht in an interval such as [0, T ] or [T, T + α], where T > 2 and 0 < α 6 o(T ). When t = 0, we can obtain asymptotics of T
4π log T
4π − T
4π + O(log T ) and
α
4π log T +o(log T ) by the classical Riemann–von Mangoldt formula and a result of Littlewood, respectively; this gives good control on the zeros down to length scales α 1. For Λ < t < 0, we were only able to obtain the weaker bounds of T
4π log T
4π − T
4π + O(log2 T ) and α
4π log T + o(log2 T ), respectively, down to
length scales α log T , but it turns out that these bounds still (barely) suffice for our arguments; see Section 3. A key input in the proof of the Riemann–von Mangoldt type formula will be some upper and lower bounds for Ht (x −i y) when y is comparable to log x; see Lemma 4 for a precise statement. The main tool used to prove these bounds is the saddle point method, in which various contour integrals are shifted until they resemble the integral for the gamma function, to which the Stirling approximation may be applied. It was shown in [11] that in the region Λ < t 6 0, the zeros x j (t) of Ht are simple, and furthermore evolve according to the system of ordinary differential
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 5
equations (ODEs)
∂t xk(t) = 2
∑
j: j6=k
1
xk(t) − x j (t) ; (5)
see Theorem 11 for a more precise statement. One can view this equation as describing the dynamics of a system of ‘particles’ x j , in which every pair of particles x j , xk experiences a repulsion that is inversely proportional to their separation. (We caution however that the dynamics here are not Newtonian in nature since (5) prescribes the velocity ∂t xk of each particle rather than the acceleration ∂2
t xk. Nevertheless we found the physical analogy to be helpful in locating the arguments used in this paper.) By refining the analysis in [11], we can obtain a more quantitative lower bound on the gap x j+1(t) − x j (t) between adjacent ‘particles’ (zeros), in particular establishing a bound of the form
log 1
x j+1(t) − x j (t) log2 j log log j
for all large j in the range Λ/2 6 t 6 0; see Proposition 13 for a more precise statement. While far from optimal, this bound almost allows one to define the Hamiltonian
H(t) :=
∑
j,k: j6=k
log 1
|x j (t) − xk(t)|
,
although in practice we will have to apply some spatial cutoffs in j, k to make this series absolutely convergent. For the sake of this informal overview, we ignore this cutoff issue for now. The significance of this quantity is that system (5) can (formally, at least) be viewed as the gradient flow for the Hamiltonian H(t). In particular, there is a formal monotonicity formula
∂t H(t) = −4E(t), (6)
where the energy E(t) is defined as
E(t) :=
∑
j,k: j6=k
1
|x j (t) − xk(t)|2 .
Again, in practice, one needs to apply spatial cutoffs to j, k to make this quantity finite, and one then has to treat various error terms arising from this cutoff, which among other things ‘renormalizes’ the summands 1
|x j (t)−xk (t)|2 so
that the renormalized energy vanishes when the zeros are arranged in the equilibrium state of an arithmetic progression; we ignore these issues for the current discussion. A further formal calculation indicates that E(t) is monotone nonincreasing in time (so that H(t) is formally convex in time, as one would expect for the gradient flow of a convex Hamiltonian). Exploiting (a variant
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 6
of) equation (6), we are able to control integrated energies that resemble the quantities ∫ 0
Λ/2 E(t) dt; see first the weak preliminary integrated energy bound in Proposition 15 and then the final integrated energy bound in Theorem 17. By exploiting local monotonicity properties of the energy (and using a pigeonholing argument of Bourgain [2]), we can then obtain good control (a truncated version) of the energy E(t) at time t = 0, which intuitively reflects the assertion that the ‘particles’ x j (t) are close to local equilibrium at time t = 0. This implies that the zeros of the Riemann zeta function behave locally like an arithmetic progression on the average. However, this can be ruled out by the existing results on the local distribution of zeros, such as pair correlation estimates of Montgomery [15]. As it turns out, it will be convenient to make use of a closely related estimate of Conrey, Ghosh, Goldston, Gonek and Heath-Brown [6]. It may be possible to use the methods of this paper to also address the generalized Newman conjecture introduced in [25], but we do not pursue this direction here.
REMARK 2. It is interesting to compare this with the results in [13, Theorem 1.14], which show that regardless of the value of Λ, the zeros of Ht will be spaced like an arithmetic progression on average for any positive t.
REMARK 3. In press: We note that in forthcoming work, Alex Dobner has found a proof that Λ > 0, which avoids the heat equation approach we have used here. Dobner’s approach instead relies on a Riemann–Siegel type approximation for Ht in order to demonstrate the existence of zeros off the critical line. There is also some very intriguing numerical work of Rudolph Dwars (see the comments to terrytao.wordpress.com/2018/12/28) that suggests that many of the zeros of Ht , t < 0 away from the critical line organize around deterministic curves.
1.1. Notation. Throughout the rest of the paper, we will assume for the sake of contradiction that Newman’s conjecture fails:
Λ < 0.
In particular, this implies the Riemann hypothesis (which, as mentioned previously, is equivalent to the assertion Λ 6 0). We will have a number of logarithmic factors appearing in our upper bounds. To avoid the minor issue of the logarithm occasionally being negative, we will use the modified logarithm
log+(x) := log(2 + |x|)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 7
for several of these bounds. We also use the standard branch of the complex logarithm, with imaginary part in the interval (−π, π], and the standard branch z1/2 := exp( 1
2 log z) of the square root, defined using the standard branch of the complex logarithm. Let Λ < t 6 0; then the zeros of Ht are all real and symmetric around the origin. It is a result of Csordas, Smith and Varga [11, Corollary 1] that the zeros are also distinct and avoid the origin. Thus we can express the zeros of Ht as (x j (t)) j∈Z∗, where Z∗ := Z\{0} are the nonzero integers,
0 < x1(t) < x2(t) < . . . ,
and x− j (t) = −x j (t) for all j > 1. For any real numbers j− 6 j+, we use [ j−, j+]Z∗ to denote the discrete interval
[ j−, j+]Z∗ := { j ∈ Z∗ : j− 6 j 6 j+}.
We use the usual asymptotic notation X Y , Y X , or X = O(Y ) to denote a bound of the form |X | 6 CY for some absolute constant C, and write X Y for X Y X . Note that as Λ is also an absolute constant, C can certainly depend on Λ; thus, for instance, |Λ| 1. If we need the implied constant C to depend on other parameters, we will indicate this by subscripts, thus, for instance, X = Oκ (Y ) denotes the estimate |X | 6 Cκ Y for some C depending on κ. If the quantities X, Y depend on an asymptotic parameter such as T , we write X = oT →∞(Y ) to denote a bound of the form |X | 6 c(T )Y , where c(T ) is a quantity that goes to zero as T → ∞. For X and Y depending on an asymptotic parameter T , we will also use the notation X / Y or X = O ̃ (Y ) for X Y logO(1) T in the last two sections of this paper. Furthermore, in sums that will appear which depend on a parameter T , we say that indices j, k are nearby, and write j ∼T k if one has 0 < | j − k| < (T 2 + | j | + |k|)0.1.
We will use a marked sum to indicate principle value summation:
′ ∑
j
· · · = Jli→m∞
∑
| j|6J
··· .
In cases where there is any chance of confusion for the range of summation, we record the index being summed and use a colon to indicate its range; for example, we write ∑
j: j6=k to indicate that the summation is over j , and j is to not equal k (where k is fixed outside the sum). Semicolons are used to separate additional conditions. We use the phrase for almost every t throughout this paper to denote that a relation holds for all t except a set of null Lebesgue measure.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 8
2. Asymptotics of Ht
In this section, we establish some upper and lower bounds on Ht (z) and its logarithmic derivative H′
t
Ht (z). We will be able to obtain reasonable upper bounds
in the regime where z = x − i y with y = O(log+ x), and obtain more precise asymptotics when y log+ x (as long as the ratio y/ log+ x is large enough); this will be the key input for the Riemann–von Mangoldt type asymptotics in the next section. More precisely, we show the following.
LEMMA 4. Let z = x − iκ log+ x for some x > 0 and 0 6 κ 6 C, and let Λ < t 6 0. Then one has
Ht (z) exp
(
−
πx
8 + OC (log2
+ x)
)
. (7)
(The reader is advised not to take the numerous factors of π ,
√
2 and so on appearing in this section too seriously, as the exact numerical values of these constants are not of major significance in the rest of the arguments.) Furthermore, there is an absolute constant C′ > 0 (not depending on C) such that if κ > C′, then one has the refinement
Ht (z) = exp
(
−
πx
8 + OC (log2
+ x)
)
, (8)
as well as the additional estimate
H
′
t
Ht
(z) =
i
4 log
( iz
4π
)
+ OC
( log+ x
x
)
, (9)
using the standard branch of the complex logarithm.
REMARK 5. With a little more effort, one could replace the hypothesis Λ < t here by −C < t; in particular (in contrast to the remaining arguments in this paper), these results are nonvacuous when Λ > 0. However, we will need to assume Λ < t in the application of these estimates in the next section, particularly with regard to the proof of (49). Our proof methods also allow for a more precise version of asymptotic (8) (as one might expect given the level of precision in (9)), but such improvements do not seem to be helpful for the rest of the arguments in this paper. In the t = 0 case, one can essentially obtain Dirichlet
series expansions for 1
H0(z) or H ′
0
H0 (z), which allow one to also obtain bounds such
as (8) or (9) when the imaginary part of z is much smaller than log+ x. However, in the t < 0 case, there does not appear to be any usable series expansions for
1
Ht (z) or H′
t
Ht (z) that could be used to prove (8) or (9). Instead, we will prove these
estimates by computing Ht (z) to a high degree of accuracy, which we can only
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 9
do when y is greater than or equal to a large multiple of log+ x in order to ensure that the series expansions we have for Ht (z) converge rapidly.
We begin by treating the easy case t = 0, in which we can exploit identity (1). We have the very crude bound
ζ (σ + i τ ) (1 + |τ |)O(1) (10)
whenever σ > 1/2 and τ ∈ R (this follows for instance from [29, Theorem 4.11]). In the region σ > 1/4, we also have the Stirling approximation (see for example, [1, 6.1.41])
Γ (σ + iτ ) = exp
((
σ
+ iτ −
1
2
)
log(σ + iτ ) − (σ + iτ )
+ log
√
2π + O
(1
|σ + iτ |
))
, (11)
where we use the standard branch of the logarithm; in particular,
Γ (σ + iτ ) exp
((
σ
−
1
2
)
log |σ + iτ | − τ arctan τ
σ
−σ
)
. (12)
As arctan τ
σ =π
2 sgn(τ ) + O( σ
σ
+|τ| ), we have in particular that
Γ (σ + iτ ) exp
(
−
π
2 |τ | + O(σ log+(|σ | + |τ |))
)
.
Inserting these bounds into (1) and (2), we obtain the crude upper bound
H0(x − i y) exp
(
−
π
|x|
8 + O((1 + y) log+(|x| + y))
)
(13)
for x ∈ R and y > 0. This gives the s = 0 case of (7). As is well known, when σ > 2 (say), we can improve (10) to
|ζ (σ + iτ )| 1
and so we obtain the improvement
H0(x − i y) = exp
(
−
π
|x|
8 + O((1 + y) log+(|x| + y))
)
when y > C′ log+ x (in fact, in this case it would suffice to have y > 4, say). This gives the s = 0 case of (8). Finally, from taking logarithmic derivatives of (1) and (2), one has
H
′
0
H0
(z) =
i
2
(1
s+
1
s−1 −
1
2 log π +
1
2
Γ
′
Γ
(s
2
)
+
ζ
′
ζ (s)
)
,
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 10
where s := 1
2 + iz
2 . From taking log-derivatives of (11) using the Cauchy integral formula, one has the well-known asymptotic
Γ
′
Γ
(s
2
)
= log s
2+O
(1
|s|
)
for the digamma function Γ ′
Γ , and from the Dirichlet series expansion ζ′
ζ (s) =
−
∑∞
n=1
Λ(n) ns
∑∞
n=2
log n
nRes , one can easily establish the bound
ζ
′
ζ (s) 1
|s|
in the regime C′ log+ x 6 y 6 C log x. Putting all this together, one obtains (9) in this case. Henceforth, we address the t < 0 case. We begin with the proof of the upper bound (7). Here it will be convenient to exploit the fundamental solution for the (backward) heat equation to relate Ht with H0. Indeed, for any t < 0, we have the classical heat equation (or Gaussian) identity
etu2 exp(i zu) =
1
√
4π
∫
R
e
−r2/4 exp(i (z + r |t |1/2)u) dr (14)
for any complex numbers z, u; replacing z, r by −z, −r and averaging, we conclude that
etu2 cos(zu) =
1
√
4π
∫
R
e
−r2/4 cos ((z + r |t |1/2)u) dr.
Multiplying by Φ(u), integrating u from 0 to infinity and using Fubini’s theorem, we conclude that
Ht (z) =
1
√
4π
∫
R
e
−r2/4 H0(z + r |t |1/2) dr. (15)
Applying (13), the triangle inequality and the hypothesis Λ < t 6 0, we conclude that
Ht (x − i y) exp
(
−
π
|x|
8 + O((1 + y) log+(|x| + y))
)
×
∫
R
exp
(
−
r2
4 + O((1 + y + |r |) log+ r )
)
dr.
Using (1 + |r |) log+ r 6 εr 2 + Oε(1) and y log+ r εr 2 + Oε(y2) for any absolute constant ε > 0, we have
−
r2
4 + O(|r |) + O((1 + y + |r |)(1 + log+ r )) 6 −
r2
8 + O((1 + y)2),
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 11
thus arriving at the bound
Ht (x − i y) exp
(
−
π
|x|
8 + O((1 + y) log+ |x| + (1 + y)2)
)
.
Since y = OC (log+ x), this gives (7). To prove the remaining two bounds (8) and (9), it is convenient to cancel off the t = 0 case that has already been established, and reduce to showing that
Ht
H0
(z) = exp (OC (log2
+ x)) (16)
and H ′
t
Ht
(z) −
H
′
0
H0
(z) C
log+ x
x (17)
when κ > C′. To prove these estimates, the heat equation approach is less effective due to the significant oscillation present in H0. Instead, we will use the method of steepest descent (also known as the saddle point method) to shift contours to where the phase is stationary rather than oscillating. We allow all implied constants to depend on C. We may assume that x is larger than any specified constant C′′ (depending on C) as the case x = OC (1) follows trivially from compactness, since the zeros of Ht for t > Λ are all real, so that Ht (z) is bounded away from zero in this region of interest. Now suppose that z = x − i y, where y = κ log+ x for some C′ 6 κ 6 C; in particular, C is large since C′ is. As Φ is even, we may write (4) as
Ht (z) =
1
2
∫
R
etu2 Φ(u)eizu du.
From (3) and Fubini’s theorem (which can be justified when t < 0), we conclude that
Ht (z) =
1
2
∞ ∑
n=1
2π 2n4 It (π n2, 9 + y + i x) − 3π n2 It (π n2, 5 + y + i x), (18)
where It (b, ζ ) denotes the oscillatory integral
It (b, ζ ) :=
∫
R
exp(tw2 − be4w + ζ w) dw, (19)
which is an absolutely convergent integral for t < 0 whenever Re b > 0. We therefore need to obtain good asymptotics on It (b, ζ ) for b > 1 and ζ in the region
Ω
:= {y + i x : x > C′′; C′ log+ x 6 y 6 2C log+ x}. (20)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 12
Observe that the phase tw2 − be4w + ζ w has a stationary point at the origin when 4b = ζ . In general, 4b will not equal ζ ; however, for any complex number w0 in
the strip
{
w0 ∈ C : 0 6 Im(w0) < π
8
}
, (21)
we see from shifting the contour in (19) to the horizontal line {w + w0 : w ∈ R} that we have the identity
It (b, ζ ) = exp(tw2
0 + ζ w0)It (be4w0 , ζ + 2tw0) (22)
whenever b > 0 (so that be4w0 has a positive real part). We will thus be able to reduce to the stationary phase case 4b = ζ if we can solve the equation
4be4w0 = ζ + 2tw0 (23)
in strip (21). This we do in the following lemma. (One could also write w0 explicitly in terms of the Lambert W -function as w0 = − ζ
2t + 1
4 W (− 8b
t exp(− 2ζ
t )), but we will not use this expression in this paper, and in fact will not explicitly invoke any properties of the W -function in our arguments.)
LEMMA 6. If b > 1 and ζ ∈ Ω, then there exists a unique w0 = w0(b, ζ ) in strip (21) such that (23) holds. Furthermore, we have the following estimates:
(i) Re(4be4w0 ) > 1.
(ii) (Precise asymptotic for small and medium b) If ζ = y + i x and b 6
x exp(100 x1/2
|t| ), then
w0 =
1
4 log x
4b + OR
(1
x
)
+i
(
π
8−
y
4x −
t log x
4b
8x + OR
C
(
log2
+x x 3/2
))
,
where the superscript in the O() notation indicates that these quantities are real-valued.
(iii) (Crude bound for huge b) If ζ = y + i x and b > x exp( x1/2
|t| ), then Rew0 is negative; in fact, we have
−Rew0 > 1
8 log+ b.
Proof. The function w0 7→ 4be4w0 − 2tw0 traverses the graph {a + i ( π|t|
4+
4be2a/|t|) : a ∈ R} on the upper edge { a
2|t |
+ iπ
8 : a ∈ R} of strip (21), while
the lower edge of the strip is of course mapped to the real axis. Since |t| 6 Λ
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 13
and C, C′ are large, the region Ω lies between these two curves, and so from the argument principle (and observing that the map w0 7→ 4be4w0 − 2tw0 sends the line segments {−R + iβ : 0 < β < π/8} and {R + iβ : 0 < β < π/8} well to the left and right of ζ , respectively, for R large enough), for every ζ ∈ Ω, there exists exactly one w0 in strip (21) such that 4be4w0 − 2tw0 = ζ , which is of course equivalent to (23). The uniqueness implies that the holomorphic function w0 7→ 4be4w0 − 2tw0 has a nonzero derivative at this value of w0. Now write ζ = y + i x as per (20), and write w0 = α + iβ for some α ∈ R and 0 < β < π/8. Taking real and imaginary parts in (23), we have the system of equations 4be4α cos 4β = y + 2tα (24)
and 4be4α sin 4β = x + 2tβ. (25)
To prove (i), suppose for contradiction that Re(4be4w0) < 1; thus
4be4α cos 4β 6 1. (26)
Since t, β = O(1), we see from (25) that 4be4α sin 4β x, and hence from sin2 4β + cos2 4β = 1, we have
4be4α x
and hence (since b > 1) α 6 1
4 log+ x + O(1). In particular, −2tα 6 |t|
2 log+ x +
O(1). Inserting this into (24) and using (26), one then has
y6
|t |
2 log+ x + O(1),
which contradicts (20) since |t| 6 Λ and C′ is large. Now we show (ii). From (25) and sin 4β 6 1, t, β = O(1), one has
4be4α > x − O(1)
and hence on taking logarithms (and using the fact that b > 1 and x is large)
α> 1
4 log x
4b − O
(1
x
)
. (27)
On the other hand, from squaring (24) and (25) and summing, we have
(4be4α)2 = (y + 2tα)2 + (x + 2tβ)2. (28)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 14
Crudely bounding x +2tβ = O(x), y = O(x), b > 1 and t = O(1), we conclude that
e8α x 2 + α2
, which implies that α 6 O(log+ x). From the hypothesis b 6 x exp(100 x1/2
|t| )
and (27), we also have α > −O(x1/2/t); thus tα x1/2. Returning to (28) and using 2tβ = O(1) and y x1/2, we conclude that
(4be4α)2 = x2 + O(x).
So on taking square roots
4be4α = x + O(1) (29)
and hence on taking logarithms, we have the matching upper bound
α6 1
4 log x
4b + O
(1
x
)
to (27). In particular,
y + 2tα = y +
t log x
4b
2 +O
(1
x
)
.
Inserting this and (29) into (24), we have
cos 4β =
y
x+
t log x
4b
2x + O
(1
x 3/2
)
and hence (by Taylor expansion of the arc cosine function)
4β =
π
2−
y
x−
t log x
4b
2x + OC
(
log2
+x x 3/2
)
,
giving (ii). Finally, we prove (iii). From identity (28) and crudely bounding y, tβ = O(x), we have (4be4α)2 x 2 + t 2|α|2
and hence either
e
−4α b
x or
e
−4α b
|t ||α|
.
Under the hypothesis b > x exp( x1/2
|t| ), so that 1/|t| and x are O(b1/10) (say), so
both options force −α > 1
8 log b as claimed.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 15
We combine the above lemma with the following asymptotic.
LEMMA 7. Let b be a complex number with Re b > 1. Then
It (b, 4b) =
√π
8 exp(−b)
(1
√
b
+O
(1
|b|3/2
))
(30)
using the standard branch of the square root.
Proof. One could establish this from Laplace’s method, but we will instead use the Stirling approximation (11). (We thank Alex Dobner for pointing out some issues in the original proof of this lemma and suggesting a repaired proof, which is reproduced here.) Writing
etw2
=
∫
R
e4iξw dμ(ξ )
, where μ is the Gaussian probability measure
dμ(ξ ) :=
2
√π |t|
e
−4ξ 2/|t|
of mean zero and variance |t|/8, and applying Fubini’s theorem, we obtain
It (b, 4b) =
∫
R
(∫
R
exp(−be4w + 4(b + i ξ )w) dw
)
dμ(ξ ).
Making the change of variables r = be4w (and contour shifting or analytic continuation) and the definition Γ (s) =
∫∞
0 e−r r s−1 dr of the Γ function, we see that
∫
R
exp(−be4w + 4(b + i ξ )w) dw =
1
4 exp(−(b + iξ ) log b)Γ (b + iξ )
and hence
It (b, 4b) =
1
4
∫
R
exp(−(b + iξ ) log b)Γ (b + iξ ) dμ(ξ ).
We divide the integral into regions |ξ | 6 10|t|1/2|b|1/2 and |ξ | > 10|t|1/2|b|1/2. By applying the Stirling approximation, the integral over the first region becomes
1
4
∫
|ξ |610|t|1/2|b|1/2
(
1+O
(1
|b + iξ |
)) √
2π
√b + iξ
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 16
× exp
(
(b + iξ ) log
(
1+
iξ
b
)
− b − iξ
)
dμ(ξ ).
Note that we may assume that |b| is sufficiently large so that |ξ | < |b|/2 in this region (the small |b| case of the lemma follows trivially from compactness), and
so we have √b1+iξ =
(
1+O
(
|ξ |
|b|
)) √1
b and (b + i ξ ) log(1 + iξ
b ) = iξ + O
(
|ξ |2
|b|
)
.
Substituting these expressions into the integrand, we get
√π
8b exp(−b)
∫
|ξ |610|t|1/2|b|1/2
(
1+O
( 1 + |ξ |2
|b|
))
dμ(ξ ),
and now the integral evaluates to 1 + O( 1
|b| ). Thus it will suffice to establish the tail bound
∫
|ξ |>10|t|1/2|b|1/2
exp(−(b + iξ ) log b)Γ (b + iξ ) dμ(ξ ) exp(−Re(b))|b|−3/2.
By applying the triangle inequality and bounding the integrand with
|exp(−(b + iξ ) log b)| 6 exp
(
−Re(b) log |b| +
π
2 (|b| + |ξ |)
)
and
|Γ (b + iξ )| 6 Γ (Re(b)) 6 exp(Re(b) log |b| − Re(b)),
we get the following upper bound:
exp
(
−Re(b) +
π
2 |b|
)2
√π |t|
∫
|ξ |>10|t|1/2|b|1/2
exp
(π
2 |ξ | −
4ξ 2
|t |
)
.
Now again we assume |b| is large enough so that we have π
2 |ξ | − 4ξ2
|t| 6 − ξ2
|t| for
all ξ in the given region, and hence the integral is bounded above by
exp
(
−Re(b) +
π
2 |b|
)2
√π |t |
∫
|ξ |>10|t|1/2|b|1/2
exp
(
−
ξ2
|t |
)
exp(−Re(b) − 10|b|)
(say), and the claim follows.
From the above two lemmas and (22), we have the asymptotic
It (b, ζ ) =
√π
8 exp(tw2
0 − be4w0 + ζ w0)
(1
√
be4w0
+O
(1
|be4w0 |3/2
))
(31)
for any b > 1 and ζ ∈ Ω, where w0 = w0(b, ζ ) is the quantity in Lemma 6.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 17
Now we can control sum (18). As before, we assume that z = x − i y, where y = κ log+ x for some C′ 6 κ 6 C. From (18), one has
Ht (x − i y) =
1
2
∞ ∑
n=1
Qt,n, (32)
where Qt,n is the quantity
Qt,n := 2π 2n4 It (π n2, 9 + y + i x) − 3π n2 It (π n2, 5 + y + i x).
We first consider the estimation of Qn in the main case when n is not too huge, in the sense that
n 6 x exp
(
100 x 1/2
|t |
)
. (33)
In this case, if we apply Lemma 6(ii) with ζ = 9 + y + i x and b = π n2, we have that the quantity w0 = w0,t,n arising in that lemma obeys the asymptotics
w0 =
1
4 log x
4π n2 + OR
(1
x
)
+i
(
π
8−
9+y
4x −
t log x
4π n2
8x + OR
C
(
log2
+x x 3/2
))
,
(34) which when combined with (23) gives
4be4w0 = i x + OC (x 1/2).
In particular, the factor 1
√
be4w0
+O
(
1
|be4w0 |3/2
)
in (31) can be expressed as
1
√i x/4 (1 + OC (x−1/2)),
and thus by (31),
|It (π n2, 9+y+i x)| =
√π
2x exp
(
Re
(
tw2
0−
ζ
4−
t w0
2 + ζ w0
)
+ OC
(x −1/2)
)
,
where we have again used (23). From (34) (and using t = O(1) and y = OC (log+ x) to bound some small error terms), we can calculate the quantity Re (tw2
0−ζ
4 − tw0
2 + ζ w0
) to be
t
16 log2 x
4π n2 −
tπ2
64 −
9+y 4−
t
8 log x
4π n2 +
9+y
4 log x
4π n2 −
πx
8
+
9+y 4+
t log x
4π n2
8 + OC
(x −1/2) ,
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 18
and thus on cancelling and gathering terms, we obtain
|It (π n2, 9 + y + i x)| =
(x
4π n2
) 9+y
4 Jt Kt,n exp(OC (x −1/2, ))
where Jt = Jt (x) and Kt,n = Kt,n(x) are the positive quantities
Jt :=
√π
2x exp
(t
16 log2 x
4π −
tπ2
64 −
πx
8
)
(35)
and
Kt,n := exp
(
−
t
4
(
log x
4π
)
log n +
t
4 log2 n
)
.
A similar computation gives
|It (π n2, 5 + y + i x)| =
(x
4π n2
) 5+y
4 Jt Kt,n exp (OC
(x −1/2)) .
In particular, we have the upper bound
Qt,n n4
(x
4π n2
) 9+y
4 Jt Kt,n
for 1 6 n 6 x exp(100 x1/2
|t| ), and for n = 1, we have the refinement
|Qt,1| = (2π 2 + OC (x −1/2))
(x
4π
) 9+y
4 Jt . (36)
Using the crude bound
Kt,b 6 exp
(
−
t
4
(
log x
4π
)
log n
)
6 n− t
4 log x ,
we conclude that
Qt,n n− 1+y
2 −t
4 log x |Qt,1|.
Since y > C′ log+ x, the 2 6 n 6 x exp(100 x1/2
|t| ) terms sum to O(|Qt,1|/x); thus
∑
n6x exp(100 x1/2
|t| )
Qt,n =
(
1 + OC
(1
x
))
Qt,1.
Also, from (35), we have
| Q t ,1 |
(x
4π
) 9+y
4 Jt = exp
(
−
πx
8 + OC (log2
+ x)
)
.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 19
Thus, to finish the proof of (8) (or (16)), one just needs to show that the tail ∑
n>x exp(100 x1/2
|t| ) Qt,n is negligible compared with the main term Qt,1 =
exp(− πx
8 + OC (log2
+ x)). Suppose now that n > x exp(100 x1/2
|t| ). If we now apply
Lemma 6(iii) with ζ = 9 + y + i x and b = π n2, and write w0 = α + iβ with 0 < β < π/8, we have that α is negative with
−α > 1
8 log n,
while from (31) and (23) (and Lemma 6(i)), we have
It (π n2, 9 + y + i x) exp
(
Re
(
tw2
0−
ζ
4−
t w0
2 + ζ w0
))
exp
(
−|t||α|2 −
|t ||α|
2 + OC (log2
+ x)
)
,
and similarly for It (π n2, 5+ y +i x). Since log n > 100 x1/2
|t| , we have |α| > 10 x1/2
|t |
and thus |t||α|2 > 10x1/2 log n.
In particular, n4 exp(−|t||α|2) exp(−9x1/2 log n) and thus
Qt,n exp(−8x1/2 log n + OC (log2
+ x))
(say). Summing, we conclude that
∑
n>x exp(100 x1/2
|t| )
Qt,n exp(−100x/|t|)
(say), which is certainly O(|Q1|/x). Inserting these bounds into (18), we conclude that
Ht (x − i y) =
(
1
2 + OC
(
log2
+x
x
))
Qt,1,
which already gives (7). Sending t to 0, taking absolute values, and then dividing using (36) and (35), we obtain after cancelling all the t-independent terms that
∣ ∣ ∣ ∣
Ht
H0
∣ ∣ ∣ ∣
(x − iy) =
(
1 + OC
(
log2
+x
x
))
exp
(t
16 log2 x
4π −
tπ2
64
)
.
Since the ratio Ht
H0 is holomorphic in the region of interest, we can thus find a
holomorphic branch of log Ht
H0 for which
Re log Ht
H0
(z) −
t
16 log2 z
4πi = −
tπ2
64 + OC
(
log2
+x
x
)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 20
for all z = x − i y in this region. Varying x, y by O(log+ x) (adjusting the constants C, C′, C′′ slightly as necessary) and using the Borel–Carath ́eodory theorem and the Cauchy integral formula, we conclude that
d
dz
(
log Ht
H0
(z) −
t
16 log2 z
4π i
)
= OC
( log+ x
x
)
,
which gives (17) after a brief calculation.
3. Riemann–von Mangoldt type formulae
For any Λ < t 6 0, the zeros of Ht are all real and simple [11, Corollary 1]. For any interval I ⊂ R, let Nt (I ) denote the number of zeros of Ht in I . The classical Riemann–von Mangoldt formula (see for example, [29, Theorem 9.4]), combined with (1), gives the asymptotic
N0([0, T ]) = Ψ (T ) + O(log+ T ) (37)
for all T > 0, where we use Ψ : R+ → R to denote the function
Ψ (T ) :=
T
4π log T
4π −
T
4π . (38)
(It is traditional to also insert the lower order term − 7
8 here, but this term will not
be of use in our analysis and will therefore be discarded. The factors of 4π are not of particular significance and may be ignored by the reader on a first read.) For future reference, we record the derivative of Ψ as
Ψ
′(T ) =
1
4π log T
4π ; (39)
in particular, Ψ is increasing for T > 4π. Applying (37) with T replaced by T + α and subtracting, we conclude from the mean value theorem that
N0([T, T + α]) =
α log+ T
4π + O(log+ T ) (40)
for all T > 0 and 0 6 α 6 C for any fixed C, where the implied constants in the asymptotic notation are allowed to depend on C. Because we are assuming the Riemann hypothesis (and hence the Lindelo ̈f hypothesis), one can improve this latter bound to
N0([T, T + α]) =
α log+ T
4π + oT →∞(log+ T ), (41)
a result of Littlewood (see [29, Theorem 13.6]). (Indeed, on the Riemann
hypothesis, one can improve the error term to O
( log+ T log+ log+ T
)
; see [29, Theorem
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 21
14.13]. However, we will not need this further refinement in this paper.) A key input in these bounds is a lower bound on |ζ (s)| when Re(s) is somewhat large, for example, between 2 and 3; this is easily obtained through the Dirichlet series identity 1
ζ(s) =
∑∞
n=1
μ(n)
ns that is valid in this region.
Define the classical location ξ j of the jth zero for j > 1 to be the unique quantity in (1, +∞) solving the equation
Ψ (ξ j ) = j, (42)
and extend this to negative j by setting ξ− j := −ξ j . (As with the quantity w0 introduced in Lemma 6, one could express ξ j explicitly in terms of the Lambert W function if desired as ξ j = 4π e exp(W ( j/e)), but we will not use this relation in this paper.) Clearly, ξ j are increasing in j. For future reference, we record the following bounds on ξ j .
LEMMA 8 (Spacing of the classical locations).
(i) For any j > 1, one has
ξ j = (1 + o| j|→∞(1)) 4π j
log+ j . (43)
In particular, ξ j
j
log+ j and log+ ξ j log+ j .
(ii) For any j, k ∈ Z∗, one has
|ξk − ξ j |
|k − j|
log+(|ξ j | + |ξk|) . (44)
(iii) If 1 6 j k, then one has the more precise approximation
ξk − ξ j =
4π(k − j)
log ξ j
+O
(
|k − j |2
j log2 ξ j
)
. (45)
Of course, the implied constant in the error term in (45) can depend on the implied constants in the hypothesis j k.
Proof. If j > 1, then from (38), one has
ξ j log+ ξ j = (1 + o j→∞(1))4π j, (46)
which implies that j 1/2 ξ j j (say), which implies that log+ ξ j log+ j ; substituting this back into (46) yields
ξj
j
log+ j .
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 22
This in turn implies that log+ ξ j = (1 + o j→∞(1)) log+ j , and using (46) one last time gives (42). Now we obtain (ii). If j, k have opposing sign, then (44) follows from (43), so by symmetry we may assume that j, k are both positive. If j is much larger than k or vice versa, then bound (44) follows from (43) and the triangle inequality, so we may now restrict attention to the case 1 6 j k. Estimates (44) and (45) are trivial for j = O(1), so we may assume j to be large. From (42), we have
Ψ (ξk) − Ψ (ξ j ) = k − j
and hence by the mean value theorem and (39), we have
1
4π log T
4π (ξk − ξ j ) = k − j
for some T between ξk and ξ j . From (43), we see that T ξ j , and so (44) follows. Furthermore, we can conclude that
T = ξ j + O(|ξk − ξ j |) = ξ j + O
(
|k − j|
log ξ j
)
and hence
log T = log ξ j + O
(
|k − j|
ξ j log ξ j
)
= log ξ j + O
(
|k − j|
j
)
and 1
log T =
1
log ξ j
+O
(
|k − j|
j log2 ξ j
)
,
giving (45).
Applying (37) to T = x j (0) for some j > 1, we conclude in particular that
Ψ (x j (0)) − Ψ (ξ j ) = O(log+ x j (0)).
From (39) and the mean value theorem, we conclude that
x j (0) = ξ j + O(1) (47)
for all j > 1, and hence for all j ∈ Z∗ by symmetry. (One may wish to treat the bounded case j = O(1) separately to avoid the minor issue that Ψ (T ) becomes decreasing for T < 1.) In particular, from (43) and the fact that x1(0) > 0, we conclude that
x j (0) j
log+ ξ j
j
log+ j
for all j > 1.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 23
In a similar vein, if 1 6 j < k 6 j + log+ j, then from applying (41) with T = x j (0) and α equal to (or slightly less than) xk(0) − x j (0), we have
k− j=
xk(0) − x j (0)
4π log+ ξ j + o j→∞(log+ ξ j )
and hence
xk(0) − x j (0) =
4π(k − j)
log+ ξ j
+ o j→∞(1).
Informally, this asserts that the zeros x j (0) behave like an arithmetic progression of spacing 4π
log+ ξj at spatial scales between o(1) and 1. (In fact, when combined with (47) and (45), we see that this behaviour persists for all scales between o(1) and o(ξ j ).) In this section, we use the asymptotics on Ht obtained in the previous section to establish analogous, but weaker, bounds for the zeros x j (t) of the functions Ht , in which we lose an additional logarithm factor in the error estimates.
THEOREM 9 (Riemann–von Mangoldt type formulae). Let Λ < t 6 0, T > 0, and let 0 6 α 6 C for some C > 0. Then one has
Nt ([0, T ]) = Ψ (T ) + O(log2
+ T ) (48)
and
Nt ([T , T + α log+ T ]) =
α log2
+T
4π + oT →∞(log2
+ T ). (49)
The decay rate in the oT→∞() error term is permitted to depend on C but is otherwise uniform in α.
Repeating the previous analysis, we conclude the following.
COROLLARY 10 (Macroscopic structure of zeros). Let Λ < t 6 0. Then one has
x j (t) = ξ j + O(log+ ξ j ) (50)
for all j ∈ Z∗; in particular,
x j (t) j
log+ ξ j
j
log+ j (51)
for all j > 1. We also have
xk(t) − x j (t) =
4π(k − j)
log+ ξ j
+ o j→∞(log+ ξ j ) (52)
whenever 1 6 j < k 6 j + log2
+ ξj.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 24
Informally, this corollary asserts that the zeros x j (t) behave like an arithmetic progression of spacing 4π
log+ ξj at spatial scales between o(log+ ξ j ) and o(ξ j ). This level of spatial resolution is worse by a factor of log+ ξ j than what one can achieve for x j (0), but will still (barely) be enough for our applications. We remark that a significantly sharper estimate (with an error term of just O(1) in the analogue of (48)) is available for any fixed t > 0; see [13, Theorem 1.4]. (In press: even sharper estimates have recently been obtained in [21, Theorem 1.5].) We now turn to the proof of the two bounds in Theorem 9.
Proof of (48). We make use of the argument principle in exactly the same manner as in the classical proof of the Riemann–von Mangoldt formula. By perturbing T slightly if necessary, we may assume that T is not a zero of Ht . Let κ > 0 be a sufficiently large absolute constant. Then the argument principle yields
Nt ([0, T ]) =
1
2π i
∫
Γ
H
′
t
Ht
(z) dz,
where Γ is the counterclockwise contour carved out by a straight line from iκ log+ 0 = iκ log 2 to −iκ log+ 0 = −iκ log 2, then along the curve ΓI parameterized by x − iκ log+ x for x ∈ [0, T ], then along the line ΓI I from T − iκ log+ T to T , then along the vertical line conjugate to ΓI I and the curve conjugate to ΓI , leading back to i log 2. As the integrand is odd, the integral along the line from iκ log+ 0 to −iκ log+ 0 vanishes. Using the symmetry Ht (z) = Ht (z), we thus have
Nt ([0, T ]) =
1
π Im
(∫
ΓI
+
∫
ΓI I
) H′
t
Ht
(z) dz.
From (9) and (39), one sees that
1 π
H
′
t
Ht
(z) =
d
dz (Ψ (i z)) + O
( log+ x
x
)
for z = x−iκ log+ x on ΓI (extending Ψ to the right half-plane using the standard branch of the logarithm), and hence by the fundamental theorem of calculus
1
π Im
∫
ΓI
H
′
t
Ht
(z) dz = ImΨ (iT + κ log+ T ) − Ψ (log+ 0) + O(log2
+ T)
= Ψ (T ) + O(log2
+ T ).
On the other hand, if we let θ be a phase so that eiθ Ht (T − iκ log+ T ) is real and
positive, then
∣ ∣ ∣ ∣
Im
∫
ΓI I
H
′
t
Ht
(z) dz
∣ ∣ ∣ ∣
6 π(m + 1),
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 25
where m is the number of zeros of Re eiθ Ht (z) along the contour ΓI I , since the left-hand side is the change in arg eiθ Ht (z) as z varies over this contour, and for each increment of π in the value of arg eiθ Ht (z), we must have that Re eiθ Ht (z) is zero for some z. Note that the number of zeros of ReHt (z) along this contour is the same as the number of zeros of
g(s) := 1
2 (e−iθ Ht (is + T ) + eiθ Ht (−is + T ))
as s ranges along the line from 0 to κ log+ T . Hence m is no more than the number of zeros m′ of g(s) in the disc of radius κ log+ T centred at κ log+ T . We can estimate the count m′ with the Jensen formula as follows. Let M be the maximum of g(s) in a disc centred at κ log+ T of radius 2κ log+ T . Using (7) and the conjugate symmetry of Ht (z), we have
M e−
π
8 T +O(log2
+ T).
Since from (8) we have g(κ log+ T ) = eiθ Ht (T − iκ log+ T ) = e−
π
8 T +O(log2
+ T),
it therefore follows from the Jensen formula (see for example, [16, Lemma 6.1]) that
m
′ log2
+ T.
This induces a corresponding bound on the integral of H′
t
Ht over ΓI I and therefore
establishes the claimed estimate for Nt ([0, T ]).
Proof of (49). We will use a ‘limiting profile argument’ (also known as a ‘compactness argument’ or ‘normal families argument’), in which one extracts and then studies a limit of suitably rescaled versions of a family of analytic functions to conclude asymptotic information about these functions. We remark that this sort of argument can also be used in a similar fashion to deduce the Lindel ̈of hypothesis from the Riemann hypothesis: see Theorem 1 of terrytao.wordpress.com/2015/03/01.
Suppose for contradiction that this claim failed; then there exists a sequence Tn → ∞, and bounded sequences Λ < tn 6 0 and 0 6 αn 6 C, as well as an ε > 0, such that
∣ ∣ ∣ ∣ ∣
Ntn ([Tn, Tn + αn log+ Tn]) −
αn log2
+ Tn
4π
∣ ∣ ∣ ∣ ∣
> ε log2
+ Tn (53)
for all n. By perturbing Tn slightly, we may assume that Htn does not vanish at Tn or Tn + αn.
Let κ > 0 be a sufficiently large absolute constant. By the hypothesis Λ < tn, the function Htn has no zeros in the lower half-plane. Thus we can define holomorphic functions Fn on the lower half-plane by the formula
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 26
Fn(z) :=
1
log2
+ Tn
log Htn (Tn + z log+ Tn)
Htn (Tn − iκ log+ Tn)
with the branch of the logarithm chosen so that Fn(−iκ) = 0. From (7), we see that Fn are uniformly bounded on any compact subset of the lower half-plane. Thus, by Montel’s theorem (see [24, Section 3.2]), we may pass to a subsequence and assume that Fn converge locally uniformly to a holomorphic function F on the lower half-plane; since Fn all vanish on −iκ, F does also. Then by the Cauchy integral formula, the derivatives
F
′
n(z) =
1
log+ Tn
H
′
tn
Htn
(Tn + z log+ Tn)
converge locally uniformly to F′. Comparing this with (9), we conclude that
F
′(z) = 1
4
whenever the imaginary part of z is sufficiently large and negative. By unique continuation, we thus have F′(z) = 1
4 for all z in the lower half-plane; as F
vanishes on −iκ, we thus have
F(z) =
z + iκ
4
on the lower half-plane. Since Fn converges locally uniformly to F, we conclude that
Htn (Tn + z log+ Tn) = Htn (Tn − iκ log+ Tn) exp
( z + iκ + on→∞(1)
4 log2
+ Tn
)
(54) uniformly for z in a compact subset of the lower half-plane. Similarly, since F′
n
converges locally to F, we have
H
′
tn
Htn
(Tn + z log+ Tn) =
1 + on→∞(1)
4 log+ Tn (55)
uniformly for z in a compact subset of the lower half-plane. Let δ > 0 be a small constant. As in the proof of (48), we can use the argument principle (and a rescaling) to write
Ntn ([Tn, Tn + αn log+ Tn])
=
log+ Tn
π Im
(∫
Γ I ,n
+
∫
ΓI I,n
+
∫
ΓI I I,n
) H′
tn
Htn
(Tn + z log+ Tn) d z,
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 27
where ΓI,n, ΓI I,n, ΓI I I,n trace the line segments from 0 to −i δ, from −i δ to αn − iδ and from αn − iδ to αn, respectively. By (55), the contribution of the
ΓI I,n integral is α+on→∞(1)+O(δ)
4π log2
+ Tn (we allow the decay rate in the on→∞(1) errors to depend on δ). Applying the Jensen formula argument used to prove (48), we see that the contribution of the ΓI,n integral is bounded in magnitude by
∫1
0
log |gn(δ + 2δe2πiα)| − log |gn(δ)| dα,
where
gn(s) := 1
2
(e−iθn Htn (Tn + is log+ Tn) + eiθn Htn (Tn − is log+ Tn)) ,
and the phase θn is chosen so that eiθn Htn (Tn − i δ log+ Tn) is real and positive. Applying (54) (and the functional equation Htn (z) = Htn (z)) when |Im(z)| >
√δ (say), and (7) (and the functional equation) otherwise, we conclude that the
ΓI,n integral is equal to (on→∞(1) + O(√δ)) log2
+ Tn. We have this similarly for the ΓI I I,n integral. Taking δ to be sufficiently small and n sufficiently large, we contradict (53).
4. Dynamics of zeros
As remarked in Section 1, the functions Ht solve a backward heat equation. As worked out in [11], this induces a corresponding dynamics on the zeros x j of Ht .
THEOREM 11 (Dynamics of zeros). For Λ < t 6 0, the zeros x j (t) depend in a continuously differentiable fashion on t for each j, with the equations of motion
∂t xk(t) = 2
′ ∑
j: j6=k
1
xk(t) − x j (t) (56)
for k ∈ Z∗ and Λ < t 6 0, where recall that the tick denotes principal value summation over j ∈ Z∗ (which will converge thanks to (50) and (43)).
Proof. This follows from [11, Lemma 2.4] (the continuity of the derivative following for instance from [11, Lemma 2.1]).
Informally, ODE (56) indicates that the zeros xk(t) will repel each other as one goes forward in time. On the other hand, if xk(t) are arranged (locally, at least) in an arithmetic progression, then ODE (56) suggests that the zeros will be
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 28
in equilibrium. If xk are not arranged in an arithmetic progression, and instead have some fluctuation in the spacing between zeros, then heuristically ODE (56) suggests that the zeros would move away from the more densely spaced regions and towards more sparsely spaced regions, thus converging towards the equilibrium of an arithmetic progression. This is the intuition behind the convergence to local equilibrium mentioned in Section 1. One can estimate the speed of this local convergence to equilibrium by the following heuristic calculation. Consider the zeros in a region [T, T +α] of space, where T > 0 is large and α is reasonably small (for example, α = O(log+ T )).
From Theorem 9 (or (43) and (50)), we see that we expect about α
4π log T zeros in
this interval, with an average spacing of 4π
log+ T . Suppose for the sake of informal discussion that there is some moderate fluctuation in this spacing, for instance, suppose that the left half of the interval contains about 1.5 α
8π log T zeros and the
right half contains only about 0.5 α
8π log+ T zeros. Then a back of the envelope
calculation suggests that for xk(t) near the middle of this interval, the right-hand
side of (56) would be positive and have magnitude α log+ T
α = log+ T . Since the
length of the interval is α, one may then predict that the time needed to relax to equilibrium is about α/ log+ T . Since we can evolve the flow for time |Λ| 1, one would expect to attain equilibrium at the final time t = 0 if the initial length scale α of the fluctuation obeys the bound α = oT →∞(log+ T ). Happily, this upper bound is precisely what asymptotic (52) gives, so we heuristically expect to (barely) be able to establish local equilibrium at time t = 0. Of course, one has to make this intuition more precise. Our strategy for doing so involves exploiting the formal gradient flow structure of ODE (56). (This strategy was loosely inspired by the work of Erd ̋os, Schlein and Yau [12] exploiting the Hamiltonian structure of Dyson Brownian motion to obtain local convergence to equilibrium since the equations for Dyson Brownian motion resemble that in (56) but with an additional Brownian motion term. Indeed, Dyson Brownian motion is the diffusion related to the Gibbs measure 1
Z e−βH
for the Hamiltonian studied here.) Indeed, one may formally write (56) as the gradient flow
∂t xk(t ) = −∂xk H((x j (t )) j∈Z∗ ),
where H is the formal ‘Hamiltonian’
H((x j ) j∈Z∗ ) :=
∑
j,k∈Z∗: j 6=k
log 1
|xk − x j|
,
where we ignore for this nonrigorous discussion the fact that the series defining H is not absolutely convergent. The Hamiltonian is convex, so one expects the
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 29
quantity
H(t) := H((x j (t)) j∈Z∗ ) =
∑
j,k∈Z∗: j 6=k
Hjk(t )
to be decreasing and convex in time, and for the state (x j (t)) j∈Z∗ to converge to a critical point of the Hamiltonian, where
Hjk(t) := log 1
|x j (t) − xk(t)|
(57)
denotes the Hamiltonian interaction between x j (t) and xk(t). Indeed, a formal calculation using (56) yields the identity
∂t H(t) = −4E(t),
where E is the ‘energy’
E(t) :=
∑
k,k′∈Z∗: k6=k′
Ekk′ (t )
and
Ekk′ (t ) :=
1
|xk(t) − xk′ (t)|2 (58)
denotes the ‘interaction energy’ between xk(t) and xk′(t), and we once again ignore the issue that the series is not absolutely convergent. A further formal calculation using (56) again eventually yields
∂t E(t) = −2
∑
k,k′∈Z∗: k6=k′


2
|xk(t ) − xk′ (t )|2
−
∑
k
′′∈Z∗: k′′6=k,k′
1
(xk′′ (t ) − xk(t ))(xk′′ (t ) − xk′ (t ))


2
,
suggesting that H(t) and E(t) are decreasing and that H(t) is convex, as claimed. In order to deal with the divergence of the infinite series appearing above, we will need to truncate the Hamiltonian and energy before differentiating them. The following lemma records some of the identities that arise when doing such truncations.
LEMMA 12 (Identities). For brevity, we suppress explicit dependence on the time parameter t ∈ (Λ, 0]. Let K ⊂ Z∗ be a finite set of some cardinality |K |. All summation indices such as i, j, k are assumed to lie in Z∗.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 30
(i) (Dynamics of a gap, cf. [11, Lemma 2.4]) If j, k ∈ Z∗ are distinct, then
∂t (xk − x j ) =
4
xk − x j
− 2(xk − x j ) ∑
i: i6=k, j
1
(xi − xk)(xi − x j ) .
(ii) (Cross-energy inequality, cf. [11, Lemma 2.5]) One has
∂t
∑
k∈K ; j6∈K
Ejk > −
∑
k∈K ; j6∈K
8
(xk − x j )4
in the weak sense that
∑
k∈K ; j6∈K
E jk(t2) − E jk(t1) > −
∫ t2
t1
∑
k∈K ; j6∈K
8
(xk − x j )4 (t) dt
whenever Λ < t1 < t2 6 0.
(iii) (Energy identity) One has
∂t
∑
k,k′∈K : k6=k′
Ekk′ =
∑
j6∈K
k,k′∈K : k6=k′
4
(xk − xk′ )2(xk − x j )(xk′ − x j )
−2
∑
k,k′∈K : k6=k′


2
(xk − xk′ )2 −
∑
k
′′∈K : k′′6=k,k′
1
(xk′′ − xk )(xk′′ − xk′ )


2
.
(iv) (Virial identity) One has
∂t
∑
k,k′∈K : k6=k′
(xk − xk′ )2 = 4|K |2(|K | − 1)
−
∑
k,k′∈K : k6=k′
(xk − xk′ )2 ∑
j6∈K
4
(xk − x j )(xk′ − x j ) .
(The terminology here is in analogy with the virial identity in N -body classical gravitational physics; see for example, [27, Exercise 1.48].)
(v) (Hamiltonian identity) One has
∂t
∑
k,k′∈K : k6=k′
Hkk′ = −4
∑
k,k′∈K : k6=k′
Ekk′ + 2
∑
j6∈K
k,k′∈K : k6=k′
1
(x j − xk)(x j − xk′ ) .
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 31
A key point in identities (iii), (iv) and (v) is that if one ignores the ‘cross terms’ involving interactions between indices in K (representing some ‘local subsystem’ of particles) and indices outside of K (representing the ‘environment’ that subsystem interacts with), the right-hand side has a definite sign (negative in the case of (iii) and (v) and positive in the case of (iv)). This gives a number of useful ‘monotonicity formulae’ as long as cross terms are under control. As discussed above, many of these various monotonicity formulae reflect the formal convexity properties of the Hamiltonian H. With more effort, one can obtain a precise formula for the defect in the inequality in (ii); see [11, Lemma 2.5].
Proof. From (56), one has
∂t xk − ∂t x j =
2
xk − x j
−
2
x j − xk
+
∑
i: i6=k, j
2
xk − xi
−
2
xk − x j
,
which gives (i). Note that the series is now absolutely convergent thanks to (43) and (50). Now we prove (ii). By monotone convergence, it suffices to show that
∑
k∈K
j ∈[−R,R]Z∗ \K
E jk(t2) − E jk(t1) > −
∫ t2
t1
∑
k∈K
j ∈[−R,R]Z∗ \K
8
(xk − x j )4 (t) dt
for all Λ < t1 6 t2 6 0 and all sufficiently large R. By the fundamental theorem of calculus, it suffices to show that
∂t
∑
k∈K
j ∈[−R,R]Z∗ \K
Ejk > −
∑
k∈K
j ∈[−R,R]Z∗ \K
8
(xk − x j )4 .
We can expand the left-hand side as
−2
∑
k∈K
j ∈[−R,R]Z∗ \K
∂t (xk − x j )
(xk − x j )3 ,
which by (i) becomes
−
∑
k∈K
j ∈[−R,R]Z∗ \K
8
(xk − x j )4 + 4
∑
k∈K
j ∈[−R,R]Z∗ \K
i: i6= j,k
1
(xk − x j )2(xi − xk)(xi − x j )
and so it will suffice to show that
∑
k∈K
j ∈[−R,R]Z∗ \K
i: i6= j,k
1
(xk − x j )2(xi − xk)(xi − x j ) > 0.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 32
If R is large enough that [−R, R]Z∗ contains k, we can split this sum into three parts, depending on whether i ∈ K , i ∈ [−R, R]Z∗\K or i 6∈ [−R, R]Z∗. The contribution of the case i ∈ K can be rewritten as
∑
j6∈K
k,k′∈K : k6=k′
4(xk′ − x j )
(xk − x j )2(xk′ − x j )2(xk − xk′ ) ,
which equals
∑
j ∈[−R,R]Z∗
k,k′∈K : k6=k′
2
(xk − x j )2(xk′ − x j )2
after symmetrizing in k and k′, which is clearly non-negative. Similarly the contribution of the case i ∈ [−R, R]Z∗\K is
∑
k∈K
j, j ′∈[−R,R]Z∗ \K : j 6= j ′
2
(xk − x j )2(xk − x j′ )2 ,
which is also clearly non-negative. Finally, for i 6∈ [−R, R]Z∗, all summands are already non-negative. This gives (ii). For (iii), we can similarly expand the left-hand side as
−2
∑
k,k′∈K : k6=k′
∂t (xk − xk′ )
(xk − xk′ )3 ,
which by (i) becomes
−
∑
k,k′∈K : k6=k′
8
(xk − xk′ )4 + 4
∑
k,k′∈K :k6=k′ i: i6=k,k′
1
(xk − xk′ )2(xi − xk )(xi − xk′ ) .
To prove (iii), it thus suffices to establish the identity
∑
k,k′∈K : k6=k′


2
(xk − xk′ )2 −
∑
k
′′∈K : k′′6=k,k′
1
(xk′′ − xk )(xk′′ − xk′ )


2
=
∑
k,k′∈K : k6=k′
4
(xk − xk′ )4 − 2
∑
k,k′,k′′∈K : k,k′,k′′ distinct
×
1
(xk − xk′ )2(xk′′ − xk )(xk′′ − xk′ ) .
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 33
The left-hand side expands as
∑
k,k′∈K : k6=k′
4
(xk − xk′ )4 −
∑
k,k′∈K : k6=k′
4
(xk − xk′ )2
∑
k
′′∈K : k′′6=k,k′
1
(xk′′ − xk )(xk′′ − xk′ )
+
∑
k,k′∈K : k6=k′
∑
k
′′∈K : k′′6=k,k′
1
(xk′′ − xk )2(xk′′ − xk′ )2
+
∑
k,k′∈K : k6=k′
∑
k
′′,k′′′∈K : k′′6=k,k′
1
(xk′′ − xk )(xk′′ − xk′ )(xk′′′ − xk )(xk′′′ − xk′ ) .
The final sum can be rewritten as
∑
k,k′,k′′,k′′′∈K : k,k′,k′′,k′′′ distinct
(xk − xk′ )(xk′′ − xk′′′ )
(xk′′ − xk )(xk′′ − xk′ )(xk′′′ − xk )(xk′′′ − xk′ )(xk − xk′ )(xk′′ − xk′′′ ) .
The denominator is a Vandermonde determinant and is totally antisymmetric in k, k′, k′′, k′′′. All the monomials appearing in the numerator disappear upon antisymmetrization, so the final sum vanishes. To conclude the proof of (iii), it suffices to show that
∑
k,k′∈K : k6=k′
∑
k
′′∈K : k′′6=k,k′
1
(xk′′ − xk )2(xk′′ − xk′ )2
=
∑
k,k′∈K :k6=k′
2
(xk − xk′ )2
∑
k
′′∈K : k′′6=k,k′
1
(xk′′ − xk )(xk′′ − xk′ ) .
The difference between the left-hand and right-hand sides can be written as
∑
k,k′,k′′∈K : k,k′,k′′ distinct
(xk − xk′ )2 − 2(xk′′ − xk )(xk′′ − xk )
(xk′′ − xk )2(xk′′ − xk′ )2(xk − xk′ )2 .
The denominator is totally symmetric in k, k′, k′′, while the numerator symmetrizes to zero, giving the claim. Now we prove (iv). The left-hand side expands as
2
∑
k,k′∈K : k6=k′
(xk − xk′ )∂t (xk − xk′ ),
which by (i) becomes
8|K |(|K | − 1) − 4
∑
k,k′∈K : k6=k′
(xk − xk′ )2 ∑
i 6=k,k′
1
(xi − xk)(xi − xk′ ) .
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 34
It will thus suffice to show that
∑
k,k′,k′′∈K : k,k′,k′′ distinct
(xk − xk′ )2
(xk′′ − xk)(xk′′ − xk′ ) = −|K |(|K | − 1)(|K | − 2).
But the left-hand side can be written as
∑
k,k′,k′′∈K : k,k′,k′′ distinct
(xk − xk′ )3
(xk′′ − xk)(xk′′ − xk′ )(xk − xk′ ) = −|K |(|K | − 1)(|K | − 2).
The denominator is totally antisymmetric in k, k′, k′′. The numerator antisymmetrizes to −(xk′′ − xk)(xk′′ − xk′ )(xk − xk′ ), giving the claim. Finally we prove (v). The left-hand side expands as
−
∑
k,k′∈K : k6=k′
∂t (xk − xk′ )
xk − xk′
,
which by (i) becomes
−
∑
k,k′∈K : k6=k′
4
(xk − xk′ )2 + 2
∑
k,k′∈K : k6=k′
∑
i: i6=k,k′
1
(xi − xk)(xi − xk′ ) .
It thus suffices to show that the expression
∑
k,k′,k′′∈K :k,k′,k′′ distinct
1
(xk′′ − xk )(xk′′ − xk′ )
vanishes. But the summand antisymmetrizes to zero, giving the claim.
5. A weak bound on gaps
In order to analyse (truncated versions of) the Hamiltonian H(t) =
∑
j6=k Hjk(t), we will need some upper bounds on the individual terms Hjk(t). It was shown in [11, Corollary 1] that these quantities are finite (that is, the zeros are simple) when Λ < t 6 0. It turns out that by refining the analysis in [11] (and by narrowing the range of times t to the region Λ/2 6 t 6 0), one can establish a more quantitative lower bound.
PROPOSITION 13 (Lower bound on gaps). For any j ∈ Z∗ and any Λ/2 6 t 6 0, one has
max
k∈Z∗: k6= j
Hjk(t) (log2
+ j ) log+ log+ j. (59)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 35
The bound in (59) is probably not optimal, but for our application any bound that grows more slowly than (say) | j |0.1 as j → ∞ would suffice. To prove this proposition, we first need the following variant of a result in [11].
LEMMA 14. Let K be a finite subset of Z∗ of cardinality |K | > 2, and let Λ/2 6 t 6 0. Then
∑
k,k′∈K : k6=k′
(xk(t) − xk′ (t ))2 |K |3
1+
∑
kj6∈∈KK E jk (t ) .
Informally, this lemma asserts that the gaps within K cannot be too small, unless there is also a small gap between an element of K and an element outside of K . The strategy will be to iterate this observation to show that a very small gap will therefore propagate until it contradicts (52).
Proof. Let A = A(t) and B = B(t) denote the functions
A(t) :=
∑
k,k′∈K : k6=k′
(xk(t ) − xk′ (t ))2
B(t) :=
∑
kj 6∈∈KK
Ekj (t ).
The function A(t) is continuously differentiable. The corresponding claim for B(t) is not obvious; however, the sum defining B(t) is uniformly convergent (thanks to (51)) and hence B(t) is at least continuous. From Lemma 12(ii), we have the lower bound
∂t′ B(t ′) > −8B(t ′)2
(cf. [11, Lemma 2.5]) in the weak sense for Λ < t′ 6 0. In particular, if there exists a time Λ < t− < t such that
sup
t
− 6t ′ 6t
B(t′) = B(t−) = 2B(t),
then we have
B(t) − B(t−) > −8B(t)2(t − t−),
which rearranges as
t − t− > 1
8B(t) .
By continuity, we conclude that B(t′) cannot attain or exceed the value 2B(t) anywhere in the interval (−Λ, t] ∩ (t − 1
8B(t) , t), that is to say that
B
′(t) < 2B(t)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 36
whenever
t−
1
8B(t) , Λ < t′ 6 t.
By hypothesis, this is a range of size at least
min
(Λ
2, 1
16 B(t )
)1
1 + B(t) .
On the other hand, for t′ in the above range, we see from Lemma 12(iv) that
∂t′ A(t′) = 4|K |2(|K | − 1) + O(B(t′) A(t′))
= 4|K |2(|K | − 1) + O(B(t) A(t′))
and hence by Gronwall’s inequality, one has
A(t) 4|K |2(|K | − 1)
1 + B(t) ,
giving the claim.
Now we fix a time Λ/2 6 t 6 0 and drop the dependence on t. For any finite set K ⊂ Z∗ with |K | > 2, set δ(K ) := maxk,k′∈K |xk − xk′ | to be the largest gap in K . Then ∑
k,k′∈K : k6=k′
(xk − xk′ )2 6 |K |2δ(K )2,
and so from the above lemma, we have
1+
∑
kj 6∈∈KK
Ekj > |K |−5δ(K )−2.
In particular, if δ(K ) 6 c|K |−5/2 for a sufficiently small absolute constant c > 0, then we have ∑
kj 6∈∈KK
Ekj > |K |−5δ(K )−2,
and hence by the pigeonhole principle, there exists k ∈ K such that
∑
j6∈K
Ekj |K |−6δ(K )−2.
From (52) and (58), we have
∑
j6∈K
Ekj 1 + (log2
+ ξk ) jm6∈iKn
|xk − x j |−2.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 37
We conclude that if δ(K ) 6 c|K |−3 for a sufficiently small c > 0, then there exists k ∈ K such that
(log2
+ ξk ) jm6∈iKn
|xk − x j |−2 |K |−6δ(K )−2
or equivalently
jm6∈iKn
|xk − x j | |K |3δ(K ) log+ ξk.
Now suppose that K is a discrete interval [k−, k+]Z∗ for some 1 < k− < k+. Then
jm6∈iKn
|xk − x j | > min(|xk− − xk−−1|, |xk+ − xk++1|),
and thus (assuming that δ(K ) 6 c|K |−3) we have
min(|xk− − xk−−1|, |xk+ − xk++1|) |K |3δ(K ) log+ k+,
which implies that
δ(K ′) |K |3 log(k+)δ(K ) (60)
whenever δ(K ) 6 c|K |−3, where K ′ is either the interval K ′ = [k− − 1, k+]Z∗ or K
′ = [k−, k+ + 1]Z∗. In either case, we call K ′ an enlargement of K . Now we can prove Proposition 13. By symmetry, we may assume j is positive. We can also assume j is large, as the claim follows from compactness for bounded j. As before, we suppress the dependence on t. It thus suffices to show that
log 1
|x j+1 − x j |
(log2 j ) log log j
for large positive j. By iterating (60) at most log j times starting from the interval K1 := [ j, j + 1]Z∗, we can find a sequence
[ j, j + 1]Z∗ = K1 ⊂ K2 ⊂ · · · ⊂ Kr
of discrete intervals Ki = [k−,i , k+,i ]Z∗ for some 1 6 r 6 log2
+ ξ j with the following properties:
(i) For each 1 6 i < r , Ki+1 an enlargement of Ki with δ(Ki+1) |Ki |3δ(Ki ) log+ k+,i .
(ii) Either δ(Kr ) > c|Kr |−3 or r + 1 > log2
+ ξj.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 38
Since |Ki | 6 r + 1 log2
+ ξ j log2 j and k+,i 6 j + r j , we have from property (i) that
δ(Ki+1) j log2 j δ(Ki )
for all 1 6 i < r , and hence
δ(Kr ) exp(O(log2 j log log j ))δ(K1).
On the other hand, from property (ii), using the bound |Kr | 6 r + 1 log2 ξ j in the first case and (52) and the pigeonhole principle in the second case, we have
δ(Kr ) log−6 ξ j log−6 j.
Combining the two estimates, we obtain the claim.
6. A weak bound on integrated energy
In addition to truncations of the Hamiltonian, we will also need to control truncations of the energy ∑
j6=k E jk(t). Although Proposition 13 provides some control on the summands here, it is too weak for our purposes (being of worse than polynomial growth in j, k), and we will need the following integrated bound that, while still weak, is at least of polynomial growth.
PROPOSITION 15 (Weak bound on integrated energy). Let J > 0. Then
∫0
Λ/2
∑
J 6 j<k62J
E jk (t ) dt J 2 logO(1)
+ J.
We will use this bound to justify an interchange of a derivative and an infinite series summation in the next section.
Proof. We may take J to be large, as the claim is trivial for J in the compact region J = O(1). For any discrete interval I , let Q I denote the quantity
Q I :=
∫0
Λ/2
∑
j,k∈I : j6=k
E jk(t) dt.
From (52), we have a crude lower bound
Q
[J,2J ]Z∗ J log−O(1) J
while from Proposition 13 we have an extremely crude upper bound
Q
[0.5J,3J]Z∗ exp(O(log2 J log log J )).
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 39
The ratio between Q[0.5J,3J]Z∗ and Q[J,2J]Z∗ is thus less than (1 + J −0.1)0.5J/J0.1 . By the pigeonhole principle, we can then therefore find an interval K := [J−, J+]Z∗ containing [ J, 2 J ]Z∗ and contained in [0.5 J + J 0.1, 3 J − J 0.1]Z∗ such that
Q K ′ 6 (1 + J −0.1)Q K , (61)
where K ′ := [ J− − J 0.1, J+ + J 0.1]Z∗ is a slight enlargement of K . Next, we apply Lemma 12(v) and use the fundamental theorem of calculus to obtain the identity
∑
k,k′∈K : k6=k′
Hkk′ (Λ/2) − Hkk′ (0)
= 4QK − 2
∫0
Λ/2
∑
j6∈K
k,k′∈K : k6=k′
1
(x j (t) − xk(t))(x j (t) − xk′ (t)) dt.
From Proposition 13, the left-hand side is O(J 2 logO(1) J ); thus
Q K J 2 logO(1) J +
∫0
Λ/2
∑
j6∈K k,k′∈[ J−, J+]Z∗ : k6=k′
1
(x j (t) − xk(t))(x j (t) − xk′ (t)) dt.
Using ab a2 + b2, we thus have
Q K J 2 logO(1) J +
∫0
Λ/2
∑
j6∈K k∈K
1
(x j (t) − xk(t))2 dt.
Using (52), the contribution to the integral of those j outside of K ′ may be crudely bounded by O(J 2 logO(1) J ) (in fact, one can improve this bound to O(J logO(1) J ) if desired, although this will not help us significantly here). The contribution of those j inside K ′ may be bounded by
Q K ′ − Q K 6 J −0.1 Q K ,
thanks to (61). We conclude that
Q K J 2 logO(1) J
, and the claim follows.
7. Strong control on integrated energy
As discussed previously, the strategy to establish convergence to local equilibrium is to study (a suitable variant of) the formal Hamiltonian
H(t) =
∑
j,k∈Z∗: j 6=k
Hjk(t )
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 40
and its derivatives, with the intention of controlling (suitable variants of) integrated energies such as
∫0
Λ/4
∑
j,k∈Z∗: j 6=k
E jk(t) dt.
Unfortunately, even with the bound just obtained in Proposition 13, the above expression is far from being absolutely convergent. To address this issue, we need to mollify and renormalize the Hamiltonian and the energy in a number of ways. We renormalize the inverse square function x 7→ 1
|x|2 for x 6= 0 that
appears in the definition of the energy interactions E jk(t) by introducing the modified potential
V (x) :=
1
|x|2 − 1 + 2(|x| − 1),
which (for positive x) is 1
x2 minus the linearization 1 − 2(x − 1) of that function
at x = 1. As 1
x2 is convex, V is non-negative, and one can verify the asymptotics
V (x) 1
|x|2 for |x| 6 1/2
V (x) (|x| − 1)2 for 1/2 < |x| 6 2
V (x) |x| for |x| > 2.
(62)
For any distinct j, k and any Λ/2 6 t 6 0, we define the renormalization
E ̃ jk(t) :=
1
|ξk − ξ j |2 V
( xk(t) − x j (t)
ξk − ξ j
)
of the interaction energy E jk(t); we observe that
E ̃ jk(t) = E jk(t) −
1
|ξk − ξ j |2 + 2 (xk(t) − ξk) − (x j (t) − ξ j )
(ξk − ξ j )3 . (63)
For any discrete interval I ⊂ Z∗, we define the renormalized energy
E ̃ I (t) :=
∑
j,k∈I : j6=k
E ̃ jk(t);
this is clearly a non-negative quantity that is nondecreasing in I . It can also be simplified up to negligible error as follows.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 41
LEMMA 16. If I = [I−, I+]Z∗ is a discrete interval and Λ/2 6 t 6 0, then
E ̃ I (t) =
( ∑
j,k∈I : j6=k
E jk(t) −
1
|ξk − ξ j |2
)
+ O(logO(1)
+ (|I−| + |I+|)).
Proof. By symmetry and the triangle inequality, we may assume without loss of generality that 0 6 I− 6 I+; we may then assume that I+ is large, as the claim is trivial for I+ in the compact region I+ = O(1). By (63), it suffices to show that
∑
j,k∈I : j6=k
(xk(t) − ξk) − (x j (t) − ξ j )
(ξk − ξ j )3 logO(1) I+.
We may desymmetrize the left-hand side as
2
∑
j∈I
(x j (t) − ξ j ) ∑
k∈I : k6= j
1
(ξk − ξ j )3 .
By (50), it thus suffices to show that
∑
j∈I
∣ ∣ ∣ ∣ ∣
∑
k∈I : k6= j
1
(ξk − ξ j )3
∣ ∣ ∣ ∣ ∣
logO(1) I+. (64)
Consider the inner sum ∑
k∈I : k6= j
1
(ξk−ξj )3 . From (44), we see that the contribution
to this inner sum of those k with |k − j| > 1
2 j (say) is O( logO(1) I+
j2
). For the
remaining range |k − j| < 1
2 j, we can use (45) to estimate
1
(ξk − ξ j )3 =
log3 ξ j (4π )3
1
(k − j )3 + O
( logO(1) I+
j (k − j )2
)
,
and so on summing we obtain
∑
k∈I : k6= j
1
(ξk − ξ j )3 =
log3 ξ j (4π )3
∑
k∈I : 0<|k− j|< 1
2j
1
(k − j )3 + O
( logO(1) I+
j
)
.
As k 7→ 1
k− j is odd around j, the sum on the right-hand side can be estimated as O( 1
max(| j−I−|,|I+− j|)2 ). Using this bound, we obtain (64).
In this section, we will establish the following significant improvement to Proposition 15.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 42
THEOREM 17. For any T > 0, one has
∫0
Λ/4
E ̃ [0.5T log T,3T log T ]Z (t ) dt = oT →∞(T log3
+ T ). (65)
The remainder of this section is devoted to a proof of Theorem 17. The claim is trivial for T in any compact region T = O(1), so we may assume without loss of generality that T is large. Recall the notation X / Y or X = O ̃ (Y ) for X Y logO(1) T introduced in the notation section of the paper; this will be convenient to use in the argument that follows. (Typically, when we use this notation, we will also have some sort of power gain T −c that will safely absorb all the logO(1) T factors.) Let ψT : Z∗ → R+ be the weight function
ψT ( j ) :=
(
1+
|j|
T log T
)−100
. (66)
This is a smooth positive weight that is mostly localized to the region j = O(T log T ) and fairly rapidly decaying away from this region. We introduce the smoothly truncated renormalized energy
E ̃T (t) :=
∑
j,k∈Z∗: j 6=k
ψT ( j )ψT (k)E ̃ jk(t) (67)
for Λ/2 6 t 6 0. This is clearly non-negative, and from Proposition 15, (66), (62) and Fubini’s theorem, we see that E ̃T is absolutely integrable in time (in particular, it is finite for almost every Λ/2 6 t 6 0). Since E jk are non-negative, we see from (66) that to prove (65) it will suffice to show that
∫0
Λ/4
E ̃ T (t) dt = oT →∞(T log3
+ T ). (68)
We have an analogue of Lemma 16.
LEMMA 18. For almost every Λ/2 6 t 6 0, one has
E ̃T (t) =


∑
j,k∈Z∗: j 6=k
ψT ( j )ψT (k)
(
E jk(t) −
1
|ξk − ξ j |2
)

 + O ̃ (1).
Proof. For almost every t, one sees from Proposition 15, (66) and Fubini’s theorem (and (51)) that the series
∑
j,k: j6=k
ψT ( j )ψT (k)
(
E jk(t) +
1
|ξk − ξ j |2 +
|x j (t)| + |xk(t)|
|ξk − ξ j |3
)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 43
is absolutely convergent. Thus, by Fubini’s theorem and (63), it will suffice to show that
∑
j,k∈Z∗: j 6=k
ψT ( j )ψT (k) (xk(t) − ξk) − (x j (t) − ξ j )
(ξk − ξ j )3 / 1.
We may desymmetrize the left-hand side (again using Fubini’s theorem) as
2
∑
j ∈Z∗
ψT ( j )(x j (t) − ξ j ) ∑
k∈Z∗: k6= j
ψT (k)
(ξk − ξ j )3 ,
and so it will suffice to establish the bound
∑
k∈Z∗: k6= j
ψT (k)
(ξk − ξ j )3 / 1
|j|
+
1
T
for all j ∈ Z∗. As in the proof of Lemma 16, we see from (44) that the contribution of those k with |k − j | > 1
2 j is acceptable. For the remaining range |k − j| < 1
2 j , we again use (45) to estimate
1
(ξk − ξ j )3 =
log3 ξ j (4π )3
1
(k − j )3 + O ̃
(1
j (k − j )2
)
and similarly
ψT (k) = ψT ( j ) + O ̃
(
|k − j|
T
)
,
and the claim follows by direct computation using the fact that k 7→ 1
k− j is odd around j.
Recall that two indices j, k ∈ Z∗ are said to be nearby, and we write j ∼T k, if one has
0 < | j − k| < (T 2 + | j | + |k|)0.1.
This is clearly a symmetric relation. Next, for Λ/2 6 t 6 0, we define the smoothly truncated renormalized Hamiltonian
H ̃ T (t) :=
∑
j,k∈Z∗: j ∼T k
ψT ( j )ψT (k)
(
Hjk(t) − log 1
|ξ j − ξk|
)
. (69)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 44
From (66), Proposition 13 and (45), we see that the sum here is absolutely convergent for every Λ/2 6 t 6 0. We can also express it in terms of nonnegative quantities plus a small error, in a manner similar to Lemma 18, as follows. We first introduce the renormalization
L(x) := log 1
|x|
+ |x| − 1
of the logarithm function x 7→ log 1
|x| ; this is a convex non-negative function on R
\{0} that vanishes precisely when |x| = 1 and obeys the asymptotics
L(x) log+
1
|x|
for 0 < |x| 6 1/2
L(x) (|x| − 1)2 for 1/2 < |x| 6 2
L(x) |x| for |x| > 2.
(70)
For any Λ/2 6 t 6 0 and distinct j, k ∈ Z∗, we define the normalization
H ̃ jk(t) := L
( x j (t) − xk(t)
ξ j − ξk
)
(71)
of the Hamiltonian interaction Hjk(t); this is symmetric in j, k and non-negative, vanishing precisely when xk(t) − x j (t) = ξk − ξ j .
LEMMA 19. For every Λ/2 6 t 6 0, one has
H ̃ T (t) =
∑
j,k∈Z∗: j ∼T k
ψT ( j )ψT (k)H ̃ jk(t) + oT →∞(T log3
+ T ).
Proof. From (71), one has
H ̃ jk(t) = Hjk(t) − log 1
|ξ j − ξk|
−
(x j (t) − ξ j ) − (xk(t) − ξk)
ξ j − ξk
,
so by (69) it suffices to show that
∑
j,k∈Z∗: j ∼T k
ψT ( j )ψT (k) (x j (t) − ξ j ) − (xk(t) − ξk)
ξ j − ξk
= oT →∞(T log3
+ T ).
Note from (43), (45), (51) and (66) that the sum here is absolutely convergent. Desymmetrizing, it suffices to show that
∑
j ∈Z∗
ψT ( j )|x j (t) − ξ j |
∣ ∣ ∣ ∣ ∣ ∣
∑
k∈Z∗: j ∼T k
ψT (k)
ξ j − ξk
∣ ∣ ∣ ∣ ∣ ∣
= oT →∞(T log3 T ).
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 45
The inner sum can be crudely bounded by O ̃ (1) for all j thanks to (66) and (45). By (43), (50) and (66), it thus suffices to show that
∑
k∈Z∗: j ∼T k
ψT (k)
ξ j − ξk
= oT →∞(log T ) (72)
whenever T 0.5 6 | j | 6 T 1.5 (say). For j ∼T k, one has ψT (k) = ψT ( j ) + O ̃ (T −0.8), and the contribution of the error term is acceptable by (45), so it suffices to show that
∑
k∈Z∗: j ∼T k
1
ξ j − ξk
= oT →∞(log T ) (73)
whenever | j | > T 0.5. But from (45), we have
ξ j − ξk =
4π
log ξ j
( j − k) + O
(
| j − k|2
| j | log2
+ ξj
)
,
and hence 1
ξ j − ξk
=
log ξ j
4π
1
j−k +O
(1
|j|
)
. (74)
As k 7→
log ξ j 4π
1
j−k is odd around j and the set {k : j ∼T k} is very nearly symmetric around j, it is then easy to establish (73) as required.
In contrast to the non-normalized interaction Hjk(t), the quantity H ̃ jk(t) is well controlled when k and j are far apart.
LEMMA 20 (Long-range decay of H ̃ jk). Let j, k be distinct elements of Z∗, and let t be in the range Λ/2 6 t 6 0. There exists a quantity ε( j) that goes to zero as | j | → ∞, such that if |k − j | > ε( j )−1 log2
+ ξ j , then
H ̃ jk(t) log4
+(| j | + |k|)
|k − j |2 ,
and if ε( j ) log2
+ ξ j 6 |k − j | 6 ε( j )−1 log2
+ ξ j , one has the refinement
H ̃ jk(t) ε( j )2 log4
+j
|k − j |2 .
Finally, in the remaining region |k − j| < ε( j) log2
+ ξ j , one has the crude bound
H ̃ jk(t) (log2
+ j ) log+ log+ j.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 46
Proof. First, suppose that |k − j| > 1
2 | j| (so in particular |k − j| | j| + |k|). From (50), one has
xk(t) − x j (t) = ξk − ξ j + O(log+(| j | + |k|))
while from (44), one has
|ξk − ξ j |
| j| + |k|
log+(| j | + |k|)
and thus
xk(t) − x j (t)
ξk − ξ j
− 1 log2
+(| j | + |k|)
| j| + |k|
,
and the claim then follows from (70) (noting that the case | j| + |k| = O(1) can be treated by compactness). Now suppose that ε( j )−1 log2
+ ξ j 6 |k − j | < 1
2 | j|. By symmetry, we can take
j positive; we may also assume j to be large, as the bounded case j = O(1) may be treated by compactness. From (50), one then has
xk(t) − x j (t) = ξk − ξ j + O(log j )
and from (44), one has
|ξk − ξ j |
|k − j|
log j (75)
and hence
xk(t) − x j (t)
ξk − ξ j
− 1 log2( j )
|k − j|
6 ε( j).
The claim then follows from (70). Next, suppose that ε( j) log2
+ ξ j 6 |k − j | 6 ε( j )−1 log2
+ ξ j . In this case, from (52) (iterated O(ε( j)−1) times) and (45), we have
xk(t) − x j (t) = ξk − ξ j + o j→∞(ε( j )−1 log j )
while from (44) we continue to have (75), and hence
xk(t) − x j (t)
ξk − ξ j
− 1 = o j→∞
(
ε( j )−1 log2( j )
|k − j|
)
,
with the decay rate in the o j→∞ notation independent of the choice of function ε(). For ε( j) going to zero sufficiently slowly, the claim once again follows from (70). Finally, for the remaining case |k − j| < ε( j) log2
+ ξ j (which implies xk(t) − x j (t) log2
+ j thanks to (52)), the claim follows from Proposition 13 and (70).
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 47
We call a (time-dependent) quantity moderately sized if it is of the form O(T log3
+ T + E ̃T (t)), and negligible if it is of the form oT →∞(T log3
+ T + E ̃T (t)). The following lemma gives some examples of moderately sized and negligible quantities.
LEMMA 21. Let t be in the range Λ/2 6 t 6 0.
(i) The quantity
∑
j,k∈Z∗: j 6=k
ψT ( j )ψT (k)
|x j (t) − xk(t)|2
is moderately sized.
(ii) The quantity
(log+ T ) ∑
j,k∈Z∗: j 6=k
ψT ( j )ψT (k)
|x j (t) − xk(t)|
is moderately sized.
(iii) For any absolute constants C, c > 0, the expression
(logC
+T) ∑
j,k∈Z∗: | j |,|k|6T 1−c
ψT ( j )ψT (k)
|x j (t) − xk(t)|
is negligible.
(iv) For any absolute constants C, c > 0, the expression
(logC
+T) ∑
j,k∈Z∗: | j |,|k|>T 1+c
ψT ( j )ψT (k)
|x j (t) − xk(t)|
is negligible.
We have this similarly if xi (t) are replaced by ξi throughout.
Proof. For brevity, we omit the explicit dependence on the time t. Also, all summation indices i, j, k are understood to range in Z∗. From (44), we see that
∑
k: k6= j
1
|ξ j − ξk|2 log2
+j
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 48
for all j ∈ Z∗, and hence
∑
j,k: j6=k
ψT ( j )ψT (k) 1
|ξ j − ξk|2 T log3
+ T.
From this and Lemma 16, we conclude (i). Using
log+ T
|x j (t) − xk(t)|
61
|x j (t) − xk(t)|2 + log2
+ T,
we then obtain (ii). If instead we use
logC
+T
|x j (t) − xk(t)|
61
log+ T
1
|x j (t ) − xk(t )|2 + log2C+1
+ T,
we obtain (iii) and (iv). We have this similarly if xi are replaced by ξi throughout.
We now have the following crucial derivative computation.
PROPOSITION 22. In the range Λ/2 6 t 6 0, the function HT is absolutely continuous, and the derivative ∂t H ̃ T (t) is equal to −4E ̃T (t) plus negligible terms for almost all t. In other words, one has
∂t H ̃ T (t) = −4E ̃ T (t) + oT →∞
(
T log3 T + E ̃T (t)
)
(76)
for almost every t.
REMARK 23. This may be compared with Lemma 12(v) or indeed the formal identity (57). That the right-hand side is approximated in terms the renormalized energy, rather than just the energy, may be thought of heuristically as being a result of ∂t H vanishing when the zeros x j settle on an equilibrium, being spaced like the points ξ j .
Proof. As before, we omit the explicit dependence on t, and all summation indices are understood to lie in Z∗. By (56), we have
∂t Hjk(t ) = −
2
xk − x j
(′ ∑
i: i6=k
1
xk − xi
−
′ ∑
i: i6= j
1
x j − xi
)
. (77)
If we formally insert this into (69) and desymmetrize in j and k, we would obtain the identity
∂t H ̃ T = −4
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
xk − x j
′ ∑
i: i6=k
1
xk − xi
. (78)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 49
However, we need to justify the interchange of the derivative and the infinite summation. First, we use the fundamental theorem of calculus to rewrite (77) in integral form as
Hjk(0) − Hjk(t0)
= −2
∫0
t0
1
xk(t) − x j (t)
(′ ∑
i: i6=k
1
xk(t) − xi (t) −
′ ∑
i: i6= j
1
x j (t) − xi (t)
)
dt
for any Λ/2 6 t0 6 0. Multiplying by ψT ( j)ψT (k), we conclude that
HT (0) − HT (t0) = −2
∑
j,k: j ∼T k
ψT ( j )ψT (k)
∫0
t0
1
xk(t) − x j (t)
×
(′ ∑
i: i6=k
1
xk(t) − xi (t) −
′ ∑
i: i6= j
1
x j (t) − xi (t)
)
dt.
By the dominated convergence theorem, we can interchange the outer sum and the integral as soon as we can show that the expression
∑
j,k: j ∼T k
ψT ( j )ψT (k)
×
∫0
t0
1
|xk(t) − x j (t)|
(∣ ∣ ∣ ∣ ∣
′ ∑
i: i6=k
1
xk(t) − xi (t)
∣ ∣ ∣ ∣ ∣
+
∣ ∣ ∣ ∣ ∣
′ ∑
i: i6= j
1
x j (t) − xi (t)
∣ ∣ ∣ ∣ ∣
)
dt
is finite. By symmetry in j and k, it suffices to show that
∑
j,k: j ∼T k
ψT ( j )ψT (k)
∫0
t0
1
|xk(t) − x j (t)|
∣ ∣ ∣ ∣ ∣
′ ∑
i: i6=k
1
xk(t) − xi (t)
∣ ∣ ∣ ∣ ∣
dt (79)
is finite. But using (50) and (52), we can crudely bound
∣ ∣ ∣ ∣ ∣
′ ∑
i: i6=k
1
xk(t) − xi (t)
∣ ∣ ∣ ∣ ∣
,
1
|xk(t) − x j (t)|
logO(1)
+ (k)
(1
|xk(t) − xk−1(t)|
+
1
|xk(t) − xk+1(t)|
)
(using the convention x0(t) = 0), so expression (79) may in turn be crudely bounded by
∑
k
ψ2
T (k)(T + |k|)0.1 logO(1)
+ (k)
∫0
t0
1
|xk(t ) − xk−1(t )|2 +
1
|xk(t) − xk+1(t)|2 dt,
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 50
and this will be finite thanks to Proposition 15 and (66). We conclude (after desymmetrizing in j and k) that
HT (0)−HT (t0) = −4
∫0
t0
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
xk(t) − x j (t)
′ ∑
i: i6=k
1
xk(t) − xi (t) dt.
The above analysis also shows that the integrand is absolutely integrable in time. From the Lebesgue differentiation theorem, we conclude that H ̃ T is absolutely continuous and that (78) holds at almost every time t. To conclude the proof of the proposition, it will thus suffice to show that
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
xk − x j
′ ∑
i 6=k
1
xk − xi
(80)
is equal to E ̃T plus negligible terms. We can split this expression as X1 + X2 + X3 + X4, where
X1 :=
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
(xk − x j )2
X2 :=
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
xk − x j
∑
i: i∼T j,k
1
xk − xi
X3 :=
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
xk − x j
∑
i: i∼T k; i6∼T j; i6= j
1
xk − xi
X4 :=
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
xk − x j
′ ∑
i: i6∼T k; i6=k
1
xk − xi
.
We first claim that X4 is negligible. From (50), we have
xk − xi = ξk − ξi + O(log+(|i | + |k|))
and hence (by (44)),
1
xk − xi
=
1
ξk − ξi
+O
(
log2
+(|i | + |k|)
|k − i |2
)
,
which implies that
′ ∑
i: i6∼T k; i6=k
1
xk − xi
=
′ ∑
i: i6∼T k; i6=k
1
ξk − ξi
+ O ̃ (T −0.1).
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 51
From (44), we may crudely bound this sum by O ̃ (1). By Lemma 21(iii), this shows that the contribution to X4 of those k for which |k| 6 T 0.9 or |k| > T 1.1 (say) is negligible, so we may assume T 0.9 6 |k| 6 T 1.1. Let A > 2 be a large constant. Using (44), we may write
′ ∑
i: i6∼T k; i6=k
1
ξk − ξi
=
∑
i : T 0.26|k−i |6 A|k|
1
ξk − ξi
+
∑
i: |i|>A|k|
1
ξk − ξi
+O
( log T
A
)
.
For the first sum on the right-hand side, we use (45) (as in the proof of (74)) as well as (43) to conclude that
1
ξk − ξi
=
log ξk
4π
1
k − i + OA
(1
|k|
)
,
where the subscript in the OA notation means that the implied constant can
depend on A. As i 7→ log ξk
4π
1
k−i is odd around k, we conclude that
∑
i : T 0.26|k−i |6 A|k|
1
ξk − ξi
= OA(1).
Meanwhile, combining the i and −i terms and using (43) and (44), we have
∑
i: |i|>A|k|
1
ξk − ξi
= −2ξk
∑
i: i>A|k|
1 ξ2
i − ξ2
k
=O
( log T
A
)
.
Sending A slowly to infinity, we conclude that
′ ∑
i: i6∼T k; i6=k
1
xk − xi
= oT →∞(log T ),
and the negligibility of X4 then follows from Lemma 21(ii). Now we claim that X2 is negligible. Thanks to the restrictions on i, j, k, we see that
ψT (i ), ψT ( j ) = (1 + O ̃ ((T + |k|)−0.8))ψT (k),
and hence
ψT ( j )ψT (k) = ψT (i )2/3ψT ( j )2/3ψT (k)2/3 + O ̃ ((T + |k|)−0.8ψT ( j )ψT (k)).
The sum
∑
i, j,k: j ∼T k; i∼T j,k
ψT (i )2/3ψT ( j )2/3ψT (k)2/3
(xk − x j )(xk − xi )
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 52
symmetrizes to zero, and hence
X2 /
∑
i, j,k: j ∼T k; i∼T j,k
(T + |k|)−0.8 ψT ( j )ψT (k)
|xk − x j ||xk − xi |
.
Estimating 1
|xk −x j ||xk −xi |
1
|xk −x j |2 + 1
|xk−xi |2 and performing the i or j summation respectively, we conclude that
X2 /
∑
j,k: j ∼T k
(T + |k|)−0.6 ψT ( j )ψT (k)
|xk − x j |2 ,
and so X2 is negligible thanks to Lemma 21(i). We have shown that expression (80) is equal to X1 + X3 plus negligible terms. A similar argument (replacing xi with ξi throughout) shows that the expression
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
ξk − ξ j
′ ∑
i: i6=k
1
ξk − ξi
(81)
is equal to X ′
1 + X′
3 plus negligible terms, where
X
′
1 :=
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
(ξk − ξ j )2
X
′
3 :=
∑
j,k: j ∼T k
ψT ( j )ψT (k) 1
ξk − ξ j
∑
i: i∼T k; i6∼T j; i6= j
1
ξk − ξi
.
From Lemma 18, we see that E ̃T is equal to
X1 − X′
1+
∑
j,k: j6∼T k; j6=k
ψT ( j )ψT (k)
(1
(xk − x j )2 −
1
(ξk − ξ j )2
)
(82)
up to negligible terms. From (43) and (44), we have
1
(xk − x j )2 −
1
(ξk − ξ j )2 / logO(1)
+ (| j | + |k|)
|k − j |3
when j 6= k and j 6∼T k, so the final term in (82) is negligible. Thus, to complete the proof of the proposition, it will suffice to show that expression (81) and the difference X3 − X ′
3 are both negligible. Expression (81) may be rearranged as
∑
k
ψT (k)
( ∑
j: j∼T k
ψT ( j)
ξk − ξ j
)( ′ ∑
i: i6=k
1
ξk − ξi
)
.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 53
By (44), both inner sums are O ̃ (1), so the contribution of those |k| 6 T 0.5 or |k| > T 1.5 (say) is negligible. For T 0.5 < |k| 6 T 1.5, we see from (72) that the factor ∑
j: j∼T k
ψT ( j)
ξk−ξj is oT →∞(log T ), and from (44) and (73) and the triangle
inequality, we also see that ∑′
i: i6=k
1 ξk −ξi
= O(log T ). Thus (81) is negligible as required. Finally, we show that X3 − X ′
3 is negligible. This quantity may be written as
∑
i, j,k: i, j ∼T k; |i − j |>(T 2+|i |+| j |)0.1
ψT ( j )ψT (k)
(1
(xk − x j )(xk − xi ) −
1
(ξk − ξ j )(ξk − ξi )
)
.
Observe that if |k − j| and |k − i| are both larger than or equal to T 0.1, then from (44) and (50), one has
1
(xk − x j )(xk − xi ) −
1
(ξk − ξ j )(ξk − ξi )
logO(1)
+ (|i| + | j | + |k|)
T 0.1|ξk − ξ j ||ξk − ξi |
logO(1)
+ (|i| + | j | + |k|)
T 0.1|k − j ||k − i |
,
and so the contribution of this case is negligible. From the triangle inequality, we see that it is not possible for |k − j| and |k − i| to both be less than T 0.1, so it remains to treat the components
∑
i, j,k: 0<| j −k|<(T 2+| j |+|k|)0.1 0<|i −k|<T 0.1; |i − j |>(T 2+|i |+| j |)0.1
× ψT ( j )ψT (k)
(1
(xk − x j )(xk − xi ) −
1
(ξk − ξ j )(ξk − ξi )
)
(83)
and
∑
i, j,k: 0<| j −k|<T 0.1
0<|i −k|<(T 2+|i |+|k|)0.1; |i − j |>(T 2+|i |+| j |)0.1
× ψT ( j )ψT (k)
(1
(xk − x j )(xk − xi ) −
1
(ξk − ξ j )(ξk − ξi )
)
. (84)
Consider first (83). From the triangle inequality, we have | j − k| T 0.2, and hence by (50),
1
xk − x j
= (1 + O ̃ (T −0.2)) 1
ξk − ξ j
.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 54
By Lemma 21(ii) and (44), we may thus replace 1
xk −x j by 1
ξk−ξj at negligible cost in (83), leaving us with
∑
i, j,k: 0<| j −k|<(T 2+| j |+|k|)0.1 0<|i −k|<T 0.1; |i − j |>(T 2+|i |+| j |)0.1
ψT ( j )ψT (k)
(1
xk − xi
−
1
ξk − ξi
)1
ξk − ξ j
up to negligible errors. But by (45) and the hypothesis |i − k| 6 T 0.1, one may bound
∑
j : 0<| j −k|<(T 2+| j |+|k|)0.1 |i − j |>(T 2+|i |+| j |)0.1
ψT ( j)
|ξk − ξ j |
/ T −0.1ψT (k)
when T 0.9 6 |k| 6 T 1.1, and use the weaker bound
∑
j : 0<| j −k|<(T 2+| j |+|k|)0.1 |i − j |>(T 2+|i |+| j |)0.1
ψT ( j)
|ξk − ξ j |
/ ψT (k)
for all other k, so this expression is also negligible by Lemma 21(ii), (iii), (iv) (noting that ψT (k) and ψT (i) are comparable). A similar argument also handles (84).
To use Proposition 22, we need estimates that ensure E ̃T is large when H ̃ T is large. To this end, we have the following lemma.
LEMMA 24. Let m be a natural number, and let Λ/2 6 t 6 0. Let T > 0, and let δ = δ(T ) go to zero as T → ∞ sufficiently slowly. If H ̃ T (t) > δmT log3
+ T,
then E ̃ T (t) δ22m T log3
+ T , where the implied constant is absolute.
Proof. As before, we suppress explicit dependence on t, and we may assume T to be large as the claim is trivial from compactness for T = O(1). From Lemma 19, we have (for δ decaying sufficiently slowly) that
∑
j,k∈Z∗: j ∼T k
ψT ( j )ψT (k)H ̃ jk(t) > 99
100 δmT log3 T.
From Lemma 20, we see that
∑
k: j ∼T k; |k− j |>ε( j ) log2
+ ξj
H ̃ jk(t) ε( j ) log2
+j
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 55
for any j ∈ Z∗, which implies that
∑
j,k: j ∼T k; |k− j |>ε( j ) log2
+ ξj
ψT ( j )ψT (k)H ̃ jk(t) 6 1
2 δT log3 T
if δ(T ) goes to zero slowly enough. By (69), we conclude that
∑
j,k: j ∼T k; |k− j|<ε( j ) log2
+ ξj
ψT ( j )ψT (k)H ̃ jk(t) δmT log3
+ T . (85)
We now claim that
∑
j,k: j ∼T k; |k− j |<ε( j) log2
+ ξj |x j −xk |>2−m |ξ j −ξk |
ψT ( j )ψT (k)H ̃ jk(t) δ2mT log3 T (86)
(say). To see this, we use (45) and (70) to bound
L jk m +
|x j − xk|
|ξ j − ξk|
m+
|x j − xk|
| j − k|
log T
and also ψT ( j) ψT (k) for j, k in the sum. Thus we may bound (86) by
m
∑
j,k: |k− j|<ε( j) log2
+ ξj
ψT ( j )2 +
∑
j,k: 0<|k− j|<ε( j) log2
+ ξj
ψT ( j )2 |x j − xk|
| j − k|
log T.
We may directly compute
∑
j,k: j ∼T k; |k− j |<ε( j) log2
+ ξj
ψT ( j )2 δ2T log3 T
if δ = δ(T ) goes to zero slowly enough. Thus it will suffice to show that
∑
j,k: 0<|k− j|<ε( j) log2
+ ξj
ψT ( j )2 |x j − xk|
| j − k|
δ2T log2 T . (87)
But for any natural number n, we see from telescoping series and (50) that
∑
j : 2n 6| j |<2n+1
|x j − x j+h| |h|
2n
n
whenever |h| 2n; summing over |h| < ε( j) log2
+ ξ j , we conclude that
∑
j,k: 2n 6| j |<2n+1 0<|k− j|<ε( j) log2
+ ξj
|x j − xk|
| j − k|
ε(2n )2n n ,
which gives (87) if δ goes to zero slowly enough.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 56
From (85) and (86), we have
∑
j,k: j∼T k; |k− j|<ε( j ) log2
+ ξj |x j −xk |62−m |ξ j −ξk |
ψT ( j )ψT (k)H ̃ jk(t) δmT log3 T .
But for j, k in this sum, we see from (62) and (70) that
H ̃ jk(t) log |ξ j − ξk|
|x j − xk|
m2−2m |ξ j − ξk |2
|x j − xk |2 m2−2m E ̃ jk ,
and the claim follows.
We can now shrink H ̃ T down to a reasonable size in finite time.
COROLLARY 25. One has H ̃ T (t) = O(δT log3
+ T ) for Λ/4 6 t 6 0.
Proof. We may take T to be large. From Proposition 22 and Lemma 24, we see that for any natural number m, and for almost every time t for which one has
H ̃ T (t) > δmT log3 T ,
one has
∂t H ̃ T (t) 6 −cδ22m T log3 T
for some absolute constant c > 0. In particular, if m is larger than some large absolute constant m0, and Λ/2 6 t 6 Λ/4 is such that
δmT log3 T 6 H ̃ T (t) 6 δ(m + 1)T log3 T, (88)
then it is not possible (for m0 large enough) to have H ̃ T (t′) > δmT log3 T for all t 6 t′ 6 t + c−12−2m, as this would violate the fundamental theorem of calculus for absolutely continuous functions. Thus, by the intermediate value theorem, there exists t 6 t′ 6 t + c−12−2m such that
δ(m − 1)T log3 T 6 H ̃ T (t′) 6 δmT log3 T ,
and on iterating this we conclude (for m0 large enough) that there exists t 6 t′′ 6 t + 2c−12−2m0 such that
H ̃ T (t′′) 6 δm0T log3 T . (89)
We run this argument with t set equal to Λ/2, and m the unique integer obeying (88), to conclude (for m0 large enough) that there exists Λ/2 6 t′′ 6 Λ/4
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 57
obeying (89). (Note that this conclusion is immediate if the initial value of m was already less than m0.) On the other hand, from Proposition 22, we have ∂t H ̃ T (t) 6 O(δT log3 T ) for almost every t′′ 6 t 6 0 if δ decays sufficiently slowly. The claim now follows from the fundamental theorem of calculus (absorbing m0 into the implied constants), recalling that H ̃ T is non-negative.
From Proposition 22 and the fundamental theorem of calculus for absolutely continuous functions, one has
H ̃ T (Λ/4) − H ̃ T (0) = (4 + oT →∞(1))
∫0
Λ/4
E ̃ T (t) dt + oT →∞(T log3
+ T ),
and claim (68) now follows from Corollary 25. This concludes the proof of Theorem 17.
8. Controlling the energy at time 0
In the previous section, we controlled a time average of the energy. Now, using monotonicity properties of the energy, we can in fact control energy at time zero.
PROPOSITION 26 (Energy bound at time zero). Let T be large. Then
E ̃ [T log T,2T log T ](0) = oT →∞(T log3 T ).
Proposition 26 will be proven by iterating the following claim.
PROPOSITION 27 (Energy propagation inequality). Let T be large, let I = [I−, I
+] be an interval containing [T log T, 2T log T ] and contained in [0.5T log T, 3T log T ], and let Λ/4 6 t1 6 t2 6 0 be such that t2 6 t1 + 1
100 log2 T . Then
E ̃ I′ (t2) 6 E ̃ I (t1) + O ̃ (1),
where I ′ := [I− + log3 T, I+ − log3 T ] is a slightly shrunken version of I .
Recall that O ̃ (1) is any quantity that is O(logO(1) T ). Let us assume Proposition 27 for the moment and finish the proof of Proposition 26. From Theorem 17, we have
∫0
Λ/4
E ̃ [0.5T log T,3T log T ](t ) dt = oT →∞(T log3
+ T ),
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 58
and so by the pigeonhole principle, we may find Λ/4 6 t0 6 0 such that
E ̃ [0.5T log T,3T log T ](t0) = oT →∞(T log3
+ T ).
Applying Proposition 27 O(log2 T ) times to get from t0 to 0, we conclude that
E ̃ [I−,I+](0) 6 oT →∞(T log3
+ T)
for some interval [I−, I+] containing [T log T, 2T log T ] and contained in [0.5T log T, 3T log T ] (in fact, we have I− = 0.5T log T + O(log5 T ) and I
+ = 3T log T − O(log5 T )). Since E ̃ I (0) is monotone in I , Proposition 26 follows. It remains to establish Proposition 27. We use an argument due to Bourgain [2, Section 4] that combines local conservation laws (or, in this case, local monotonicity formulae) with the pigeonhole principle. The first step is to locate a good subset of particles indexed by an interval close to [I−, I+] that does not gain too much energy due to interactions with its environment because of the separation between these particles and the environment. From (50) and the pigeonhole principle, one can find natural numbers
I
− 6 j− − 1 < j− 6 I− + log3 T 6 I+ − log3 T 6 j+ < j+ + 1 6 I+
such that
x j− (t2) − x j−−1(t2) > 1
log T (90)
(say) and similarly
x j++1(t2) − x j+ (t2) > 1
log T .
From Lemma 12(iv) applied to K = { j− − 1, j−}, we have
∂t (x j− (t ) − x j−−1(t ))2 6 8
for all t1 6 t 6 t2. Since t2 − t1 6 1
100 log2 T , we conclude from the fundamental theorem of calculus and (90) that
x j− (t ) − x j−−1(t ) 1
log T (91)
for all t1 6 t 6 t2. Similarly
x j++1(t ) − x j+ (t ) 1
log T . (92)
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 59
The basic point is that because the particles x j−, . . . , x j+ never get too close to the remaining particles x j , j < j− and x j , j > j+ in the system, the total energy of the former set of particles will remain approximately conserved over short periods of time thanks to Lemma 12. More precisely, let K denote the discrete interval K := [ j−, j+], and define the un-normalized energy
E K (t) :=
∑
k,k′∈K : k6=k′
Ekk′ (t ).
From Lemma 12, we have
∂t E K (t) 6
∑
j6∈K
k,k′∈K : k6=k′
4
(xk − xk′ )2(xk − x j )(xk′ − x j )
for t1 6 t 6 t2. But from (50), (91) and (92), we have
∑
j6∈K
k,k′∈K : k6=k′
4
(xk − xk′ )2(xk − x j )(xk′ − x j ) / 1.
From the fundamental theorem of calculus, we conclude that
E K (t2) 6 E K (t1) + O ̃ (1),
which by monotonicity of E K in K implies that
E I′ (t2) 6 E I (t1) + O ̃ (1).
Applying Lemma 16, we conclude that
E ̃ I′ (t2) 6 E ̃ I (t1) + O ̃ (1) + 2
∑
j∈I\I′ k∈I : j6=k
1
(ξ j − ξk)2 .
But from (44), one has
∑
j∈I\I′ k∈I : j6=k
1
(ξ j − ξk)2 / 1,
and Proposition 27 follows.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 60
9. Contradicting pair correlation
It remains to see that Proposition 26 is in contradiction with results that are known to be the case for the points x j (0). Note in particular that
∑
T log T 6 j, j+162T log T
1
|ξ j+1 − ξ j |2 V
( x j+1(0) − x j (0)
ξ j+1 − ξ j
)
6 E ̃ [T log T,2T log T ](0).
In this range using (43) and (45), we have ξ j+1 − ξ j ∼ 4π/ log+ T , and so Proposition 26 implies that
log2 T
∑
T log T 6 j, j+162T log T
V
( x j+1(0) − x j (0)
ξ j+1 − ξ j
)
= oT →∞(T log3 T ).
By Markov’s inequality (see [28, Ch. 1]), this implies that
V
( x j+1(0) − x j (0)
ξ j+1 − ξ j
)
= oT →∞(1)
for a fraction 1 − oT→∞(1) of j ∈ [T log T, 2T log T ]. But using the properties (62) of the function V , this implies that
x j+1(0) − x j (0)
ξ j+1 − ξ j
= 1 + oT →∞(1)
or
x j+1(0) − x j (0) =
4π + oT →∞(1)
log T (93)
for a fraction 1 − oT →∞(1) of j ∈ [T log T, 2T log T ]. In particular, since the points x j (0) are twice the imaginary ordinates of nontrivial zeros of the Riemann zeta function, this implies that the gaps between the zeros of the zeta function are rarely much larger or smaller than the mean spacing. But this contradicts perhaps most strikingly the results of Montgomery [15], who determined on the Riemann hypothesis the pair correlation measure for the zeros, measured against a class of band-limited functions. As noted by Montgomery, his result implies that a positive proportion of zeros have a spacing between them strictly smaller than the mean spacing. The proof of this claim is not written down in [15], but Conrey et al. prove as their main result of [6] (using different ideas) that for any λ > .77, there exists a constant c(λ) > 0 such that at least a proportion c(λ) of j 6 T log T satisfy
x j+1(0) − x j (0) 6 λ 4π
log T .
This contradicts (93) and therefore the assumption that Λ < 0.
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 The De Bruijn–Newman constant is non-negative 61
Acknowledgements
The first author received partial support from the NSF grant DMS-1701577 and an NSERC grant. The second author is supported by NSF grant DMS1266164 and by a Simons Investigator Award. We thank anonymous referees for useful suggestions, and likewise we thank Charles Newman for helpful comments and Alex Dobner for corrections.
Conflict of Interest: The authors have no conflicts of interest to declare.
References
[1] M. Abramowitz and I.A. Stegun, Handbook of Mathematical Functions (Dover, New York, 1965). [2] J. Bourgain, ‘Global wellposedness of defocusing critical nonlinear Schro ̈dinger equation in the radial case’, J. Amer. Math. Soc. 12(1) (1999), 145–171.
[3] K. Broughan, Equivalents of the Riemann Hypothesis, Vol. 2, Analytic Equivalents, Encyclopedia of Mathematics and its Applications, 165 (Cambridge University Press, Cambridge, 2017). [4] N. C. de Bruijn, ‘The roots of trigonometric integrals’, Duke J. Math. 17 (1950), 197–226. [5] A. Chang, D. Mehrle, S. J. Miller, T. Reiter, J. Stahl and D. Yott, ‘Newman’s conjecture in function fields’, J. Number Theory 157 (2015), 154–169. [6] J. B. Conrey, A. Ghosh, D. Goldston, S. M. Gonek and D. R. Heath-Brown, ‘On the distribution of gaps between zeros of the zeta-function’, Q. J. Math. 36 (1985), 43–51. [7] J. B. Conrey, A. Ghosh and S. M. Gonek, ‘A note on gaps between zeros of the zeta function’, Bull. Lond. Math. Soc. 16(4) (1984), 421–424.
[8] G. Csordas, T. S. Norfolk and R. S. Varga, ‘A lower bound for the de Bruijn–Newman constant Λ’, Numer. Math. 52 (1988), 483–497. [9] G. Csordas, A. M. Odlyzko, W. Smith and R. S. Varga, ‘A new Lehmer pair of zeros and a new lower bound for the De Bruijn–Newman constant Lambda’, Electron. Trans. Numer. Anal. 1 (1993), 104–111. [10] G. Csordas, A. Ruttan and R. S. Varga, ‘The Laguerre inequalities with applications to a problem associated with the Riemann hypothesis’, Numer. Algorithms 1 (1991), 305–329. [11] G. Csordas, W. Smith and R. S. Varga, ‘Lehmer pairs of zeros, the de Bruijn–Newman constant Λ, and the Riemann hypothesis’, Constr. Approx. 10(1) (1994), 107–129. [12] L. Erdo ̋s, B. Schlein and H.-T. Yau, ‘Universality of random matrices and local relaxation flow’, Invent. Math. 185(1) (2011), 75–119. [13] H. Ki, Y. O. Kim and J. Lee, ‘On the de Bruijn–Newman constant’, Adv. Math. 22 (2009), 281–306. [14] D. H. Lehmer, ‘On the roots of the Riemann zeta-function’, Acta Math. 95 (1956), 291–298. [15] H. L. Montgomery, ‘The pair correlation of zeros of the zeta function’, in Analytic Number Theory (Proceedings of Symposia in Pure Mathematics, Vol. XXIV, St. Louis Univ., St. Louis, MO, 1972) (American Mathematical Society, Providence, RI, 1973), 181–193.
[16] H. L. Montgomery and R. C. Vaughan, Multiplicative Number Theory. I. Classical Theory, Cambridge Studies in Advanced Mathematics, 97 (Cambridge University Press, Cambridge, 2007).
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press


 B. Rodgers and T. Tao 62
[17] C. M. Newman, ‘Fourier transforms with only real zeroes’, Proc. Amer. Math. Soc. 61 (1976), 246–251. [18] T. S. Norfolk, A. Ruttan and R. S. Varga, A Lower Bound for the de Bruijn–Newman Constant Λ II, (eds. A. A. Gonchar and E. B. Saff) Progress in Approximation Theory (Springer, New York, 1992), 403–418. [19] A. M. Odlyzko, ‘An improved bound for the de Bruijn–Newman constant’, Numer. Algorithms 25 (2000), 293–303. [20] G. P ́olya, ‘U ̈ ber trigonometrische Integrale mit nur reelen Nullstellen’, J. Reine Angew. Math. 58 (1927), 6–18. [21] D. H. J. Polymath, ‘Effective approximation of heat flow evolution of the Riemann ξ function, and a new upper bound for the de Bruijn–Newman constant’, Res. Math. Sci. 6 (2019), 3, Paper No. 31, 67 pp. [22] H. J. J. te Riele, ‘A new lower bound for the de Bruijn–Newman constant’, Numer. Math. 58 (1991), 661–667. [23] Y. Saouter, X. Gourdon and P. Demichel, ‘An improved lower bound for the de BruijnNewman constant’, Math. Comp. 80 (2011), 2281–2287. [24] E. M. Stein and R. Shakarchi, Complex Analysis, Vol. 2 (Princeton University Press, Princeton, NJ, 2010). [25] J. Stopple, ‘Notes on Low discriminants the generalized Newman conjecture’, Funct. Approx. Comment. Math. 51(1) (2014), 23–41.
[26] J. Stopple, ‘Lehmer pairs revisited’, Exp. Math. 26(1) (2017), 45–53.
[27] T. Tao, Nonlinear Dispersive Equations: Local and Global Analysis, CBMS Regional Conference Series in Mathematics, 106 (American Mathematical Society, Providence, RI, 2006), Published for the Conference Board of the Mathematical Sciences, Washington, DC. [28] T. Tao and V. H. Vu, Additive Combinatorics, Vol. 105 (Cambridge University Press, Cambridge, 2006). [29] E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd edn (Oxford University Press, Oxford, 1986), (revised by D. R. Heath-Brown).
https://doi.org/10.1017/fmp.2020.6 Published online by Cambridge University Press