---
title: "New large value estimates for Dirichlet polynomials"
authors:
  - "Larry Guth"
  - "James Maynard"
date: "2024-00-00 2024"
publication: "Annals of Mathematics"
doi: null
url: "https://annals.math.princeton.edu/articles/22049"
zotero:
  attachment_key: "HRQ9DQIP"
  parent_key: "6HFW39UU"
  item_id: 1965
  attachment_item_id: 2052
---

arXiv:2405.20552v1 [math.NT] 31 May 2024
NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS
LARRY GUTH AND JAMES MAYNARD
Abstract. We prove new bounds for how often Dirichlet polynomials can take large values. This gives improved estimates for a Dirichlet polynomial of length N taking values of size close to N 3/4, which is the critical situation for several estimates in analytic number theory connected to prime numbers and the Riemann zeta function. As a consequence, we deduce a zero density estimate N (σ, T ) ≤ T 30(1−σ)/13+o(1) and asymptotics for primes in short intervals of length x17/30+o(1).
1. Introduction
In this paper we prove new bounds for the frequency of large values of Dirichlet polynomials. This gives improved estimates for a Dirichlet polynomial of length N taking values of size close to N 3/4. Our main result is the following.
Theorem 1.1 (Large values estimate). Suppose (bn) is a sequence of complex numbers with |bn| ≤ 1, and (tr)r≤R is a sequence of 1-separated points in [0, T ]
such that ∣∣∣
2∑N
n=N
bnnitr
∣∣∣ ≥ V
for all r ≤ R. Then we have
R ≤ T o(1)(
N 2V −2 + N 18/5V −4 + T N 12/5V −4)
.
The bound of Theorem 1.1 can be compared with the bound
(1.1) R ≤ T o(1)(
N 2V −2 + T min(N V −2, N 4V −6)
)
coming from combining the classical Mean Value Theorem for Dirichlet polynomials and the Montgomery-Halasz-Huxley large values estimate. Together these previous results give stronger bounds when V is smaller than N 7/10−ǫ or bigger than N 8/10+ǫ, but Theorem 1.1 gives a stronger bound when N 7/10+ǫ < V < N 8/10−ǫ and N ≤ T 5/6−ǫ. There are various improvements of the large values estimate which will supersede ours when V is a bit larger than N 3/4 (see [Iv, Chapter 11], for example), but Theorem 1.1 represents the first substantive improvement on the bound (1.1) coming from the Mean Value Theorem when V ≤ N 3/4 or on bounds when V is close to N 3/4.
1


 2 LARRY GUTH AND JAMES MAYNARD
The key interest in this result is that for many applications in analytic number theory, it is the case when V ≈ N 3/4 which is the critical limiting scenario. In this situation the Mean Value Theorem and Large Values Estimate both give a bound of roughly N 1/2 + T N −1/2 whereas Theorem 1.1 gives roughly N 3/5 + T N −3/5. Therefore we obtain an improvement for N smaller than T 10/11, and correspondingly we expect Theorem 1.1 to lead to a quantitative improvement to any result where this covers the limiting situation.
One well-studied situation where the limiting case is improved by Theorem 1.1 is zero-density estimates for the Riemann Zeta function ζ(s). Let N (σ, T ) be the number of zeroes of ζ(s) in the rectangle R(s) ≥ σ and |I(s)| ≤ T . After early work by Carlson [Ca], Ingham [In] proved the bound
(1.2) N (σ, T ) ≤ T 3(1−σ)
2−σ +o(1),
ultimately relying on the Mean Value Theorem for Dirichlet polynomials. Huxley [Hu], building on work of Montgomery [M3] and Halasz [Ha] and ultimately relying on the Montgomery-Halasz large values estimate, proved the bound
(1.3) N (σ, T ) ≤ T 3(1−σ)
3σ−1 +o(1).
This improves on (1.2) for σ > 3/4 (corresponding to when the term N 4V −6 is smaller than N V −2 for V = N σ in min(N V −2, N 4V −6) in (1.1)).
When σ ≈ 3/4 the bounds (1.2) and (1.3) coincide, and the critical situation turns out to be related to values of size V = N 3/4 of Dirichlet polynomials of length N = T 4/5, where both estimates give R ≤ T 3/5+o(1). In this situation Theorem 1.1 gives an improved estimate of R ≤ T 13/25+o(1). Incorporating Theorem 1.1 into the zero density machinery gives the following result.
Theorem 1.2 (Zero density estimate). Let N (σ, T ) denote the number of zeros ρ of ζ(s) with R(ρ) ≥ σ and |I(ρ)| ≤ T . Then we have
N (σ, T ) ≪ T 15(1−σ)/(3+5σ)+o(1).
Combining this with Ingham’s estimate when σ ≤ 7/10, we obtain
(1.4) N (σ, T ) ≪ T 30(1−σ)/13+o(1).
The exponent 30/13 improves on the previous exponent of 12/5 due to Huxley [Hu]. This has the following corollaries for the distribution of primes in short intervals.
Corollary 1.3 (Count of primes in short intervals). Let y ∈ [x17/30+ǫ, x0.99]. Then we have
π(x + y) − π(x) = y
log x + Oǫ
(
y exp(− 4 √log x)
) .


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 3
The exponent 17
30 improves on the previous exponent 7
12 due to Huxley [Hu].
Corollary 1.4 (Count of primes in ‘almost-all’ short intervals). Let y ∈ [X2/15+ǫ, X0.99].
Then for all but O(X exp(− 4 √log x)) choices of x ∈ [X, 2X] we have
π(x + y) − π(x) = y
log x + Oǫ
(
y exp(− 4 √log x)
) .
The exponent 2
15 improves on the previous exponent 1
6 due to Huxley [Hu].
We expect there to be various further applications of Theorem 1.1 (and the underlying ideas) to improving quantitative estimates related to the primes and similar objects.
1.1. Background. Given an integer N ∈ N and a sequence (bn)n∈[N,2N], a Dirichlet polynomial is a trigonometric sum of the form
(1.5) D(t) =
2∑N
n=N
bneit log n.
We say such a polynomial has length N , and we study the question how often a Dirichlet polynomial can be large in the interval [0, T ]. The precise question can be formulated as follows.
Main Question. Suppose that D(t) is a Dirichlet polynomial of the form (1.5) with |bn| ≤ 1 for all n. Suppose that W ⊂ [0, T ] is a 1-separated set of points t
where |D(t)| > N σ. What is the largest possible cardinality of W , in terms of N , T , and σ?
There are many examples where |W | & N 2−2σ. Montgomery’s large value conjecture [M2, page 142, Conjecture 2] predicts that under some natural conditions this lower bound is essentially tight.
Conjecture 1.5 (Montgomery’s large value conjecture). Let σ > 1/2 and D(t) =
∑2N
n=N bneit log n with |bn| ≤ 1. Suppose W ⊂ [0, T ] is a 1-separated set such that
|D(t)| > N σ for t ∈ W . Then
|W | ≤ C(σ)T o(1)N 2−2σ.
Using a simple orthogonality argument, it has long been known that for any T ≥ N ,
(1.6) |W | . T N 1−2σ,
which corresponds to the term N V −2 in min(N V −2, N 4V −6) in (1.1).
This basic estimate has been improved in several regimes. An integer power of a Dirichlet polynomial is a Dirichlet polynomial, and applying (1.6) to powers of D


 4 LARRY GUTH AND JAMES MAYNARD
gives improved bounds when N is fairly small compared with T . For σ ≤ 3/4, the best previous bounds on our main question came from this approach. In particular, if σ ≤ 3/4 and if N ∈ [T 2/3, T ], then (1.6) represented the best known bound.
In the late 60s, Montgomery [M], building on ideas of Halasz [Ha] and Tur ́an [HT], showed that Conjecture 1.5 is true if σ is sufficiently large. Indeed, (1.1) gives Conjecture 1.5 when N σ > N 1/2T 1/4. The large value method gives very strong information for large σ, but it gives no information if σ ≤ 3/4 as Montgomery explains in [M2, page 141]. For σ closer to 1, there have been several refinements of the underlying ideas (see, for example, [Bo, HB3, Ju]).
If one knows some more structure about the set of large values of a Dirichlet polynomial, then one can hope to have improved bounds. For example, another important result is Heath-Brown’s work about the behavior of Dirichlet polynomials on difference sets:
Theorem 1.6 (Heath-Brown, [HB]). Suppose that T is a 1-separated set of points in an interval of length T . Let |an| / 1 be a complex sequence. Then
∑
t1 ,t2 ∈T
∣∣∣
2∑N
n=N
an ni(t1 −t2 ) ∣∣∣
2 / |T |2N + |T |N 2 + |T |5/4T 1/2N.
In the range N ∈ [T 2/3, T ], the last term can be ignored and the right-hand side is essentially sharp. Theorem 1.6 gives strong information about our main question if the set W has a lot of additive structure, such as arithmetic progressions.
We will make this precise using the idea of additive energy, which we define as follows. For a finite set W , let
(1.7) E(W ) := #{w1, w2, w3, w4 ∈ W : |w1 + w2 − w3 − w4| < 1}.
A simple consequence of Theorem 1.6 is the following (we give a proof, as well as refined bounds, in Section 11).
Lemma 1.7. Let N ∈ [T 2/3, T ], σ > 1/2 and D(t) = ∑2N
n=N bnnit with |bn| ≤ 1.
Suppose W ⊂ [0, T ] is a 1-separated set such that |D(t)| > N σ for t ∈ W . Then
E(W ) ≤ |W |3N 1−2σ+o(1) + |W |2N 2−2σ+o(1).
If E(W ) is very large, say E(W ) > |W |3T −o(1), then E(W ) is larger than the first term on the right hand side, so it must be bounded by the second term. This implies Conjecture 1.5 for Dirichlet polynomials DN with E(W ) ' |W |3. Thus we can obtain improved bounds for Dirichlet polynomials whose large value set has a lot of additive structure.
We introduce a new method that gives good bounds for Dirichlet polynomials on sets of small energy. We outline our method in the next section.


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 5
1.2. Notations and conventions. We write A . B to mean that A ≤ CB for an absolute constant C, and A .z B to denote that the constant C may depend on the parameter z. We write A ≍ B to mean A . B and B . A both hold, and A ∼ B to mean B < A ≤ 2B. Similarly, we write A / B to mean that for any ǫ > 0, there is a constant C(ǫ) > 0 depending only on ǫ such that A ≤ C(ǫ)T ǫB for all large T , and A /z B to denote a dependency on a parameter z. Asymptotic quantities such as o(1) are interpreted as T → ∞.
We use e(x) := e2πix to denote the complex exponential. Summations will run over integers unless specified otherwise.
1.3. Acknowledgements. LG would like to thank Yuqiu Fu for many interesting discussions about this problem. LG is supported by a Simons Investigator Award. JM is supported by the European Research Council (ERC) under the European Union’s Horizon 2020 research and innovation programme (grant agreement No 851318).
2. Sketch outline
For a heuristic description of our argument, let us consider a critical case of previous zero density estimates, where σ = 3/4 and we wish to improve upon the bound |W | / T N −1/2 for any set W of separated points in an interval of length T such that |DN (t)| > N 3/4 when t ∈ W . We focus on the situation when T = N 1+δ for some small constant δ > 0 (a corresponding improvement for larger values of T then follows by subdivision), and suppress many technical details (such as the presence of smoothing in most summations) for exposition.
Let M be the |W | × N matrix with entries
Mt,n = nit
for t ∈ W and n ∼ N . We see that if b = (bn)n∼N then
DN (t) = ∑
n
bnnit = (M b)t,
and so we have (recalling |bn| ≤ 1)
N 3/2|W | = N 2σ|W | < ∑
t∈W
|Db(t)|2 = ‖M b‖22 ≤ ‖M ‖2‖b‖22 ≤ N ‖M ‖2,
where ‖M ‖ is the matrix (operator) norm of M . Thus we wish to improve upon the bound ‖M ‖ / T 1/2 which follows from the Mean Value Theorem (or the Large Values Estimate), and we might hope that ‖M ‖ ≈ |N |1/2. We note that
‖M ‖ = s1(M )


 6 LARRY GUTH AND JAMES MAYNARD
where s1(M ) is the largest singular value of M . This is also the square-root of the
largest eigenvalue of M ∗M . A simple bound for s1(M ) is then given by the trace
of powers of M ∗M ; for any r ∈ N
s1(M ) ≤ tr((M ∗M )r)1/2r.
We might hope tr((M ∗M )r) ≈ |W |N r, which would imply s1(M ) ≤ N 1/2|W |1/2r. Unfortunately it appears to be very difficult to estimate these traces accurately for large r, and we would only improve upon the bound |W | / T N −1/2 if (T N −1/2)1/r ≤ T N −1, which requires r to be large. Nevertheless, a variant of this bound for r = 3 (which reduces the contribution from some of the trivial terms) allows one to show a bound similar to
s1(M )6 /
∣∣∣ ∑
t1 ,t2 ,t3 ∈W
|tj −tk |>T ǫ ∀j,k
∑
n1 ,n2 ,n3 ∼N
ni(t1 −t2 )
1 ni(t2−t3)
2 ni(t3−t1)
3
∣∣∣.
The right hand side would be tr((M ∗M )3) if we didn’t have the lower bounds on |ti − tj| (and so we avoid the t1 = t2 = t3 terms). To improve upon the bound |W | / T N −1/2 we wish to show the right hand side is a bit smaller than T 3.
The natural approach to estimating the right hand side would be to apply Poisson summation and stationary phase to each of the inner sums, which would yield a bound of roughly
N3
T 3/2
∣∣∣ ∑
t1 ,t2 ,t3 ∈W
∑
m1,m2,m3∼T /N
mi(t1 −t2 )
1 mi(t2−t3)
2 mi(t3−t1)
3 ct1−t2 ct2−t3 ct3−t1
∣∣∣
for some coefficients ct of size 1. Unfortunately the cti−tj coefficients link the variables t1, t2 and t3, and this makes it difficult to show any cancellation over these summations. Without any cancellation in the t1, t2, t3 sums we would be
limited to a bound of |W |3N 3/2 ≈ T 3 even if we obtained square-root cancellation in the sums over m1, m2, m3, and so this would fail to give the desired improvement on T 3 (but could potentially give results if σ > 3/4).
A key observation is that it can be beneficial to avoid the use of stationary phase. Applying Poisson summation without simplifying the Fourier integrals yields a bound of roughly
N3 ∑
t1 ,t2 ,t3 ∈W
∑
|m1|,|m2|,|m3|∼T /N
∫
[1,2]3
e−2πiN m·u( u1
u3
)it1 ( u2
u1
)it2 ( u3
u1
)it3 du
≤ N3 ∑
|m|∼T /N
∣∣∣
∫
[1,2]3
e−2πiN m·uR
( u1
u3
) R
( u2
u1
) R
( u3
u2
)
du
∣∣∣,


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 7
where R(x) := ∑
x∈W xit. By not simplifying the integrals over u directly we have
given up a factor of T 3/2, but now the variables t1, t2, t3 are nicely separated from one another, and we can hope to show cancellation in these sums by showing the R function exhibits cancellation. However, even square-root cancellation in R(x) would only win back a factor of |W |3/2 which is less than the T 3/2 factor we gave up by not applying stationary phase. Therefore we need to exploit simultaneous cancellation in the integral over u and the R functions.
The next important observation is that the arguments of the R functions only lie in a two dimensional subvariety z1z2z3 = 1. If we change variables to v1 = u1/u3 and v2 = u2/u3 then the integral above is roughly
∫
[1/2,2]2
(∫
[1,2]
e−2πiN (m1v1+m2v2+m3)u3 du3
)
R(v1)R
( v2
v1
) R
(1
v2
)
dv1dv2.
There is a large amount of cancellation in the inner integral unless m1v1 + m2v2 + m3 ≈ 0, and this allows us to win back a factor of T . We are then reduced to bounding expressions of the form
(2.1) N 3
T
∑
|m|∼T /N
∣∣∣
∫
(v1 ,v2 )∈[1/2,2]2
m1 v1 +m2 v2 +m3 =0
R(v1)R
( v2
v1
) R
(1
v2
)
dv1
∣∣∣.
If we had uniform square-root cancellation in the R functions, we would now get a bound of T 2|W |3/2, which comfortably beats the desired bound of T 3 when |W | ≈ T N −1/2, and so we would get a corresponding improvement to the large value estimates and zero density results.
Of course, we cannot expect to prove uniform square-root cancellation in the R function for arbitrary sets W . Nevertheless, one can show that R does exhibit cancellation on average; ‖R(v)‖2L2([1/2,2]) / |W | and ‖R(v)‖4L4([1/2,2]) / E(W ), where E(W ) from (1.7) counts approximate additive quadruples in W . Treating the m summation trivially, this would give a bound
(2.2) T 2|W |1/2E(W )1/2,
which would beat the target of T 3 if E(W ) is a bit smaller than T 2/|W | ≈ N 2|W |3/T 2. Thus we obtain good bounds whenever E(W ) is small. In particular, when T ≈ N 1+δ with δ small, this means that we can handle any set W except those for which the additive energy is close to the maximal possible value of |W |3.
We would like to complement this with an argument for when E(W ) is large. As mentioned in the introduction, Heath-Brown’s result becomes useful in this situation. Lemma 1.7 can handle the case when E(W ) is larger than |W |2N 1/2 ≈ |W |3N/T , which isn’t quite strong enough to cover all ranges. A refinement of this lemma can handle the situation when E(W ) is larger than |W |3N 2/T 2 (at


 8 LARRY GUTH AND JAMES MAYNARD
least when δ is small and |W | ≈ T N −1/2), which then allows us to get a small improvement in all cases except when E(W ) ≈ |W |3N 2/T 2.
To overcome this final obstacle when E(W ) ≈ |W |3N 2/T 2, we go back to (2.1), and exploit the averaging over m. After a change of variables we need to consider
N3
T
∑
|m1|,|m2|,|m3|∼T /N
∫
v1 ∈[1/2,2]
∣∣∣R(v1)R
( m1v1 + m3
m2v1
) R
( m1v1 + m3
m2
)∣∣∣dv1.
The only way the bound above could be tight is if there is a sparse set U on which R(u) is large, and such that for most u ∈ U and most |m1|, |m2|, |m3| ∼ T /N we have (m1u + m3)/m2 ∈ U and (m1u + m3)/(m2u) ∈ U . We show that there cannot be a small set U which has this property of being approximately closed under such affine transformations, and this ultimately leads to an improvement of (2.2) to roughly
T N |W |1/2E(W )1/2.
This now gives an improvement on the desired bound of T 3 whenever E(W ) is smaller than |W |3, and so the bounds obtained on E(W ) stemming from HeathBrown’s result above are now sufficient to give an improvement for any size of E(W ). Therefore we obtain an improvement on the bound |W | / T N −1/2 for arbitrary W .
3. Reduction to Main Proposition
We fix a smooth function w : R → R≥0 supported on [1, 2] with ‖w(j)‖∞ = Oj(1) for all j ∈ Z≥0 and with w(t) = 1 for t ∈ [6/5, 9/5].
Proposition 3.1. Let σ ∈ [7/10, 8/10] and ǫ > 0. If bn is a sequence of complex
numbers with |bn| ≤ 1 and W is a set of T ǫ-separated points in an interval of length T = N 6/5 such that
∣∣∣∑
n
w
(n
N
)
bnnit∣∣∣ ≥ N σ
for all t ∈ W. Then we have
|W | ≤ T N (12−20σ)/5+oǫ(1).
Proof of Theorem 1.1 assuming Proposition 3.1. As mentioned in the introduction, the result follows from (1.1) if V ≤ N 7/10+o(1) or if V ≥ N 8/10−o(1), so we may assume V ∈ [4N 7/10, N 8/10], in which case N 2V −2 ≤ N 18/5V −2. By splitting DN into 3 separate pieces (and using the triangle bound), we see that it suffices to show the result when bn = 0 unless n ∈ [6N/5, 9N/5]. Since the function w is 1 on [6/5, 9/5], we then have that bn = bnw(n/N ), so we may insert the weight w(n/N ).
Finally, by now relaxing the vanishing of the coefficients and letting V = N σ,


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 9
it suffices to show that whenever σ ∈ [7/10, 8/10], (an) is a 1-bounded complex sequence and W is a set of 1-separated points such that
∣∣∣∑
n
w
(n
M
)
annit∣∣∣ ≥ M σ
for each t ∈ W , we have
|W | ≤ T o(1)(M 18/5−4σ + T M 12/5−4σ).
We now fix ǫ > 0 and choose W ′ ⊂ W so that W ′ is T ǫ-separated and |W ′| ≥ |W |/T ǫ (this can be achieved by picking the smallest element of W and then repeatedly choosing the next smallest element which is at least T ǫ away from all picked elements). If T ≤ N 6/5, then we apply Proposition 3.1 to bound W ′ directly, which implies that
|W | ≤ T ǫ|W ′| ≤ N (18−20σ)/5+2ǫ+oǫ(1).
Letting ǫ → 0 sufficiently slowly then gives the result in this case. If instead T > N 6/5, then we divide W ′ into ⌈T /N 6/5⌉ subsets Wj′ each supported on an interval of length N 6/5, and we apply Proposition 3.1 to bound each Wj′ separately. This gives
|W | ≤ T ǫ ∑
j≤⌈T /N 6/5 ⌉
|Wj′| ≤ T 1+ǫN (12−20σ)/5+ǫ+oǫ(1).
Letting ǫ → 0 sufficiently slowly then gives the result in this case too.
4. The matrix MW and its singular values
Now we begin to work on the proof of Proposition 3.1. Recall that DN is a Dirichlet polynomial of the form
DN (t) = ∑
n
w
(n
N
)
bn nit ,
where w is a smooth bump supported on [1, 2], as defined in Section 3.
Given a set W ⊆ R, let MW be the |W | × N matrix with entries
(4.1) Mt,n = w(n/N )nit,
where t ∈ W and n ∼ N .
Lemma 4.1 (Large values of Dirichlet polynomials controlled by singular values). Let MW be the matrix defined in (4.1), and s1(MW ) its largest singular value. If
|DN (t)| ≥ N σ on W and if |bn| ≤ 1, then we have


 10 LARRY GUTH AND JAMES MAYNARD
|W | . N 1−2σs1(MW )2.
Proof. Let b be the vector with components bn. Then note that for each t in W ,
DN (t) = ∑
n
w(n/N )bnnit = (MW b)t.
Therefore we can relate the behavior of DN on W (for arbitrary b) to properties of the matrix MW , in particular its singular values. We write sj(MW ) for the jth singular value of MW , with the convention that s1(MW ) ≥ s2(MW ) ≥ ... ≥ sk(MW ). Let MW have singular value decomposition MW = U ΣV , so that Σ is a rectangular matrix with Σii = si(MW ) and Σij = 0 if i 6= j, and U , V are unitary matrices.
If |DN (t)| ≥ N σ on W , then we see
|W |N 2σ ≤ ∑
t∈W
|DN (t)|2 = (MW b)∗MW b = (V b)∗Σ2V b
≤ s1(MW )2‖V b‖l22
= s1(MW )2‖b‖l22.
Finally, if |bn| ≤ 1 then ‖b‖l22 . N . Substituting this into the expression above
and rearranging now gives the result.
Now s1(MW ) is equal to the square root of the largest eigenvalue value of the W ×W
matrix MW M ∗W , with entries
(MW M ∗W )t1,t2 = ∑ n
w
(n
N
)2 ni(t1−t2).
A simple bound for s1(MW ) is therefore to use the trace: for any integer r ≥ 1 we have
s1(MW )2 = s1(MW M ∗W ) ≤
( k ∑
j=1
sj (MW M ∗W )r )1/r = tr((MW M ∗W )r)1/r.
One might guess that sj(MW ) / N 1/2 for all j, in which case we would have tr((MW M ∗W )r)1/r / |W |1/rN . If one could establish such a sharp bound on
tr((M ∗W MW )r) for large r, this would give Conjecture 1.5. Unfortunately we do not know how to obtain good bounds when r ≥ 4, so we work with r = 3. In this case, even a sharp bound tr((MW M ∗W )3)1/3 / |W |1/3N would only yield |W | / N 3−3σ, which is worse than the bounds established by previous works. To get around this issue, we note that if we are in the extreme scenario when


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 11
1 k
k ∑
i=1
si(MW )6 =
(1
k
k ∑
i=1
si(MW )2)3
then in fact we must have that all the singular values are the same, and so s1(MW ) = tr((MW M ∗W )3)1/6k−1/6, a significant improvement on the bound tr((MW M ∗W )3)1/6
we had before. Similarly, we would expect that if tr((MW M ∗W )3) is close to
tr(MW M ∗W )3/k2, then we would also get an improved bound on s1(MW ) since
most of the contribution to tr((MW M ∗W )3) would be coming from the many other singular values. The following lemma makes this precise, stating that we can essentially replace tr((MW M ∗W )3) with the difference tr((MW M ∗W )3) − tr(MW M ∗W )3/k2 for the purposes of bounding s1(MW ).
Lemma 4.2 (Bound for singular values in terms of traces). Let A be an m × n complex matrix. Then we have
s1(A) ≤ 2
(
tr((AA∗)3) − tr(AA∗)3
m2
)1/6 + 2
( tr(AA∗) m
)1/2.
Proof. Recall that tr((AA∗)j) = ∑m
i=1 λj
i where λ1, . . . , λm are the eigenvalues
of the m × m matrix AA∗, which are real and non-negative, and that s1(A) = maxi λ1/2
i . We see that it is sufficient to show for any non-negative reals x1, . . . xk
(4.2) x1 ≤ 2
( k ∑
i=1
xi6 − (∑k
i=1 xi2)3 k2
)1/6 + 2
( ∑k
i=1 xi2
k
)1/2 .
By Ho ̈lder’s inequality, we have that ∑k
i=2 xi6 ≥ (∑k
i=2 xi2)3/(k−1)2 ≥ (∑k
i=2 xi2)3/k2.
Thus
x61 =
k ∑
i=1
xi6 −
k ∑
i=2
xi6 ≤
k ∑
i=1
xi6 − (∑k
i=2 xi2)3 k2
≤
( k ∑
i=1
xi6 − (∑k
i=1 xi2)3 k2
)
+ 3x21
(∑k
i=1 xi2)2
k2 .
This in turn implies (4.2) (if (4.2) failed then x61 would be larger than the right hand side above.)
Thus we wish to estimate tr(MW M ∗W ) and tr((MW M ∗W )3). In both cases we expand the trace and use Poisson summation as a first step. In anticipation of this, we introduce the function
(4.3) ht(u) := w(u)2uit,


 12 LARRY GUTH AND JAMES MAYNARD
which appears in the sums defining the coefficients of MW M ∗W . We first record a
basic tail estimate for the Fourier transform ˆht.
Lemma 4.3 (Non-stationary phase). Let ht(u) = w(u)2uit. Then we have
(1) For any integer j ≥ 0 we have
hˆt(ξ) .j (1 + |t|)j/|ξ|j.
(2) For any integer j ≥ 0 we have
hˆt(ξ) .j (1 + |ξ|)j/|t|j.
Proof. Since ‖w(j)‖∞ .j 1 for all j ≥ 0, we have that ‖h(j)
t ‖∞ .j 1 + |t|j for all j ≥ 0. Thus, by integration by parts (and using that w is compactly supported), we have that
ˆht(ξ) =
∫
e(−ξu)ht(u)du = 1
ξj
∫
e(−ξu)h(j)
t (u)du .j
1 + |t|j
|ξ|j .
Similarly, if gξ(u) = e(−ξu)w(u)2 then ‖g(j)
ξ ‖∞ .j 1 + |ξ|j, so integration by parts
gives
ˆht(ξ) =
∫
gξ(u)uitdu = 1
(it + 1) · · · (it + j)
∫
g(j)
ξ (u)uit+j du .j
1 + |ξ|j
|t|j .
Lemma 4.4 (Hibert-Schmidt Norm estimate). If W ⊂ R is a finite set with |W | ≤ N O(1), then
tr(MW M ∗W ) = N |W | ‖w‖2L2 + O(N −100).
Proof. Expanding the trace, we see that
tr(MW M ∗W ) = ∑
t∈W
∑
n
w(n/N )2 = |W | ∑
n∈Z
h0(n/N ).
Because h0 is a smooth compactly supported function, the sum ∑
n h0(n/N ) is very
close to the integral N ∫
R h0(u)dξ = N ‖w‖2L2. We can get a precise estimate using
Poisson summation, which gives (separating the term m = 0)
∑
n
h0(n/N ) = N ∑
m
̂h0(N m) = N ̂h0(0) + O
(∑
m6=0
|̂h0(N m)|
) .
The first term on the right hand side is N ‖w‖2L2 and the second term is O(N −100)
by Lemma 4.3.
Lemma 4.5 (Expansion of the cubic trace). Let W be T ǫ-separated. Then we have
tr((MW M ∗W )3) = N 3|W |‖w‖6L2 + ∑
m∈Z3\{0}
Im + Oǫ(T −100),


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 13
where
Im := N 3 ∑
t1 ,t2 ,t3 ∈W
ˆht1−t2 (m1N )ˆht2−t3 (m2N )ˆht3−t1 (m3N ).
Proof. First we expand tr((MW M ∗W )3) as the sum S, given by
S= ∑
n1 ,n2 ,n3 ∈Z
∑
t1 ,t2 ,t3 ∈W
w
( n1 N
)2w
( n2 N
)2w
( n3 N
)2 ni(t1 −t2 )
1 ni(t2−t3)
2 ni(t3−t1)
3
=∑
t1 ,t2 ,t3 ∈W
∑
n1 ,n2 ,n3 ∈Z
ht1−t2
( n1 N
)
ht2−t3
( n2 N
)
ht3−t1
( n3 N
) ,
where, as in (4.3), we have ht(u) = w(u)2uit. We now perform Poisson summation in n1, n2, n3, which gives
S = N3 ∑
m1 ,m2 ,m3 ∈Z
∑
t1 ,t2 ,t3 ∈W
ˆht1−t2 (m1N )ˆht2−t3 (m2N )ˆht3−t1 (m3N ) = ∑
m∈Z3
Im.
Finally, we separate the term m1 = m2 = m3 = 0, which contributes
I0 = N 3 ∑
t1 ,t2 ,t3 ∈W
ˆht1−t2 (0)ˆht2−t3 (0)ˆht3−t1 (0).
Since W is T ǫ-separated, ˆht1−t2 (0) .ǫ T −200 if t1 6= t2 by Lemma 4.3. Thus the terms in the I0 above are negligible unless t1 = t2 = t3, and so
I0 = N 3 ∑
t∈W
ˆh0(0)3 + Oǫ(T −100) = |W |‖w‖6L2 + Oǫ(T −100).
Putting this together gives the result.
Putting together Lemmas 4.1-Lemma 4.5, and noting that the N 3|W |‖w‖3L2 term
cancels with tr(MW M ∗W )3/|W |2, gives the following.
Proposition 4.6. Let W be T ǫ-separated, and let |bn| ≤ 1 be such that |DN (t)| >
N σ for all t ∈ W . Then we have
|W | .ǫ N 2−2σ + N 1−2σ( ∑
m∈Z3\{0}
Im
)1/3,
where Im is the quantity defined in Lemma 4.5.
The first term above corresponds to the best possible estimate is |W | . N 2−2σ of Conjecture 1.5, and so our task is reduced to getting a good bound for the sum of Im.


 14 LARRY GUTH AND JAMES MAYNARD
5. The pieces of the sum S
Recall from Proposition 4.6, we have
|W |3 . N 6−6σ + N 3−6σ ∑
m∈Z3\{0}
Im,
where
Im = N 3 ∑
t1 ,t2 ,t3 ∈W
ˆht1−t2 (m1N )ˆht2−t3 (m2N )ˆht3−t1 (m3N ).
To get started, we note a few cases when |ˆht1−t2 (mN )| is easy to understand via
Lemma 4.3. Since W is T ǫ-separated, we see that if t1 6= t2, by Lemma 4.3 we have
(5.1) |ˆht1−t2 (0)| .ǫ T −100.
On the other hand, if t1 = t2, then we have
(5.2) ˆht1−t2 (0) = ˆh0(0) =
∫
w2(u)du ≍ 1.
If t1 = t2 but m 6= 0, then by Lemma 4.3 we have
(5.3) |ˆht1−t2 (mN )| . m−100N −100.
Finally, if m > T 1+ǫ/N , then since W is contained in an interval of length T , we have by Lemma 4.3 and taking j = ⌈200/ǫ⌉ + 100
(5.4) |ˆht1−t2 (mN )| .ǫ
T 100
(mN )100
(T
T 1+ǫ
)200/ǫ . T −100m−100.
With this in mind, we divide the sum into pieces
(5.5) ∑
m∈Z3\{0}
Im = S1 + S2 + S3,
where S1 contains the terms where exactly one mi is non-zero, S2 contains the terms where exactly two mi are non-zero, and S3 contains the terms where all three mi are non-zero.
We will see that S1 is negligible. In the next section, we will bound S2 using Heath-Brown’s theorem, Theorem 1.6. The main part of the paper is concerned with studying S3, which contains most of the terms and is most difficult.


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 15
Proposition 5.1 (S1 bound). We have
S1 = Oǫ(T −10).
Proof. By symmetry, we see that
S1 ≤ 3N 3 ∑
t1 ,t2 ,t3 ∈W
∑
m36=0
|ˆht1−t2 (0)ˆht2−t3 (0)ˆht3−t1 (m3N )|.
By (5.4) (using the trivial bound |ˆht(ξ)| . 1 for the other factors), terms with
|m3| > T 1+ǫ/N contribute
.ǫ N 3|W |3 ∑
m>T 1+ǫ/N
T −100m−100 . T −10.
Thus we may restrict attention to terms with |m3| < T 1+ǫ/N . Next we consider
terms with t1 6= t2. Using (5.1) to bound |ˆht1−t2(0)| (and the trivial bound ˆht . 1
for the remaining factors), we see the terms with t1 6= t2 and |m3| < T 1+ǫ/N contribute
.ǫ N 3|W |3 T 1+ǫ
N T −100 / T −10.
Similarly, the terms with t2 6= t3 contribute Oǫ(T −10). The remaining terms have
t1 = t2 = t3. For these terms we apply (5.3) to bound |ˆht3−t1(m3N )|, which shows
that the terms with t1 = t2 = t3 also contribute Oǫ(T −10). This gives the result.
6. The contribution of S2
The aim of this section is to establish the following bound for the sum S2, which ultimately relies on Heath-Brown’s estimate 1.6.
Proposition 6.1 (S2 bound). For any choice of k ∈ N
S2 / N 2|W |2 + T N |W |2−1/k + N 2|W |2( T 1/2
|W |3/4
)1/k .
The proof of this proposition relies on the following consequence of stationary phase, which is part of the well-known ‘reflection principle’ for Dirichlet polynomials, or the approximate functional equation (values of a Dirichlet polynomial of length N at t ∈ [T, 2T ] are determined by values of a Dirichlet polynomial of length T /N ).
Lemma 6.2 (Approximate functional equation). For every t with |t| ∼ T0 ≥ T ǫ, we have ∣∣∣ ∑
m6=0
ˆht(mN )
∣∣∣ . 1
T 1/2
0
∫
u/1
∣∣∣ ∑
m/T0/N
m−i(t+u)∣∣∣du + O(T −100).
Although somewhat standard, we will give a detailed proof of Lemma 6.2 below. Let us first use it to bound S2.


 16 LARRY GUTH AND JAMES MAYNARD
Proof of Proposition 6.1 assuming Lemma 6.2. Recall that S2 is the sum of those Im where exactly two mi are non-zero. By symmetry, we have
S2 = 3N 3 ∑
m1 ,m2 6=0
∑
t1 ,t2 ,t3 ∈W
ˆht1−t2 (m1N )ˆht2−t3 (m2N )ˆht3−t1 (0).
If t1 6= t3, then (5.1) shows that the last factor ˆht3−t1 (0) is Oǫ(T −100), and so using
the bound ˆht(u) . (1 + |t|2)/|u|2 from Lemma 4.3 for the remaining factors, these
terms contribute Oǫ(T −10) in total. Therefore we have
S2 = 3N 3ˆh0(0) ∑
m1 ,m2 6=0
∑
t1 ,t2 ∈W
ˆht1−t2 (m1N )ˆht2−t1 (m2N ) + Oǫ(T −10).
Since ht(u) = w(u)2uit, we have h−t(u) = ht(u), and so ˆh−t(ξ) = ˆht(−ξ). In particular,
ˆht2−t1 (m2N ) = ˆht1−t2 (−m2N ).
Therefore, we can simplify the last equation to get
S2 = 3N 3ˆh0(0) ∑
t1 ,t2 ∈W
∣∣∣ ∑
m6=0
ˆht1−t2 (mN )
∣∣∣
2 + Oǫ(T −10).
Remark. Heath-Brown’s theorem, Theorem 1.6, gives a good estimate for the sum
∑
t1,t2∈W | ∑
m∈Z ˆht1−t2 (mN )|2. However we cannot apply it immediately because we need to be careful to leave out the term with m = 0. This term is related to I0 which we handled carefully in the previous section.
If t1 = t2, then ∑
m6=0 ˆht1−t2 (mN ) is negligible by (5.3) and (5.4). So, splitting the sum dyadically according to the size of t1 − t2, we find
S2 / N 3 sup
M =2j
T ǫ/N <M <2T /N
∑
t1 6=t2 ∈W |t1−t2|∼M N
∣∣∣ ∑
m6=0
ˆht1−t2 (mN )
∣∣∣
2 + Oǫ(T −10).
If |t1 − t2| ∼ M N , then ∑
m6=0 ˆht1−t2 (mN ) can be approximated by a Dirichlet polynomial of length M . Indeed, by Lemma 6.2, for such t1, t2 we have
∣∣∣ ∑
m6=0
ˆht1−t2 (mN )
∣∣∣ . 1
M 1/2N 1/2
∫
|u|/1
∣∣∣ ∑
1≤m/M
m−i(t−u)∣∣∣du + O(T −100).
Squaring and summing over t1, t2 ∈ W with |t1 − t2| ∼ N M gives


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 17
S2 / sup
M≤2T /N |u|/1
N2
M
∑
t1 6=t2 ∈W |t1−t2|∼M N
∣∣∣ ∑
1≤m/M
mi(t−u) ∣∣∣
2 + O(T −10).
We can now drop the condition |t1 − t2| ∼ M N for an upper bound, and split the summation range m / M into dyadic intervals. Noting that choosing all am to be zero apart from one gives a contribution which dominates the error term, we find
(6.1) S2 / N 2
M
∑
t1 ,t2 ∈W
∣∣∣ ∑
m∼M
am mi(t1 −t2 ) ∣∣∣
2
for some choice of M / T /N and some coefficients |am| ≤ 1.
We apply Ho ̈lder’s inequality to this sum, and rewrite the 2kth power of the Dirichlet polynomial as the 2nd power of a bigger Dirichlet polynomial. For any choice of positive integer k, we find that
∑
t1 ,t2 ∈W
∣∣∣ ∑
m∼M
am mi(t1 −t2 ) ∣∣∣
2 ≤ |W |2−2/k( ∑
t1 ,t2 ∈W
∣∣∣ ∑
m≍M k
bm mi(t1 −t2 ) ∣∣∣
2)1/k
(6.2)
for some coefficients bm ≤ M ok(1) (by the divisor bound). Theorem 1.6 bounds sums of this type. We recall the statement.
Theorem (Heath-Brown). Let T be a 1-separated set of reals, contained in an interval of length T . Let |an| / 1 be a complex sequence. Then
∑
t1 ,t2 ∈T
∣∣∣
2∑N
n=N
an ni(t1 −t2 ) ∣∣∣
2 / |T |2N + |T |N 2 + |T |5/4T 1/2N.
This result implies that
(6.3) ∑
t1 ,t2 ∈W
∣∣∣ ∑
m≍M k
bm mi(t1 −t2 ) ∣∣∣
2 /k |W |M 2k + |W |2M k + |W |5/4T 1/2M k.
Substituting (6.2) and (6.3) back into (6.1), we see that
S2 /k
N2
M (|W |2M + M 2|W |2−1/k + |W |2M T 1/2k|W |−3/4k)
/k N 2|W |2 + T N |W |2−1/k + N 2|W |2( T 1/2
|W |3/4
(6.4) )1/k.
This gives the result.


 18 LARRY GUTH AND JAMES MAYNARD
Now we return to the proof of Lemma 6.2, which roughly says ˆht(mN ) can be thought of as a smoothed version of t−1/2mit supported on m ≍ t/N .
Proof of Lemma 6.2. By Lemma 4.3, when |t| ≥ T ǫ we have ˆht(0) = O(T −100)
so we can include the term m = 0 at the cost of an Oǫ(T −100) error term. Let
W (s) := ∫ w(u)2us−1du be the Mellin transform of w2, which is entire and has |W (s)| .j |s|−j for all j ∈ N. Then by Poisson summation and Mellin inversion
(w(u)2 = (2πi)−1 ∫ 2+i∞
2−i∞ W (s)u−sds), we have that
(6.5) N 1+it ∑
m
ˆht(mN ) = ∑
n
w(n/N )2nit = 1
2πi
∫ 2+i∞
2−i∞
W (s)N sζ(s − it)ds.
We move the line of integration to R(s) = −1, picking up a pole at s = 1 + it, and then on the remaining contour we use the functional equation of the zeta function (see [Da, Chapter 8]), which states that ζ(s) = G(s)ζ(1 − s), where
G(s) := π−1/2+s Γ
( 1−s 2
)
Γ
(s 2
).
Thus we have (using the rapid decay of W to bound the contribution from the pole)
1 2πi
∫ 2+i∞
2−i∞
W (s)N sζ(s − it)ds = N 1+itW (1 + it) + 1
2πi
∫ −1+i∞
−1−i∞
W (s)N sζ(s − it)ds
= O(T −100) + 1
2πi
∫ −1+i∞
−1−i∞
(6.6) W (s)N sG(s − it)ζ(1 − s + it)ds.
We fix a small constant η > 0 and split the sum defining ζ(1 − s + it) at M := T ηT0/N . More specificall, write ζ(1 − s + it) = Z1(1 − s + it) + Z2(1 − s + it), where
Z1(s) := ∑
1≤m≤M
m−s, Z2(s) := ∑
m>M
m−s,
noting that Z2(s) converges absolutely when R(s) > 1. We substitute this into the integral above, and then move the integral involving Z1 to R(s) = 1 and the integral involving Z2 to R(s) = −2k for a large k ∈ N. This gives
(6.7) 1
2πi
∫ −1+i∞
−1−i∞
W (s)N sG(s − it)ζ(1 − s + it)ds = I1 + I2,
where (making a change of variables s = 1 + iu in I1 and s = −2k + iv in I2)


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 19
I1 := 1
2π
∫∞
−∞
W (1 + iu)N 1+iuG(1 + i(u − t))
(∑
1≤m≤M
mi(u−t))
du,
I2 := 1
2π
∑
m>M
∫∞
−∞
W (−2k + iv)N −2k+iv G(−2k + i(v − t))m−2k−1+i(v−t)dv.
From the rapid decay of W (s), we can truncate these integrals to |u|, |v| / 1 at the cost of an O(T −100) error term. It follows from well-known properties of the Gamma function (Stirling’s formula and the functional equation; see [Da, Chapter 10]) that for |u|, |v| / 1 and |t| > N we have
∣∣∣
Γ
( 1+i(u−t) 2
)
Γ
( i(t−u) 2
)
∣∣∣ . 1
|t|1/2 ,
∣∣∣
Γ
( 2k+1−i(v−t) 2
)
Γ
( −2k+i(v−t) 2
)
∣∣∣ =
∣∣∣
Γ
( 2k+1−i(v−t) 2
)
Γ
( 2k+i(v−t) 2
)
∣∣∣
k∏−1
j=−k
| − j + i(v − t)/2| .k |t|2k+1/2.
Recalling that |t| ∼ T0, we have G(1 + i(u − t)) . T −1/2
0 and G(−2k + i(v − t)) .k
T 2k+1/2
0 . Substituting these bounds in (and recalling M = T ηT0/N ), we find that
I1 . N
T 1/2
0
∫
|u|/1
∣∣∣ ∑
1≤m≤T ηM
mi(u−t)∣∣∣du + O(T −100),
I2 /k
T 2k+1/2
0 N −2k
(T ηT0/N )2k−1
∑
m>M
1
m2 .
If we choose k sufficiently large in terms of η, we then see that I2 = Oη(T −200). Substituting these bounds into (6.7), and combining this with (6.6) and (6.5) gives the result on letting η → 0.
7. The contribution of S3: a key cancellation
Now we begin to study S3, which is the most difficult term. Recall that
S3 = ∑
m1 ,m2 ,m3 6=0
Im,
where
Im = N 3 ∑
t1 ,t2 ,t3 ∈W
ˆht1−t2 (m1N )ˆht2−t3 (m2N )ˆht3−t1 (m3N ).


 20 LARRY GUTH AND JAMES MAYNARD
By Lemma 4.3, |ˆht(ξ)| /j (|ξ| + 1)j/|t|j for any j ∈ N, and so ˆht is rapidly decaying when |ξ| is much bigger than |t|, and hence Im is negligible unless |m| / T /N . Thus
(7.1) S3 = ∑
0<|m1|,|m2|,|m3|/T /N
Im + O(T −100).
The first step in our argument is an estimate for |Im|. We introduce the function
(7.2) R(v) := ∑
t∈W
vit = Wˆ (log v)
which will play an important role in our analysis of S3.
Proposition 7.1 (Cancellation within the Im integrals). We have
|Im| . N 3
∫
|m1v1+m2v2+m3|/ 1
N
v1 ≍v2 ≍1
∣∣∣R(v1)R
( v2
v1
)
R(v2)
∣∣∣dv1dv2 + O(T −200).
Moreover, if |m1| ≤ |m2| ≤ |m3|, then |Im| = O(T −200) unless |m2| ≍ |m3|.
Proof. Expanding the definition of ˆht as an integral and swapping the order of summation and integration, we have
Im = N 3 ∑
t1 ,t2 ,t3 ∈W
∫
R3
e(−N m · u)w1(u)ui(t1−t2)
1 ui(t2−t3)
2 ui(t3−t1)
3 du
= N3
∫
R3
e(−N m · u)w1(u)R
( u1
u3
) R
( u2
u1
) R
( u3
u2
)
(7.3) du,
where
(7.4) w1(u) := w(u1)2w(u2)2w(u3)2,
In (7.3), the R functions depend on u1/u3, u2/u1 and u3/u2. We therefore rewrite the integral using these variables. We define v1 and v2 by
v1 := u1
u3
, v2 := u2
u3
.
We rewrite the integral Im in terms of the variables v1, v2, u3. When we change variables, the R factors depend on v1, v2 but not on u3.
R
( u1
u3
) R
( u2
u1
) R
( u3
u2
)
= R(v1)R
( v2
v1
) R
(1
v2
)


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 21
The exponential factor also works out in a nice way in the new variables:
e−N m·u = e−N (m1u1+m2u2+m3u3) = e−N (m1v1+m2v2+m3)u3 .
And a Jacobian computation shows that
du1du2du3 = u23dv1dv2du3.
So in the new variables, our integral Im becomes
N3
∫
R3
e(−N (m1v1 + m2v2 + m3)u3)w1(u)R(v1)R
( v2
v1
) R
(1
v2
)
u23dv1dv2du3.
Since the R factors don’t involve u3 we rewrite our formula to do the u3 integral first:
N3
∫
R2
(∫
R
e(−N (m1v1 + m2v2 + m3)u3)w1(u)u23du3
)
R(v1)R
( v2
v1
) R
(1
v2
)
dv1dv2.
A key observation in our proof is that we can analyze the norm of this inner integral very accurately using non-stationary phase. Recalling the definition (7.4) of w1, we
see that for any j ∈ N, w1(u)u23 has jth derivative with respect to u3 bounded by
Oj(1) (since w is supported on [1, 2] with ‖w(l)‖∞ .l 1 for all l ∈ N). Thus for
any η > 0, the inner integral is Oη(T −300) unless |m1v1 + m2v2 + m3| ≤ T η/N by repeated integration by parts. In general, the inner integral has size . 1. In addition, w1(u) vanishes unless v1, v2 ∈ [1/2, 2], because
w1(u) = w(u1)2w(u2)2w(u3)2 = w(u3v1
)2w(u3v2
)2w(u3)2,
and w(u) is supported on u ∈ [1, 2]. Therefore, the inner integral vanishes unless v1 ∈ [1/2, 2] and v2 ∈ [1/2, 2]. Using these bounds for the inner integral and the triangle inequality, we see that since η > 0 was arbitrary
|Im| . N 3
∫
|m1v1+m2v2+m3|/ 1
N
v1 ,v2 ∈[1/2,2]
∣∣∣R(v1)R
( v2
v1
) R
(1
v2
)∣∣∣dv1dv2 + O(T −200).
Since |R(v)| = |R(1/v)|, we can replace R(1/v2) by R(v2). (This is not really important, but it makes later computations cleaner.)
Finally, this integral vanishes unless we can find v1 ≍ 1 and v2 ≍ 1 so that m1v1 + m2v2 + m3 is almost zero. If |m1| ≤ |m2| ≤ |m3|, this can only happen if |m2| ≍ |m3|. This gives the last claim in the proposition.


 22 LARRY GUTH AND JAMES MAYNARD
Remark. The cancellation in the inner integral when |m1v1 + m2v2 + m3| is not / 1/N is one of the key observations in our proof. This cancellation is specific to Dirichlet polynomials as opposed to more general trigonometric polynomials. For instance, one may consider a ‘generalized’ Dirichlet polynomial of the
form D ̃(t) = ∑
n∼N bneitφ(n), where the function φ(n) has smoothness and con
vexity properties similar to those of log n. One can follow the argument above,
but the inner integral will have the form ∫ e(N gm,v1,v2(u3))du3 for some function gm,v1,v2 (u3). In general, the function gm,v1,v2 (u3) will not be linear in u3. So one would have to use stationary phase as opposed to non-stationary phase, and the bounds would not work out as they do here.
Because of the last claim in Proposition 7.1, we can restrict attention to m with 0 < |m1| ≤ |m2| ≍ |m3|. The domain of integration can be rewritten in the form
∣∣∣∣v2 − m1v1 + m3
−m2
∣∣∣∣ / 1
|m2|N ≍ 1
|m3|N .
So the domain of integration is essentially the 1
N|m3| -neighborhood of the curve
v2 = m1v1+m3
−m2 . Therefore, |Im| is morally bounded by
N3
N |m3|
∫
v1 ≍1
∣∣∣R(v1)R
( m1v1 + m3 −m2v1
) R
( m1v1 + m3 −m2
)∣∣∣dv1.
We can make this rigorous by using a smoothed version of R. Suppose that ψ ̃(x) is a smooth bump which is ≍ 1 for |x| / 1 and supported in |x| / 1 (i.e. satisfying ‖ψ ̃(j)‖∞ /j 1 for all j ∈ N). Define a smoothed version of |R(u)| by
(7.5) R ̃M (u) :=
(∫
N M ψ ̃(N M (u − u′))ψ ̃(eu)|R(u′)|2du′)1/2.
The following proposition gives an expansion of S3 in terms of such integrals.
Proposition 7.2 (Expansion of S3). There is a choice of 0 < M1 ≤ M / T /N such that
S3 / N 2
M
∑
|m1|∼M1,|m2|,|m3|∼M
I ̃m + O(T −100),
where
I ̃m :=
∫
v1 ≍1
∣∣∣R(v1)R ̃M
( m1v1 + m3
m2v1
)R ̃M
( m1v1 + m3
m2
)∣∣∣dv1.
Proof. Recall from (7.1) that S3 is bounded by


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 23
S3 ≤ ∑
0<|m1|,|m2|,|m3|/T /N
|Im| + O(T −100).
From (7.3), we have
Im = N 3
∫
R3
e(−N m · u)w1(u)R
( u1
u3
) R
( u2
u1
) R
( u3
u2
)
du.
From the definition (7.2) for R(v), we see that R(1/v) = R(v). Therefore we see that I(m1,m2,m3) = I(m2,m1,m3), and similarly for any other transposition of (m1, m2, m3). Thus |Im| is invariant under any permutation of (m1, m2, m3), and so we can reduce to the case |m1| ≤ |m2| ≤ |m3| at the cost of a factor of 6. By Proposition 7.1, such terms are negligible unless |m2| ≍ |m3|. Thus, by choosing dyadic scales to maximize the right hand side, we find that there is an M1 ≤ M / T /N such that
(7.6) S3 / ∑
|m1 |∼M1 |m2|∼M |m3|∼M
|Im| + O(T −100).
By Proposition 7.1, we have for m2 ≍ M
|Im| . N 3
∫
v1 ≍1
|R(v1)|
(∫
∣∣∣v2− m1v1+m3
−m2
∣∣∣/ 1
MN
∣∣∣R
( v2
v1
)
R(v2)
∣∣∣dv2
)
dv1 + O(T −200).
Using Cauchy-Schwarz, we bound the inner integral by
(∫
∣∣∣v2− m1v1+m3
−m2
∣∣∣/ 1
MN
∣∣∣R
( v2
v1
)∣∣∣
2dv2
)1/2 (∫
∣∣∣v2− m1v1+m3
−m2
∣∣∣/ 1
MN
∣∣∣R(v2)
∣∣∣
2dv2
)1/2
.1
M N R ̃M
( m1v1 + m3 −m2v1
)
R ̃M
( m1v1 + m3 −m2
) .
Thus we find that
|Im| . N 2
M I ̃m + O(T −100).
Finally, since we are summing over m2 with |m2| ∼ M , we can replace −m2 with m2 without changing the overall sum. Substituting this into our expression (7.6) for S3 above then gives the result.


 24 LARRY GUTH AND JAMES MAYNARD
8. Basic estimate for the low energy case
In this section, we begin to estimate S3 using Proposition 7.2. Recall that R(v) =
∑
t∈W vit. The best bound for |R(v)| we can hope for is square root cancella
tion: |R(v)| . |W |1/2. If indeed |R(v)| ≈ |W |1/2 for all v ≍ 1, then we get S3 / N 2M 2|W |3/2 / T 2|W |3/2. We will see more generally that this bound holds whenever the energy of W is very small.
Proposition 8.1 (S3 controlled by energy). If W is a T ǫ-separated set contained in an interval of length T , then
S3 / T 2|W |1/2E(W )1/2.
Remark. If we look at the critical case when T = N 5/4 and σ = 3/4, then this estimate (together with our bounds for S2) gives an improvement to the basic orthogonality estimate (1.6) when E(W ) is significantly below |W |7/3. In the special case when E(W ) ≈ |W |2, this Proposition is enough to prove our main theorem, Theorem 1.1. On the other hand, when E(W ) is very large, then we will get good estimates using Theorem 1.6. However there is an intermediate range of energy that is not yet covered. In the next two sections, we will develop a strengthening of this proposition that gives new estimates for a wider range of energies.
We begin with some basic lemmas about the moments of R.
Lemma 8.2 (L2 bound). Let W be a T ǫ-separated set contained in an interval of length T . Then ∫
v≍1
|R(v)|2dv .ǫ |W |.
Proof. Let ψ1(v) be a smooth bump function which majorizes the range of integration of the integral in the lemma and is supported on v ≍ 1 (so satisfies ‖ψ(j)
1 ‖∞ .j 1 for all j ∈ N). Then we have
∫
v≍1
|R(v)|2dv ≤
∫
ψ1 (v)|R(v)|2 dv.
Recall from (7.2) that
R(v) = ∑
t∈W
vit = Wˆ (log v),
and let ψ2(τ ) := eτ ψ1(eτ ). Then, making a change of variables v = eτ
∫
ψ1(v)|R(v)|2dv =
∫
ψ2(τ )|Wˆ (τ )|2dτ = ∑
t1 ,t2 ∈W
ψˆ2(t1 − t2).
Note that ψ2 is a smooth bump around the origin with ‖ψ(j)
2 ‖∞ .j 1 for all j ∈ N,
so |ψˆ2(ξ)| .j |ξ|−j for any j ∈ N. Thus the terms with t1 = t2 contribute . |W |


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 25
to the sum above. Since W is T ǫ-separated, if t1 6= t2 we have that ψˆ2(t1 − t2) .ǫ
T −100, so the terms with t1 6= t2 are negligible. Thus the total sum is Oǫ(|W |), as required.
Lemma 8.3 (L4 bound). For any M we have
∫
v≍1
|R ̃M (v)|4dv / E(W ) and
∫
v≍1
|R(v)|4dv / E(W ).
Proof. From the definition (7.5) of R ̃ and Cauchy-Schwarz, we have
∫
v≍1
|R ̃M (v)|4dv / N 2M 2
∫
v≍1
|u−v|/1/N M |u′−v|/1/N M
|R(u′)|4du′dudv /
∫
u′≍1
|R(u′)|4du′.
Therefore it suffices to prove the result for R. We recall that R(v) = Wˆ (log v), so by a change of variables τ = ev we see that it suffices to show
∫
τ ≍1
|Wˆ (τ )|4dτ / E(W ).
Let η > 0 and let ψ be a smooth bump supported on τ . 1 such that ψ(τ /T η) majorizes the range of integration. Then we see that
∫
τ ≍1
|Wˆ (τ )|4dτ ≤
∫ ψ
(τ
Tη
)
|Wˆ (τ )|4dτ
=∑
t1 ,t2 ,t3 ,t4 ∈W
∫ ψ
(τ
Tη
)
e(τ (t1 + t2 − t3 − t4))dτ
= Tη ∑
t1 ,t2 ,t3 ,t4 ∈W
ψˆ
(
T η(t3 + t4 − t1 − t2)
) .
Since ψˆ decays rapidly, we may restrict the summation to |t1 + t2 − t3 − t4| ≤ 1 at
the cost of an Oη(T −100) error term. The remaining terms contribute . T ηE(W ). Thus, letting η → 0 we obtain
∫
τ ≍1
|Wˆ (τ )|4dτ / E(W ).
We can now quickly prove Proposition 8.1.
Proof of Proposition 8.1. Starting with Proposition 7.2, we have for some M1 ≤ M / T /N


 26 LARRY GUTH AND JAMES MAYNARD
S3 / ∑
|m1 |∼M1 |m2|,|m3|∼M
N2
M
∫
v1 ≍1
∣∣∣R(v1)R ̃M
( m1v1 + m3
m2v1
)R ̃M
( m1v1 + m3
m2
)∣∣∣dv1.
Using Ho ̈lder’s inequality, we find that the integral over v1 is bounded by
(∫
v1 ≍1
|R(v1)|2dv1
)1/2 (∫
v1≍1
∣∣∣∣R ̃M
( m1v1 + m3
m2v1
)∣∣∣∣
4
dv1
)1/4
×
(∫
v1 ≍1
∣∣∣∣R ̃M
( m1v1 + m3
m2
)∣∣∣∣
4
dv1
)1/4
.
In the second integral we do a change of variables u = m1v1+m3
m2v1 with Jacobian
factor ≍ 1. In the third integral we do a change of variables u = m1v1+m3
m2 with a
Jacobian factor of norm ∼ M/M1. Therefore we obtain
S3 . N 2M 2
(∫
v1≍1
|R(v1)|2dv1
)1/2 (∫
u≍1
∣∣∣R ̃M (u)
∣∣∣
4 du
)1/2
Using M / T /N and Lemmas 8.2 and 8.3, we find
S3 / T 2|W |1/2E(W )1/2.
When E(W ) ≈ |W |2, the bound from Proposition 8.1 is the best bound for S3 we know how to prove. But for larger E(W ), we can improve the bound for S3. Let us indicate the general direction here, and then we will develop the tool we need in the next section.
Ignoring some technical smoothing, we morally have
S3 / ∑
|m1|∼M1,|m2|,|m3|∼M
N2
M
∫
v1 ≍1
∣∣∣R(v1)R
( m1v1 + m3
m2v1
) R
( m1v1 + m3
m2
)∣∣∣dv1.
We can split up the domain of integration into pieces where the first R factor has size ∼ A1, the second R factor has size ∼ A2, and the third R factor has size ∼ A3. For simplicity, suppose that A1 = A2 = A3 = A, which we expect to be the critical case, and focus on the value of A that dominates the integral. If A ≈ |W |1/2, then we get the bound corresponding to minimal energy. If A is larger, then |R(v)| ∼ A for only a small subset UA ⊂ {v ≍ 1} by Lemma 8.2. If the simple analysis in Proposition 8.1 was sharp, it would mean that for most v ∈ UA and
most m1, m2, m3, we have m1v+m3
m2 ∈ UA. We will see that a small set U cannot be
approximately invariant under this large set of affine transformations. In the next


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 27
section, we will prove a precise estimate in this spirit, and then we will use it to give stronger bounds for S3 when the energy is greater than |W |2.
9. Summing over affine transformations
Given M > 0 and a compactly supported smooth function f , we define
J(f ) := sup
0<M1 ,M2 ,M3 <M
∫( ∑
|m1 |∼M1 ,m2 ∼M2 ,|m3 |.M3
f
( m1u + m3
m2
))2du,
which is an average of sums of affine transformations of f . The aim of this section is to establish the following general bound for J(f ).
Proposition 9.1 (Equidistribution over affine transformations). Suppose that f (u) is non-negative and supported on u ≍ 1 and that |fˆ(ξ)| /j (|ξ|/T )j for all j ∈ N. Then
J(f ) / M 6( ∫
f (u)du
)2 + M 4
∫
f (u)2du.
Remark. By a simple Cauchy-Schwarz argument, we can bound the left hand side
by M 6 ∫ |f (u)|2du. This bound is tight if f (u) is a smooth bump on u ∼ 1. But the Proposition improves on this bound when f (u) is sparse. To get a sense of what it means, it’s good to imagine the example that f = χU where U is a union of (smoothed) 1/T -intervals. The proposition says that if |U | is much smaller than 1, then the sets { m1U+m3
m2 }m1,m2,m3∼M cannot overlap too much.
There are two key examples which correspond to the two terms on the right-hand
side. If U is a random subset, then the left-hand side is comparable to M 6 (∫ f (u)du)2. If U is the 1/T neighborhood of the set of rational numbers p/q with p ∼ q ∼ B with the denominators having a divisor of size ∼ M , then the left-hand side is compara
ble to M 4 ∫ |f (u)|2du (the subsum where m1 divides the denominator of the closest such rational to u gives roughly this contribution).
The following lemma is the main technical result used to prove Proposition 9.1, which is based on a fairly long Fourier analytic argument.
Lemma 9.2 (Iterative bound for J(f )). Let f be as in Proposition 9.1. Then there is a bump function ψ(x) supported on |x| / 1 such that
J (f ) / M 6
(∫
f (u)du
)2
+
(
M4
∫
f (u)2du
)1/2J (f ̃)1/2.
where f ̃ is defined in terms of ψ(x) by


 28 LARRY GUTH AND JAMES MAYNARD
f ̃(u) :=
∫
T ψ(T (u − u′))f (u′)du′
Before we prove Lemma 9.2, we first show how to deduce Proposition 9.1 from it.
Proof of Proposition 9.1 assuming Lemma 9.2. We wish to show that for any ǫ > 0 there is a C(ǫ) > 0 such that
(9.1) J(f ) ≤ C(ǫ)T ǫ(
M6( ∫
f (u)du
)2 + M 4
∫
f (u)2du
) .
We wish to prove this by downwards induction on ǫ. As a base case, the result clearly holds for ǫ = 100. By induction, we can assume that (9.1) holds with 3ǫ/2 in place of ǫ and seek to establish (9.1). We first apply Lemma 9.2 to give
J(f ) / M 6( ∫
f (u)du
)2 +
(
M4
∫
f (u)2du
)1/2J (f ̃)1/2.
Since f (u) is supported on u ≍ 1 and ψ(x) is supported on x / 1, we see that f ̃(u) is also supported on u ≍ 1. Thus we may apply the induction hypothesis to J(f ̃), which shows
J (f ̃) .ǫ T 3ǫ/2(
M6( ∫
f ̃(u)du
)2 + M 4
∫
f ̃(u)2du
) .
Since f ̃ is a smoothed version of f , we can bound ∫ f ̃(u)du / ∫ f (u)du and
∫ f ̃(u)2du / ∫ f (u)2du. Substituting these bounds back into our bound for J(f ), we find
J (f ) /ǫ T 3ǫ/4
(
M6( ∫
f (u)du
)2 + M 4
∫
f (u)2du
)
.
Thus (9.1) holds for C(ǫ) sufficiently large, which completes the induction.
We now return to the proof of Lemma 9.2.
Proof of Lemma 9.2. The most interesting situation is when M1 = M2 = M3 = M . We encourage the reader to keep this case in mind on first reading.
We let ψ1(x) be a smooth bump supported on |x| . 1 so that ψ1(m3/M3) majorizes the summation condition m3 . M3. Thus we can bound the inner sum in J(f ) by
g(u) := ∑
|m1 |∼M1 ,m2 ∼M2
∑
m3
ψ1
( m3
M3
) f
( m1u + m3
m2
) .


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 29
Squaring and integrating over u, and then applying Plancherel gives (for the choice of M1, M2, M3 achieving the supremum)
(9.2) J(f ) ≤
∫
|g(u)|2du =
∫
|gˆ(ξ)|2dξ.
We wish to estimate gˆ(ξ). We have
gˆ(ξ) = ∑
|m1 |∼M1 ,m2 ∼M2
∫∑
m3
ψ1
( m3
M3
) f
( m1u + m3
m2
)
e(−ξu)du.
We do a change of variables: u ̃ = u + m3
m1 , so that f ( m1u+m3
m2 ) = f ( m1u ̃
m2 ). In the
new variables, we get
gˆ(ξ) = ∑
|m1 |∼M1 ,m2 ∼M2
(∫
f
( m1u ̃
m2
)
e(−ξu ̃)du ̃
)( ∑
m3 ∈Z
ψ1
( m3
M3
) e
( m3
m1
ξ
)) .
The integral in parentheses is m2
m1
fˆ( m2
m1 ξ). The first key point in our analysis is
that we can explicitly do the last sum by Poisson summation. It is equal to M3
∑
l ψˆ1(M3l − ξ
m1 )). So all together we have
gˆ(ξ) = ∑
|m1 |∼M1
M3
∑
l
ψˆ
(
M3
(ξ
m1
−l
)) ∑
m2 ∼M2
m2
m1
fˆ
( m2
m1
ξ
) .
Since ψˆ is rapidly decaying, ψˆ(M3( ξ
m1 − l)) is negligible unless |ξ − lm1| / M1
M3 .
Therefore, we have
(9.3) |gˆ(ξ)| ≤ ∑
|m1 |∼M1
∑
l:|ξ−m1l|/ M M31
M3
∣∣∣ ∑
m2 ∼M2
m2
m1
fˆ
( m2
m1
ξ
)∣∣∣ + O(T −100).
We have to estimate ∫
R |gˆ(ξ)|2dξ. For a small η > 0, we break up the domain of integration into the region |ξ| ≤ T ηM1/M3, the region T ηM1/M3 < |ξ| ≤ T 2 and the remainder:
(9.∫4)
R
|gˆ(ξ)|2dξ =
∫
|ξ|≤T η M M31
|gˆ(ξ)|2dξ
} {{ }
I
+
∫
T η M M13 <|ξ|≤T 2
|gˆ(ξ)|2dξ
} {{ }
II
+
∫
|ξ|≥T 2
|gˆ(ξ)|2dξ
} {{ }
III
.
If |ξ| > T 2, then since fˆ(ξ) is rapidly decaying for |ξ| > T , we see that fˆ(m2ξ/m1)
is negligible and |gˆ(ξ)| . T −100|ξ|−2. Thus


 30 LARRY GUTH AND JAMES MAYNARD
(9.5) III = O(T −100).
If |ξ| ≤ T ηM1/M3, then in the sum over l in (9.3), the only terms that contribute
have |l| . T η/M3 . T η. Therefore, this sum is O(T η). Thus, by Cauchy-Schwarz we obtain
|gˆ(ξ)|2 . T 2ηM1
∑
|m1 |∼M1
M32
∣∣∣ ∑
m2 ∼M2
m2
m1
fˆ
( m2
m1
ξ
)∣∣∣
2 ≤ T 2ηM24M32 sup
ξ
|fˆ(ξ )|2 .
Therefore
I=
∫
|ξ|≤T η M1/M3
|gˆ(ξ)|2dξ . T 3ηM1M24M3 sup
ξ
|fˆ(ξ)|2
. T 3ηM 6
(∫
f (u)du
)2 (9.6) .
Now suppose that T ηM1/M3 < |ξ| ≤ T 2. We return to (9.3) and consider the number of terms in the outer double sum. Let s = m1l. In this range, s must be a non-zero integer in the / M1/M3 neighborhood of ξ as soon as T is sufficiently large in terms of η. The number of such integers s is / 1 + M1/M3. Since |ξ| ≤ T 2 and s is non-zero, each such integer s has / 1 factorizations as s = m1l. All together the number of terms in the outer double sum is / 1 + M1/M3. Therefore, we can use Cauchy-Schwarz to bound |gˆ(ξ)|2 by
/
(
1 + M1
M3
)∑
|m1 |∼M1
∑
l
|ξ−lm1|/M1/M3
M32
∣∣∣ ∑
m2 ∼M2
m2
m1
fˆ
( m2
m1
ξ
)∣∣∣
2 + O(T −200).
Therefore the term II satisfies
II / (M1M3 + M32) ∑
|m1 |∼M1
∑
l
∫
|ξ−lm1|/M1/M3
∣∣∣ ∑
m2 ∼M2
m2
m1
fˆ
( m2
m1
ξ
)∣∣∣
2dξ.
Morally this integral does not depend on m1, and we can make this precise by
changing variables. For each m1, l, we write ξ = lm1 + m1
M3 τ and do a change of
variables to get (extending the range of integration slightly for an upper bound so we have a range independent of m1)
II . (M1 + M3) ∑
l
∫
|τ |/1
∣∣∣ ∑
m2 ∼M2
m2fˆ
(
lm2 + m2
M3
τ
)∣∣∣
2dτ.


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 31
Since fˆ(ξ) = O(T −200) unless |ξ| / T , we can restrict the sum over l to the range |l| / T /M2 at the cost of a negligible error. We introduce a bump ψ2(x) supported on |x| / 1 so that ψ2(M2l/T ) majorizes this summation condition, and bound the last sum by
. (M1 + M3)ΣII + O(T −100),
where
ΣII := ∑
l
ψ2
( M2l T
)∫
|τ |/1
∣∣∣ ∑
m2 ∼M2
m2fˆ
(
lm2 + m2
M1
τ
)∣∣∣
2dτ.
We write out fˆ as an integral, expand out the square and bring the summation over l and integration over τ on the inside to get
ΣII =
∫∫ ∑
m2 ,m′2 ∼M2
m2m′2f (u)f (u′)Σ1Σ2du′du,
where
Σ1 :=
∫
|τ |/1
e
( τ
( m′2
M1
u′ − m2
M1
u
))
dτ,
Σ2 := ∑
l
ψ2
( M2l T
) e
( l
(
m′2u′ − m2u
)) .
Trivially we have |Σ1| / 1. By Poisson summation, and the rapid decay of ψˆ2, we have
Σ2 = T
M2
∑
j
ψˆ2
( j − m′2u′ + m2u M2/T
)
=T
M2
∑
j |j−m′
2 u′ +m2 u|/M2 /T
ψˆ2
( j − m′2u′ + m2u M2/T
)
+ O(T −100).
Substituting these back into our bound (9.7) for ΣII , we find
ΣII / M2
∫
f (u) ∑
m2 ,m′2 ∼M2
∑
j
T
∫
|u′ − m2u+j
m′2
|/ 1
T
f (u′)du′du.
This gives
II / M2(M1 + M3)
∫
f (u) ∑
m2 ,m′2 ∼M2
∑
j
T
∫
|u′ − m2u+j
m′2
|/ 1
T
f (u′)du′du.


 32 LARRY GUTH AND JAMES MAYNARD
Since fˆ(ξ) rapidly decays for |ξ| > T , f is morally almost constant on intervals of length 1/T . We let ψ(x) be a smooth bump function supported on x / 1, and then define f ̃ to be a slightly smoothed version of f given by
f ̃(u) :=
∫
T ψ(T (u − u′))f (u′)du′
We can choose ψ such that the integral over u′ in the bound for II above is
bounded by f ̃( m2u+j
m′2 ). Thus we find (recalling that f is supported on u ≍ 1
and M1, M2, M3 ≤ M )
II / M2
∫
u≍1
f (u) ∑
m2 ,m′2 ∼M2
∑
j
f ̃
( m2u + j m′2
)
du.
Now we apply Cauchy-Schwarz to get
(9.7) II /
[
M4
∫
f (u)2du
]1/2[ ∫
u≍1
(∑
m2 ,m′2 ∼M2 ,j ∈Z
f ̃
( m2u + j m′2
))2du
]1/2.
Since u ≍ 1 and f (x) is supported on x ≍ 1, we may restrict the summation over j to j . M2. Thus we see that the second term in square brackets is bounded by
J(f ̃). Putting together (9.2), (9.4), (9.5), (9.6) and (9.7) we find that for any η > 0, provided T is sufficiently large in terms of η, we have
J (f ) / T 3ηM 6
(∫
f (u)du
)2
+
(
M4
∫
f (u)2du
)1/2J (f ̃)1/2.
This now gives the result on letting η → 0 sufficiently slowly with T .
10. Further bounds for S3
In this section, we use our bounds for sums over affine transformations to improve our bound for S3. We will get the following estimate.
Proposition 10.1 (Refined S3 bound). If W is a T ǫ-separated set contained in an interval of length T , then
(10.1) S3 / T 2|W |3/2 + T N |W |1/2E(W )1/2.
Remark. Comparing with Proposition 8.1, when E(W ) ≈ |W |2 both propositions give S3 / T 2|W |3/2. But when E(W ) is large, Proposition 10.1 is better by a factor of N/T . If we look at the critical case when T = N 5/4 and σ = 3/4, then this estimate (together with our bounds for S2) gives an improvement to the basic orthogonality estimate (1.6) when E(W ) is significantly below |W |3. In other words, this Proposition gives an improvement unless the energy is essentially maximal. But


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 33
when E(W ) is very large, then we will get good estimates in the next section using Theorem 1.6.
Proof. Recall from Proposition 7.2 that we have
S3 / N 2
M
∫
v1 ≍1
|R(v1)| ∑
|m1 |∼M1 |m2|,|m3|∼M
∣∣∣∣R ̃M
( m1v1 + m3
m2v1
)R ̃M
( m1v1 + m3
m2
)∣∣∣∣ dv1.
Thus by Cauchy-Schwarz we have
S3 . N 2
M S1/2
3,1 S1/2
3,2 ,
where
S3,1 :=
∫
v≍1
|R(v)|2dv . W,
S3,2 :=
∫
v≍1
(∑
|m1 |∼M1 ,|m2 |,|m3 |∼M
∣∣∣R ̃
( m3 + m1v m2v
)R ̃
( m3 + m1v
m2
)∣∣∣
)2dv.
By Cauchy-Schwarz again, we have that
S3,2 . S1/2
3,3 S1/2
3,4 ,
where
S3,3 :=
∫
v≍1
(∑
|m1|∼M1,|m2|,|m3|∼M
∣∣∣R ̃
( m3 + m1v m2v
)∣∣∣
2)2dv,
S3,4 :=
∫
v≍1
(∑
|m1|∼M1,|m2|,|m3|∼M
∣∣∣R ̃
( m3 + m1v
m2
)∣∣∣
2)2dv.
We bound S3,3 and S3,4 using Proposition 9.1. To bound S3,4, we use f (v) = ψ(v)R ̃(v)2, where ψ(v) is a smooth bump supported on v ≍ 1. To control S3,3, we make a change of variables u = 1/v and rewrite S3,3 as
S3,3 .
∫
u≍1
(∑
|m1|∼M1,|m2|,|m3|∼M
∣∣∣R ̃
( m3u + m1
m2
)∣∣∣
2)2du.
Then we use Proposition 9.1 with f (u) = ψ(u)|R ̃(u)|2. To apply Proposition 9.1, we have to check that fˆ(ξ) is rapidly decaying for |ξ| > T . Both R(v) and R ̃(v)


 34 LARRY GUTH AND JAMES MAYNARD
have the desired Fourier decay. Let’s check for R ̃(v). Recall that ψ ̃(u) is a smooth bump supported on |u| / 1 and that
R ̃(v)2 =
∫
M N ψ ̃(M N (u − u′))|R(u)|2du.
Therefore, R ̃(v)2 has Fourier transform rapidly decaying when |ξ| > M N , and T ' M N . Then it follows that f has the desired Fourier decay. Proposition 9.1 then gives the bounds
S3,3, S3,4 / M 6( ∫
v≍1
|R(v)|2dv
)2 + M 4
∫
v≍1
|R(v)|4dv.
Applying Lemmas 8.2 and 8.3, we get
S3,3, S3,4 / M 6|W |2 + M 4E(W ).
The same bound holds for S3,2 since S3,2 ≤ S1/2
3,3 S1/2
3,4 . Then we get
S3 / N 2
M S1/2
3,1 S1/2
3,2 / N 2
M |W |1/2(M 6|W |2 + M 4E(W ))1/2
= N 2M 2|W |3/2 + N 2M |W |1/2E(W )1/2.
Since M / T /N , we get
S3 / T 2|W |3/2 + T N |W |1/2E(W )1/2.
11. Energy Bound
In this section, we prove bounds related to the energy of W , which show that a Dirichlet polynomial cannot be too large on a set of large energy. These bounds ultimately rely on Heath-Brown’s bound Theorem 1.6, and are closely related to (and refine) arguments in [HB2]. Recall that in equation (1.7), we defined the energy of a finite set W ⊂ R by
E(W ) := #{t1, t2, t3, t4 ∈ W : |t1 + t2 − t3 − t4| < 1}.
We will prove two bounds about the behavior of Dirichlet polynomials on sets of high energy. The first bound is Lemma 1.7. We recall the statement here.
Lemma. Let N ∈ [T 2/3, T ], σ > 1/2 and D(t) = ∑2N
n=N bnnit with |bn| ≤ 1.
Suppose W ⊂ [0, T ] is a 1-separated set such that |D(t)| > N σ for t ∈ W . Then
E(W ) ≤ |W |3N 1−2σ+o(1) + |W |2N 2−2σ+o(1).


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 35
Combining Lemma 1.7 with our previous results is enough to get an improvement on previous estimates in the key scenario T = N 4/5, |W | = T 3/5. The second bound is a little more complicated, but it leads to stronger estimates in our applications.
Proposition 11.1 (Bound for energy). Suppose that DN (t) = ∑
n∼N bnnit with
|bn| ≤ 1. Suppose that W is a 1-separated set contained in an interval of length T , and that |DN (t)| ≥ N σ for t ∈ W . If T 3/4 ≤ N ≤ T , then
(11.1) E(W ) / |W |N 4−4σ + |W |21/8T 1/4N 1−2σ + |W |3N 1−2σ.
Since the algebra is a little messy, we take a moment to process the bounds. For one thing, if E(W ) is very large, we get very strong bounds on σ. For instance, if E(W ) ≈ |W |3, and if N 2/3 ≤ T ≤ N , then Lemma 1.7 gives a sharp estimate: either N σ / N 1/2 or |W |N 2σ / N 2. More important for our application is when we get an improvement on the basic orthogonality bound |W |N 2σ . T N . The full equations are a little messy, but if we plug in the key scenario N = T 4/5 and |W | = T 3/5, then Lemma 1.7 gives an improvement when E(W ) ≥ |W | 8
3 +ǫ and Proposition 11.1 gives an improvement when E(W ) ≥ |W | 7
3 (for some ǫ > 0).
If |W | ≈ T N 1−2σ, then the bound in Proposition 11.1 would be (N/T )2|W |3 + (|W |5/8T −6/8)|W |3 +|W |4/T . The first term will be the most important for us, and generally sets the limitations on our bounds. The second term will be negligible in practice (and could be improved with a bit more effort). The final term corresponds to the additive energy of a random set in an interval of length T .
An immediate consequence of Proposition 11.1 is a good bound for the key term S3 by substituting the bound of Proposition 11.1 into Proposition 10.1.
Proposition 11.2 (S3 Bound). Let N ≥ T 3/4. Then we have
S3 / T 2|W |3/2 + T |W |N 3−2σ + T |W |2N 3/2−σ + T 9/8|W |29/16N 3/2−σ.
Now we turn to the proof of Proposition 11.1.
Suppose that DN (t) = ∑
n∼N bnnit and |DN (t)| ≥ N σ on W . Morally, we also have
|DN (t)| ' N σ if the distance from t to W is . 1. In particular, if |t1+t2−t3−t4| / 1,
then morally |DN (t1 + t2 − t3)| ' N σ. Therefore morally we should expect that
E(W ) / N −2σ ∑
t1 ,t2 ,t3 ∈W
∣∣∣DN (t1 + t2 − t3)
∣∣∣
2 = N −2σ ∑
n1 ,n2 ∼N
R
( n1
n2
)2R
( n2
n1
) .
We can make this moral argument literally true by working with a slightly smoothed version of DN .
Lemma 11.3 (Dirichlet polynomials do not vary too fast). We have
|DN (t)| /
∫
|u−t|/1
|DN (u)|du + O(T −100).


 36 LARRY GUTH AND JAMES MAYNARD
Proof. Let ψ(x) be a smooth bump which is supported on |2πx − log N | . 1 and is equal to 1 on [(2π)−1 log N, (2π)−1 log 2N ]. Then we have
DN (t) = ∑
n
w(n/N )bnnit = ∑
n
w(n/N )bnnitψ
( log n 2π
) =
∫
ψˆ(ξ)DN (t − ξ)dξ.
By the rapid decay of ψˆ we may restrict to |ξ| / 1 at the cost of an error O(T −100).
Lemma 11.4 (Energy controlled by discrete 3rd moment). We have that
E(W ) / N −2σ ∑
n1 ,n2 ∼N
∣∣∣R
( n1
n2
)∣∣∣
3.
Proof. Since |DN (t)| > N σ for t ∈ W , we have
E(W ) = ∑
t1 ,t2 ,t3 ,t4 ∈W |t1 +t2 −t3 −t4 |≤1
1 ≤ N −2σ ∑
t1 ,t2 ,t3 ,t4 ∈W |t1 +t2 −t3 −t4 |≤1
|DN (t4)|2.
By Lemma 11.3 and Cauchy-Schwarz, we have for |t1 + t2 − t3 − t4| ≤ 1
|DN (t4)|2 /
∫
|u−t4|/1
|DN (u)|2du /
∫
|u−t1 +t2 −t3 |/1
|DN (u)|2du.
Since W is T ǫ-separated, given t1, t2, t3 there is at most 1 choice of t4 ∈ W such that |t1 + t2 − t3 − t4| / 1. Thus we see that
E(W ) / N −2σ ∑
t1 ,t2 ,t3 ∈W
∫
s/1
|DN (t1 + t2 − t3 − s)|2ds
= N −2σ ∑
n1 ,n2
w
( n1 N
) w
( n2 N
)∫
s/1
( n2
n1
)isR
( n1
n2
)2R
( n2
n1
) ds
/ N −2σ ∑
n1 ,n2 ∼N
∣∣∣R
( n1
n2
)∣∣∣
3.
Next we note that Heath-Brown’s theorem (Theorem 1.6) gives bounds for ∑
n1 ,n2 ∼N
∣∣∣R
( n1 n2
)∣∣∣
2
and also ∑
n1 ,n2 ∼N
∣∣∣R
( n1 n2
)∣∣∣
4.
Lemma 11.5 (Discrete second moment). For any M ≥ 1,
∑
n1 ,n2 ∼M
∣∣∣R
( n1
n2
)∣∣∣
2 / |W |M 2 + |W |2M + |W |5/4T 1/2M.


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 37
Proof. We have that
∑
n1 ,n2 ∼M
∣∣∣R
( n1
n2
)∣∣∣
2= ∑
t1 ,t2 ∈W
∣∣∣ ∑
n∼M
ni(t1 −t2 ) ∣∣∣
2,
so by Theorem 1.6 this is
/ |W |M 2 + |W |2M + |W |5/4T 1/2M.
Lemma 1.7 is now a quick consequence of our arguments so far.
Proof of Lemma 1.7. By Lemma 11.4 and the trivial bound |R(x)| ≤ |W | we have
E(W ) / N −2σ ∑
n1 ,n2 ∼N
∣∣∣R
( n1
n2
)∣∣∣
3 ≤ |W |N −2σ ∑
n1 ,n2 ∼N
∣∣∣R
( n1
n2
)∣∣∣
2.
Lemma 11.5 (which is just Theorem 1.6) now shows for N > T 2/3 we have
E(W ) / |W |3N 1−2σ + |W |2N 2−2σ.
To do better we look at higher moments to avoid the potentially wasteful use of the trivial bound |R(x)| ≤ |W |.
Lemma 11.6 (Discrete fourth moment). For any M ≥ 1,
∑
n1 ,n2 ∼M
∣∣∣R
( n1
n2
)∣∣∣
4 / M 2E(W ) + |W |4M + E(W )3/4|W |T 1/2M.
Proof. We split the sum in the R function according to the number of representations of u as approximately t1 − t2. Let ⌊x⌋ denote the largest integer ≤ x, and define
UB :=
{
u ∈ Z : #{(t1, t2) ∈ W 2 : ⌊t1 − t2⌋ = u} ∼ B
} .
Clearly UB is empty if B < 1/2 or if B > |W |. Thus, using Cauchy-Schwarz
|R(x)|4 =
∣∣∣ ∑
t1 ,t2 ∈W
xi(t1 −t2 ) ∣∣∣
2=
∣∣∣ ∑
B=2j
∑
u∈UB
∑
t1 ,t2 ∈W ⌊t1 −t2 ⌋=u
xi(t1 −t2 ) ∣∣∣
2
/∑
B=2j ≤|W |
∣∣∣ ∑
u∈UB
∑
t1 ,t2 ∈W ⌊t1 −t2 ⌋=u
xi(t1 −t2 ) ∣∣∣
2.
Taking x = n1/n2 and summing over n1, n2 ∼ M then gives


 38 LARRY GUTH AND JAMES MAYNARD
∑
n1 ,n2 ∼M
∣∣∣R
( n1
n2
)∣∣∣
4 / sup
B≤|W |
∑
n1 ,n2 ∼M
∣∣∣ ∑
u∈UB
∑
t1 ,t2 ∈W ⌊t1 −t2 ⌋=u
( n1
n2
)i(t1 −t2 ) ∣∣∣
2
≤ sup
B≤|W |
∣∣∣ ∑
u1 ,u2 ∈UB
(∑
t1 ,t3 ∈W ⌊t1 −t3 ⌋=u1
1
)( ∑
t2 ,t4 ∈W ⌊t2 −t4 ⌋=u2
1
)
sup
|s|.1
∣∣∣ ∑
n∼M
ni(u1 −u2 +s) ∣∣∣
2
/ sup
B≤|W |
B2 ∑
u1 ,u2 ∈UB
sup
|s|.1
∣∣∣ ∑
n∼M
ni(u1 −u2 +s) ∣∣∣
2.
By using Lemma 11.3 to replace the supremum with an integral, and then applying Theorem 1.6, we find
∑
n1 ,n2 ∼M
∣∣∣R
( n1
n2
)∣∣∣
4 / sup
B≤|W |
B2
∫
t/1
∑
u1 ,u2 ∈UB
∣∣∣ ∑
n∼M
ni(u1 −u2 +t) ∣∣∣
2dt
/ sup
B≤|W |
B2(
M 2|UB| + |UB|2M + T 1/2|UB|5/4M
) .
We have that B|UB| / |W |2 and B2|UB| / E(W ), so this gives
∑
n1 ,n2 ∼M
∣∣∣R
( n1
n2
)∣∣∣
4 / M 2E(W ) + |W |4M + E(W )3/4|W |T 1/2M.
To bound ∑
n1,n2∼N |R
( n1 n2
)
|3, we could use Ho ̈lder:
∑
n1 ,n2 ∼N
∣∣∣R
( n1
n2
)∣∣∣
3≤

∑
n1 ,n2 ∼N
∣∣∣R
( n1
n2
)∣∣∣
2


1/2 
∑
n1 ,n2 ∼N
∣∣∣R
( n1
n2
)∣∣∣
4


1/2
and then bound the two factors using Lemmas 11.5 and 11.6. However, this Ho ̈lder step is somewhat lossy. If n′1/n′2 is a rational number of small height, then the
sum ∑
n1 ,n2 ∼N
∣∣∣R
( n1 n2
)∣∣∣
p counts |R(n′1/n′2)|p many times – because there are many
n1, n2 ∼ N with n1/n2 = n′1/n′2. The 4th moment tends to be dominated by n1, n2
with large gcd(n1, n2). But the 2nd moment tends to be dominated by n1, n2 with small gcd(n1, n2). Therefore, instead of doing Ho ̈lder immediately, we now split our argument according to the size of gcd(n1, n2).
Let d = gcd(n1, n2) and n1 = n′1d, n2 = n′2d for some n′1, n′2 ∼ N/d with
gcd(n′1, n′2) = 1. Thus we have for any choice of parameter D (dropping the coprimality constraint when d is large)
(11.2) E(W ) ≤ N −2σ ∑
d≤D
∑
n′1 ,n′2 ∼N/d
gcd(n′1 ,n′2 )=1
∣∣∣R
( n′1
n′2
)∣∣∣
3 + N −2σ ∑
d≥D
∑
n′1 ,n′2 ∼N/d
∣∣∣R
( n′1
n′2
)∣∣∣
3.


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 39
First we consider small d. When d is small enough, the distinct fractions n′1/n′2 are
very well distributed and so it makes sense to compare our sum with ∫
v≍1 |R(v)|3dv.
We recall that W is contained in an interval of length T . Morally, |Wˆ (τ )| is locally constant on intervals of length 1/T . Since R(v) = Wˆ (log v), we see that for v ≍ 1, |R(v)| is morally locally constant at scale 1/T . We make this precise in the following lemma:
Lemma 11.7. For v ≍ 1,
|R(v)| . T
∫
|v′ −v|/1/T
|R(v′)|dv′ + O(T −100).
Proof. Since v ≍ 1, we can do a change of variables, τ = log v, and it suffices to prove that
|Wˆ (τ )| . T
∫
|τ ′−τ |/1/T
|Wˆ (τ ′)|dτ ′ + O(T −100).
We know that W is contained in an interval of length T ; call this [T0, T0 + T ]. Let ψ be a smooth bump which is 1 on [0, 1]. Then we have
Wˆ (τ ) = ∑
t∈W
e(−tτ ) = ∑
t∈W
e(−tτ )ψ
( t − T0 T
) =
∫
ψˆ(ξ)Wˆ
(
τ− ξ
T
) e
( T0ξ T
)
dξ.
By the rapid decay of ψˆ, we may restrict the integral to ξ / 1 at the cost of an O(T −100) error term. Since ψˆ . 1 this then gives the result.
Lemma 11.8 (Small GCD terms). We have
∑
n1 ,n2 ∼N gcd(n1 ,n2 )≤D
∣∣∣R
( n1
n2
)∣∣∣
3/
(
DT + N2)
|W |1/2E(W )1/2.
Proof. Let d = gcd(n1, n2) and n1 = n′1d, n2 = n′2d for some n′1, n′2 ∼ N/d with
gcd(n′1, n′2) = 1. By Lemma 11.7, we have
∑
n′1 ,n′2 ∼N/d
gcd(n′1 ,n′2 )=1
∣∣∣R
( n′1
n′2
)∣∣∣
3.T
∫
v≍1
|R(v)|3( ∑
n1 ,n′2 ∼N/d
gcd(n′1 ,n′2 )=1
|v−n′
1 /n′
2|/1/T
1
)
dv.
Since the fractions n′1/n′2 are d2/N 2-separated, we have that the inner sum over
n′1, n′2 on the right hand side is / 1 + N 2/(d2T ). Thus we find


 40 LARRY GUTH AND JAMES MAYNARD
∑
d≤D
∑
n′
1 ,n′
2∼N/d
gcd(n′
1 ,n′
2 )=1
∣∣∣R
( n′1
n′2
)∣∣∣
3/ ∑
d≤D
(
T + N2
d2
)∫
v≍1
|R(v)|3dv
≤∑
d≤D
(
T + N2
d2
) (∫
v≍1
|R(v)|2dv
)1/2 (∫
v≍1
|R(v)|4dv
)1/2
.
(
DT + N2)
|W |1/2E(W )1/2.
We choose D := N 2/T , so this gives
(11.3) ∑
n1 ,n2 ∼N gcd(n1 ,n2 )≤D
∣∣∣R
( n1
n2
)∣∣∣
3 / N 2|W |1/2E(W )1/2.
Lemma 11.9 (Large GCD terms). Let D = N 2/T and N ≥ T 3/4. Then we have ∑
n1 ,n2 ∼N gcd(n1 ,n2 )≥D
∣∣∣R
( n1
n2
)∣∣∣
3 . N |W |3 + N T 1/4|W |21/8 + E(W )1/2|W |1/2N 2.
Proof. As in the previous lemma, we let d = gcd(n1, n2) and n1 = n′1d, n2 = n′2d.
When d is large, we keep the discrete summation over n′1, n′2 and apply CauchySchwarz directly, giving
∑
n′1 ,n′2 ∼N/d
∣∣∣R
( n′1
n′2
)∣∣∣
3.
(∑
n′1 ,n′2 ∼N/d
∣∣∣R
( n′1
n′2
)∣∣∣
4)1/2( ∑
n′1 ,n′2 ∼N/d
∣∣∣R
( n′1
n′2
)∣∣∣
2 )1/2 .
Now we can bound the factors on the right-hand side by Lemmas 11.5 and 11.6, with M = N/d. This gives
∑
n′1 ,n′2 ∼N/d
∣∣∣R
( n′1
n′2
)∣∣∣
3/
( |W |N 2
d2 + |W |2N
d + |W |5/4T 1/2N
d
)1/2
×
( N 2E(W )
d2 + N |W |4
d + E(W )3/4|W |T 1/2N
d
)1/2
.
Summing over d ≥ D, using Cauchy-Schwarz, and recalling that D = N 2/T then gives
∑
n1 ,n2 ∼N gcd(n1,n2)≥D
∣∣∣R
( n1
n2
)∣∣∣
3/
( |W |N 2
D + |W |2N + |W |5/4T 1/2N
)1/2
×
( N 2E(W )
D + N |W |4 + E(W )3/4|W |T 1/2N
)1/2.


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 41
Next we work on simplifying and organizing the algebra. Recall that we have N > T 3/4 and D = N 2/T . Therefore, we have |W |5/4T 1/2N > |W |T = |W |N 2/D, and we can ignore the first term in the first factor. Thus the above expression is bounded by
(11.4) /
(
|W |2N +|W |5/4T 1/2N
)1/2(
E(W )T +N |W |4+E(W )3/4|W |T 1/2N
)1/2 .
There are two main cases, depending on whether |W | > T 2/3 or not. If |W | > T 2/3 then |W |2N > |W |5/4T 1/2N , and so the first factor is dominated by |W |2N . We turn to the second factor. If |W | > T 2/3, then N |W |4 > N |W |13/4T 1/2 ≥ E(W )3/4|W |T 1/2N . Also, since N > T 3/4 > T 1/2, N |W |4 > |W |3T ≥ E(W )T . So the second factor is dominated by N |W |4. Therefore, if |W | > T 2/3, (11.4) simplifies to
∑
n1 ,n2 ∼N gcd(n1,n2)≥D
∣∣∣R
( n1
n2
)∣∣∣
(11.5) 3 / N |W |3.
Now suppose |W | < T 2/3. Recalling that N > T 3/4 > T 1/2, we see that |W |2N < |W |5/4T 1/2N , so the first factor is dominated by |W |5/4T 1/2N . Turning to the second factor, we see that E(W )3/4|W |T 1/2N > E(W )T . Thus, if |W | < T 2/3 we see that (11.4) simplifies to
∑
n1 ,n2 ∼N gcd(n1 ,n2 )≥D
∣∣∣R
( n1
n2
)∣∣∣
3/
(
|W |5/4T 1/2N
)1/2(
N |W |4 + E(W )3/4|W |T 1/2N
)1/2
/ N T 1/4|W |21/8 + E(W )1/2|W |1/2N 2( T 1/2|W |5/8
E(W )1/8N
) (11.6) .
Since E(W ) > |W |2 and |W | < T 2/3 and N > T 3/4, we see that T 1/2|W |5/8 < E(W )1/8N , so the final term in (11.6) is O(|W |1/2E(W )1/2N 2). Thus, combining (11.5) and (11.6), we find that provided N > T 3/4, regardless of the size of W , we have
∑
n1 ,n2 ∼N gcd(n1 ,n2 )≥D
∣∣∣R
( n1
n2
)∣∣∣
3 / N |W |3 + N T 1/4|W |21/8 + E(W )1/2|W |1/2N 2.
Proof of Proposition 11.1. First we use Lemma 11.4 to give
E(W ) / N −2σ ∑
n1 ,n2 ∼N
∣∣∣R
( n1
n2
)∣∣∣
3.


 42 LARRY GUTH AND JAMES MAYNARD
Splitting according to whether gcd(n1, n2) ≤ D = N 2/T or not, we find by Lemma 11.8 and Lemma 11.9 that
E(W ) ≤ N −2σ(
N |W |3 + N T 1/4|W |21/8 + E(W )1/2|W |1/2N 2)
.
This simplifies to give
E(W ) / |W |N 4−4σ + |W |21/8T 1/4N 1−2σ + |W |3N 1−2σ.
12. Proof of results on large values of Dirichlet polynomials
In this section we prove our main results on the large values of Dirichlet polynomials by assembling the tools in the previous sections.
Proof of Proposition 3.1. Suppose that |DN (t)| ≥ N σ on the set W contained in an interval of length T = N 6/5. By Proposition 4.6 and (5.5), we have
|W | .ǫ N 2−2σ + N 1−2σ( ∑
m∈Z3\{0}
Im
)1/3 = N 2−2σ + N 1−2σ(
S1 + S2 + S3
)1/3 .
By Proposition 5.1, S1 is negligible. We bound S2 by Proposition 6.1, and S3 by Proposition 11.2. Therefore we get for any choice of k ∈ N
|W |3N 6σ−3 / N 3 + S2 + S3
/ N 3 + |W |2N 2 + T N |W |2−1/k + N 2|W |2−3/4kT 1/2k + T 2|W |3/2
+ T |W |N 3−2σ + T |W |2N 3/2−σ + T 9/8|W |29/16N 3/2−σ.
In this formula k comes from the bound for S2. It is a positive integer that we can choose. The last inequality rearranges to give
|W | / N 2−2σ + N 5−6σ + T k
k+1 N (4−6σ) k
k+1 + N (5−6σ) 4k
4k+3 T 2
4k+3 + T 4/3N 2−4σ
(12.1) + T 1/2N 3−4σ + T N 9/2−7σ + T 18/19N 72/19−112σ/19.
We choose k = 4. We also simplify the formulas using T = N 6/5.
|W | / T
(
N (4−10σ)/5 + N (19−30σ)/5 + N (74−120σ)/25 + N (298−480σ)/95
+ N (12−20σ)/5 + N (9−14σ)/2 + N (354−560σ)/95)
/ T N (4−10σ)/5 + T N (12−20σ)/5 + T N (9−14σ)/2.
If σ ∈ [7/10, 8/10] the first and third terms can be dropped and we get


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 43
|W | / T N (12−20σ)/5.
When N > T 5/6 the process of going from Proposition 3.1 to Theorem 1.1 is somewhat wasteful since it actually bounds the number of large values in [0, N 6/5]. By using a variation of the above argument, the bound in Theorem 1.1 could be improved. We record one such improvement here.
Proposition 12.1 (Large values estimate for N ≥ T 5/6). Suppose (bn)n∈[N,2N], (tr)r≤R are as in Theorem 1.1, and that T 5/6 ≤ N ≤ T and V = N σ with σ ≥ 7/10. Then we have
R / N 2−2σ + T 1/2N 3−4σ + kin∈fN
( T
k
k+1 N (4−6σ) k
k+1 + N (5−6σ) 4k
4k+3 T 2
4k+3
) .
In particular, we have
R / N 2−2σ + T 1/2N 3−4σ + T (30σ−21)/5N (46−60σ)/5.
Proposition 12.1 implies that the N 18/5V −4 term in Theorem 1.1 can be replaced by T 1/2N 3−4σ + T (30σ−21)/5N (46−60σ)/5, which is smaller. When σ = 3/4, Proposition 12.1 improves on (1.1) by a factor of (T /N )1/2. Since we anticipate the main uses of Theorem 1.1 to be when N < T 5/6 we content ourselves to the simpler formulation of Theorem 1.1.
Proof. Jutila’s large values estimate [Ju, Theorem (1.4)] with k = 3 gives
R / N 2−2σ + T N (10−16σ)/3 + T N 18−24σ,
which implies our bound for σ ≥ 39/50 since the second and third terms above are then both smaller than T 1/2N 3−4σ. Thus we only need to consider σ ∈ [7/10, 39/50]. The bound now follows from (12.1), (1.1) and a little algebra. We find for σ ∈ [7/10, 39/50] and N ∈ [T 5/6, T ] we have that
T 1/2N 3−4σ & T 4/3N 2−4σ + T N 9/2−7σ + T 18/19N 72/19−112σ/19.
Therefore the T 1/2N 3−4σ term in (12.1) dominates the 5th, 7th and 8th terms in (12.1). We also have
T 1/2N 3−4σ & min(T N 4−6σ, N 2−2σ) + min(T N 1−2σ, N 5−6σ).
Therefore, by combining (12.1) and (1.1) we find that
R / N 2−2σ + T 1/2N 3−4σ + kin∈fN
( T
k
k+1 N (4−6σ) k
k+1 + N (5−6σ) 4k
4k+3 T 2
4k+3
) .


 44 LARRY GUTH AND JAMES MAYNARD
This gives the first bound. For the final bound, we note that if N 4−4σ > T then T N 1−2σ < T 1/2N 3−4σ so the bound follows from (1.1). Therefore we may assume that N 4−4σ ≤ T . In this case N 15−18σ ≤ T 2 and so in the expression in parentheses above, the first term is decreasing in k and the second term is increasing in k. Thus, for the expression to be less than T (30σ−21)/5N (46−60σ)/5 we require
−73 + 138n + 90σ − 180nσ
12(1 − n)(7 − 10σ) ≤ k ≤ −21 + 46n + 30σ − 60nσ
2(1 − n)(13 − 15σ)
where n := log N/ log T . The upper bound of this interval is always at least 1 for n ∈ [5/6, 1), σ ∈ [7/10, 39/50] and the length of this interval is
1 + 5(6n − 5)(−41 + 123σ − 90σ2)
12(1 − n)(10σ − 7)(13 − 15σ) .
Thus the interval has length at least 1 whenever σ ∈ [7/10, 39/50], and so there is a choice of k ∈ N giving the desired bound.
13. Applications to Riemann zeta function and prime numbers
13.1. Proof of Theorem 1.2. As noted in the introduction, Theorem 1.2 follows from Ingham’s result (1.2) if σ ≤ 7/10 and Huxley’s result (1.3) if σ ≥ 8/10, so we may assume that σ ∈ [7/10, 8/10]. Clearly it suffices to show the bound of Theorem 1.2 for zeros with imaginary part in [T, 2T ], since the result for [0, T ] then follows by considering T /2, T /4, . . . in place of T .
We now briefly recall the classical zero-detecting methodology, referring the reader to [M3, Chapter 12] or [MP, Appendix C] for more complete details. Given a parameter N , we let
DN (s) := ∑
n∈[N,2N ]
bnn−s,
bn :=
(∑
d|n
d≤2T 1/√log log T
μ(d)
)
w0
(n
N
)
exp
(
−n
T 1/2
) .
Here w0 is a fixed smooth bump function supported on [1, 2].
Then, a non-trivial zero ρ = β + iγ of ζ(s) with β ≥ σ and γ ∈ [T, 2T ] is called a ‘Type I zero’ if there is a choice of N ∈ [T 1/ log log T , T 1/2(log T )2] such that DN (ρ) ≥ 1/(3 log T ). If it is not a Type I zero then it is a ‘Type II zero’, and the number of Type II zeros is ≤ T 2−2σ(log T )O(1) by [MP, Lemma 33]. Thus it suffices to bound the number of Type I zeros. There are O(log T ) choices of N so we focus on the value of N which gives the largest number of Type I zeros.
We now make a slight modification to DN to remove the dependencies on the real parts. Let ρ = β + iγ be a Type I zero with β ≥ σ, and let ψ(u) be a smooth


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 45
function equal to eu(β−σ) on [log N, log 2N ] and supported on [(log N )/2, 2 log N ] with ‖ψ(j)(t)‖∞ .j t−j for all j ∈ N. We then note that by Fourier expansion
DN (ρ) = ∑
n∈[N,2N ]
bnn−σ−iγ ψ(log n) = 1
2πi
∫
ξ
ψˆ(ξ)
(
DN (σ + i(γ + 2πξ))
)
dξ.
Since ψˆ is rapidly decreasing, we may truncate the integral to ξ / 1 at the cost of an O(T −100) error term. Therefore we see that if ρ is a Type I zero, we have |DN (σ+iγ +iξ)| ' 1 for some ξ / 1. There are O(log T ) non-trivial zeros ρ = β +iγ with γ ∈ [t, t + 1] for any t ∈ [T, 2T ]. Therefore we can find a 1-separated set of points (sr)r≤R in [T, 2T ] with |DN (σ+isr)| ' 1 and the number R of points satisfies R ' N (σ, 2T ) − N (σ, T ). Let
b ̃n :=
(N
n
)σbn, D ̃N (t) := ∑
n∈[N,2N ]
b ̃nnit = N σDN (σ + it).
Thus it suffices to show that if N < T 1/2+o(1) and W is a 1-separated set in [T, 2T ] such that |D ̃N (t)| ' N σ, we have |W | / T 15(1−σ)/(3+5σ)+o(1).
If T 5/(3+5σ) ≤ N 2 ≤ T 75(1−σ)/(54+30σ−100σ2), then we use Theorem 1.1 applied to the Dirichlet polynomial D ̃2N of length N 2, which shows that (noting that σ ∈
[7/10, 8/10] implies that the N 2V −2 term is dominated by the N 18/5V −4 term)
|W | / (T 75(1−σ)/(54+30σ−100σ2))18/5−4σ + T (T 5/(3+5σ))12/5−4σ
/ T 15(1−σ)/(3+5σ).
If instead N lies outside of these ranges, we can use classical estimates. If T 2/3 <
N 2 < T 5/(3+5σ) then the Mean Value Theorem applied to D ̃ 3N gives
|W | / N 6−6σ / T 15(1−σ)/(3+5σ).
If T ' N 2 > T 75(1−σ)/(54+30σ−100σ2) then the Mean Value Theorem applied to N 2 gives
|W | / T (T 75(1−σ)/(54+30σ−100σ2))1−2σ = T (129−195σ+50σ2)/(54+30σ−100σ2).
A quick calcuation verifies (129 − 195σ + 50σ2)/(54 + 30σ − 100σ2) < 15(1 − σ)/(3 + 5σ). Finally, if N < T 1/3, we choose k ≥ 3 such that N k ≤ T ≤ N k+1. The Mean Value Theorem applied to N k and N k+1 gives


 46 LARRY GUTH AND JAMES MAYNARD
|W | / min
(
N (k+1)(2−2σ), T N k(1−2σ))
/
(
N (k+1)(2−2σ)) k(2σ−1)
k+2−2σ (
T N k(1−2σ)) (k+1)(2−2σ)
k+2−2σ
= T (k(2−2σ)+2−2σ)/(k+2−2σ)
/ T (4−4σ)/(3−σ).
Here we noted that the penultimate bound is decreasing in k and so maximized at k = 3. A quick calculation verifies that (4 − 4σ)/(3 − σ) < 15(1 − σ)/(3 + 5σ), so this gives an acceptable bound too.
Remark. For the purposes of proving a zero density estimate of the form N (σ, T ) / T A(1−σ) with A a fixed constant as small as possible, the critical case in our work is when σ = 7/10, N = T 10/13, we subdivide [0, T ] into intervals of length T1 = T 12/13 and where the set W of large values on each subinterval has |W | ≈ T 2/3
1 and
E(W ) ≈ |W |5/2 ≈ |W |4/T1. In this critical situation our bounds for S1 and S2 are both best possible, and so any further improvement would have to come from the S3 term. Our bound for E(W ) is also likely to be difficult to improve since a random set W would have E(W ) ≈ |W |4/T1. The argument of Section 9 is also essentially tight if the R function is taking T 2/3
1 values of size |W |/M ≈ T 1/2
1
and the set of these values is highly concentrated on rationals with numerator and denominator of size T 1/3
1.
13.2. Proof of Corollary 1.3 and Corollary 1.4. These are well-known to follow quickly from (1.4), but for completeness we give a proof. By partial summation, it suffices to prove corresponding results for the Von Mangoldt function in place of the prime indicator function. By the explicit formula (see, for example [Da, Chapter 17]) we have for any choice of T ≥ 2
∑
n∈[x,x+y]
Λ(n) = y − ∑
|ρ|≤T
( (x + y)ρ − xρ ρ
)
+O
( x(log x)3 T
) .
We choose T = xy−1 exp(2 4 √log x) so the error term is O(y exp(− 4 √log x), and note
that the term in parentheses is ∫ x+y
x tρ−1dt ≪ yxR(ρ)−1. Therefore, by considering
1/ log x-separated values of σ, we find that
∑
n∈[x,x+y]
Λ(n) = y + O
(
y(log x) sup
σ
xσ−1N (σ, T )
)
+ O(y exp(− 4 √log x)).
By combining (1.4) with a slightly stronger result (such as [Ju] or [M3, Theorem 12.1]) that loses at most logarithmic factors for σ closer to 1, we have the bound
(13.1) N (σ, T ) . T (30/13+o(1))(1−σ)(log T )O(1).


 NEW LARGE VALUE ESTIMATES FOR DIRICHLET POLYNOMIALS 47
Using this and the Vinogradov-Korobov zero-free bound N (σ, T ) = 0 for σ ≥ 1 − c(log T )−2/3(log log T )−1/3 (for a suitable constant c > 0; see [M3, Corollary 11.4], we find that
sup
σ
xσ−1N (σ, T ) . (log T )O(1) sup
σ≤1−c(log T )−5/7
( T 30/13+o(1)
x
)1−σ
.ǫ exp(− 4 √log x)
provided T < x13/30−ǫ/2. Recalling that T = xy−1 exp(2 4 √log x) and y ≥ x17/30+ǫ, this gives Corollary 1.3.
For Corollary 1.4, we first let δ = X−13/15+ǫ/2. By splitting [x, x + y] into intervals of length δx, we see that
∫ 2X
X
(∑
n∈[x,x+y]
Λ(n) − y
)2dx . y2
δ2X2
∫ 2X
X
(∑
n∈[x,x+δx]
Λ(n) − δx
)2dx + O(δ2X3).
If the corollary was false, the left hand side would be significantly larger than
y2X exp(−3 4 √log x), so it suffices to show that the integral on the right hand side
is . δ2X3 exp(−3 4 √log x). Applying the Explicit Formula as above with T =
δ−1 exp(4 4 √log x), we see that it suffices to show that
(13.2)
∫ 2X
X
∣∣∣ ∑
|ρ|<T
xρ( (1 + δ)ρ − 1
ρ
)∣∣∣
2dx . δ2X3 exp(−3 4 √log x).
Expanding the sum, and performing the integral over x, we obtain
∑
|ρ1 |,|ρ2 |≤T
( (1 + δ)ρ
1 −1
ρ1
)( (1 + δ)ρ2 − 1
ρ2
) ∫ 2X
X
xρ1+ρ2 dx . δ2 ∑
|ρ1 |,|ρ2 |<T
xR(ρ1 )+R(ρ2)+1
|ρ1 + ρ2 + 1| .
Since xR(ρ1)+R(ρ2)+1 ≤ x2R(ρ1)+1 + x2R(ρ2)+1, and noting that (since there are O(log T ) zeros in a horizontal strip of height 1) we have
∑
|ρ2 |<T
|1 + z + ρ2|−1 . (log T )2
for any |z| < T with R(z) ≥ 0. Thus we find that
∫ 2X
X
∣∣∣ ∑
|ρ|<T
xρ( (1 + δ)ρ − 1
ρ
)∣∣∣
2dx . (log X)2δ2 sup
σ
x2σ+1N (σ, T ).
As above, applying (1.4) and the zero-free region, we have that


 48 LARRY GUTH AND JAMES MAYNARD
sup
σ
x2σ+1N (σ, T ) . x3 sup
σ≤1−c(log T )−5/7
( T 30/13+o(1)
x2
)1−σ .ǫ x3 exp(−10 4 √log x),
on recalling that T = δ−1 exp(4 4 √log x) / x13/15−ǫ/3. Putting this together then gives (13.2), as required.
Remark. By using a prime decomposition (such as the Heath-Brown Identity) and Mellin inversion, it is possible to relate the count of primes in short intervals directly to Dirichlet polynomials. The critical situation for both Corollary 1.3 and Corollary 1.4 is handling a product of six Dirichlet polynomials each of size roughly x1/6 (this was the limiting case in the earlier work of Huxley [Hu] too). As in [HB4], by bounding this contribution corresponding to six almost equal sized primes using a sieve method, one could obtain an asymptotic estimate in the slightly larger range y ∈ [x17/30−ǫ, x0.99] and y ∈ [X2/15−ǫ, X0.99] at the cost of a worse error term of size roughly O(ǫ5y/ log x).
References
[Bo] J. Bourgain, On large values estimates for Dirichlet polynomials and the density hypothesis for the Riemann zeta function, Internat. Math. Res. Notices, (2000), no. 2, 133–146. [Ca] F. Carlson. Uber die Nullstellen der Dirichletschen Reihen und der Riemannschen ζ-Funktion. Ark. Mat. Astron. Fys., 15(20):28 pp., 1921 [Da] H. Davenport, Multiplicative number theory, third ed.. Springer-Verlag, New York, 2000. [Ha] G. Halasz, Uber die Mittelwerte multiplikativer zahlentheoretischer Funktionen. Acta Math. Acad. Sci. Hungaricae 19, 365-403 (1968). [HT] G. Halasz, and P. Turan, On the distribution of roots of Riemann zeta and allied functions, I, Journal of Number Theory 1.1 (1969): 121-137. [HB] D. R. Heath-Brown, A large values estimate for Dirichlet polynomials. Journal of the London Mathematical Society 2.1 (1979): 8-18. [HB2] D. R. Heath-Brown, The Differences between Consecutive Primes, II. Journal of the London Mathematical Society, 2.19 (1979): 207-220. [HB3] D. R. Heath-Brown, Zero Density Estimates for the Riemann Zeta-Function and Dirichlet L-Functions. Journal of the London Mathematical Society, 2.19 (1979): 221-232. [HB4] D. R. Heath-Brown, Prime Numbers in Short Intervals and a Generalized Vaughan Identity. Canadian Journal of Mathematics, 34.6 (1982): 1365–1377. [Hu] M. N. Huxley. On the difference between consecutive primes. Invent. Math., 15:164-170, 1972 [In] A. E. Ingham. On the estimation of N (σ, T ). Quart. J. Math. Oxford Ser., 11:291–292, 1940. [Iv] A. Ivic. The Riemann Zeta-Function, Wiley, 1985 .
[IK] H. Iwaniec and E. Kowalski. Analytic number theory, Vol. 53. American Mathematical Soc., 2021. [Ju] M. Jutila, Zero-density estimates for L-functions, Acta Arith., 32 (1977), 55–62. [MP] J. Maynard and K. Pratt, Half-isolated zeros and zero-density estimates. arXiv preprint arXiv:2206.11729 (2022). [M] H. Montgomery, Mean and large values of Dirichlet polynomials. Inventiones mathematicae 8.4 (1969): 334-345.
[M2] H. Montgomery, Ten Lectures On The Interface Between Analytic Number Theory And Harmonic Analysis, No. 84. American Mathematical Soc., 1994. [M3] H. Montgomery. Topics in multiplicative number theory. Lecture Notes in Mathematics, Vol. 227. Springer-Verlag, Berlin-New York, 1971.