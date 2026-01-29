---
title: "Jensen polynomials for the Riemann zeta function and other sequences"
authors:
  - "Michael Griffin"
  - "Ken Ono"
  - "Larry Rolen"
  - "Don Zagier"
date: "2019-00-00 2019"
publication: "Proceedings of the National Academy of Sciences USA"
doi: "10.1073/pnas.1902572116"
url: null
zotero:
  attachment_key: "J9VH6H4K"
  parent_key: "MTN59V47"
  item_id: 1962
  attachment_item_id: 1984
---

MATHEMATICS SEE COMMENTARY INAUGURAL ARTICLE
Jensen polynomials for the Riemann zeta function and other sequences
Michael Griffina, Ken Onob,1, Larry Rolenc, and Don Zagierd
aDepartment of Mathematics, Brigham Young University, Provo, UT 84602; bDepartment of Mathematics, Emory University, Atlanta, GA 30022; cDepartment of Mathematics, Vanderbilt University, Nashville, TN 37240; and dMax Planck Institute for Mathematics, 53111 Bonn, Germany
This contribution is part of the special series of Inaugural Articles by members of the National Academy of Sciences elected in 2017.
Edited by Kenneth A. Ribet, University of California, Berkeley, CA, and approved April 8, 2019 (received for review February 12, 2019)
In 1927, P  ́olya proved that the Riemann hypothesis is equivalent to the hyperbolicity of Jensen polynomials for the Riemann zeta function ζ(s) at its point of symmetry. This hyperbolicity has been proved for degrees d ≤ 3. We obtain an asymptotic formula for the central derivatives ζ(2n)(1/2) that is accurate to all orders, which allows us to prove the hyperbolicity of all but finitely many of the Jensen polynomials of each degree. Moreover, we establish hyperbolicity for all d ≤ 8. These results follow from a general theorem which models such polynomials by Hermite polynomials. In the case of the Riemann zeta function, this proves the Gaussian unitary ensemble random matrix model prediction in derivative aspect. The general theorem also allows us to prove a conjecture of Chen, Jia, and Wang on the partition function.
Riemann hypothesis | Jensen polynomials | hyperbolic polynomials
1. Introduction and Statement of Results
Expanding on notes of Jensen, P ́olya (1) proved that the Riemann hypothesis (RH) is equivalent to the hyperbolicity of the Jensen polynomials for the Riemann zeta function ζ(s) at its point of symmetry. More precisely, he showed that the RH is equivalent to the hyperbolicity of all Jensen polynomials associated with the sequence of Taylor coefficients {γ(n)} defined by
(−1 + 4z 2) Λ
(1
2 +z
)
=
∞
∑
n =0
γ (n )
n! · z 2n , [1]
where Λ(s) = π−s/2Γ(s/2)ζ(s) = Λ(1 − s), where we say that a polynomial with real coefficients is hyperbolic if all of its zeros are real, and where the Jensen polynomial of degree d and shift n of an arbitrary sequence {α(0), α(1), α(2), . . . } of real numbers is the polynomial
J d,n
α (X ) : =
d
∑
j =0
(d
j
)
α(n + j )X j . [2]
Thus, the RH is equivalent to the hyperbolicity of the polynomials J d,n
γ (X ) for all nonnegative integers d and n (1–3). Since this condition is preserved under differentiation, to prove RH, it would be enough to show hyperbolicity for the J d,0
γ (X ).∗ Due to the difficulty of proving RH, research has focused on establishing hyperbolicity for all shifts n for small d . Previous to this paper, hyperbolicity was known for d ≤ 3 by work† of Csordas et al. (5) and Dimitrov and Lucas (3). Asymptotics for the γ(n) were obtained from Coffey (6) and Pustyl’nikov (7). We improve on their results by obtaining an arbitrary precision asymptotic formula‡ (Theorem 9), a result that is of independent interest. We will use this strengthened result to prove the following theorem for all degrees d .
Significance
The P  ́olya–Jensen criterion for the Riemann hypothesis asserts that RH is equivalent to the hyperbolicity of certain Jensen polynomials for all degrees d ≥ 1 and all shifts n. For each degree d ≥ 1, we confirm this criterion for all sufficiently large shifts n. This represents a theoretical advance in the field. The method of proof is rooted in the newly discovered phenomenon that these polynomials are nicely approximated by Hermite polynomials. Furthermore, it is shown that this method applies to a large class of related problems.
Author contributions: M.G., K.O., L.R., and D.Z. wrote the paper.y
The authors declare no conflict of interest.y
This article is a PNAS Direct Submission.y
This open access article is distributed under Creative Commons Attribution-NonCommercial-NoDerivatives License 4.0 (CC BY-NC-ND).y
See Commentary on page 11085.y
1 To whom correspondence should be addressed. Email: ken.ono@emory.edu.y
Published online May 21, 2019.y
*The hyperbolicity for Jd,0
γ (X) has been confirmed for d ≤ 2 · 1017 by Chasse (cf. theorem 1.8 of ref. 4).
†These works use a slightly different normalization for the γ(n).
‡Our results imply the results in refs. 6 and 7 after typographical errors are corrected.
www.pnas.org/cgi/doi/10.1073/pnas.1902572116 PNAS | June 4, 2019 | vol. 116 | no. 23 | 11103–11110
Downloaded from https://www.pnas.org by 37.201.193.13 on October 17, 2025 from IP address 37.201.193.13.


 Theorem 1. If d ≥ 1, then J d,n
γ (X ) is hyperbolic for all sufficiently large n.
An effective proof of Theorem 1 for small d gives the following theorem.
Theorem 2. If 1 ≤ d ≤ 8, then J d,n
γ (X ) is hyperbolic for every n ≥ 0.
Theorem 1 follows from a general phenomenon that Jensen polynomials for a wide class of sequences α can be modeled by the Hermite polynomials Hd (X ), which we define (in a somewhat nonstandard normalization) as the orthogonal polynomials for the measure μ(X ) = e−X 2/4 or more explicitly by the generating function
∞
∑
d =0
Hd (X ) t d
d ! = e−t2+Xt = 1 + X t + (X 2 − 2) t 2
2! + (X 3 − 6X ) t3
3! + · · · . [3]
More precisely, we will prove the following general theorem describing the limiting behavior of Jensen polynomials of sequences with appropriate growth.
Theorem 3. Let {α(n)}, {A(n)}, and {δ(n)} be three sequences of positive real numbers with δ(n) tending to zero and satisfying
log
( α(n + j ) α(n )
)
= A(n)j − δ(n)2j 2 + o
(
δ(n)d )
as n → ∞, [4]
for some integer d ≥ 1 and all 0 ≤ j ≤ d . Then, we have
nli→m∞
( δ(n)−d
α(n) J d,n
α
( δ(n) X − 1 exp(A(n ))
))
= Hd (X ), [5]
uniformly for X in any compact subset of R.
Since the Hermite polynomials have distinct roots, and since this property of a polynomial with real coefficients is invariant under small deformation, we immediately deduce the following corollary.
Corollary 4. The Jensen polynomials J d,n
α (X ) for a sequence α : N → R satisfying the conditions in Theorem 3 are hyperbolic for all but finitely many values n.
Theorem 1 is a special case of this corollary. Namely, we shall use Theorem 9 to prove that the Taylor coefficients {γ(n)} satisfy the required growth conditions in Theorem 3 for every d ≥ 2. Theorem 3 in the case of the Riemann zeta function is the derivative aspect Gaussian unitary ensemble (GUE) random matrix model prediction for the zeros of Jensen polynomials. To make this precise, recall that Dyson (8), Montgomery (9), and Odlyzko (10) conjecture that the nontrivial zeros of the Riemann zeta function are distributed like the eigenvalues of random Hermitian matrices. These eigenvalues satisfy Wigner’s Semicircular Law, as do the roots of the Hermite polynomials Hd (X ), when suitably normalized, as d → +∞ (see chapter 3 of ref. 11). The roots of J d,0
γ (X ), as d → +∞, approximate the zeros of Λ ( 1
2 + z ) (see
ref. 1 or lemma 2.2 of ref. 12), and so GUE predicts that these roots also obey the Semicircular Law. Since the derivatives of Λ
(1
2 + z ) are also predicted to satisfy GUE, it is natural to consider the limiting behavior of J d,n
γ (X ) as n → +∞. The work here proves that these derivative aspect limits are the Hermite polynomials Hd (X ), which, as mentioned above, satisfy GUE in degree aspect. Returning to the general case of sequences with suitable growth conditions, Theorem 3 has applications in combinatorics where the hyperbolicity of polynomials determines the log-concavity of enumerative statistics. For example, see the classic theorem by Heilmann and Leib (13), along with works by Chudnovsky and Seymour (14), Haglund (15), Haglund et al. (16), Stanley (17), and Wagner (18), to name a few. Theorem 3 represents a criterion for establishing the hyperbolicity of polynomials in enumerative combinatorics. The theorem reduces the problem to determining whether suitable asymptotics hold. Here, we were motivated by a conjecture of Chen, Jia, and Wang concerning the Jensen polynomials J d,n
p (X ), where p(n) is the partition function. Nicolas (19) and Desalvo and Pak (20) proved that J 2,n
p (X ) is hyperbolic for n ≥ 25, and, more recently, Chen et al. proved (21) that J 3,n
p (X ) is hyperbolic for n ≥ 94, inspiring them to state as a conjecture the following result.
Theorem 5 (Chen–Jia–Wang Conjecture). For every integer d ≥ 1, there exists an integer N (d ) such that J d,n
p (X ) is hyperbolic for n ≥ N (d ).
Table 1 gives the conjectured minimal value for N (d ) for d = 2j with 1 ≤ j ≤ 5. More precisely, for each d ≤ 32 it gives the smallest integer such that J d,n
p (X ) is hyperbolic for N(d) ≤ n ≤ 50,000.
Remark 6: Larson and Wagner (22) have made the proof of Theorem 5 effective by a brute-force implementation of Hermite’s criterion (see theorem C of ref. 3). They showed that the values in the table are correct for d = 4 and d = 5 and that
N (d ) ≤ (3d )24d (50d )3d2 in general. The true values are presumably much smaller and are probably of only polynomial growth,
the numbers N (d ) in the table being approximately of size 10 d 2 log d .
Table 1. Conjectured minimal values of N(d)
d 1 2 4 8 16 32
N(d) 1 25 206 1,269 6,917 35,627
11104 | www.pnas.org/cgi/doi/10.1073/pnas.1902572116 Griffin et al.
Downloaded from https://www.pnas.org by 37.201.193.13 on October 17, 2025 from IP address 37.201.193.13.


 MATHEMATICS SEE COMMENTARY INAUGURAL ARTICLE
Table 2. Comparison of γ(n) and ̂γ(n)
n
̂γ(n) γ(n) γ(n)/̂γ(n)
10 ≈ 1.6313374394 ×10−17 ≈ 1.6323380490 ×10−17 ≈ 1.000613367 100 ≈ 6.5776471904 ×10−205 ≈ 6.5777263785 ×10−205 ≈ 1.000012038 1,000 ≈ 3.8760333086 ×10−2567 ≈ 3.8760340890 ×10−2567 ≈ 1.000000201 10,000 ≈ 3.5219798669 ×10−32265 ≈ 3.5219798773 ×10−32265 ≈ 1.000000002 100,000 ≈ 6.3953905598 ×10−397097 ≈ 6.3953905601 ×10−397097 ≈ 1.000000000
Theorem 5 suggests a natural generalization. As is well known, the numbers p(n) are the Fourier coefficients of a modular form, namely,
1
η(τ ) =
∞
∑
n =0
p(n) q n− 1
24 ( =(τ ) > 0, q = e2πiτ ), [6]
where η(τ ) = q1/24 ∏(1 − qn ) is the Dedekind eta-function. Theorem 5 is then an example of a more general theorem about the Jensen polynomials of the Fourier coefficients of an arbitrary weakly holomorphic modular form, which, for the purposes of this work, will mean a modular form (possibly of fractional weight and with multiplier system) with real Fourier coefficients on the full modular group SL2(Z) that is holomorphic apart from a pole of (possibly fractional) positive order at infinity. If f is such a form, we denote its Fourier expansion by§
f (τ ) =
∑
n ∈−m +Z≥0
af (n) qn (m ∈ Q>0, af (−m) 6= 0). [7]
Then, we will prove the following theorem, which includes Theorem 5.
Theorem 7. If f is a weakly holomorphic modular form as above, then for any fixed d ≥ 1, the Jensen polynomials J d,n
af (X ) are hyperbolic for all sufficiently large n.
Our results are proved by showing that each of the sequences of interest to us [the partition function, the Fourier coefficients of weakly holomorphic modular forms, and the Taylor coefficients at s = 1
2 of 4s(1 − s)Λ(s)] satisfies the hypotheses of Theorem 3,
which we prove in Section 2. Actually, in Section 2, we prove a more general result (Theorem 8) that gives the limits of suitably normalized Jensen polynomials for an even bigger class of sequences having suitable asymptotic properties (but without necessarily the corollary about hyperbolicity). Theorem 7 giving the hyperbolicity for coefficients of modular forms (and hence also for the partition function) is proved in Section 3. In Section 4, we prove Theorem 9, which gives an asymptotic formula to all orders for the Taylor coefficients of Λ(s) at s = 1
2 , and in Section 5, we prove Theorems 1 and 2 for the Riemann zeta function by using these
asymptotics to verify that the hypotheses of Theorem 3 are fulfilled by the numbers γ(n). We conclude in Section 6 with some numerical examples.
2. Proof of Theorem 3
We deduce Theorem 3 from the following more general result.
Theorem 8. Suppose that {E (n)} and {δ(n)} are positive real sequences with δ(n) tending to 0, and that F (t) = ∑∞
i=0 ci t i is a
formal power series with complex coefficients. For a fixed d ≥ 1, suppose that there are real sequences {C0(n)}, . . . , {Cd (n)}, with limn→+∞ Ci (n) = ci for 0 ≤ i ≤ d , such that for 0 ≤ j ≤ d , we have
α(n + j )
α(n) E (n)−j =
d
∑
i =0
Ci (n) δ(n)i j i + o
(
δ(n)d )
as n → +∞. [8]
Then, the conclusion of Theorem 3 holds with exp(A(n)) replaced by E (n) and Hd (X ) replaced by HF,d (X ), where the polynomials HF,m (X ) ∈ C[x ] are now defined either by the generating function F (−t) eXt = ∑ HF,m (X ) tm /m! or in closed form by HF,m (X ) : = m! ∑m
k=0 (−1)m−k cm−k X k /k ! .
Proof of Theorems 8 and 3. After replacing exp(A(n)) by E (n), the polynomial appearing on the left-hand side of [5] becomes
δ(n )−d
α(n) J d,n
α
( δ(n) X − 1 E (n)
)
=
d
∑
k =0
(
d k
)

δ(n )k −d
d
∑
j =k
(−1)j −k
(
d −k j −k
)
α(n + j ) α(n)E (n)j

Xk.
Since 0 ≤ j ≤ d , and since the error term in [8] is o(δ(n)d ), we may reorder summation and find that the limiting value as n → +∞ of the quantity in square brackets satisfies
lim
n →+∞


d
∑
i =0
Ci (n) δ(n)k−d+i
d
∑
j =k
(−1)j −k
(
d −k j −k
)
ji

 = (−1)d−k (d − k )! cd−k ,
§Note that with these notations we have p(n) = af (n − 1
24 ) for f = 1/η, but making this shift of argument is irrelevant for the applicability of Theorem 7 to Theorem 5, since the required asymptotic property is obviously invariant under translations of n.
Griffin et al. PNAS | June 4, 2019 | vol. 116 | no. 23 | 11105
Downloaded from https://www.pnas.org by 37.201.193.13 on October 17, 2025 from IP address 37.201.193.13.


 Table 3. The polynomials ̂Jp2, n and ̂Jp3, n
n
̂ J2, n
p (X) ̂ J3, n
p (X)
100 ≈ 0.9993X2 + 0.0731X − 1.9568 ≈ 0.9981X3 + 0.2072X2 − 5.9270X + 1.1420 200 ≈ 0.9997X2 + 0.0459X − 1.9902 ≈ 0.9993X3 + 0.1284X2 − 5.9262X − 1.4818 300 ≈ 0.9998X2 + 0.0346X − 1.9935 ≈ 0.9996X3 + 0.0965X2 − 5.9497X − 1.3790 400 ≈ 0.9999X2 + 0.0282X − 1.9951 ≈ 0.9998X3 + 0.0786X2 − 5.9621X − 1.2747
...
...
...
108 ≈ 0.9999X2 + 0.0000X − 1.9999 ≈ 0.9999X3 + 0.0000X2 − 5.9999X − 0.0529
because the inner sum, which is the (d − k )th difference of the polynomial j 7→ j i evaluated at j = 0, vanishes for i < d − k and equals (d − k )! for i = d − k . Theorem 8 follows, and Theorem 3 is just the special case E (n) = eA(n) and F (t) = e−t2 .
3. Proof of Theorem 7
Assume that f is a modular form of (possibly fractional) weight k on SL2(Z) (possibly with multiplier system) and with a pole of (possibly fractional) order m > 0 at infinity and write its Fourier expansion at infinity as in [7]. It is standard, either by the circle method of Hardy–Ramanujan–Rademacher or by using Poincar ́e series (for example, see ref. 23), that the Fourier coefficients of f have the asymptotic form
af (n) = Af n k−1
2 Ik−1(4π√mn) + O
(
n C e2π√mn )
, [9]
as n → ∞ for some nonzero constants Af [an explicit multiple of af (−m)] and C , where Iκ(x ) denotes the usual I -Bessel function. In view of the expansion of Bessel functions at infinity, this implies that af (n) has an asymptotic expansion to all orders in 1/n of the form
af (n ) ∼ e4π√mn n 2k−3
4 exp
(
c0 + c1
n + c2
n2 + ···
)
,
for some constants c0, c1, . . . depending on f [and in fact only on m and k if we normalize the leading coefficient af (−m) of f to be equal to 1]. This gives an asymptotic expansion
log
( af (n + j ) af (n)
)
∼ 4π√m
∞
∑
i =1
(
1/2 i
)
ji
ni− 1
2
+ 2k − 3
4
∞
∑
i =1
(−1)i−1j i
i ni +
∑
i,k ≥1
ck
(
−k i
)
ji
ni+k , [10]
valid to all orders in n, and it follows that the sequence {af (n)} satisfies the hypotheses of Theorem 3 with A(n) = 2π√m/n + O(1/n) and δ(n) = (π/2)1/2m1/4n−3/4 + O(n−5/4). Theorem 7 then follows from the corollary to Theorem 3.
4. Asymptotics for Λ(n)( 1
2)
Previous work of Coffey (6) and Pustyl’nikov (7) offer asymptotics¶ for the derivatives Λ(n) ( 1
2
). Here, we follow a slightly different approach and obtain effective asymptotics, a result which is of independent interest. To describe our asymptotic expansion, we first give a formula for these derivatives in terms of an auxiliary function, whose asymptotic expansion we shall then determine. Following Riemann (cf. chapter 8 of ref. 25), we have
Λ(s) =
∫∞
0
ts
2 −1 θ0(t ) dt = 1
s(s − 1) +
∫∞
1
(
ts
2 + t 1−s
2
)
θ0(t) dt
t,
where θ0(t) = ∑∞
k =1 e −πk 2t = 1
2 (t −1/2 − 1) + t −1/2θ0(1/t ). It follows that
Λ(n) ( 1
2
)= − 2n+2 n! + F (n)
2n−1 , [11]
for n > 0 (both are of course zero for n odd), where F (n) is defined for any real n ≥ 0 by
F (n) =
∫∞
1
(log t )n t −3/4 θ0(t ) dt . [12]
In particular, if n is a positive integer, then the Taylor coefficients γ(n) defined in [1] satisfy
γ(n) = n!
(2n)! ·
(
8
(
2n 2
)
Λ(2n−2) ( 1
2
)− Λ(2n) ( 1
2
)
)
= n!
(2n)! · 32(2n
2
)F (2n − 2) − F (2n)
22n−1 . [13]
¶It is interesting to note that Hadamard obtained rough estimates for these derivatives in 1893. His formulas are correctly reprinted on p. 125 of ref. 24.
11106 | www.pnas.org/cgi/doi/10.1073/pnas.1902572116 Griffin et al.
Downloaded from https://www.pnas.org by 37.201.193.13 on October 17, 2025 from IP address 37.201.193.13.


 MATHEMATICS SEE COMMENTARY INAUGURAL ARTICLE
Theorem 9. If n > 0, then the function F (n) defined by [12] is given to all orders in n by the asymptotic expansion
F (n) ∼ √2π Ln+1
√
(1 + L)n − 3
4 L2
e L/4−n/L+3/4
(
1 + b1
n + b2
n2 +···
)
(n → ∞),
where L = L(n) ≈ log
(n log n
)
is the unique positive solution of the equation n = L(πeL + 3
4 ) and each coefficient bk belongs to Q(L), the
first value being b1 = 2L4+9L3+16L2+6L+2
24 (L+1)3 .
Example 10: Here, we illustrate Theorem 9. The two-term approximation
F (n) ≈ √2π Ln+1
√
(1 + L)n − 3
4 L2
e L/4−n/L+3/4
(
1 + b1
n
)
= : ̂F (n),
is sufficiently strong for the proof of Theorem 1. In particular, Theorem 9 and [13] imply
̂γ(n) : = n!
(2n)! 26−2n
(
2n 2
)
̂F (2n − 2) = γ(n)
(
1+O
(1
n 2−ε
))
. [14]
Here are some approximations ̂γ(n) obtained from this expression by numerically computing L using its defining equation above. Table 2 illustrates the high precision of this formula.
Proof of Theorem 9: We approximate the integrand in [12] by f (t) = (log t)n t−3/4e−πt (from now on, we consider n as fixed and omit it from the notations). We have t d
dt log f (t ) = n
log t − πt − 3
4 , so f (t) assumes its unique maximum at t = a, where a = eL is the solution in (1, ∞) of
n=
(
πa + 3
4
)
log a.
We can then apply the usual saddle point method. The Taylor expansion of f (t) around t = a is given by
f ((1 + λ)a)
f (a) =
(
1 + log(1 + λ)
log a
)n
(1 + λ)−3/4e−πλa = e−C λ2/2 (1 + A3λ3 + A4λ4 + · · · ),
where C = (ε + ε2)n − 3
4 (here we have set ε = 1
log a = L−1) and the Ai (i ≥ 3) are polynomials of degree bi /3c in n with coefficients in Q[ε]. This expansion is found by expanding log(f ((1 + λ)a)) − log(f (a)) in λ. The linear term vanishes by the choice of a, the
quadratic term is −C λ2/2, and the coefficients of the higher powers of λ are all linear expressions in n with coefficients in Q[ε]. Exponentiating this expansion gives the claimed expression for f ((1 + λ)a)/f (a), where the dominant term of each Ai is governed primarily by the exponential of the cubic term of the logarithmic expansion. The first few Ai are
A3 =
(ε
3 + ε2
2 + ε3
3
)
n−1
4 , A4 = −
(ε
4 + 11ε2
24 + ε3
2 + ε4
4
)
n+ 3
16 ,
A5 =
(ε
5 + 5ε2
12 + 7ε3
12 + ε4
2 + ε5
5
)
n− 3
20 ,
A6 =
( ε2
18 + ε3
6 + 17ε4
72 + ε5
6 + ε6
18
)
n2 −
(ε
4 + 91ε2
180 + 17ε3
24 + 17ε4
24 + ε5
2 + ε6
6
)
n+ 5
32 .
Table 4. The polynomials ̂J2γ, n and ̂J3γ, n
n
̂ J2, n
γ (X) ̂ J3, n
γ (X)
100 ≈ 0.9896X2 + 0.3083X − 2.0199 ≈ 0.9769X3 + 0.7570X2 − 5.8690X − 1.2661 200 ≈ 0.9943X2 + 0.2271X − 2.0061 ≈ 0.9872X3 + 0.5625X2 − 5.9153X − 0.9159 300 ≈ 0.9960X2 + 0.1894X − 2.0029 ≈ 0.9911X3 + 0.4705X2 − 5.9374X − 0.7580 400 ≈ 0.9969X2 + 0.1663X − 2.0016 ≈ 0.9931X3 + 0.4136X2 − 5.9501X − 0.6623
...
...
...
108 ≈ 0.9999X2 + 0.0003X − 2.0000 ≈ 0.9999X3 + 0.0009X2 − 5.9999X − 0.0014
Griffin et al. PNAS | June 4, 2019 | vol. 116 | no. 23 | 11107
Downloaded from https://www.pnas.org by 37.201.193.13 on October 17, 2025 from IP address 37.201.193.13.


 Plugging in t = (1 + λ)a immediately gives the asymptotic expansion
∫∞
1
f (t) dt = a f (a)
∫∞
−1+1/a
e−C λ2/2 (1 + A3λ3 + A4λ4 + · · · ) d λ
= a f (a)
√ 2π C
(
1 + 3A4
C 2 + 15A6
C 3 + · · · + (2i − 1)!!A2i
Ci +···
)
.
(Here, only the part of the integral with C λ2 < B log n, where B is any function of n going to infinity as n does, contributes.) This equality and the expression in Theorem 9 are interpreted as asymptotic expansions. Although these series themselves may not converge for a fixed n, we may truncate the resulting approximation at O(n−A) for some A > 0, and as n → +∞, this approximation becomes true to the specified precision. Substituting into this expansion the formulas for C and Ai in terms of n, we obtain the statement of the theorem with F (n) replaced by the integral over f (t), with only A2i (i ≤ 3k ) contributing to bk . But then the same asymptotic formula holds also for F (n), since the ratio f (t)/θ0(t) = 1 + e−3πt + · · · is equal to 1 + O(n−K ) for any K > 0 for t near a.
5. Proof of Theorems 1 and 2
A. Proof of Theorem 1. For each d ≥ 1, we use Theorem 3 with sequences {A(n)} and {δ(n)} for which
log
( γ(n + j ) γ (n )
)
= A(n)j − j 2δ(n)2 +
d
∑
i =3
gi (n)j i + o
(
δ(n)d )
, [15]
for all 0 ≤ j ≤ d , where gi (n) = o (δ(n)i ). Stirling’s formula, [13], and [14] give
γ(n) = en−2nn+ 1
2 (1 + 1
12n )L̂n
2
̂n −3
̂n ̂n+ 1
2 (1 + 1
12̂n )
√ 2π
K · exp
(L
4 − ̂n
L+3
4
)(
1 + b1(̂n)
̂n
)(
1+O
(1
n 2−ε
))
, [16]
where ̂n : = 2n − 2, L : = L(̂n), and K : = K (̂n) : = (L(̂n)−1 + L(̂n)−2)
̂n − 3/4. The L(̂n) are values of a nonvanishing holomorphic function for <(n) > 1, and so for |j | < n − 1, we have the Taylor expansion
L(j ; n) : = L(̂n + 2j )
L(̂n) = 1 +
∑
m ≥1
`m (n) j m
m!.
If J = λ(n − 1) with −1 < λ < 1, then the asymptotic L(n) ≈ log( n
log n ) implies
lim
n→+∞ L(J , n) = lim
n →+∞
L (̂n(λ + 1))
L(̂n) = 1.
In particular, we have `1(n) = 2
K ·L2 and `2(n ) = −8(̂n−3/4L)(1+L/2)
K 3·L5 and `m (n) = o
(1 (n −1)m
)
. By a similar argument applied to
K(j ; n) : = K (̂n + 2j )
K (̂n) = 1 +
∑
m ≥1
km (n) j m
m! and B(j ; n) : = 1 + b1(̂n+2j )
̂n +2j 1 + b1(̂n)
̂n
=1+
∑
m ≥1
βm (n) j m
m!,
we find that βm (n) = o
(1
(n −1)m +1
)
, k1(n) = 2(L+1)
K ·L2 − 2̂n(L+2)
K 2L4 , and km (n) = o
(1 (n −1)m
)
for m ≥ 2.
Table 5. The polynomials ̂J6γ, n
n
̂ J6, n
γ (X)
100 ≈ 0.912X6 + 3.086X5 − 24.114X4 − 55.652X3 + 133.109X2 + 151.696X − 85.419 200 ≈ 0.950X6 + 2.374X5 − 26.625X4 − 42.824X3 + 153.246X2 + 115.849X − 100.510 300 ≈ 0.965X6 + 2.011X5 − 27.608X4 − 36.282X3 + 161.084X2 + 97.843X − 106.295 400 ≈ 0.973X6 + 1.780X5 − 28.139X4 − 32.111X3 + 165.303X2 + 86.428X − 109.388
...
...
1010 ≈ 0.999X6 + 0.000X5 − 29.999X4 − 0.008X3 + 179.999X2 + 0.020X − 119.999
11108 | www.pnas.org/cgi/doi/10.1073/pnas.1902572116 Griffin et al.
Downloaded from https://www.pnas.org by 37.201.193.13 on October 17, 2025 from IP address 37.201.193.13.


 MATHEMATICS SEE COMMENTARY INAUGURAL ARTICLE
Let R(j ; n) be the approximation for γ(n + j )/γ(n) obtained from [16]. We then expand log R(j ; n)= : ∑
m≥1 gm (n)j m , with the
idea that we will choose A(n) ∼ g1(n) and δ(n) ∼ √−g2(n). To this end, if J = λ(n − 1) for −1 < λ < 1, then a calculation reveals that
− (1 + λ) log(1 + λ) = lim
n →+∞
log R(J ; n)−J log
( nL2 4
̂n 2
)
−J
n − 1 . [17]
Therefore, gm (n) = O ((n − 1)1−m ), and algebraic manipulations give
g1(n) = log
( nL2
4
̂n 2
)
+
̂n`1(n) L + 1
L −2
L + `1(n) · L
4 − k1(n)
2 +O
(1
n 2−ε
)
,
g2(n) = − 1
̂n + (4`1(n) + ̂n`2(n)) L + 1
2L − ̂n`1(n)2 L + 2
2L + O
(1
n 2−ε
)
.
Using the formulas for `1(n), `2(n), and k1(n) above, we define
δ(n) : =
√1
̂n − 2
L2 · K and A(n) : = log
( nL2
4
̂n 2
)
+ L−1
L2 · K + ̂n(L + 2)
L4 · K 2 . [18]
The bounds for the gm (n) and the asymptotics above imply the o(1) error term in [15], and also that for sufficiently large n we have 0 < δ(n) → 0. Therefore, Theorem 3 applies, and its corollary gives Theorem 1.
B. Sketch of the Proof of Theorem 2. Let A(n) and δ(n) be as in [18]. If we let
̂J d,n
γ (X ) : = δ(n)−d
γ(n) · J d,n
γ
( δ(n) X − 1 exp(A(n ))
)
=
d
∑
k =0
β d ,n
k Xk,
then Theorem 1 implies that limn→+∞ ̂J d,n
γ (X ) = Hd (X ) = : ∑d
k=0 hk X k . We have confirmed the hyperbolicity of the ̂J d,n
γ (X ) for n ≤ 106 and 4 ≤ d ≤ 8 using Hermite’s criterion (see theorem C of ref. 3). Using this criterion, we also chose vectors εd : = (εd (d ), εd (d − 1), . . . , εd (0)) of positive numbers and signs sd , sd−1, . . . , s0 ∈ {±1} for which ̂J d,n
γ (X ) is hyperbolic if 0 ≤ sk (βd,n
k − hk ) < εd (k ) for all k . To make use of these inequalities, for positive integers n and 1 ≤ j ≤ 8, define real numbers C (n, j ) by
γ(n + j )
γ(n)eA(n)j · eδ(n)2j 2 = 1 + C (n, j )
n3/2 . [19]
Using an effective form of [16], it can be shown‖ that 0 < C (n, j ) < 14.25 for all n ≥ 7 and 1 ≤ j ≤ 8. Finally, we determined numbers Mεd for which the required inequalities hold for n ≥ Mεd . The proof follows from the fact that we found suitable choices for which
Mεd < 106.
Example 11: We illustrate the case of d = 4 using ε4 : = (0.041, 1.384, 0.813, 7.313, 0.804). For n ≥ 100 the odd degree coefficients satisfy
0 < β4,n
3 < 28 δ(n) and − 145.70δ(n) < β4,n
1 < 0,
while the even degree coefficients satisfy
1 − 16.05 δ(n)2 < β4,n
4 < 1, −12 < β4,n
2 < −12 + 16.20 δ(n), 12 − 16.01 δ(n) < β4,n
0 < 12.
It turns out that Mε4 : = 104 < 106.
6. Examples
For convenience, we let the ̂J d,n
α (X ) denote the polynomials which converge to Hd (X ) in [5]. We now illustrate Theorem 7 with [6], where m = 1/24 and k = −1/2. Using [10], we may choose A(n) = 2π
√24n−1 − 24
24n−1 and δ(n) =
√ 12π
(24n−1)3/2 − 288
(24n−1)2 . Although
the one-term approximations of [10] given at the end of Section 3 also satisfy Theorem 3, the two-term approximations converge more quickly and better illustrate the result. With these data, we observe in Table 3 indeed that the degree 2 and 3 partition Jensen
polynomials are modeled by H2(X ) = X 2 − 2 and H3(X ) = X 3 − 6X . Table 4 illustrates Theorem 1 for the Riemann zeta function using (18) in the case of degrees 2 and 3.
Finally, we conclude in Table 5 with data for the degree 6 renormalized Jensen polynomials J 6,n
γ (X ) which converge to H6(X ) = X 6 − 30X 4 + 180X 2 − 120.
ACKNOWLEDGMENTS. We thank the Max Planck Institute for Mathematics in Bonn for its support and hospitality; William Y. C. Chen, Rick Kreminski, Hannah Larson, Steffen L  ̈obrich, Peter Sarnak, and Ian Wagner for discussions related to this work; and Jacques G  ́elinas for bringing their attention to old work of Hadamard cited as a footnote in Section 4. M.G. and K.O. were supported by NSF Grants DMS-1502390 and DMS-1601306. K.O. was supported by Asa Griggs Candler Fund.
‖It turns out that δ(6) is not real.
Griffin et al. PNAS | June 4, 2019 | vol. 116 | no. 23 | 11109
Downloaded from https://www.pnas.org by 37.201.193.13 on October 17, 2025 from IP address 37.201.193.13.


 1. P  ́olya G (1927)  ̈Uber die algebraisch-funktionentheoretischen Untersuchungen von J. L. W. V. Jensen. Kgl Danske Vid Sel Math-Fys Medd 7:3–33. 2. Csordas G, Varga RS (1990) Necessary and sufficient conditions and the Riemann hypothesis. Adv Appl Math 11:328–357. 3. Dimitrov DK, Lucas FR (2011) Higher order Tura ́ n inequalities for the Riemann ξ-function. Proc Amer Math Soc 139:1013–1022. 4. Chasse M (2013) Laguerre multiplier sequences and sector properties of entire functions. Complex Var Elliptic Equ 58:875–885. 5. Csordas G, Norfolk TS, Varga RS (1986) The Riemann hypothesis and the Tura ́ n inequalities. Trans Amer Math Soc 296:521–541. 6. Coffey MW (2009) Asymptotic estimation of ξ(2n)(1/2): On a conjecture of Farmer and Rhoades. Math Comput 78:1147–1154. 7. Pustyl’nikov LD (2001) Asymptotics of the coefficients of the Taylor series of the ξ(s) function. Izv Ross Akad Nauk Ser Mat 65:93–106. 8. Katz NM, Sarnak P (1999) Zeroes of zeta functions and symmetry. Bull Amer Math Soc 36:1–27. 9. Montgomery HL (1973) The Pair Correlation of Zeros of the Zeta Function (American Mathematical Society, Providence, RI). 10. Odlyzko AM (2001) The 1022-nd zero of the Riemann zeta function. Dynamical, Spectral, and Arithmetic Zeta Functions, San Antonio, TX, eds Lapidus LL, van Frankenhuysen M. Contemporary Mathematics (American Mathematical Society, Providence, RI), Vol 290, pp 139–144. 11. Anderson GW, Guionnet A, Zeitouni O (2010) An Introduction to Random Matrices, Cambridge Studies in Advanced Mathematics (Cambridge Univ Press, Cambridge, UK), Vol 118. 12. Craven T, Csordas G (1989) Jensen polynomials and the Tura ́ n and Laguerre inequalities. Pac J Math 136:241–260. 13. Heilmann OJ, Lieb EH (1972) Theory of monomer-dimer systems. Commun Math Phys 25:190–232. 14. Chudnovsky M, Seymour P (2007) The roots of the independence polynomial of a clawfree graph. J Combin Theory Ser B 97:350–357. 15. Haglund J (2000) Further investigations involving rook polynomials with only real zeros. Eur J Combin 21:1017–1037. 16. Haglund J, Ono K, Wagner DG (1999) Theorems and conjectures involving rook polynomials with only real zeros. Topics in Number Theory, eds Ahlgren SD, Andrews GE, Ono K. Mathematics and its Applications (Kluwer Academic, Dordrecht, The Netherlands), Vol 467, pp 207–221. 17. Stanley RP (1989) Log-concave and unimodal sequences in algebra, combinatorics, and geometry. Ann NY Acad Sci 576:500–535. 18. Wagner DG (1991) The partition polynomial of a finite set system. J Combin Theory Ser A 56:138–159. 19. Nicolas J-L (1978) Sur les entiers N pour lesquels il y a beaucoup de groupes abe ́ liens d’ordre N. Ann Inst Fourier 28:1–16. 20. DeSalvo S, Pak I (2015) Log-concavity of the partition function. Ramanujan J 38:61–73. 21. Chen WYC, Jia DXQ, Wang LXW (December 26, 2018) Higher order Tura ́ n inequalities for the partition function. Trans Amer Math Soc, 10.1090/tran/7707. 22. Larson H, Wagner I (2019) Hyperbolicity of the partition Jensen polynomials. Res Numb Th, 10.1007/s40993-019-0157-y. 23. Bringmann K, Folsom A, Ono K, Rolen L (2017) Harmonic Maass Forms and Mock Modular Forms: Theory and Applications, American Mathematical Society Colloquium Publications (American Mathematical Society, Providence, RI), Vol 64. 24. Wang ZX, Guo DR (1989) Special Functions (World Scientific, Teaneck, NJ). 25. Davenport H (2000) Multiplicative Number Theory, Graduate Texts in Mathematics (Springer, New York), Vol 74, 3rd Ed.
11110 | www.pnas.org/cgi/doi/10.1073/pnas.1902572116 Griffin et al.
Downloaded from https://www.pnas.org by 37.201.193.13 on October 17, 2025 from IP address 37.201.193.13.