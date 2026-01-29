---
title: "Effective approximation of heat flow evolution of the Riemann \u03be function, and a new upper bound for the de Bruijn\u2013Newman constant"
authors:
  - "D. H. J. Polymath"
date: "2019-00-00 2019"
publication: "Research in the Mathematical Sciences"
doi: "10.1007/s40687-019-0193-1"
url: null
zotero:
  attachment_key: "9M3QFAX6"
  parent_key: "9SILYYYC"
  item_id: 1822
  attachment_item_id: 1839
---

D. H. J. Polymath Res Math Sci (2019) 6:31 https://doi.org/10.1007/s40687-019-0193-1
RESEARCH
Effective approximation of heat flow evolution of the Riemann ξ function, and a new upper bound for the de Bruijn–Newman constant
D. H. J. Polymath
*Correspondence: tao@math.ucla.edu http://michaelnielsen.org/polymath1/ index.php
Abstract
For each t ∈ R, define the entire function
Ht (z ):=
∫∞
0
etu2 Φ(u) cos(zu) du,
where Φ is the super-exponentially decaying function
Φ (u):=
∞ ∑
n=1
(2π 2n4e9u − 3π n2e5u) exp(−π n2e4u).
This is essentially the heat flow evolution of the Riemann ξ function. From the work of de Bruijn and Newman, there exists a finite constant Λ (the de Bruijn–Newman constant) such that the zeroes of Ht are all real precisely when t ≥ Λ. The Riemann hypothesis is equivalent to the assertion Λ ≤ 0; recently, Rodgers and Tao established the matching lower bound Λ ≥ 0. Ki, and Kim and Lee established the upper bound Λ< 1
2 . In this paper, we establish several effective estimates on Ht(x + iy) for t ≥ 0,
including some that are accurate for small or medium values of x. By combining these estimates with numerical computations, we are able to obtain a new upper bound Λ ≤ 0.22 unconditionally, as well as improvements conditional on further numerical verification of the Riemann hypothesis. We also obtain some new estimates controlling the asymptotic behavior of zeroes of Ht(x + iy) as x → ∞.
1 Introduction
Let H0 : C → C denote the function
H0(z) := 1
8ξ
(1
2 + iz
2
)
, (1)
where ξ : C → C denotes the Riemann ξ function
ξ (s) := s(s − 1)
2 π −s/2Γ
(s
2
)
ζ (s) (2)
123
© Springer Nature Switzerland AG 2019.
0123456789().,–: volV


 31 Page 2 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
(which is an entire function after removing all singularities) and ζ is the Riemann ζ function. Then, H0 is an entire even function with functional equation H0(z) = H0(z), and the Riemann hypothesis (RH) is equivalent to the assertion that all the zeroes of H0 are real. It is a classical fact (see [p. 255]) that H0 has the Fourier representation
H0(z) =
∫∞
0
Φ(u) cos(zu) du,
where Φ is the super-exponentially decaying function
Φ(u) :=
∑ ∞
n=1
(2π 2n4e9u − 3π n2e5u) exp(−π n2e4u). (3)
The sum defining Φ(u) converges absolutely for negative u also. From Poisson summation, one can verify that Φ satisfies the functional equation Φ(u) = Φ(−u) (i.e., Φ is even); this fact is of course closely related to the functional equation for ζ . de Bruijn [9] introduced (with somewhat different notation) the more general family of functions Ht : C → C for t ∈ R, defined by the formula
Ht (z) :=
∫∞
0
etu2 Φ(u) cos(zu) du. (4)
As noted in [8, p.114], one can view Ht as the evolution of H0 under the backward heat equation ∂t Ht (z) = −∂zzHt (z). As with H0, each of the Ht is entire even functions with functional equation Ht (z) = Ht (z); from the super-exponential decay of etu2 Φ(u), we see that the Ht is in fact entire of order 1. It follows from the work of Polya [15] that if Ht has purely real zeroes for some t, then Ht′ has purely real zeroes for all t′ > t; de Bruijn showed that the zeroes of Ht are purely real for t ≥ 1/2. Newman [11] strengthened this result by showing that there is an absolute constant − ∞ < Λ ≤ 1/2, now known as the de Bruijn–Newman constant, with the property that Ht has purely real zeroes if and only if t ≥ Λ. The Riemann hypothesis is then clearly equivalent to the upper bound Λ ≤ 0. Recently, in [18] the complementary bound Λ ≥ 0 was established, answering a conjecture of Newman [11] and improving upon several previous lower bounds for Λ [5–7,12,13,19]. Furthermore, Ki et al. [10] sharpened the upper bound Λ ≤ 1/2 of de Bruijn [9] slightly to Λ < 1/2. In this paper, we improve the upper bound:
Theorem 1.1 (New upper bound) We have Λ ≤ 0.22.
The proof of Theorem 1.1 combines numerical verification with some new asymptotics and observations about the Ht which may be of independent interest. Firstly, by analyzing the dynamics of the zeroes of Ht , we establish in Sect. 3 the following criterion for obtaining upper bounds on Λ:
Theorem 1.2 (Upper-bound criterion) Suppose that t0, X > 0 and 0 < y0 ≤ 1 obey the following hypotheses:
(i) (Numerical verification of RH at initial time 0) There are no zeroes ζ (σ + iT ) = 0 with 1+y0
2 ≤ σ ≤ 1 and 0 ≤ T ≤ X
2.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 3 of 67 31
Fig. 1 A visualization of Theorem 1.2. If at time t0 one can show that there are no zeroes Ht (x + iy) = 0 in the “canopy” 0 ≤ x < ∞, y0 ≤ y ≤ 1, then a theorem of de Bruijn allows one to conclude the desired bound Λ ≤ t0 + 1
2 y2
0 . The hypothesis (i) prevents zeroes hitting this canopy from an initial position to the left of the barrier; the hypothesis (ii) prevents zeroes from lying in the canopy to the right of the barrier; and the hypothesis (iii) prevents zeroes from starting to the right of the barrier and reaching the canopy to the left of the barrier
(ii) (Asymptotic zero-free region at final time t0) There are no zeroes Ht0 (x + iy) = 0 with
x≥X+
√
1 − y20 and y0 ≤ y ≤ √1 − 2t0.
(iii) (Barrier at intermediate times) There are no zeroes Ht (x + iy) = 0 with X ≤ x ≤
X+
√
1 − y20,
√
y20 + 2(t0 − t) ≤ y ≤ √1 − 2t, and 0 ≤ t ≤ t0.
Then, Λ ≤ t0 + 1
2 y20.
Informally, hypothesis (i) implies that at time t = 0, there are no zeroes Ht (x + iy) = 0 with large values of y to the left of the barrier region in (iii). The absence of zeroes in that barrier, together with a continuity argument and an analysis of the time derivative of each zero, can then be used to show that for later times 0 < t ≤ t0, there continue to be no zeroes Ht (x + iy) = 0 with large values of y to the left of the barrier; see Fig. 1. Hypothesis (ii) then gives the complementary assertion to the right of the barrier, and one can use an existing theorem of de Bruijn (Theorem 3.2) to conclude. In practice, we have found it convenient numerically to replace the barrier region in Theorem 1.2 with the larger and simpler region
X ≤ x ≤ X + 1; y0 ≤ y ≤ 1; 0 ≤ t ≤ t0.
We will obtain Theorem 1.1 by applying Theorem 1.2 with the specific numerical choices t0 = 0.2, X = 6 × 1010 + 83,952 − 0.5, and y0 = 0.2. The reason we choose X close to 6 × 1010 is that this is near the limit of known numerical verifications of the Riemann hypothesis such as [14], which we need for the hypothesis (i) of the above theorem; the
shift 83,952 − 0.5 is in place to make the partial Euler product ∏
p≤11
(
1− 1
p 1−2iX
)−1
large, which helps in keeping the functions Ht (x + iy), Ht0 (x + iy) large in magnitude, which in turn is helpful for numerical verifications of (ii) and (iii); see also Fig. 2. The choices t0 = 0.2, y0 = 0.2 are then close to the limit of our ability to numerically verify hypothesis (ii) for this choice of X. (The hypothesis (iii) is also verified numerically, but


 31 Page 4 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Fig. 2 Improving approximation of epn(x) w.r.t. |f0(x + iy)| as n is increased, where epn(x) = eulerprod(x, pn),
shown near X = 6 × 1010 + 83,951.5, which was chosen as a barrier location
can be done quite quickly compared to (ii), and so does not present the main bottleneck to further improvements to Theorem 1.1.) Further upper bounds to Λ can be obtained if one assumes the Riemann hypothesis to hold up to larger heights than that in [14]; see Sect. 10. To verify (ii) and (iii), we need efficient approximations (of Riemann–Siegel type) for Ht (x + iy) in the regime where t, y are bounded and x is large. For the sake of numerically explicit constants, we will focus attention on the region
0<t≤ 1
2 ; 0 ≤ y ≤ 1; x ≥ 200, (5)
though the results here would also hold (with different explicit constants) if the numerical quantities 1
2 , 1, 200 were replaced by other quantities. A key difficulty here is that Ht (x + iy) decays exponentially fast in x [basically because of the gamma factor in (2)]; see Fig. 3. This means that any direct attempt to numerically establish a zero-free region for Ht (x + iy) for large x would require enormous amounts of numerical precision. To get around this, we will first renormalize the function Ht (x + iy) by dividing it by a nowhere vanishing explicit function Bt (x + iy) (basically a variant of the aforementioned gamma factor) that removes this decay. To describe this function, we first introduce the function M0: C\(−∞, 1] → C\{0} defined by the formula
M0(s) := 1
8
s(s − 1)
2 π −s/2√2π exp
(( s
2−1
2
)
Log s
2−s
2
)
, (6)
where Log denotes the standard branch of the complex logarithm, with branch cut at the negative axis and imaginary part in (− π , π ]. One may interpret M0(s) as the Stirling approximation to the factor 1
8
s(s−1)
2 π −s/2Γ ( s
2
) appearing in (1), (2); it decays exponentially as one moves to infinity s → ±i∞ along the critical strip. We may form a holomorphic branch log M0: C\(−∞, 1] → C of the logarithm of M0 by the formula
log M0(s) := Logs + Log(s − 1) − s
2 log π + log
√2π
16 +
(s
2−1
2
)
Log s
2−s
2 ; (7)


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 5 of 67 31
Fig. 3 The quantities log |Ht (x + iy)| and log |Bt (x + iy)| when y = t = 0.4 and log10 x ≤ 7. Both quantities
decay like − π
8 x ≈ −0.393x
differentiating this, we see that the logarithmic derivative α: C\(−∞, 1] → C of this function, defined by
α := (log M0)′ = M′0
M0
, (8)
is given explicitly by the formula
α(s) = 1
s+ 1
s−1 − 1
2 log π + 1
2 Log s
2− 1
2s
=1
2s + 1
s−1 + 1
2 Log s
2π .
(9)
For any time t ∈ R, we then define the deformation Mt : C\(−∞, 1] of M0 by the formula
Mt (s) := exp
(t
4 α(s)2
)
M0(s) (10)
for any t ≥ 0. In the region (5), we introduce the quantity
Bt (x + iy) := Mt
( 1 + y − ix 2
)
. (11)
For fixed t ≥ 0 and y > 0, Bt (x + iy) is nonvanishing, and it is easy to verify the asymptotic
|Bt (x + iy)| = e−( π
8 +o(1))x. As it turns out, Bt (x + iy) is an asymptotic approximation to Ht (x + iy) in the region (5), in the sense that
xli→m∞
Ht (x + iy)
Bt (x + iy) = 1 (12)
for any fixed t > 0 and y > 0; see Fig. 4. (However, the convergence of (12) is not uniform as t approaches zero.)


 31 Page 6 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Fig. 4 The quantity |Ht (x + iy)/Bt (x + iy) − 1| when y = t = 0.4 and log10 x ≤ 12 (left) and when for 1000 ≤ x ≤ 1030 and various choices of (y, t) (right)
In fact, we have the following significantly more accurate approximation (of RiemannSiegel type) with effective error estimates. For any real number X, let O≤(X) denote a quantity that is bounded in magnitude by X. We also use x+ = max(x, 0) to denote the positive part of a real number x.
Theorem 1.3 (Effective Riemann–Siegel approximation to Ht (x + iy)) Let t, x, y lie in the region (5). Then, we have
Ht (x + iy)
Bt (x + iy) = ft (x + iy) + O≤ (eA + eB + eC,0) , (13)
where
ft (x + iy) :=
N ∑
n=1
btn
ns∗ + γ
N ∑
n=1
ny btn
ns∗+κ (14)
btn := exp
(t
4 log2 n
)
(15)
γ = γ (x + iy) :=
Mt
( 1−y+ix 2
)
Mt
( 1+y−ix 2
) (16)
s∗ = s∗(x + iy) := 1 + y − ix
2 +t
2α
( 1 + y − ix 2
)
(17)
κ = κ(x + iy) := t
2
( α
( 1 − y + ix 2
)
−α
( 1 + y + ix 2
))
(18)
N :=
⌊√ x
4π + t
16
⌋
(19)
and eA, eB, eC,0 are certain explicitly computable positive quantities1 depending on t and x + iy. Furthermore, we have the following bounds:
|γ | ≤ e0.02y ( x
4π
)−y/2 (20)
1See (71)–(74) for the precise definition of these quantities.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 7 of 67 31
Fig. 5 Comparison of |ft (x + iy)| and |Ht (x + iy)|/|Bt (x + iy)| for y = 0.9, t = 0.1, 1000 ≤ x ≤ 1030, (left) and when 106 ≤ x ≤ 106 + 30 (right). The approximation improves as x gets larger
Fig. 6 Comparison of |ft (x + iy)| and |Ht (x + iy)|/|Bt (x + iy)| for y = 0, t = 0.3, 1000 ≤ x ≤ 1030 (left), and when 106 ≤ x ≤ 106 + 30 (right). Again notice the improving approximation with x
Re s∗ ≥ 1 + y
2 +t
4 log x
4π − t
2x2
(
1 − 3y + 4y(1 + y)
x2
)
+
(21)
|κ| ≤ ty
2(x − 6) (22)
eA + eB ≤
N ∑
n=1
(1 + |γ |N |κ|ny) btn
nRe s∗
⎛
⎝exp
⎛
⎝
t2
16 log2 x
4πn2 + 0.626
x − 6.66
⎞
⎠−1
⎞
⎠ (23)
eC,0 ≤
(x
4π
)− 1+y
4 exp
(
−t
16 log2 x
4π + 1.24 × (3y + 3−y)
N − 0.125 + 3| log x
4π + i π
2 | + 10.44
x − 12
)
. (24)
This theorem will be proven in Sect. 6; see Figs. 5 and 6 for a numerical illustration of the approximation. The strategy is to express Ht as a convolution of H0 with a Gaussian heat kernel and then apply an effective Riemann–Siegel expansion to H0 to rewrite Ht as the sum of various contour integrals; see Sect. 4 for details. One then uses the saddle point method to shift each such contour to a location that is suitable for effective estimation. We remark that ft (x + iy) is a holomorphic function of x + iy in the region (5) as long as N is constant, but has jump discontinuities when N is incremented.


 31 Page 8 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Fig. 7 The error upper bound |eA + eB + eC,0| versus |ft − Ht /Bt | when y = t = 0.2 and 2 ≤ log10 x ≤ 5
Fig. 8 The individual error upper bounds |eA|, |eB| and |eC,0| with y = t = 0.2 and 2 ≤ log10 x ≤ 5. The eC,0-term clearly dominates.
From (13) and the triangle inequality, we have a numerically verifiable criterion to establish nonvanishing of Ht at a given point:
Corollary 1.4 (Criterion for nonvanishing) Let t, x, y lie in the region (5), and let ft , eA, eB, eC,0 be as in Theorem 1.3. If one has the inequality
|ft (x + iy)| > eA + eB + eC,0 (25)
then Ht (x + iy) = 0.
Actually, for some regions of x, y, t we will use a more complicated criterion than (25), in order to exploit the argument principle. To numerically estimate ft (x + iy) in a feasible amount of time, we will use Taylor expansion to be able to efficiently compute many values of ft (x + iy) simultaneously (see Sect. 7), and for some ranges of the parameters t, x, y we will also use an Euler product mollifier to reduce the amount of oscillation in the sum ft (x + iy) (see Sect. 8.5) (Figs. 7, 8).


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 9 of 67 31
Fig. 9 Comparison of |ft (x + iy)|, |ft (x + iy) − Ct (x+iy)
Bt(x+iy) | and |Ht (x + iy)|/|Bt (x + iy)| for y = 0, t = 0.3,
1000 ≤ x ≤ 1012
For y, t fixed and x sufficiently large, we have the asymptotics
eA, eB, eC,0 = O(x−ct )
ft (x + iy) = 1 + O(x−ct )
for some absolute constant c > 0; see Proposition 9.1(i) and its proof. This gives the crude asymptotic (12) in the region (5) at least. In practice, the eC,0 term numerically dominates the eA + eB term, although both errors will be quite small in the ranges of x under consideration; in particular, for the ranges needed to verify conditions (ii) and (iii) of Theorem 1.2, we can make eA + eB and eC,0 both significantly smaller than |ft (x + iy)|. In the spirit of expanding the Riemann–Siegel approximation to higher order, we also obtain an even more accurate explicit approximation in which a correction term − Ct
Bt is added to ft , and the error term eC,0 is replaced by a smaller quantity eC ; see (69) and Fig. 9. In addition to establishing upper bounds such as Theorem 1.1, one can use Theorem 1.3 and Corollary 1.4 (together with variants in slightly larger regions than (5), for instance if y is allowed to be as large as 10) to obtain asymptotic control on the zeroes of Ht , refining previous work of Ki et al. [10]. Indeed, in Sect. 9 we will establish
Theorem 1.5 (Distribution of zeroes of Ht ) Let 0 < t ≤ 1/2, let C > 0 be a sufficiently large absolute constant, and let c > 0 be a sufficiently small absolute constant. For x ≥ 4π, define
g(x, t) := x
4π log x
4π − x
4π + 11
8+t
16 log x
4π
and for all n ≥ C, let xn be the unique real number greater than 4π such that
g(xn, t) = n. (26)
(This is well defined since the g(x, t) is increasing in x for x ≥ 4π.)


 31 Page 10 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
(i) If x ≥ exp( C
t ) and Ht (x + iy) = 0, then y = 0, and
x = xn + O(x−ct )
for some n. (ii) Conversely, for each n ≥ exp( C
t ) there is exactly one zero Ht in the disk {x + iy: |x +
iy − xn| ≤ c
log xn } [and by part (i), this zero will be real and lie within O(x−ct ) of xn].
(iii) If X ≥ exp( C
t ), the number Nt (X) of zeroes with real part between 0 and X (counting multiplicity) is
Nt (X) = g(X, t) + O(1).
(iv) For any X ≥ 0, one has
Nt (X + 1) − Nt (X) ≤ O(log(2 + X))
and
Nt (X) = g(X, t) + O(log(2 + X)).
Here and in the sequel, we use X = O(Y ) to denote the estimate |X| ≤ AY for some constant A that is absolute (in particular, A is independent of t and C).
Roughly speaking, these estimates tell us that the zeroes of Ht behave (on macroscopic scales) like those of H0 in the region x = O(exp(O(1/t))) and are very evenly spaced (and on the real axis) outside of this range. The factor t
16 log xn
4π in (26) indicates that as time t advances, the zeroes (or at least those with large values of x) will tend to move toward the origin at a speed of approximately π
4 . Although we will not prove this here, the conclusions (i) and (iii) suggest that one in fact has an asymptotic of the form
Nt (X) = ⌊g(X, t) + O(X−ct )⌋
when X ≥ exp(C/t); in particular (since the sawtooth function x − x has average value
1
2 ) one would have the heuristic approximation
Nt (X) ≈ X
4π log X
4π − X
4π + 7
8+ t
16 log X
4π after performing some averaging in X, thus recovering the familiar 7
8 term in the usual averaged asymptotics for N0(X). The results in Theorem 1.5 refine previous results of Ki et al. [10, Theorems 1.3, 1.4], which gave similar results but with constants that depended on t in a non-uniform (and ineffective) fashion, and error terms that were of shape o(1) rather than O(x−ct ) in the limit x → ∞ (holding t fixed). The results may also be compared with those in [3], who (in our notation) show that assuming RH, the zeroes of H0 are precisely the solutions xn to the equation
1
2π arg
⎛
⎝−e2iθ(xn/2) ζ ′ ( 1−ixn
2
)
ζ ′ ( 1+ixn
2
)
⎞
⎠=n
for integer n, where − θ(t) is the phase of ζ ( 1
2 + it) and one chooses a branch of the
argument so that the left-hand side is − 1
2 when xn = 0 (Fig. 10).
Remark 1.6 One can draw an analogy between the various potential behaviors of zeroes of Ht and the three classical states of matter. A “gaseous” state corresponds to the situation in


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 11 of 67 31
Fig. 10 The real zeroes xi of Ht will converge to integer values of g(xi, t) when t (left) and/or x (right) increases
which some fraction of the zeroes of Ht are strictly complex. A “liquid” state corresponds to a situation in which the zeroes are real, but disordered (with highly unequal spacings between zeroes). A “solid” state corresponds to a situation in which the zeroes are real and arranged roughly in an arithmetic progression. Thus, for instance the Riemann hypothesis and the GUE hypothesis assert (roughly speaking) that the zeroes of H0 should exhibit liquid behavior everywhere, while Theorem 1.5 asserts that the zeroes of Ht , t > 0 “solidify” in the region x ≥ exp(C/t). Below this region, we expect liquid behavior. In general, as the parameter t increases, the zeroes appear2 to “cool” down, transitioning from gaseous to liquid to solid type states; see [18] for some formalizations of this intuition.
1.1 About this project
This paper is part of the Polymath project, which was launched by Timothy Gowers in February 2009 as an experiment to see if research mathematics could be conducted by a massive online collaboration. The current project (which was administered by Terence Tao) is the fifteenth project in this series. Further information on the Polymath project can be found on the Web site michaelnielsen.org/polymath1. Information about this specific project may be found at
http://michaelnielsen.org/polymath1/index.php?title=De_Bruijn-Newman_constant
and a full list of participants and their grant acknowledgments may be found at
http://michaelnielsen.org/polymath1/index.php?title=Polymath15_grant_ acknowledgments
We thank the anonymous referees for their careful reading of the paper and for several useful corrections and suggestions.
2 Notation
We use the standard branch Log of the logarithm to define the standard complex powers
zw := exp(wLogz) and, in particular, define the standard square root √z := z1/2 = exp( 1
2 Logz). We record the familiar Gaussian identity
2This is the picture for positive t at least. As t becomes very negative, it appears that the “gaseous” zeroes become more ordered again, for instance organizing themselves into curves in the complex plane. See [17] for further discussion of this phenomenon.


 31 Page 12 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
∫
R
exp (−(au2 + bu + c)) du =
√π
a exp
( b2
4a − c
)
(27)
for any complex numbers a, b, c with Re a > 0. When using order of magnitude notation such as O≤(X), any expression of the form A = B using this notation should be interpreted as the assertion that any quantity of the form A is also of the form B, thus for instance O≤(1) + O≤(1) = O≤(3). (In particular, the equality relation is no longer symmetric with this notation.) If F is a meromorphic function, we use F ′ to denote its derivative. We also use F ∗ to denote the reflection F ∗(s) := F (s) of F . Observe from analytic continuation that if F : Ω → C is holomorphic on a connected open domain Ω ⊂ C containing an interval in R and is real-valued on Ω ∩ R, then it is equal to its own reflection: F = F ∗ (since the holomorphic function F − F ∗ has an uncountable number of zeroes).
3 Dynamics of zeroes
In this section, we control the dynamics of the zeroes of Ht in order to establish Theorem 1.2. As Ht is even with functional equation Ht = Ht∗, the zeroes are symmetric around the origin and the real axis; from (4) and the positivity of Φ, we also see that Ht (iy) > 0 for all y ∈ R, so there are no zeroes on the imaginary axis. From the super-exponential decay of Φ and (4), we see that the entire function Ht is of order 1; by Jensen’s formula, this implies that the number of zeroes in a large disk D(0, R) is at most O(R1+o(1)) as R → ∞. We begin with the analysis of the dynamics of a single zero of Ht :
Proposition 3.1 (Dynamics of a single zero) Let t0 ∈ R, and let (zk (t0))k∈Z\{0} be an enumeration of the zeroes of Ht0 in C (counting multiplicity), with the symmetry condition z−k (t0) = −zk (t0).
(i) If j ∈ Z\{0} is such that zj(t0) is a simple zero of Ht0 , then there exists a neighborhood U of zj(t0), a neighborhood I of t0 in R, and a smooth map zj: I → U such that for every t ∈ I, zj(t) is the unique zero of Ht in U . Furthermore, one has the equation
dzj
dt (t0) = 2
′ ∑
k =j
1
zj(t0) − zk (t0) (28)
where the sum is over those k ∈ Z\{0} with k = j, and the prime means that the k and − k terms are summed together (except for the k = −j term, which is summed separately) in order to make the sum convergent. (ii) If j ∈ Z\{0} is such that zj(t0) is a repeated zero of Ht0 of order m ≥ 2, then there is
a neighborhood U of zj(t0) such that for t sufficiently close to t0, there are precisely m zeroes of Ht in U , and they take the form
zj(t0) + √2(t − t0)1/2λj + O(|t − t0|)
for j = 1, . . . , m as t → t0, where λ1 < · · · < λm are the roots of the mth Hermite polynomial
Hem(z) := (−1)m exp
( z2
2
) dm
dzm exp
(
− z2
2
)
(29)


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 13 of 67 31
=∑
0≤l≤m/2
m!
l!(m − 2l)! (−1)l zm−2l
2l (30)
and the implied constant in the O() notation can depend on t0, j, and m.
The differential equation (28) was previously derived in [8, Lemma 2.4] in the case t > Λ (in which all zeroes are real and simple); however, in our applications we also need to consider the regime t ≤ Λ in which the zeroes are permitted to be complex or repeated. The roots λ1, . . . , λm appearing in Proposition 3.1(ii) can be given explicitly for small values of m as
λ1 = −1; λ2 = +1
when m = 2,
λ1 = −√3; x2 = 0; λ3 = +√3
when m = 3, and
xλ1 = −
√
3 + √6; λ2 = −
√
3 − √6; λ3 =
√
3 − √6; λ4 =
√
3 + √6
when m = 4. From (29) and iterating Rolle’s theorem, we see that all the roots λ1, . . . , λm of Hem are real; from the Hermite equation
( d2
dz2 − z d
dz + m
)
Hem(z) = 0 and the Picard uniqueness theorem for ODE, we see that the zeroes are all simple.
Proof First suppose we are in the situation of (i). As zj(t0) is simple, ∂∂z Ht is nonzero at zj(t0); since Ht (z) is a smooth function of both t and z, we conclude from the implicit function theorem that there is a unique solution zj(t) ∈ U to the equation
Ht (zj(t)) = 0
with zj(t) in a sufficiently small neighborhood U of zj(t0), if t is in a sufficiently small neighborhood I of t0; furthermore, zj(t) depends smoothly on t and agrees with zj(t0) when t = t0. Differentiating the above equation at t0, we obtain
∂ Ht
∂t |t=t0 (zj(t0)) + dzj
dt (t0)Ht′0 (zj(t0)) = 0,
where the primes denote differentiation in the z variable. On the other hand, from (4) and differentiation under the integral sign (which can be justified using the rapid decrease in Φ) we have the backward heat equation
∂ Ht
∂t = −Ht′′ (31)
for all t ≥ 0. Inserting this into the previous equation, we conclude that
dzj
dt (t0) = Ht′′
Ht′
(zj(t0)), (32)
noting that the denominator Ht′(zj(t0)) is nonvanishing by the hypothesis that the zero at zj(t0) is simple. Henceforth, we omit the dependence on t0 for brevity. From Taylor expansion of Ht , Ht′, and Ht′′ around the simple zero zj, we see that
Ht′′
Ht′
(zj) = 2 zli→mzj
( Ht′
Ht
(z) − 1
z − zj
)
. (33)


 31 Page 14 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
On the other hand, as Ht is even, nonzero at the origin [as follows from (4) and the positivity of Φ], and entire of order 1, we see from the Hadamard factorization theorem that
Ht (z) = Ht (0)
′∏
k
(
1− z
zk
) ,
where the prime indicates that the k and − k factors are multiplied together. The product is locally uniformly convergent, so we may take logarithmic derivatives and conclude that
Ht′
Ht
(z) =
∑′
k
1 z − zk
.
Inserting this into (32), (33) and using the continuity of z → ∑′
k:k =j 1
z−zk at zj (which follows from the growth in the number of zeroes, either from the dominated convergence theorem or the Weierstrass M-test), we obtain the claim (i). Now, we prove (ii). We abbreviate zj(t0) as zj. By Taylor expansion, we have
∂2k Ht0
∂z2k (z) = m(m − 1) . . . (m − 2k + 1)am(z − zj)m−2k + O(|z − zj|max(m−2k+1,0))
as z → zj for any fixed integer k ≥ 0 and some nonzero complex number am = am(zj, t0) (with the implied constant in the O() notation allowed to depend on k, zj, t0); applying the backward heat equation (31), we thus have
∂k Ht
∂tk |t=t0 (z) = (−1)k m(m − 1) . . . (m − 2k + 1)am(z − zj)m−2k
+ O(|z − zj|max(m−2k+1,0)).
Performing Taylor expansion in time and using (30), we conclude that in the regime z − zj = O(|t − t0|1/2), one has the bound
Ht (z) = 2 m
2 am((t − t0)1/2)m
(
Hem
( z − zj
√2(t − t0)1/2
)
+ O (|t − t0|1/2))
as t → t0, using (say) the standard branch of the square root. By the inverse function theorem (and the simple nature of the zeroes of Hem), we conclude that for t sufficiently close but not equal to t0, we have m zeroes of Ht of the form
zj + √2(t − t0)1/2λj + O(|t − t0|).
By Rouche’s theorem, if U is a sufficiently small neighborhood of zj then these are the only zeroes of Ht in U for t sufficiently close to t0. The claim follows.
Next, we recall the following bound of de Bruijn:
Theorem 3.2 Suppose that t0 ∈ R and y0 > 0 is such that there are no zeroes Ht0 (x+iy) = 0 with x ∈ R and y > y0. Then, for any t > t0, there are no zeroes Ht (x + iy) = 0 with x ∈ R and y > max(y20 − 2(t − t0), 0)1/2. In particular, one has Λ ≤ t0 + 1
2 y20.
Proof See [9, Theorem 13].
We are now ready to prove Theorem 1.2. The main step is to establish
Proposition 3.3 (Zero-free region criterion) Suppose that t0, X > 0 and 0 < y0 ≤ 1 obey the following hypotheses:


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 15 of 67 31
(i) There are no zeroes H0(x + iy) = 0 with 0 ≤ x ≤ X and
√
y20 + 2t0 ≤ y ≤ 1.
(ii) There are no zeroes Ht0 (x + iy) = 0 with x ≥ X +
√
1 − y20 and y0 ≤ y ≤ √1 − 2t0.
(iii) There are no zeroes Ht (x + iy) = 0 with X ≤ x ≤ X +
√
1 − y20,
√
y20 + 2(t0 − t) ≤
y ≤ √1 − 2t, and 0 ≤ t ≤ t0.
Then, there are no zeroes Ht0 (x + iy) = 0 with x ∈ R and y ≥ y0.
Proof It is well known that the Riemann ξ function has no zeroes outside of the strip {0 ≤ Re s ≤ 1}; hence, there are no zeroes H0(x + iy) = 0 with y > 1. By Theorem 3.2,
we may thus remove the upper-bound constraints y ≤ 1, y ≤ √1 − 2t0, and y ≤ √1 − 2t from (i), (ii), and (iii), respectively. By hypotheses (ii), (iii) and the symmetry properties of Ht , it suffices to show that for every 0 ≤ t ≤ t0, there are no zeroes Ht (x + iy) = 0 with 0 ≤ x ≤ X and y ≥ Y (t),
where Y (t) :=
√
y20 + 2(t0 − t). By hypothesis (i), this is true at time t = 0. Suppose the claim failed for some time 0 < t ≤ t0. Let t1 ∈ (0, t0] be the minimal time in which this occurred (such a time exists because Ht varies continuously in t, and there are no zeroes Ht (x + iy) = 0 with (say) y > 1). From Rouche’s theorem (or Proposition 3.1) we conclude that there is a zero Ht1 (x + iy) = 0 with x + iy on the boundary of the region {x + iy: 0 ≤ x ≤ X, y ≥ Y (t1)}. The right side x = X of this boundary is ruled out by hypothesis (iii), and (as mentioned at the start of the section) the left side x = 0 is ruled out by (4) and the positivity of Φ. Thus, by the symmetry properties of Ht1 we must have
Ht1 (x + iY (t1)) = 0
for some 0 < x < X. Suppose first that Ht1 has a repeated zero at x + iy0. Using Proposition 3.1(ii) and observing (from the symmetry of Hem) that at least one of the roots x1, . . . , xm is positive, we then see that for t < t1 sufficiently close to t1, Ht has a zero in the region {x + iy : 0 ≤ x ≤ X, y ≥ Y (t)}, contradicting the minimality of t1. Thus, the zero x + iY (t1) of Ht1 must be simple. In particular, by Proposition 3.1(i) we can write x + iY (t1) = zj(t1) for some smooth function zj in a neighborhood of t1 obeying (28), such that zj(t) is a zero of Ht for all t close to t1. We will prove that
Im d
dt zj(t1) < d
dt Y (t1), (34)
which implies that there is a zero of Ht in the region {x + iy: 0 ≤ x ≤ X, y ≥ Y (t)} for t < t1 sufficiently close to t1, giving the required contradiction. The right-hand side of (34) is
d
dt Y (t1) = − 1
Y (t1) .
By Proposition 3.1(i), the left-hand side of (34) is
−2
′ ∑
k =j
Y (t1) − yk
(x − xk )2 + (Y (t1) − yk )2
where we write zk = xk + iyk . Clearly, any zero xk + iyk with imaginary part yk in [− Y (t1), Y (t1)] gives a non-positive contribution to this sum, the contribution of the zero


 31 Page 16 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
x−iY (t1) is − 1
Y (t1) , the contribution of the zero − x+iY (t1) vanishes, and the contribution of − x − iY (t1) is negative. Grouping the remaining zeroes with their complex conjugates, it then suffices to show that
Y (t1) − yk
(x − xk )2 + (Y (t1) − yk )2 − Y (t1) + yk
(x − xk )2 + (Y (t1) + yk )2 ≤ 0
whenever yk > Y (t1). Cross-multiplying and canceling like terms, this inequality eventually simplifies to
y2
k ≤ (x − xk )2 + Y (t1)2.
But from the hypothesis (iii) and the assumption yk > Y (t1), we have |xk | ≥ X +
√1 − Y (t1)2, so (x − xk )2 ≥ 1 − Y (t1)2. On the other hand, from Theorem 3.2 one has yk < 1, giving the required contradiction.
By combining Proposition 3.3 with Theorem 3.2, we obtain Theorem 1.2, noting from (1), (2) that condition (i) of Proposition 3.3 is implied by condition (i) of Theorem 1.2.
4 Applying the fundamental solution for the heat equation
As discussed in Introduction, we will establish Theorem 1.3 by writing Ht in terms of H0 using the fundamental solution to the heat equation. Namely, for any t > 0, we have from (27) that
etu2 =
∫
R
e±2√tvu √1π e−v2 dv
for any complex u and either choice of sign ±. Multiplying by e±izu and averaging, we conclude that
etu2 cos(zu) =
∫
R
cos
((
z − 2i√tv
) u
) √1π e−v2 dv
for any complex z, u. Multiplying by Φ(u) and using Fubini’s theorem, we conclude the heat kernel representation
Ht (z) =
∫
R
H0(z − 2i√tv) √1π e−v2 dv
for any complex z. Using (1), we thus have
Ht (z) =
∫
R
1
8ξ
( 1 + iz
2 + √tv
) √1π e−v2 dv. (35)
Remark 4.1 We have found numerically that the formula (35) gives a fast and accurate means to compute Ht (z) when z is of moderate size, e.g., if z = x + iy with |x| ≤ 106 and |y| ≤ 1. However, we will not need to directly compute the right-hand side of (35) for our application to bounding Λ, as we will only need to control Ht (x + iy) for large values of x, and we will shortly develop tractable approximations of Riemann–Siegel type that are more suitable for this regime.
We now combine this formula with expansions of the Riemann ξ -function. From [(2.10.6)], we have the Riemann–Siegel formula
1
8 ξ (s) = R0,0(s) + R0∗,0(1 − s) (36)


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 17 of 67 31
for any complex s that is not an integer (in order to avoid the poles of the gamma function), where R0,0(s) is the contour integral
R0,0(s) := 1
8
s(s − 1)
2 π −s/2Γ
(s
2
)∫
0↙1
w−s eiπ w2
eπiw − e−πiw dw
with 0 ↙ 1 any infinite line oriented in the direction e5πi/4 that crosses the interval [0, 1]. From the residue theorem (and the Gaussian decrease in eiπw2 along the eπi/4 and e5πi/4 directions), we may expand
R0,0(s) =
N ∑
n=1
r0,n(s) + R0,N (s)
for any nonnegative integer N , where r0,n, R0,N are the meromorphic functions
r0,n(s) := 1
8
s(s − 1)
2 π −s/2Γ
(s
2
)
n−s, (37)
R0,N (s) := 1
8
s(s − 1)
2 π −s/2Γ
(s
2
)∫
N ↙N +1
w−s eiπ w2
eπiw − e−πiw dw (38)
and N ↙ N + 1 denotes any infinite line oriented in the direction e5πi/4 that crosses the interval [N, N + 1]. For any z that is not purely imaginary, we see from Stirling’s approximation that the functions r0,n( 1+iz
2 + √tv) and R0,N ( 1+iz
2 + √tv) grow slower than Gaussian as v → ±∞ (indeed they grow like exp(O(|v| log |v|)), where the implied constants depend on t, z). From this and (35), (36), we conclude that
Ht (z) =
N ∑
n=1
rt,n
( 1 + iz 2
) +
N ∑
n=1
rt∗,n
( 1 − iz 2
)
+ Rt,N
( 1 + iz 2
)
+ Rt∗,N
( 1 − iz 2
)
(39)
for any t > 0, any z that is not purely imaginary, and any nonnegative integer N , where rt,n(s), Rt,N (s) are defined for non-real s by the formulae
rt,n(s) :=
∫
R
r0,n
(
s + √tv
) √1π e−v2 dv
Rt,N (s) :=
∫
R
R0,N
(
s + √tv
) √1π e−v2 dv;
these can be thought of as the evolutions of r0,n, R0,N , respectively, under the forward heat equation. The functions r0,n(s), R0,N (s) grow slower than Gaussian as long as the imaginary part of s is bounded and bounded away from zero. As a consequence, we may shift contours (replacing v by v +
√t
2 αn) and write
rt,n(s) = exp
(
−t
4 αn2
)∫
R
exp
(
−√tvαn
)
r0,n
(
s + √tv + t
2 αn
) √1π e−v2 dv (40)
for any complex number αn with Im (s), Im (s + t
2 αn) having the same sign. Similarly, we may write


 31 Page 18 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Rt,N (s) = exp
(
−t
4 β2N
)∫
R
exp
(
−√tvβN
)
R0,N
(
s + √tv + t
2 βN
) √1π e−v2 dv
(41)
for any complex number βN with Im s, Im (s + t
2 βN ) having the same sign. In the spirit of the saddle point method, we will select the parameters αn, βN later in the paper in order to make the integrands in (40), (41) close to stationary in phase at v = 0, in order to obtain good estimates and approximations for these terms.
5 Elementary estimates
In order to explicitly estimate various error terms arising in the proof of Theorem 1.3, we will need the following elementary estimates:
Lemma 5.1 (Elementary estimates) Let x > 0.
(i) If a > 0 and b ≥ 0 are such that x > b/a, then
O≤
(a
x
)
+ O≤
(b
x2
)
= O≤
(a
x − b/a
) .
More generally, if a > 0 and b, c ≥ 0 are such that x > b/a, √c/a, then
O≤
(a
x
)
+ O≤
(b
x2
)
+ O≤
(c
x3
)
= O≤
(a
x − max(b/a, √c/a)
) .
(ii) If x > 1, then
log
(
1 + O≤
(1
x
))
= O≤
(1
x−1
) .
or equivalently
1 + O≤
(1
x
)
= exp
(
O≤
(1
x−1
)) .
(iii) If x > 1/2, then
exp
(
O≤
(1
x
))
= 1 + O≤
(1
x − 0.5
) .
(iv) We have
exp (O≤(x)) = 1 + O≤(ex − 1).
(v) If z is a complex number with |Im z| ≥ 1 or Re z ≥ 1, then
Γ (z) = √2π exp
((
z− 1
2
)
log z − z + O≤
(1
12(|z| − 0.33)
)) .
(vi) If a, b > 0, y ≥ 0 and x ≥ x0 ≥ exp(a/b) and x0 > c ≥ 0, then
loga |x + iy|
(x − c)b ≤ loga |x0 + iy|
(x0 − c)b .
Proof Claim (i) follows from the geometric series formula
a
x−t = a
x + at
x2 + at2
x3 + · · ·
whenever 0 ≤ t < x.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 19 of 67 31
For Claim (ii), we use the Taylor expansion of the logarithm to note that
log
(
1 + O≤
(1
x
))
= O≤
(1
x+ 1
2x2 + 1
3x3 + · · ·
)
which on comparison with the geometric series formula
1
x−1 = 1
x+ 1
x2 + 1
x3 + · · ·
gives the claim. Similarly, for Claim (iii), we may compare the Taylor expansion
exp
(
O≤
(1
x
))
= 1 + O≤
(1
x+ 1
2!x2 + 1
3!x3 + · · ·
)
with the geometric series formula
1
x − 0.5 = 1
x+ 1
2x2 + 1
22x3 + · · ·
and note that k! ≥ 2k for all k ≥ 2. Claim (iv) follows from the trivial identity ex = 1+(ex −1) and the elementary inequality e−x ≥ 1 − (ex − 1). For Claim (v), we may use the functional equation Γ = Γ ∗ to assume that Im z ≥ 0. From the work of Boyd [4, (1.13), (3.1), (3.14), (3.15)], we have the effective Stirling approximation
Γ (z) = √2π exp
((
z− 1
2
)
log z − z
)(
1+ 1
12z + R2(z)
)
where the remainder R2(z) obeys the bound
|R2(z)| ≤ (2√2 + 1) C2Γ (2)
(2π )3|z|2
for Re z ≥ 0 and
|R2(z)| ≤ (2√2 + 1) C2Γ (2)
(2π )3|z|2|1 − e2πiz|
for Re z ≤ 0, where C2 is the constant
C2 := 1
2 (1 + ζ (2)) = 1
2
(
1 + π2
6
) .
In the latter case, we have Im z ≥ 1 by hypothesis, and hence |1 − e2πiz| ≥ 1 − e−2π . We conclude that in all ranges of z of interest, we have
|R2(z)| ≤ (2√2 + 1) C2Γ (2)
(2π )3|z|2(1 − e−2π ) ≤ 0.0205
|z|2
and hence by Claim (i)
Γ (z) = √2π exp
((
z− 1
2
)
log z − z
)(
1 + O≤
(1
12(|z| − 0.246)
))
and the claim then follows by Claim (ii).
For Claim (vi), it suffices to show that the function x → loga |x+iy|
(x−c)b is non-increasing for
x ≥ exp(a/b). Since log |x + iy| = (log x)(1 + log(1+ y2
x2 )
2 log x ) and the second factor is monotone
decreasing in x, it suffices to show that x → loga x
(x−c)b is non-increasing in this region. Taking
logarithms and differentiating, we wish to show that a
x log x − b
x−c ≤ 0. But this is clear
since b
x−c ≥ b
x and log x ≥ a/b.


 31 Page 20 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
6 Proof of Theorem 1.3
In this section, we establish Theorem 1.3. The strategy is to use the expansion (39), which turns out to be an effective approximation in the region (5), since we will be able to ensure
that quantities such as s + √tv + t
2 αn or s + √tv + t
2 βN , with s = 1+i(x+iy)
2 , stay away from the real axis where the poles of Γ are located (and also where the error terms in the Riemann–Siegel approximation deteriorate). Accordingly, we will need effective estimates on the functions rt,n, Rt,N appearing in Sect. 4. We will treat these two functions separately.
6.1 Estimation of rt,n
We recall the function α(s) defined in (8). From differentiating (9) we see that
α′(s) = − 1
2s2 − 1
(s − 1)2 + 1
2s (42)
whenever s ∈ C\(−∞, 1]. If Im s > 3, we conclude in particular the useful bound
α′(s) = O≤
(1
2Im (s)2
)
+ O≤
(1
Im (s)2
)
+ O≤
(1
2Im (s)
)
= O≤
(1
2Im (s) − 6
) (43)
thanks to Lemma 5.1(i). We also recall the function Mt and the coefficients btn from (10), (15), respectively. As it turns out, we have a good approximation
rt,n(σ + iT ) ≈ Mt (σ + iT ) btn
nσ +iT + t
2 α(σ +iT ) .
More precisely, we have
Proposition 6.1 (Estimate for rt,n) Let σ be real, let T > 10, let n be a positive integer, and let 0 < t ≤ 1/2. Then,
rt,n(σ + iT ) = Mt (σ + iT ) btn
nσ +iT + t
2 α(σ +iT ) (1 + O≤(εt,n(σ + iT )))
where
εt,n(σ + iT ) := exp
( t2
8 |α(σ + iT ) − log n|2 + t
4+1
6
T − 3.33
)
− 1. (44)
Proof From (37), (6) and Lemma 5.1(v), one has
r0,n(s) = M0(s)n−s exp
(
O≤
(1
6(|s| − 0.66)
))
whenever Im s > 2. Let αn denote the quantity
αn := α(σ + iT ) − log n; (45)
this is the logarithmic derivative of M(s)n−s at s = σ + iT . By (9) and the hypothesis T ≥ 10, the imaginary part of αn may be lower-bounded by
Im αn ≥ − 1
2T − 1
T ≥ −0.15; (46)


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 21 of 67 31
in particular, σ + iT and σ + iT + t
2 αn have imaginary parts of the same sign. We can now apply (40) to obtain
rt,n(σ + iT ) = exp
(
−t
4 αn2
)∫
R
exp
(
−√tvαn
)
M0
(
σ + iT + √tv + t
2 αn
)
× exp
( −
(
σ + iT + √tv + t
2 αn
)
log n
+ O≤
( 1
6(|σ + iT + √tv + t
2 αn| − 0.66)
))
√1π e−v2 dv.
From (46), we see that σ + iT + √tv + t
2 αn has imaginary part at least T − 0.08. Thus,
O≤
( 1
6(|σ + iT +√tv+ t
2 αn|−0.66)
)
= O≤
(1
6(T −0.74)
)
= O≤
(1
6(T −3.08)
) .
From (43), we have
α′(s) = O≤
(1
2(T − 3.08)
)
for all s on the line segment between σ + iT and σ + iT + √tv + t
2 αn. Applying Taylor’s theorem with remainder to the branch of the logarithm log M0 defined in (7), we conclude that
M0
(
σ + iT + √tv + t
2 αn
)
= M0(σ + iT ) exp
(
α(σ + iT )(√tv + t
2 αn) + O≤
( |√tv + t
2 αn|2
4(T − 3.08)
))
.
Combining these estimates, writing α(σ + iT ) = αn + log n, estimating |√tv + t
2 αn|2 by
2tv2 + t2
2 |αn|2, and simplifying, we conclude that
rt,n(s) = M0(σ + iT ) exp
(t
4 αn2 − (σ + iT ) log n
)
×
∫
R
exp
(
O≤
(t
2 v2 + t2
8 |αn|2 + 1
6
T − 3.08
))
√1π e−v2 dv.
Using (45), (10), and (15), we see that
M0(σ + iT ) exp
(t
4 αn2 − (σ + iT ) log n
)
= Mt (σ + iT ) btn
nσ +iT + t
2 α(σ +iT )
and so it suffices to show that ∫
R
exp
(
O≤
(t
2 v2 + t2
8 |αn|2 + 1
6
T − 3.08
))
√1π e−v2 dv
=1+O
(
exp
( t2
8 |αn|2 + t
4+1
6
T − 3.33
)
−1
)
.
Since √1π e−v2 dv integrates to one, it suffices by Lemma 5.1(iv) to show that
∫
R
exp
(t
2 v2 + t2
8 |αn|2 + 1
6
T − 3.08
)
√1π e−v2 dv ≤ exp
( t2
8 |αn|2 + t
4+1
6
T − 3.33
)
.


 31 Page 22 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Since 1
T −3.08 < 1
T −3.33 , we can remove the t2
8 |αn|2 + 1
6 terms from both sides and reduce to show that
∫
R
exp
( tv2
2(T − 3.08)
) √1π e−v2 dv ≤ exp
(t
4(T − 3.33)
)
. (47)
Using (27), the left-hand side may be calculated exactly as (
1− t
2(T − 3.08)
)−1/2 .
Applying Lemma 5.1(ii) and using the hypotheses t ≤ 1/2, T ≥ 10, one has
1− t
2(T − 3.08) = exp
(
O≤
(t
2(T − 3.33)
))
and the claim follows.
6.2 Estimation of Rt,N
We begin with the following estimates of Arias de Reyna [2] on the term ∫
N ↙N +1
w−s eiπ w2
eπiw −e−πiw
appearing in (38):
Proposition 6.2 Let σ be real and T ′ > 0, and define the quantities
s := σ + iT ′ (48)
a :=
√ T′
2π (49)
N := a (50)
p := 1 − 2(a − N ) (51)
U := exp
(
−i
(T′
2 log T ′
2π − T ′
2 −π
8
))
. (52)
Let K be a positive integer. Then, we have the expansion
∫
N ↙N +1
w−s eiπ w2
eπiw − e−πiw dw = (−1)N −1Ua−σ
( K ∑
k =0
Ck (p, σ )
ak + RSK (s)
)
where C0(p, σ ) = C0(p) is independent of σ and is given explicitly by the formula
C0(p) := eπi( p2
2 +3
8 ) − i√2 cos πp
2
2 cos(πp) (53)
(removing the singularities at p = ±1/2), while for k ≥ 1 the Ck (p, σ ) are complex numbers obeying the bounds
|Ck (p, σ )| ≤
√2
2π
9σ Γ (k/2)
2k (54)
for σ > 0 and
|Ck (p, σ )| ≤ 2 1
2 −σ
2π
Γ (k/2)
2π ((3 − 2 log 2)π )k/2 (55)


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 23 of 67 31
Fig. 11 Plot of |C0(p)| for − 1 ≤ p ≤ 1
for σ ≤ 0, while the error term RSK (s) is a complex number obeying the bounds
|RSK (s)| ≤ 1
7 23σ /2 Γ ((K + 1)/2)
(a/1.1)K +1 (56)
for σ ≥ 0, and
|RSK (s)| ≤ 1
2
(9
10
) −σ Γ ((K + 1)/2)
(a/1.1)K +1 (57)
if σ < 0 and K + σ ≥ 2.
Proof This follows from [2, Theorems 3.1, 4.1, 4.2] combined with [2, (3.2), (5.2)]. The dependence of Ck (p, σ ), k ≥ 1 on σ and the dependence of RSK (s) on s is suppressed in [2], but can be discerned from the definitions of these quantities (and the related quantities g(τ , z), Pk (z) = Pk (z, σ ), RgK (τ , z)) in [2, (3.9), (3.10), (3.7), (3.6)].
Note that p ranges in the interval [−1, 1]. One can show that
|C0(p)| ≤ 1
2 (58)
for all p ∈ [− 1, 1]; this follows for instance from the n = 0 case of [2, Theorem 6.1]. See also Fig. 11. Informally, the above proposition [and (38), (6)] yields the approximation
R0,N (s) ≈ 1
8
s(s − 1)
2 π −s/2Γ
(s
2
)
(−1)N−1Ua−σ C0(p)
≈ (−1)N−1UM0(s)a−σ C0(p).
If one writes s = σ + iT , then by using the approximation α(s) ≈ 1
2 log iT
2π for the logderivative of M0, one can then obtain the approximate formula
R0,N (s) ≈ (−1)N −1Ueπiσ /4M0(iT )C0(p).


 31 Page 24 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
In fact, we have the more general approximation
Rt,N (s) ≈ (−1)N −1Ueπiσ /4 exp
(tπ2
64
)
M0(iT ′)C0(p)
where T ′ := T + πt
8 . More precisely, we have
Proposition 6.3 (Estimate for Rt,N ) Let 0 ≤ σ ≤ 1, let T ≥ 100, and let 0 < t ≤ 1/2. Set
T ′ := T + π t
8
and then define a, N, p, U, C0(p) using (49), (50), (52), (53). Then,
Rt,N (σ + iT ) = (−1)N −1Ueπiσ /4 exp
(tπ2
64
)
M0(iT ′) (C0(p) + O≤(ε ̃(σ + iT )))
where
ε ̃(σ + iT ) :=
( 0.397 × 9σ
a − 0.865 + 5
3(T − 6)
)
exp
( 3.49 T −4
)
. (59)
Proof We apply (41) with βN := π i/4 to obtain
Rt,N (σ + iT ) = exp
(tπ2
64
)∫
R
exp
(
−
√t vπ i 4
)
R0,N (σ + iT ′ + √tv) √1π e−v2 dv.
From (38), we have
R0,N (σ + iT ′ + √tv) = 1
8
sv(sv − 1)
2 π −sv/2Γ
( sv 2
)
(−1)N −1Ua−σ −√tv
×
( K ∑v
k =0
Ck (p, σ + √tv)
ak + RSKv (sv)
)
for any positive integer Kv that we permit to depend (in a measurable fashion) on v, where
sv := σ + iT ′ + √tv. From (6) and Lemma 5.1(v), we thus have
R0,N (σ + iT ′ + √tv) = M0(sv) exp
(
O≤
( 1
12( T ′
2 − 0.33)
))
(−1)N −1Ua−σ −√tv
×
( K ∑v
k =0
Ck (p, σ + √tv)
ak + RSKv (sv)
)
.
From (43) and Taylor expansion of the logarithm log M0 defined in (7), we have
M0(sv) = M0(iT ′) exp
(
α(iT ′)(σ + √tv) + O≤
(
(σ + √tv)2 4(T − 3)
))
.
From (9) and (49), one has
α(iT ′) = O≤
(1
2T ′
)
+ O≤
(1
T′
)
+1
2 Log iT ′
2π = log a + iπ
4 + O≤
(3
2T ′
)
and hence [bounding 3
2T ′ by 6
4(T −3) ]
α(iT ′)(σ + √tv) = (σ + √tv) log a + π iσ
4+
√t vπ i
4 + O≤
(
6|σ + √tv| 4(T − 3)
)
.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 25 of 67 31
We conclude [bounding 1
12( T ′
2 −0.33) ≤ 1/3
4(T −3) ] that
exp
(
−
√t vπ i 4
)
R0,N (σ + iT ′ + √tv)
= M0(iT ′) exp
(
O≤
(
(σ + √tv)2 + 6|σ + √tv| + 1
3
4(T − 3)
))
× (−1)N −1Ueπiσ /4
( K ∑v
k =0
Ck (p, σ + √tv)
ak + RSKv (sv)
)
.
Bounding 6|σ + √tv| ≤ 3(σ + √tv)2 + 3, we have
(σ + √tv)2 + 6|σ + √tv| + 1
3
4(T ′ − 0.33) ≤ (σ + √tv)2 + 5
6
T −3 .
Putting all this together, we obtain
Rt,N (σ + iT ) = (−1)N −1Ueπiσ /4 exp
(tπ2
64
)
M0(iT ′)
×
∫
R
exp
(
O≤
(
(σ + √tv)2 + 5
6
T −3
))
×
( K ∑v
k =0
Ck (p, σ + √tv)
ak + RSKv (sv)
)
√1π e−v2 dv.
We separate the k = 0 term from the rest. By Lemma 5.1(iv) and the fact that √1π e−v2 integrates to one, we can write the above expression as
Rt,N (σ + iT ) = (−1)N −1Ueπiσ /4 exp
(tπ2
64
)
M0(iT ′) (C0(p)(1 + O≤( )) + O≤(δ))
(60)
where
:=
∫
R
(
exp
(
(σ + √tv)2 + 5
6
T −3
)
−1
)
√1π e−v2 dv
and
δ :=
∫
R
exp
(
(σ + √tv)2 + 5
6
T −3
) ( K ∑v
k =1
|Ck (p, σ + √tv)|
ak + |RSKv (sv)|
)
√1π e−v2 dv.
Bounding (σ + √tv)2 ≤ 2σ 2 + 2tv2 and using (27), we obtain
≤ exp
(
2σ 2 + 5
6
T −3
)(
1 − 2t
T ′ − 0.33
)−1/2
− 1.
Applying Lemma 5.1(ii) and using the hypotheses t ≤ 1/2, T ≥ 100, one has
1 − 2t
T − 3 = exp
(
O≤
( 2t T −6
))


 31 Page 26 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
and hence
≤ exp
(
2σ 2 + t + 5
6
T −6
)
− 1.
With t ≤ 1/2 and 0 ≤ σ ≤ 1, one has 2σ 2 + t + 5
6 ≤ 10
3 . By the mean value theorem, we then have
≤ 10
3(T − 6) exp
( 10
3(T − 6)
)
. (61)
Now, we work on δ. Making the change of variables u := σ + √tv, we have
δ=
∫
R
exp
(
u2 + 5
6
T −3
)⎛
⎝
K ̃∑u
k =1
|Ck (p, u)|
ak + |RSK ̃u (u + iT ′)|
⎞
⎠ √1π t e−(u−σ )2/t du,
where K ̃u is a positive integer parameter that can depend arbitrarily on u (as long as it is measurable, of course). We choose K ̃u to equal 1 when u ≥ 0 and max( −u + 3, T′
π ) when u < 0, so that Proposition 6.2 applies. The expression
K ̃∑u
k =1
|Ck (p, u)|
ak + |RSK ̃u (u + iT ′)|
is then bounded by
√2
2π
9uΓ (1/2)
2a + 1
7 23u/2 Γ (1)
(a/1.1)2 ≤ 0.200 × 9u
a + 0.173 × 23u/2
a2 (62)
for u ≥ 0 and
∑
1≤k ≤K ̃ u
21
2 −u
2π
Γ (k/2)
2π ((3 − 2 log 2)π )k/2ak + 1
2 (9/10) −u Γ ((K ̃u + 1)/2)
(a/1.1)K ̃u+1 (63)
for u < 0. One can calculate that
21
2
2π
1
2π ≤ 0.036 ≤ 1
2 and
1
((3 − 2 log 2)π )1/2 ≤ 0.445 ≤ 1.1
and hence we can bound (63) by
(0.036)2−u ∑
1≤k≤ T ′
π
(0.445)k Γ (k/2)
ak + 1
2 2−u ∑
T′
π ≤k≤−u+4
Γ (k/2)
(a/1.1)k .
For u ≥ 0, we can estimate (62) by
0.2 × 9u
(1
a + 0.865
a2
)
≤ 0.2 × 9u
a − 0.865
thanks to Lemma 5.1(i). For u < 0, we observe that if k ≤ 2a2 = T′
π then
Γ ( k+2
2)
ak+2 = k
2a2
Γ (k/2)
ak ≤ Γ (k/2)
ak


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 27 of 67 31
and hence by the geometric series formula
∑
2≤k≤ T ′
π ,k even
(0.445)k Γ (k/2)
ak ≤ (0.445)2
1 − (0.445)2
Γ (2/2)
a2 ≤ 0.247
a2
and similarly
∑
3≤k≤ T ′
π ,k odd
(0.445)k Γ (k/2)
ak ≤ (0.445)3
1 − (0.445)2
Γ (3/2)
a3 ≤ 0.098
a3
and hence we can bound (63) by
(0.036)2−u
( 0.445√π
a + 0.247
a2 + 0.098
a3
)
+1
2 2−u ∑
T′
π ≤k≤−u+4
Γ (k/2)
(a/1.1)k .
By Lemma 5.1(i), we have
0.036
( 0.445√π
a + 0.247
a2 + 0.098
a3
)
≤ 0.029
a − 0.353
and thus we can bound (63) by
0.029 × 2−u
a − 0.353 + 1
2 2−u ∑
T′
π ≤k≤−u+4
(1.1)k Γ (k/2)
ak .
Putting this together, we conclude that
K ̃∑u
k =1
|Ck (p, u)|
ak + |RSK ̃u (u + iT ′)| ≤ 0.2 × 9u
a − 0.865 + 0.029 × 2−u
a − 0.353
+ 2−u
2
∑
T′
π ≤k≤−u+4
(1.1)k Γ (k/2)
ak
for all u (positive or negative). We conclude that δ ≤ δ1 + δ2 + δ3, where
δ1 :=
∫
R
exp
(
u2 + 5
6
T −3
)
0.2 × 9u a − 0.865
√1π t e−(u−σ )2/t du
δ2 :=
∫
R
exp
(
u2 + 5
6
T −3
)
0.029 × 2−u a − 0.353
√1π t e−(u−σ )2/t du
δ3 :=
∫
R
exp
(
u2 + 5
6
T −3
)
2−u
2
∑
T′
π ≤k≤−u+4
(1.1)k Γ (k/2)
ak
√1π t e−(u−σ )2/t du. (64)
For δ1, we translate u by σ to obtain
δ1 = 0.2 × 9σ
a − 0.865
∫
R
exp
(
u2 + 2σ u + σ 2 + 5
6
T ′ − 0.33 + 2u log 3
)
√1π t e−u2/t du
and hence by (27)
δ1 = 0.2 × 9σ
a − 0.865 exp
( σ2 + 5
6
T ′ − 0.33 + t(log 3 + σ
T ′−0.33 )2
1− t
T −3
)(
1− t
T −3
)−1/2
. (65)


 31 Page 28 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
One can write
1 1− t
T −3
=1+ t
T −3−t ≤1+ t
T − 3.5 , (66)
while by Lemma 5.1(ii) we have
1− t
T − 3 = exp
(
O≤
(t
T −3−t
))
= exp
(
O≤
(t
T − 3.5
))
. (67)
We conclude that
δ1 ≤ 0.2 × 9σ
a − 0.865 exp
(
5 + 3t + 6σ 2
6(T − 3.5) + t
(
log 3 + σ
T −3
)2 (
1+ t
T − 3.5
))
.
From Lemma 5.1(i) and the hypothesis 0 ≤ σ ≤ 1, we have
(
log 3 + σ
T −3
)2
≤ (log2 3)
(
1 + 2σ / log 3
T −3− σ
2 log 3
)
≤ (log2 3)
(
1 + 2σ / log 3
T − 3.5
)
and therefore by a further application of Lemma 5.1(i)
(
log 3 + σ
T −3
)2 (
1+ t
T − 3.5
)
≤ log2 3
⎛
⎝1 +
2σ
log 3 + t T − 3.5 − 2σ t/ log 3
2σ / log 3+t
⎞
⎠
≤ log2 3
(
1+
2σ
log 3 + t
T − 3.5 − t
)
≤ log2 3
(
1+
2σ
log 3 + t
T −4
)
and thus
δ1 ≤ 0.2 × 9σ exp(t log2 3)
a − 0.865 exp
(
5 + 3t + 6σ 2 + 12tσ log 3 + 6t2 log2 3 6(T − 4)
)
.
By repeating the proof of (65), we have
δ2 = 0.029 × 2−σ
a − 0.353 exp
⎛
⎜⎝ σ 2 + 5
6
T −3 +
t
(
− log √2 + σ
T −3
)2
1− t
T −3
⎞
⎟⎠
(
1− t
T −3
)−1/2 .
We can bound (− log √2 + σ
T−3 )2 by log2 √2. Using (66) and (67), we thus have
δ2 ≤ 0.029 × 2−σ exp(t log2 √2)
a − 0.353 exp
(
5 + 3t + 6σ 2 + 6t2 log2 √2 6(T − 4)
)
.
With t ≤ 1/2 and 0 ≤ σ ≤ 1, one has


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 29 of 67 31
0.2 exp(t log2 3) ≤ 0.366
0.029 exp(t log2 √2) ≤ 0.031
5 + 3t + 6σ 2 + 6t2 log2 √2
6 ≤ 5 + 3t + 6σ 2 + 12tσ log 3 + 6t2 log2 3
6 ≤ 3.49
and hence δ1 ≤ 0.366 × 9σ
a − 0.865 exp
( 3.49 T −4
)
and δ2 ≤ 0.031 × 2−σ
a − 0.353 exp
( 3.49 T −4
) .
Now, we turn to δ3, which will end up being extremely small compared to δ1 or δ2. By (64) and the Fubini–Tonelli theorem, we have
δ3 = 1
2√π t
∑
k≥ T′
2.2π
(1.1)k Γ (k/2)
ak
∫ 4−k
−∞
exp
(
u2 + 5
6
T ′ − 0.33 − (u − σ )2
t − u log 2
)
du.
Since u ≤ 4 − k, k ≥ T′
2.2π , and T ′ ≥ T ≥ 100, we have k ≥ 14 and u ≤ −10; since
σ ≥ 0, we may thus lower-bound (u − σ )2/t by u2/t. Since t ≤ 1/2, we can upper-bound
u2+ 5
6
T ′−0.33 − u2
t by (say) − u2
2t , thus
δ3 ≤ 1
2√π t
∑
k≥ T′
2.2π
(1.1)k Γ (k/2)
ak
∫ 4−k
−∞
e− u2
2t −u log 2 du.
We can bound e− u2
2t ≤ e (k−4)u
2t , in the range of integration and thus
∫ 4−k
−∞
e− u2
2t −u log 2 du ≤ 1
k −4
2t − log 2 e− (k−4)2
2t +(k−4) log 2
≤1
k −4
2t − log 2 e−(k−4)2+(k−4) log 2;
bounding k −4
2t − log 2 = k − 4 − 2t log 2
2t ≥ k − 6
2t we conclude that
δ3 ≤
√√πt
∑
k≥ T′
2.2π
(1.1)k Γ (k/2)
(k − 6)ak e−(k−4)2+(k−4) log 2.
For k ≥ 14, one can easily verify that (1.1)k Γ (k/2)e−(k−4)2+(k−4) log 2 ≤ 10−30; discarding the
√√πt and 1
k−6 factors, we thus have
δ3 ≤ ∑
k ≥14
10−30
ak ≤ 2 × 10−30
a14
(say). Since
0.031 × 2−σ
a − 0.353 + 2 × 10−30
a14 ≤ 0.031 × 2−σ
a − 0.865 , we thus have δ ≤ δ1 + δ2 + δ3 ≤ 0.366 × 9σ + 0.031 × 2−σ
a − 0.865 exp
( 3.49 T −4
) .
Inserting this and (61), (58) into (60), and crudely bounding 2−σ by 9σ , we obtain the claim.


 31 Page 30 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
6.3 Combining the estimates
Combining Propositions 6.1 and 6.3 with (39) and the triangle inequality (and noting that M0 = M0∗, Mt = Mt∗ and α = α∗, and that U has magnitude 1), we conclude the following “A + B − C approximation to Ht ”:
Corollary 6.4 (A + B − C approximation) Let t, x, y obey (5). Set
T ′ := x
2 + πt
8 (68)
and then define a, N, p, U, C0(p) using (49), (50), (52), (53). Define the quantities
s+ = s+(x + iy) := 1 + y − ix
2
s− = s−(x + iy) := 1 − y + ix
2
At,N (x + iy) := Mt (s−)
N ∑
n=1
btn
ns−+ t
2 α(s−)
Bt,N (x + iy) := Mt (s+)
N ∑
n=1
btn
ns++ t
2 α(s+)
Ct (x + iy) := 2e−πiy/8(−1)N exp
(tπ2
64
)
Re (M0(iT ′)C0(p)Ueπi/8),
where M0 and btn were defined in (10) and (15). Then,
Ht (x + iy) = At,N (x + iy) + Bt,N (x + iy) − Ct (x + iy) + O≤(EA(x + iy)
+ EB(x + iy) + EC (x + iy)),
where
EA(x + iy) := ∣∣Mt (s−)∣∣
N ∑
n=1
btn
n 1−y
2 +t
2 Re α(s−) εt,n(s−)
EB(x + iy) := ∣∣Mt (s+)∣∣
N ∑
n=1
btn
n 1+y
2 +t
2 Re α(s+) εt,n(s+)
EC (x + iy) := exp
(tπ2
64
)
|M0(iT ′)| (ε ̃(s−) + ε ̃(s+))
and εt,n, ε ̃ were defined in (44), (59).
In our applications, we will just use the cruder “A + B” approximation that is immediate from the above corollary and (58):
Corollary 6.5 (A+B approximation) With the notation and hypotheses as in Corollary 6.4, we have
Ht (x+iy) = At,N (x+iy) + Bt,N (x+iy) + O≤(EA(x + iy) + EB(x + iy) + EC,0(x + iy)),
where
EC,0(x + iy) := exp
(tπ2
64
)
|M0(iT ′)| (1 + ε ̃(s−) + ε ̃(s+)) .


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 31 of 67 31
We can now prove Theorem 1.3. Dividing by the expression Bt from (11), and using (14), we conclude that
Ht (x + iy)
Bt (x + iy) = ft (x + iy) − Ct (x + iy)
Bt (x + iy) + O≤ (eA + eB + eC ) (69)
and
Ht (x + iy)
Bt (x + iy) = ft (x + iy) + O≤ (eA + eB + eC,0) , (70)
where
eA := eA(x + iy) := |γ |
N ∑
n=1
ny btn
nRe s+Re κ εt,n(s−) (71)
eB := eB(x + iy) :=
N ∑
n=1
btn
nRe s εt,n(s+) (72)
eC := eC (x + iy) :=
exp
( tπ2 64
)
|M0(iT ′)|
|Mt (s+)| (ε ̃(s−) + ε ̃(s+)) . (73)
eC,0 := eC,0(x + iy) :=
exp
( tπ2 64
)
|M0(iT ′)|
|Mt (s+)| (1 + ε ̃(s−) + ε ̃(s+)) , (74)
and where γ , s∗, κ were defined in (16)–(18). Note also from (68), (49), (50) that N is given by (19). To conclude the proof of Theorem 1.3, it thus suffices to obtain the following estimates.
Proposition 6.6 (Estimates) Let the notation and hypotheses be as above.
(i) One has
|γ | ≤ e0.02y ( x
4π
)−y/2
(ii) One has
Re s∗ ≥ 1 + y
2 +t
4 log x
4π − (1 − 3y + 8y(1−y)
x2 )+t
2x2 .
(iii) One has
κ = O≤
( ty
2(x − 6)
) .
(iv) One has
eA ≤ |γ |N |κ|
N ∑
n=1
ny btn
nRe s∗
⎛
⎝exp
⎛
⎝
t2
16 log2 x
4πn2 + 0.626
x − 6.66
⎞
⎠−1
⎞
⎠.
(v) One has
eB ≤
N ∑
n=1
btn
nRe s∗
⎛
⎝exp
⎛
⎝
t2
16 log2 x
4πn2 + 0.626
x − 6.66
⎞
⎠−1
⎞
⎠.


 31 Page 32 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
(vi) One has
eC ≤
(x
4π
)− 1+y
4 exp
(
−t
16 log2 x
4π + 3| log x
4π + i π
2 | + 3.58
x − 8.52
)
×
( 1.24 × (3y + 3−y)
N − 0.125 + 6.92
x − 12
) .
and
eC,0 ≤
(x
4π
)− 1+y
4 exp
(
−t
16 log2 x
4π + 3| log x
4π + i π
2 | + 3.58
x − 8.52
)
×
(
1 + 1.24 × (3y + 3−y)
N − 0.125 + 6.92
x − 12
) .
Note that to obtain the bound (24) from Proposition 6.6(vi) we may simply use the inequality 1 + u ≤ exp(u) for any u ∈ R, and then bound 1
x−8.52 ≤ 1
x−12 .
Proof From the mean value theorem (and noting that Mt = Mt∗, so that
∣∣∣Mt
( 1+y−ix 2
)∣∣∣ =
∣∣∣Mt
( 1+y+ix 2
)∣∣∣), we have
log |γ | = −y d
dσ log
∣∣∣∣Mt
(
σ + ix
2
)∣∣∣∣
for some 1−y
2 ≤ σ ≤ 1+y
2 . From (8) and (10), we have
d
dσ log
∣∣∣∣Mt
(
σ + ix
2
)∣∣∣∣ = Re
(t
2α
(
σ + ix
2
) α′
(
σ + ix
2
)
+α
(
σ + ix
2
)) .
From (43), one has
α′
(
σ + ix
2
)
= O≤
(1
x−6
)
(75)
and from Taylor expansion we also have
α
(
σ + ix
2
)
=α
( ix 2
)
+ O≤
(σ
x−6
) ;
from (9) one has
α
( ix 2
)
= O≤
(1
x
)
+ O≤
(1
x
)
+1
2 Log ix
4π = 1
2 log x
4π + i π
4 + O≤
(2
x
)
and hence
α
(
σ + ix
2
)
=1
2 log x
4π + i π
4 + O≤
(2+ σ x−6
)
. (76)
Inserting these bounds, we conclude that
log |γ | = −yRe
(( 1
2 log x
4π + i π
4 + O≤
(2 +σ x−6
)) (
1 + O≤
(t
2(x − 6)
))) .
Expanding this out, we have
log |γ | = −y
⎛
⎝1
2 log x
4π + O≤
⎛
⎝2 + σ + t
4 log x
4π + tπ
8 + t(2+σ )
2(x−6)
x−6
⎞
⎠
⎞
⎠.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 33 of 67 31
In the region (5), which implies that 0 ≤ σ ≤ 1, we have
2 + σ + tπ
8 + t(2 + σ )
2(x − 6) ≤ 3.21
and thus
log |γ | ≤ − y
2 log x
4π + y
t
4 log x
4π + 3.21
x−6 .
The function x → log x
4π
x−6 is decreasing for x ≥ 200 thanks to Lemma 5.1(vi), and hence
y
t
4 log x
4π + 3.21
x−6 ≤y
t
4 log 200
4π + 3.21
200 − 6 ≤ 0.02y.
Claim (i) follows. We remark that one can improve the e0.02y factor here by Taylor expanding α to second order rather than first order, but we will not need to do so here. To prove claim (ii), it suffices by (21) to show that
Re α(s+) ≥ 1
2 log x
4π − (1 − 3y)+
x2 − 4y(1 + y)
x4 .
By (9), one has
Re α(s+) = 1 + y
(1 + y)2 + x2 − 2(1 − y)
(1 − y)2 + x2 + 1
2 log
√(1 + y)2 + x2
4π .
We bound √(1 + y)2 + x2 ≥ x and calculate
1+y
(1 + y)2 + x2 − 2(1 − y)
(1 − y)2 + x2 = − 1 − 3y
(1 + y)2 + x2 − 8y(1 − y)
((1 + y)2 + x2)((1 − y)2 + x2)
≥ − 1 − 3y + 8y(1−y)
x2
(1 + y)2 + x2 .
Lower-bounding the numerator by its nonnegative part and then lower-bounding (1 + y)2 + x2 by x2, we obtain the claim. Claim (iii) is immediate from (75) and the fundamental theorem of calculus. Now, we turn to (iv), (v). From (76), one has
α
( 1 ± y + ix 2
)
− log n = 1
2 log x
4π n2 + i π
4 + O≤
(3
x−6
)
for either choice of sign ±. In particular, we have
∣∣∣∣α
( 1 ± y + ix 2
)
− log n
∣∣∣∣
2
=1
4 log2 x
4π n2 + π 2
16
+ O≤
( 3| log x
4πn2 + i π
2|
x−6 + 9
(x − 6)2
)
. (77)
For any 1 ≤ n ≤ N , we have
1 ≤ n2 ≤ N 2 ≤ a2 = x + πt
4
4π ;
in the region (5), the right-hand side is certainly bounded by ( x
4π )2, so that
4π
x≤ x
4π n2 ≤ x
4π


 31 Page 34 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
and hence
∣∣∣log x
4π n2 + i π
2
∣∣∣ ≤
∣∣∣log x
4π + i π
2
∣∣∣ .
In the region (5) we have x ≥ 200, we see from Lemma 5.1(vi) (after squaring) that
| log x
4π +i π
2|
x−6 is decreasing in x. Thus,
π2
16 + 3| log x
4πn2 + i π
2|
x−6 + 9
(x − 6)2 ≤ π 2
16 + 3| log 200
4π + i π
2|
200 − 6 + 9
(200 − 6)2
≤ 0.667.
Similarly, in (5) we also have
t2
8 × 0.667 + t
4+1
6 ≤ 0.313.
We conclude from (44) that
εt,n
( 1 ± y + ix 2
)
≤ exp
⎛
⎝
t2
32 log2 x
4πn2 + 0.313
T − 3.33
⎞
⎠ − 1.
Inserting this bound into (71) and (72), we obtain claims (iv) and (v). Now, we establish (vi). From (10), we have
exp
( tπ2 64
)
|M0(iT ′)|
|Mt (s+)| = exp
(tπ2
64 − t
4 Re (α(s+)2)
) |M0(iT ′)|
|M0(s+)| .
Note that 1+y+ix
2 = iT ′ + 1+y
2 − πit
8 . From (43), we see that |α′(s)| ≤ 1
x−6 for any s on the
line segment between iT ′ and 1+y+ix
2 . From Taylor’s theorem with remainder applied to
a branch of log M0, and noting that |M0(s+)| = |M0( 1+y+ix
2 )|, we conclude that
|M0(iT ′)|
|M0(s+)| = exp
(
Re
((
−1 + y
2 + πit
8
)
α(iT ′)
)
+ O≤
( | − 1+y
2 + πit
8 |2
2(x − 6)
))
.
For 0 ≤ y ≤ 1 and 0 < t ≤ 1
2 , we have
| − 1+y
2 + πit
8 |2
2 ≤ 0.52
and from (9) one has
α(iT ′) = O≤
(1
2T ′
)
+ O≤
(1
T′
)
+1
2 Log iT ′
2π = 1
2 log T ′
2π + iπ
4 + O≤
(3
2T ′
)
and hence
|M0(iT ′)|
|M0(s+)| = exp
(
−1 + y
4 log T ′
2π − tπ 2
32 + O≤
(
3| − 1+y
2 + πit
8|
2T ′ + 0.52
x−6
))
.
Bounding 1
2T ′ ≤ 1
x−6 and | − 1+y
2 + πit
8 | ≤ 1.02, this becomes
|M0(iT ′)|
|M0(s+)| =
( T′
2π
)− 1+y
4
exp
(
−tπ2
32 + O≤
( 3.58 x−6
))
and hence


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 35 of 67 31
exp
( tπ2 64
)
|M0(iT ′)|
|Mt ( 1+y+ix
2 )| =
( T′
2π
)− 1+y
4
× exp
(
−tπ2
64 − t
4 Re
(
α
( 1+y+ix 2
)2)
+O≤
( 3.58 x−6
))
.
By repeating the proof of (77), we have
Re
(
α
( 1 ± y + ix 2
)2)
=1
4 log2 x
4π − π2
16 + O≤
( 3| log x
4π + i π
2|
x−6 + 9
(x − 6)2
) .
As before, in the region (5) we have
3| log x
4πn2 + i π
2|
x−6 + 9
(x − 6)2 ≤ 3| log x
4π + i π
2|
x−6 + 9
(x − 6)2
and thus
exp
( tπ2 64
)
|M0(iT ′)|
|Mt (s+)|
=
( T′
2π
)− 1+y
4
exp
(
−t
16 log2 x
4π + O≤
( 3| log x
4π + i π
2 | + 3.58
x−6 + 9
(x − 6)2
))
=
( T′
2π
)− 1+y
4
exp
(
−t
16 log2 x
4π + O≤
( 3| log x
4π + i π
2 | + 3.58
x − 8.52
))
thanks to Lemma 5.1(i). Finally, since T ′ ≥ x
2 ≥ 100 in (5), one has
exp
( 3.49 T −4
)
≤ 1.037
and hence by (59)
ε ̃
( 1 ± y + ix 2
)
≤ 1.24 × 3±y
a − 0.125 + 1.73
T − 6.
Hence,
ε ̃(s+) + ε ̃(s−) ≤ 1.24 × (3y + 3−y)
a − 0.125 + 3.46
T −6
giving the claim (substituting T ′ = x/2 and a ≥ N ).
7 Fast evaluation of multiple sums
Fix t ≥ 0. For the verification of the barrier criterion (Theorem 1.2(iii)) using Corollary 1.4, we will need to evaluate the quantity ft (s) to reasonable accuracy for a large number of values of s in the vicinity of a fixed complex number X + iy. From (14), we have
ft (s) =
N ∑
n=1
nbbtn
n 1+y−iX
2
+ γ (s)
N ∑
n=1
nabtn
n 1−y+iX
2
, (78)
where btn is given by (15), γ (s) is given by (16), N is given by (19) and
b = b(s) := 1 + y − iX
2 − s∗
and
a = a(s) := 1 − y − iX
2 − s∗ − κ


 31 Page 36 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
with s∗, κ defined by (17) and (18). In practice, the exponents a, b will be rather small, and N will be fixed. (In our main verification, we will in fact have N = 69,098.) A naive computation of ft (s) for M values of s would take time O(NM), which turns out to be somewhat impractical for the ranges of N, M we will need; indeed, for our main theorem, the total number of pairs (t, s) at which we need to perform the evaluation is 785,052 (spread out over 152 values of t), and direct computation of all these data required 78.5 h of computer time, which was still feasible at this order of magnitude of X but would not scale to significantly higher magnitudes. However, one can significantly speed up the computation (to about 0.025 h) to extremely high accuracy by using Taylor series expansion to factorize the sums in (78) into combinations of sums that do not depend on s and thus can be computed in advance. We turn to the details. To make the Taylor series converge3 faster, we recenter the sum in n, writing
N ∑
n=1
F (n) =
(N +1)/2
∑
h=− N /2 +1
F (n0 + h)
for any function F , where n0 := N /2 . We thus have
ft (s) = B(b) + γ (s)A(a),
where
B(b) :=
(N +1)/2
∑
h=− N /2 +1
(n0 + h)bbt
n0 +h (n0 + h) 1+y−iX
2
and
A(a) :=
(N +1)/2
∑
h=− N /2 +1
(n0 + h)abt
n0 +h (n0 + h) 1−y+iX
2
.
We discuss the fast computation of B(b) for multiple values of b; the discussion for A(a) is analogous. We can write the numerator (n0 + h)bbt
n0+h as
exp
(
b log(n0 + h) + t
4 log2(n0 + h)
) ;
writing log(n0 + h) = log n0 + log(1 + h
n0 ), this becomes
nb+ t
4 log n0
0 exp
(t
4 log2
(
1+ h
n0
))
exp
((
b+ t
2 log n0
)
log
(
1+ h
n0
)) .
By Taylor expanding4 the exponentials, we can write this as
nb+ t
4 log n0 0
∞ ∑
i=0
∑ ∞
j=0
(t
4 log2 (
1+ h
n0
))i
i! logj
(
1+ h
n0
) (b + t
2 log n0
)j
j!
and thus the expression B(b) can be written as
B(b) = nb+ t
4 log n0 0
∑ ∞
i=0
∑ ∞
j=0
Bi,j
(b + t
2 log n0
)j
j!
3One can obtain even faster speedups here by splitting the summation range ∑N
n=1 into shorter intervals and using a Taylor expansion for each interval, although ultimately we did not need to exploit this. 4It is also possible to proceed by just performing Taylor expansion on the second exponential and leaving the first exponential untouched; this turns out to lead to a comparable numerical run time.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 37 of 67 31
Fig. 12 Achieved error term in the Taylor expansion at t = 0. Target was set at 20 decimal places accuracy
where
Bi,j :=
(N +1)/2
∑
h=− N /2 +1
(t
4 log2 (
1+ h
n0
))i
i!
logj (
1+ h
n0
)
(n0 + h) 1+y−iX
2
.
If we truncate the i, j summations at some cutoff E, we obtain the approximation
B(b) ≈ nb+ t
4 log n0 0
E−1
∑
i=0
E−1
∑
j=0
Bi,j (n0 )
(b + t
2 log n0
)i
i! .
The quantities Bi,j, i, j = 0, . . . , E − 1 may be evaluated in time O(NE2), and then the sums B(b) for M values of b may be evaluated in time O(ME2), leading to a total computation time of O((N + M)E2) which can be significantly faster than O(NM) even for relatively large values of E. We took E = 50, which is more than adequate to obtain extremely high accuracy;5 for ft (s), see Fig. 12. The code for implementing this may be found in the file
dbn_upper_bound/pari/barrier_multieval_t_agnostic.txt
in the GitHub repository [16].
8 A new upper bound for the de Bruijn–Newman constant
In this section, we prove Theorem 1.1.
8.1 Selection of parameters
As stated in Introduction, it suffices to verify the conditions (i), (ii), (iii) of Theorem 1.2 t0 := 0.2, X := X0 − 0.5, and y0 := 0.2, where X0 := 6 × 1010 + 83,952. The choice t0 = y0 = 0.2 is due to the limitations of our numerical verifications, particularly the known numerical verification of RH. We now explain the choice of X0.
5One can obtain more than adequate analytic bounds for the error (which are several orders of magnitude more than necessary) for the parameter ranges of interest by very crude bounds, e.g., bounding b and log(1 + h
n0 ) by (say) O≤(2), and relying primarily on the i! and j! terms in the denominator to make the tail terms small. We omit the details as they are somewhat tedious.


 31 Page 38 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Recall the familiar Euler product factorization
ζ (s) = ∏
p
(
1− 1
ps
)−1
for the Riemann zeta function. This leads to the heuristic
H0(x + iy) ∝ ∏
p≤P
(
1− 1
ps
)−1
for some small prime cutoff P, where s = 1+y+ix
2 and we are extremely vague as to what the proportionality symbol ∝ means. This heuristic extends to nonzero times t as
Ht (x + iy) ∝ ∏
p≤P
(
1 − btp
ps
)−1
and we also have
ft (x + iy) ∝ ∏
p≤P
(
1 − btp
ps
)−1
. (79)
One can non-rigorously justify the latter assertion by inspecting the first series of ft (x + iy) in (14) and ignoring the fact that the sequence n → btn is not multiplicative when t = 0. We will be relying heavily on Corollary 1.4 and therefore seek to ensure that |ft (x + iy)| is as large as possible. It would therefore seem to be advantageous to try to work as much as possible in regions where Euler product
∏
p≤P
(
1 − btn
ps
)
is small, which heuristically corresponds to x
4π log p being close to an integer for p ≤ P (so that ps has argument close to zero). If one chooses x to lie in the vicinity of
X := 6 × 1010 + 83,952 − 0.5,
then indeed the fractional parts { X
4π log p} for p ≤ 11 are somewhat close to zero:
{X
4π log 2
}
= 0.0275 . . .
{X
4π log 3
}
= 0.0437 . . .
{X
4π log 5
}
= 0.0640 . . .
{X
4π log 7
}
= 0.0774 . . .
{X
4π log 11
}
= 0.0954 . . .
We found this shift by the following somewhat ad hoc procedure. We first introduced the quantity


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 39 of 67 31
eulerprod(x, pn) :=
∣∣∣∣∣∣
∏
p≤pn
1
1− 1
p1−ix/2
∣∣∣∣∣∣ ,
which is the exponent corresponding to y = 1 (where the minimum value of |ft (x + iy)| in the barrier region is expected to occur). We numerically located candidate integers 1 ≤ q ≤ 105 for which the quantity
min
x−6×1010−q∈{−0.5,0,0.5} |eulerprod(x, 29)|
exceeded a threshold (we chose 4), to obtain seven candidates for q: 1046, 22,402, 24,198, 52,806, 77,752, 83,952, and 99,108. Among these candidates, we selected the value of q which maximized the quantity
min
x−6×1010−q∈{−0.5,0,0.5} |f0(x + i)|,
namely q = 83,952 (this quantity being ≈ 4.32 for this value of q).
8.2 Verifications of claims
Claim (i) of Theorem 1.2 is immediate from the result of Platt [14] that all the nontrivial zeroes of ζ with imaginary part between 0 and 3.06 × 1010 lie on the critical line {Re s = 1/2}. For the remaining claims (ii), (iii) of Theorem 1.2, it will suffice to verify that Ht (x + iy) = 0 for the following three regions of (x, y, t):
(ii) x ≥ X0 − 0.5 + √0.96, 0.2 ≤ y ≤ √0.6, and t = 0.2.
(iii) X0 − 0.5 ≤ x ≤ X0 + 0.5, 0.2 ≤ y ≤ √0.6, and 0 ≤ t ≤ 0.2.
Here, we have enlarged the region (iii) for simplicity. Both of these regions lie in (5). We can of course replace Ht (x + iy) by Ht (x + iy)/Bt (x + iy). Set
N :=
⌊√ x
4π + t
16
⌋
so in particular
xN ≤ x < xN+1 (80)
where
xN := 4π N 2 − π t
4.
Write N0 := 69,098 and N1 := 1.5 × 106. In region (ii), we then have N ≥ N0, while in region (iii) we have N = N0. It will now suffice to verify Ht(x+iy)
Bt(x+iy) = 0 in the following three regions:
(a) When X0 − 0.5 ≤ x ≤ X0 + 0.5, N = N0, 0 ≤ t ≤ 0.2, and 0.2 ≤ y ≤ 1. (b) When x ≥ X0 − 0.5, N0 ≤ N ≤ N1, t = 0.2, and 0.2 ≤ y ≤ 1. (c) When N ≥ N1, t = 0.2, and 0.2 ≤ y ≤ 1.
In all three regions, we use the following approximation:


 31 Page 40 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Proposition 8.1 Let (x, y, t) lie in one of the regions (a), (b), (c). Define
ft (x + iy) :=
N ∑
n=1
btn
ns∗ + γ
N ∑
n=1
ny btn
ns∗+κ
btn := exp
(t
4 log2 n
) ,
where κ, s∗, γ are as in Theorem 1.3. Then,
Ht (x + iy)
Bt (x + iy) = ft (x + iy) + O≤(1.25 × 10−3). (81)
Proof By Theorem 1.3, it suffices to show that
eA + eB + eC,0 ≤ 1.25 × 10−3.
From Theorem 1.3 again, we have
eA + eB ≤ (eδ1 − 1)(FN,t (Re s∗) + |γ |N |κ|FN,t (Re s∗ − y)) (82)
where
FN,t (σ ) :=
N ∑
n=1
btn
nσ . (83)
and
δ1 :=
t2
16 log2 x
4π + 0.626
x − 6.66 . (84)
From Lemma 5.1(vi), the quantity δ1 is monotone decreasing in x in the region (5). Thus, we have
δ1 ≤
(0.2)2
16 log2 X0−0.5
4π + 0.626
X0 − 0.5 − 6.66 (85)
whenever x ≥ X0 − 0.5 ≥ 200 and 0 ≤ t ≤ 0.2. Computing the right-hand side, we conclude that
δ1 ≤ 3.12 × 10−11
and hence by Taylor expansion
eδ1 − 1 ≤ 1.001δ1
(say). Also, from Theorem 1.3 and (83) we can bound
|γ |FN,t (Re s∗ − y − |κ|) ≤ |γ |N yN |κ|FN,t (Re s∗)
≤ exp
(
0.02y + y
(
log N − 1
2 log x
4π
)
+ ty
2(x − 6) log N
)
FN,t (Re s∗)
≤ exp
(
0.02y +
(
y + ty
2(x − 6)
)1
2 log
(
1 + πt
4x
)
+ ty
4(x − 6) log x
4π
)
FN,t (Re s∗).


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 41 of 67 31
For 0.2 ≤ y ≤ 1, 0 ≤ t ≤ 0.2, and x ≥ X0 − 0.5, we see from Lemma 5.1(vi) that
ty
4(x − 6) log x
4π ≤ 0.2
4(X0 − 0.5 − 6) log X0 − 0.5
4π ≤ 1.86 × 10−11
and (
y + ty
2(x − 6)
)1
2 log
(
1 + πt
4x
) ≤
(
1 + 0.2
2(X0 − 0.5 − 6)
)
×1
2 log
(
1 + 0.2π
4(X0 − 0.5)
)
≤ 1.31 × 10−12
and thus
|γ |FN,t (Re s∗ − y − |κ|) ≤ 1.021FN,t (Re s∗). (86)
Thus,
eA + eB ≤ 1.023δ1FN,t (Re s∗).
To estimate Re s∗, we use Proposition 6.6(ii) or (22), together with the inequality
t 2x2
(
1 − 3y + 8y(1 − y)
x2
)
+
≤ 0.2
2(X0 − 0.5)2
(
1 − 3 × 0.2 + 8
(X0 − 0.5)2
)
+ ≤ 1.2 × 10−23
to obtain
Re s∗ ≥ 0.5999 + t
4 log x
4π
(say). Since FN,t (σ ) is non-increasing in σ , we conclude
eA + eB ≤ 1.023δ1FN,t
(
0.5999 + t
4 log x
4π
) .
Since
N=
⌊√ x
4π + t
16
⌋
,
0 ≤ t ≤ 0.2, and x ≥ X0 − 0.5, it is easy to see that
N≤ x
4π
and hence by (15)
btn
nt
4 log x
4π
≤1
for all 1 ≤ n ≤ N . Therefore,
FN,t
(
0.5999 + t
4 log x
4π
) ≤
N ∑
n=1
1
n0.6001
and hence by the integral test
FN,t
(
0.5999 + t
4 log x
4π
) ≤
∫ N +1
1
ds
s0.5999 = 1
0.4001 (N + 1)0.4001
so that [by (84)]
eA + eB ≤ 1.023
(0.2)2
16 log2 x
4π + 0.626
x − 6.66
1
0.5999 (N + 1)0.5999.


 31 Page 42 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
We have
N + 1 ≤ (1.001)
( x − 6.66 4π
)1/2
(say), and hence
eA + eB ≤ 0.7220 0.0025 log2 x
4π + 0.626 (x − 6.66)0.80005
From Lemma 5.1(vi), the right-hand side is monotone decreasing in the region x ≥ X0 − 0.5, thus
eA + eB ≤ 0.7220 0.0025 log2 X0−0.5
4π + 0.626
(X0 − 0.5 − 6.66)0.80005
≤ 3.444 × 10−9.
Meanwhile, from Proposition 6.6(vi) one has
eC,0 ≤
(x
4π
)− 1+y
4 exp
(
−t
16 log2 x
4π + 3| log x
4π + i π
2 | + 3.58
x − 8.52
)
×
(
1 + 1.24 × (3y + 3−y)
N − 0.125 + 6.92
x − 6.66
) .
From Lemma 5.1(vi), the quantity log2 x
4π + π2
4
(x−8.52)2 is monotone decreasing in x in (5), hence
| log x
4π +i π
2|
x−8.52 is also monotone decreasing. Also, the expression is monotone decreasing in y. We conclude that
eC,0 ≤
( X0 − 0.5 4π
)− 1+0.2
4
exp
( 3| log X0−0.5
4π + i π
2 | + 3.58
X0 − 0.5 − 8.52
)
×
(
1 + 1.24 × (3
√0.6 + 3−√0.6)
N0 − 0.125 + 6.92
X0 − 0.5 − 6.66
)
≤ 1.249 × 10−3
(87)
where we have discarded the negative term − t
16 log2 X0−0.5
4π . Combining the estimates, we obtain the claim.
Now, we attend to the three claims.
8.3 Proof of claim (c)
We begin with claim (c), which is the easiest. By Proposition 8.1, it suffices to establish the bound
|ft (x + iy)| > 1.25 × 10−3.
In fact, we will establish the stronger estimate
ft (x + iy) = 1 + O≤(0.955). (88)
In the region (c), we have from (80) that
x ≥ xN1 ≥ 2.82 × 1013.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 43 of 67 31
Our main tool here is the triangle inequality. From (14), one has
ft (x + iy) = 1 +
N ∑
n=2
btn
ns∗ + γ
N ∑
n=1
ny btn
ns∗+κ
and hence
ft (x + y) = 1 + O≤
( N ∑
n=2
btn
nσ + |γ |
N ∑
n=1
ny btn
nσ −|κ|
)
where σ := Re s∗. Restoring the n = 1 term in the first sum and recalling that t = 0.2, it thus suffices to show that
N ∑
n=1
b0n.2
nσ + |γ |
N ∑
n=1
ny b0n.2
nσ −|κ| < 1.955. (89)
Our main tool here will be
Lemma 8.2 Let N ≥ N0 ≥ 1 be natural numbers, and let σ , t > 0 be such that
σ>t
2 log N.
Then,
N ∑
n=1
btn
nσ ≤
N ∑0
n=1
btn
nσ + max(N 1−σ
0 btN0 , N 1−σ btN ) log N
N0
.
Proof From the identity
btn
nσ = exp ( t
4 (log N − log n)2 − t
4 (log N )2)
nσ − t
2 log N ,
we see that the summands btn
nσ are decreasing for 1 ≤ n ≤ N ; hence, by the integral test one has
N ∑
n=1
btn
nσ ≤
N ∑0
n=1
btn
nσ +
∫N
N0
bta
aσ da. (90)
Making the change of variables a = eu, the right-hand side becomes
N ∑0
n=1
btn nσ
∫N
N0
exp
(
(1 − σ )u + t
4 u2
)
du.
The expression (1 − σ )u + t
4 u2 is convex in u and is thus bounded by the maximum of its values at the endpoints u = log N0, log N ; thus,
exp
(
(1 − σ )u + t
4 u2
)
≤ N 1−σ
0 btN0 , N 1−σ btN .
The claim follows.
Remark 8.3 The right-hand side of (90) can be evaluated exactly as
N ∑0
n=1
btn
nσ +
√√πt exp
( −(σ −1)2 t
)(
erfi
(t
2 log N −σ +1
√t
)
− erfi
(t
2 log N0−σ +1
√t
))


 31 Page 44 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
where erfi(z) = −i erf (iz) is the imaginary error function, with erf (z) := √2π
∫z
0 e−t2 dt.
In practice, this upper bound for ∑N
n=1
btn
nσ is slightly more accurate than the one in Lemma 8.2 and is a good approximation even for relatively small values of N0 (e.g., N0 = 100). However, the cruder bound above suffices for the numerical values of parameters needed to establish the bound Λ ≤ 0.22.
Observe from (22) that
|κ| ≤ 0.2 × 1
2(2.82 × 1013 − 6) ≤ 3.55 × 10−15,
while from (20) one has
|γ | ≤ 1.005
( xN 4π
)−y/2
so in particular since 0.2 ≤ y ≤ 1 and n ≤ 1.0001( xN
4π )1/2 ≤ 1.0002N
|γ |ny ≤ 1.006N −0.2n0.2.
Also, from (21) one has
σ ≥ 0.6 + 0.2
4 log xN
4π − 0.2
2x2N1
(
0.4 + 0.96
x2N1
)
+
≥ 0.6 + 0.1 log N + 0.05 log
(
1− t
16(N1)2
)
− 0.2
2x2N1
(
0.4 + 0.96
x2
1.5×106
)
+
≥ 0.6 + 0.1 log N − 5.1 × 10−29.
We can then apply Lemma 8.2 twice to bound the left-hand side of (89) by A + B, where
A :=
N ∑0
n=1
b0n.2
nσ ′ + 1.006
( xN 4π
)−0.1 N ∑0
n=1
b0n.2
nσ ′′ ,
B := (max(N 1−σ ′
0 b0N.02, N 1−σ ′ b0N.2) + 1.006N −0.2 max(N 1−σ ′′
0 b0N.02, N 1−σ ′′ b0N.2)) log N
N0
σ ′ := 0.6 + 0.1 log N − 5.1 × 10−29
σ ′′ := 0.4 + 0.1 log N − 7.09 × 10−16.
The quantity A is decreasing in N , so we may bound it by its value at N = N1. Performing the sum numerically, we obtain
A ≤ 1.88.
Finally, the quantity B can also be seen to be decreasing6 in N in the range N ≥ N1 and obeys the bound
B ≤ 0.075.
The claim (88) follows.
6This is visually apparent from Fig. 13, but to prove it analytically, it suffices to show that the quantities N −σ′
0 log N
N0 ,
N 1−σ ′ b0N.2 log N
N0 , N −0.2N −σ ′′
0 log N
N0 , N −0.2N 1−σ ′′ b0N.2 log N
N0 are decreasing in N for N ≥ N1. This can in turn be established by computing the log-derivative of all these quantities, multiplied by N ; there will be a negative term − 0.1 log N0 or − 0.1 log N which dominates all the other terms when N ≥ N1. We leave the details to the interested reader.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 45 of 67 31
Fig. 13 Plot of B versus N
8.4 Proof of claim (a)
As N = N0 is constant in this region, the function ft (x +iy) is holomorphic, so by Rouche’s theorem, it suffices to show that for each time 0 ≤ t ≤ 0.2, as x +iy traverses the boundary ∂R of the rectangle
R := {x + iy: X0 − 0.5 ≤ x ≤ X0 + 0.5; 0.2 ≤ y ≤ 1} ,
the function ft (x + iy) stays outside of the ball B := {z: |z| ≤ 1.25 × 10−3} and furthermore has a winding number of zero around the origin. To verify this claim numerically for a given value of t, we subdivide each edge of ∂R into some number n of equally spaced mesh points, thus approximating ∂R by a discrete mesh xj + iyj, j = 1, . . . , 4n, with any two adjacent points on this mesh separated by a distance at most 1/n. Using the techniques in Sect. 7, we evaluate ft (xj + iyj) numerically for each such value of j. The polygonal path connecting these points then winds around the origin with winding number
1 2π
4∑n
j=1
arg(ft (xj+1 + iyj+1)/ft (xj + iyj))
which can be easily computed (and verified to be zero). To pass from this polygonal path to the true trajectory ft (∂R) of ft (x + iy) on ∂R, we again use Rouche’s theorem. If one has a derivative bound | ∂∂z ft (z)| ≤ Dz on the boundary of the rectangle, the polygonal path
and the true trajectory ft (∂R) differ by a distance of at most Dz
2n , and the latter will have the same winding number around the origin (and stay outside of the ball B) as long as
|ft (xj + iyj)| > 1.25 × 10−3 + Dz
2n .
Furthermore, the same is true for nearby times t ≤ t′ ≤ 0.2 to t, as long as one has the stronger bound
|ft (xj + iyj)| > 1.25 × 10−3 + Dz
2n + Dt |t′ − t|
2n (91)
and a bound of the form | ∂∂t ft ̃(z)| ≤ Dt for t ≤ t ̃ ≤ 0.2 and z ∈ ∂R.


 31 Page 46 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
This gives the following algorithm to verify (a) for the entire range 0 ≤ t ≤ 0.2. We start with t = 0 and obtain bounds Dt , Dz for the derivatives of ft ̃(z) in the indicated ranges. Because of the way the barrier location X was selected, we expect |ft (x + iy)| to stay well above 1 in magnitude. We thus choose n so that Dz
2n ≤ 1 and evaluate ft (xj + iyj) at all the mesh points (in particular confirming that |ft (xj + iyj)| does stay well above 1). Using the minimum value of |ft (xj + iyj)|, we can then use the condition (91) to establish the claim for times in the interval [t, t′) where t′ > t is chosen so that (91) holds (or t′ = 0.2, if that is also possible); the most aggressive choice of t′ would be one in which (91) held with equality, but in practice we can afford to take more conservative values of t′ and still obtain good runtime performance. If t′ < 0.2, we then repeat the process, replacing t by t′, until the entire range 0 ≤ t ≤ 0.2 is verified. To run this algorithm, we need bounds on Dt and Dz. This is achieved by the following lemma, which gives bounds which are somewhat complicated but which can be easily upper-bounded numerically on ∂R:
Lemma 8.4 In the region (5), and away from the jump discontinuities of N , we have
∣∣∣∣
∂ ft ∂z
∣∣∣∣ ≤
N ∑
n=1
btn
nRe s∗
( log n
2 + t log n
4(x − 6)
)
+ |γ |N |κ|
N ∑
n=1
btnny
nRe s∗
( t log n
4(x − 6) +
(
log |1 + y + ix|
4π + π + 3
x
)
×
(1
2+ t
4(x − 6)
))
and
∣∣∣∣
∂ ft ∂t
∣∣∣∣ ≤
N ∑
n=1
btn
nRe s∗
(1
4 log n log x
4πn + π
8 log n + 2 log n
x−6
)
+ |γ |N |κ|
N ∑
n=1
btnny
nRe s∗
(1
4 log n log x
4πn + π
8 log n + 2 log n
x−6
+1
4
(π
2+ 8
x−6
)(
log x
4π + 8
x−6
)) .
Proof We begin with the first estimate. Write
s∗∗ := s∗ − y + κ = 1 − y + ix
2 +t
2α
( 1 − y + ix 2
)
then
ft =
N ∑
n=1
btn
ns∗ + γ
N ∑
n=1
btn
ns∗∗ . (92)
One can check that s∗, s∗∗, γ are holomorphic functions of x + iy; hence, by the CauchyRiemann equations
∣∣∣∣
∂ ft ∂x
∣∣∣∣ =
∣∣∣∣
∂ ft ∂y
∣∣∣∣ .


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 47 of 67 31
By the product and chain rules, we may calculate
∂ ft
∂x = −
N ∑
n=1
btn
ns∗
∂ s∗
∂x log n + γ
N ∑
n=1
btn
ns∗∗
(∂
∂x log γ − ∂s∗∗
∂x log n
) .
From (17) and (43), we have
∂ s∗
∂x = − i
2 − it
4 α′
( 1 + y − ix 2
)
=−i
2 + O≤
(t
4(x − 6)
) .
Similarly, we have
∂ s∗∗
∂x = i
2 + O≤
(t
4(x − 6)
) .
Writing s = 1−y+ix
2 , we have from (16) and (10) that
log γ = t
4 (α(s)2 − α(1 − s)2) + log M0(s) − log M0(1 − s)
and hence by (8)
∂
∂x log γ = it
4 (α(s)α′(s) + α(1 − s)α′(1 − s)) + i
2 α(s) + i
2 α(1 − s).
From the triangle inequality and (43), we thus have
| ∂ft
∂x | ≤
N ∑
n=1
btn
nRe s∗
( log n
2 + t log n
4(x − 6)
)
+ |γ |
N ∑
n=1
btn
nRe s∗∗
( t log n
4(x − 6) + |α(s)| + |α(1 − s)| − log n
2
+ t(|α(s)| + |α(1 − s)|)
4(x − 6)
) .
We have from (9) that
|α(s)|, |α(s) − 1
2 log n| ≤ 1
2 log |1 − y + ix|
4π + π
2+ 3
2x
since n ≤ N ≤ x
4π ≤ |1−y+ix|
4π . Similarly,
|α(1 − s)|, |α(1 − s) − 1
2 log n| ≤ 1
2 log |1 + y + ix|
4π + π
2+ 3
2x
and thus
|α(s) + α(1 − s)|, |α(s) + α(1 − s) − log n| ≤ log |1 + y + ix|
4π + π + 3
x.
Writing Re s∗∗ = Re s∗ − y + Re κ, we then have the first estimate. Now, we estimate the time derivative. Since
∂
∂t log btn = 1
4 log2 n
∂
∂t s∗ = 1
2 α(1 − s)


 31 Page 48 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
∂
∂t s∗∗ = 1
2 α(s)
∂
∂t log γ = 1
4
(α(s)2 − α2(1 − s))
we see from differentiating (92) that we obtain
∂ ft
∂t =
N ∑
n=1
btn
ns∗
(
log2 n
4 − α(1 − s)
2 log n
)
+γ
N ∑
n=1
btn
ns∗∗
(
log2 n
4 − α(s)
2 log n + 1
4 (α(s)2 − α2(1 − s))
)
.
From (43) and (9), we have
α
( 1 ± y + ix 2
)
=α
( ix 2
)
+ O≤
(1
x−6
)
=1
2 log x
4π + πi
4 + O≤
(4
x−6
)
and hence (since α = α∗)
α
( 1 ± y − ix 2
)
=1
2 log x
4π − πi
4 + O≤
(4
x−6
)
so in particular (recalling that 1 − s = 1+y−ix
2 and s = 1−y+ix
2)
α(s) − α(1 − s) = πi
2 + O≤
(8
x−6
)
and
α(s) + α(1 − s) = log x
4π + O≤
(8
x−6
)
so that
∣∣α(s)2 − α(1 − s)2∣∣ ≤
(π
2+ 8
x−6
)(
log x
4π + 8
x−6
) .
We conclude from the triangle inequality that
∣∣∣∣
∂ ft ∂t
∣∣∣∣ ≤
N ∑
n=1
btn
nRe s∗
(1
4 log n log x
4πn + π
8 log n + 2 log n
x−6
)
+ |γ |
N ∑
n=1
btn
nRe s∗∗
(1
4 log n log x
4πn + π
8 log n + 2 log n
x−6
+1
4
(π
2+ 8
x−6
)(
log x
4π + 8
x−6
))
giving the second claim.
The next few graphs summarize the numerical output of the algorithm for the following barrier parameters: x = 6 × 1010 + 83,952 ± 0.5, y = 0.2 . . . 1, t = 0 . . . 0.2. The first step in the barrier verification process was to precalculate a “stored sum” of Taylor expansion terms that allows for fast recreation of ft (x + iy) during the execution of


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 49 of 67 31
Fig. 14 Derivative bounds versus their actual values at all required steps of t
Fig. 15 The number of mesh points required per rectangle for each step of t
the algorithm as per Sect. 7. The number of Taylor terms required was determined through an iterative process targeted to achieve a 20 decimal accuracy. Figure 12 illustrates the achieved accuracy for all rectangular mesh points at t = 0. The derivative bounds determine the number of mesh points required on each xyrectangle and in the t-direction. Figure 14 illustrates that these bounds have been chosen quite conservatively: The number of rectangle mesh points varies with t ranging from 11076 at t = 0 to 56 at t = 0.195; see Fig. 15. The overall winding number for the barrier at this specific location came out at 0. Figures 16 and 17 show the winding process at t = 0, 0.2, respectively. Due to the choice of the barrier location and the small barrier width compared to the wavelength in the x variable, little oscillation is expected to occur in each rectangle. The code for implementing these computations may be found in the directory
dbn_upper_bound/arb
in the GitHub repository [16].


 31 Page 50 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Fig. 16 Winding the rectangle at t = 0
Fig. 17 Winding the rectangle at t = 0.2
8.5 Proof of claim (b)
Fix t = 0.2, and let R denote the rectangle
R := {x + iy: 0.2 ≤ y ≤ 1; x ≥ X0 − 0.5; N ≤ N1
}.
We wish to show that the holomorphic function Ht (x+iy)/Bt (x+iy) does not vanish in this rectangle. We would like to establish this by the argument principle; however, this turns out to be difficult to accomplish due to the oscillation in Ht (x + iy)/Bt (x + iy) ≈ ft (x + iy) indicated by the heuristic (79). To damp out this oscillation, we introduce an7 “Euler mollifier”
Et,5(x + iy) := ∏
p≤5
(
1 − btp
ps∗
)
,
7In the literature, one also sees other choices of mollifier than this Euler product used, for instance to control the extreme values of Dirichlet polynomials; however, our numerical experimentations with alternative mollifiers to ft (x +iy) turned out to give inferior results for our application.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 51 of 67 31
where s∗ is given by (17); the choice to use the first three primes 2, 3, 5 was obtained after significant trial and error as giving the best numerical results in this range of t, x, y. We have the upper bound
|Et,5(x + iy)| ≤ ∏
p≤5
(
1 + btp
pRe s∗
)
.
When N ≥ N0, 0.2 ≤ y ≤ 1 and t = 0.2, one easily verifies from (21) that
Re s∗ ≥ 1.7143
and hence
|Et,5(x + iy)| ≤ 1.635
In particular, by Proposition 8.1 we have
Et,5(x + iy) Ht (x + iy)
Bt (x + iy) = Et,5(x + iy)ft (x + iy) + O≤(2.05 × 10−3).
The left-hand side remains holomorphic in x + iy (even though ft (x + iy) has jump discontinuities). Thus, by the argument principle, it will suffice to show that the left-hand side avoids the negative real axis (− ∞, 0] as x + iy traverses the boundary ∂R of the rectangle R. In other words, it will suffice to show that
dist(Et,5(x + iy)ft (x + iy), (− ∞, 0]) > 2.05 × 10−3 (93)
for x +iy ∈ ∂R. For future reference, we also observe that for any x +iy ∈ R, the magnitude of Et,5(x + iy) can be bounded below by
|Et,5(x + iy)| ≥ ∏
p≤5
(
1 − btp
pRe s∗
)
≥ 0.534 (94)
and the argument has magnitude at most
|arg(Et,5(x + iy))| ≤ ∑
p≤5
sin−1 btp
pRe s∗ ≤ 0.553. (95)
Of the four sides of the rectangle ∂R, the required estimate (93) will hold with significant room to spare, and we can proceed using rather crude estimates. We first attend to the right edge of ∂R, in which N = N1. From (88), we have
ft (x + iy) = 1 + O≤(0.955)
in this region. In particular, ft (x + iy) has argument of magnitude at most sin−1 0.955 ≤ 1.27. Combining this with (94), (95), we conclude that Et,5(x + iy)ft (x + iy) has magnitude at least 0.024 and argument at most 1.823 in magnitude, giving the claim (93) on this side from elementary trigonometry. Now, we attend to the left edge of ∂R, in which x = X0 − 0.5 and 0.2 ≤ y ≤ 1. From the calculations for part (a) (see in particular Fig. 17), one can verify that (for instance) |ft (x + iy)| ≥ 1 and |argft (x + iy)| ≤ π
2 in this region. Combining this with (94) and (95), we conclude that Et,5(x + iy)ft (x + iy) has magnitude at least 0.534 and argument at most 2.13 in magnitude, again giving the claim (93) on this side from elementary trigonometry.


 31 Page 52 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Now, we attend to the upper edge of ∂R, in which N0 ≤ N ≤ N1 and y = 1. From (21), one now has
Re s∗ ≥ 2.1143.
In particular,8
N ∑
n=1
btn
ns∗ = 1 + O≤
( N ∑1
n=2
btn
n2.1143
)
= 1 + O≤(0.7).
Meanwhile, from (20) one has
|γ | ≤ e0.02 ( x
4π
)−1/2 ≤ 1.03N −1
and from (22) one has
|κ| ≤ ty
2(x − 6) ≤ 4 × 10−13
and hence
|γ | ny
ns∗+κ = O≤
( 1.03
Nn1.1142
)
and
γ
N ∑
n=1
ny btn
ns∗+κ = O≤
⎛
⎝
N ∑0
n=1
1.03btn
N0n1.1142 +
N ∑1
n=N0 +1
1.03btn
n2.1142
⎞
⎠ = O≤(0.1)
and hence
ft (x + iy) = 1 + O≤(0.8).
In particular, ft (x+iy) has magnitude at least 0.2 and argument at most 0.928 in magnitude; hence, Et (x + iy)ft (x + iy) has magnitude at least 0.1068 and argument at most 1.481, at which point the claim follows from elementary trigonometry. It remains to attend to the lower edge of ∂R, in which N0 ≤ N ≤ N1 and y = 0.2. This is by far the most delicate side of the rectangle for the purposes of verifying (93). We will split the range [N0, N1] into a number of subintervals [N−, N+] and obtain a uniform lower bound for dist(Et,5(x + iy)ft (x + iy), (− ∞, 0]) when N is in one of these subintervals [N−, N+].
Fix [N−, N+] ⊂ [N0, N1], suppose that N ∈ [N−, N+] and write s∗ = σ + iT . We first deal with the κ term in the definition of ft (x + iy) by writing
n−κ = 1 + O≤(n|κ| − 1)
and hence
ft (x + iy) =
N ∑
n=1
btn
nσ +iT + γ
N ∑
n=1
ny btn
nσ −iT + O≤
(
|γ |
N ∑
n=1
ny btn
nσ (n|κ| − 1)
)
. (96)
In particular, using (20) to bound
8The sum ∑N1
n=2
btn
n2.1143 can be numerically computed directly, but one could also use Lemma 8.2 (using for instance
N0 = 69,098) to obtain a usable upper bound as well. Similarly, for the other sums of this type that appear in this argument.


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 53 of 67 31
|γ |ny ≤ e0.02y(xN /4π n2)−y/2
≤ e0.02
((
N2 − 1
80
)
/n2
)−y/2
≤ 1.03(N 2/n2)−0.1
≤ 1.03(n/N−)−0.2,
we have
Et,5(x + iy)ft (x + iy) = Et,5(x + iy)
N ∑
n=1
btn
nσ +iT
+ O≤
(
1.03|Et,5(x + iy)|
∣∣∣∣∣
N ∑
n=1
(n/N−)0.2 btn
nσ −iT
∣∣∣∣∣
)
+ O≤(Z),
where
Z := 1.644
N ∑
n=1
(n/N )0.2 btn
nσ (n|κ| − 1).
We can write
Et,5(x + iy) = ∑
d|D
λd dσ +iT
where D := 2 × 3 × 5 and
λd := ∏
p|d
(−btp).
As a consequence, we have
Et,5(x + iy)
N ∑
n=1
btn
nσ +iT =
D∑N
n=1
βn
nσ +iT ,
where
βn := ∑
d|n,D
λd bt
n/d .
Thus, for instance β1 = 1 and βp = 0 for p = 2, 3, 5, so that the Dirichlet series ∑DN
n=1
βn
nσ +iT
is expected to experience less oscillation than the series ∑N
n=1
btn
nσ +iT .
The product of Et,5(x + iy) and ∑N
n=1(n/N−)0.2 btn
nσ−iT is not favorable due to the negative sign in the σ − iT exponent. But since |z||w| = |zw|, we have
1.03|Et,5(x + iy)|
∣∣∣∣∣
N ∑
n=1
(n/N−)0.2 btn
nσ −iT
∣∣∣∣∣ = 1.03
∣∣∣∣∣Et,5(x + iy)
N ∑
n=1
(n/N−)0.2 btn
nσ +iT
∣∣∣∣∣
=
∣∣∣∣∣
D∑N
n=1
N −0.2
− αn nσ +iT
∣∣∣∣∣ ,
where
αn := 1.03
∑
d|n,D
λd (n/d )0.2 bt
n/d .


 31 Page 54 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Note that the coefficients αn, βn are both real. We now have
Et,5(x + iy)ft (x + iy) =
D∑N
n=1
βn
nσ +iT + O≤
(∣∣∣∣∣
D∑N
n=1
N −0.2
− αn nσ +iT
∣∣∣∣∣
)
+ O≤(Z). (97)
A naive application of the triangle inequality (using β1 = 1) would give the lower bound
dist(Et,5(x + iy)ft (x + iy), (−∞, 0]) ≥ 1 − N −0.2
− α1 −
D∑N
n=2
|βn| + |N −0.2
− αn|
nσ − Z.
(98)
As it turns out, this bound is not quite strong enough to be satisfactory for the numerical ranges of parameters we need. To do better, we need to exploit the fact that when the
sum ∑DN
n=1
βn
nσ+iT exhibits a significant cancellation, the sum ∑DN
n=1
N −0.2αn
nσ+iT will also. The key tool here is
Lemma 8.5 (Improved triangle inequality) We have
dist(Et,5(x + iy)ft (x + iy), (− ∞, 0]) ≥ 1 − N −0.2
− α1
−
D∑N
n=2
max
(
|βn − N −0.2
− αn|, 1−N−−0.2α1
1+N−−0.2α1 |βn + N −0.2
− αn|
)
nσ − Z.
Proof Write
Y :=
D∑N
n=2
max
(
|βn − N −0.2
− αn|, 1−N−−0.2α1
1+N−−0.2α1 |βn + N −0.2
− αn|
)
nσ .
We may assume that N −0.2
− α1 +Y < 1, otherwise the claim is trivial. By (97) and convexity, it suffices to show that
dist
( D∑N
n=1
βn + eiθ N −0.2
− αn
nσ +iT , (−∞, 0]
)
≥ 1 − N −0.2
− α1 − Y
for all phases θ ∈ R. We may write
D∑N
n=1
βn + eiθ N−−0.2αn
nσ +iT = 1 + eiθ N−−0.2α1 + O≤
( D∑N
n=2
|βn + eiθ N−−0.2αn| nσ
)
=
(
1 + eiθ N−−0.2α1
)(
1 + O≤
( D∑N
n=2
|βn + eiθ N−−0.2αn|/|1 + eiθ N−−0.2α1| nσ
))
.
By the cosine rule, we have
(
|βn + eiθ N −0.2
− αn|/|1 + eiθ N −0.2
− α1|
)2 = βn2 + N −0.4
− αn2 + 2N −0.2
− αnβn cos θ
1 + N −0.4
− α12 + 2N −0.2
− α1 cos θ .
This is a fractional linear function of cos θ with no poles in the range [− 1, 1] of cos θ. Thus, this function is monotone on this range and attains its maximum at either cos θ = +1 or cos θ = −1. We conclude that
|βn + eiθ N −0.2
− αn| |1 + eiθ N −0.2
− α1| ≤ max
( |βn − N −0.2
− αn|
1 − N −0.2
− α1
, |βn + N −0.2
− αn|
1 + N −0.2
− α1
)


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 55 of 67 31
and thus
D∑N
n=2
|βn + eiθ N −0.2
− αn|/|1 + eiθ N −0.2
− α1|
nσ ≤ 1
1 − N −0.2
− α1
Y.
We conclude from the triangle inequality that
D∑N
n=1
βn + eiθ N −0.2
− αn
nσ +iT = 1 + eiθ N −0.2
− α1 + O≤
( |1 + eiθ N −0.2
− α1|
1 − N −0.2
− α1
Y
)
.
By further application of the triangle inequality
dist
( D∑N
n=1
βn + eiθ N −0.2
− αn
nσ +iT , (−∞, 0]
)
≥ dist
(
1 + eiθ N −0.2
− α1, (−∞, 0]
)
− |1 + eiθ N −0.2
− α1|
1 − N −0.2
− α1
Y
= |1 + eiθ N −0.2
− α1| − |1 + eiθ N −0.2
− α1|
1 − N −0.2
− α1
Y
= |1 + eiθ N −0.2
− α1|
(
1− Y
1 − N −0.2
− α1
)
≥ (1 − N −0.2
− α1)
(
1− Y
1 − N −0.2
− α1
)
= 1 − N −0.2
− α1 − Y
as desired, where we have used the fact that 1+eiθ N −0.2
− α1 lies to the right of the imaginary axis (so that the closest element of (− ∞, 0] is the origin).
Bounding DN ≤ DN+, we see that in order to establish (93) in the range N ∈ [N−, N+], it suffices to verify the inequality
1 − N −0.2
− α1 −
D∑N+
n=2
max(|βn − N −0.2
− αn|, 1−N−−0.2α1
1+N−−0.2α1 |βn + N −0.2αn|)
nσ
−Z ≥ 2.14 × 10−3.
From (21) and (80), one has
σ ≥ 1+y
2 +t
4 log xN
4π − t
2x2N
(
1 − 3y + 4y(1 + y)
x2N
)
+
= 0.6 + 1
20 log xN
4π − 1
10x2N
(
0.4 + 0.96
x2N
)
= 0.6 + 1
20 log
(
N2 − 1
80
)
−1
10x2N0
(
0.4 + 0.96
x2N0
)
≥ σN− ,
where
σN− := 0.599 + 1
10 log N−


 31 Page 56 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
while from (22) and (80) one has
|κ| ≤ ty
2(xN − 6) ≤ 0.02
xN0 − 6 ≤ 4 × 10−13
and hence it suffices to show that
FN−,N+ − ZN−,N ≥ 2.14 × 10−3,
where
FN−,N+ := 1 − N −0.2
− α1 −
D∑N+
n=2
max
(
|βn − N −0.2
− αn|, 1−N−−0.2α1
1+N−−0.2α1 |βn + N −0.2
− αn|
)
nσN−
and
ZN−,N := 1.644
N ∑
n=1
(n/N )0.2 btn
nσN− (n4×10−13 − 1).
Since σN− ≥ 1.714, we may crudely bound
ZN−,N ≤ 1.644
N ∑1
n=1
btn
n1.714 (n4×10−13 − 1) ≤ 10−10
so it will suffice to show that
FN−,N+ ≥ 2.15 × 10−3
for a collection of intervals [N−, N+] covering [N0, N1]. This can be done by ad hoc numerical experimentation; for instance, one can calculate that
F69098,8×104 = 0.0263 . . .
F8×104,1.1×105 = .0470 . . .
F1.1×105,2.2×105 = 0.093 . . .
F2.2×105,1.5×106 = 0.060 . . . .
9 Asymptotic results
In this section, we use the effective estimates from Theorem 1.3 to obtain asymptotic information about the function Ht , which improves (and makes more effective) the results of Ki et al. [10], by establishing Theorem 1.5. We begin with
Proposition 9.1 (Preliminary asymptotics) Let 0 < t ≤ 1/2, x ≥ 200, and −10 ≤ y ≤ 10.
(i) If x ≥ exp( C
t ) for a sufficiently large absolute constant C, then
Ht (x + iy) = (1 + O(x−ct ))Mt
( 1 + y − ix 2
)
+ (1 + O(x−ct ))Mt
( 1 − y + ix 2
)
for an absolute constant c > 0, where Mt is defined in (10). (ii) If instead we have 3 ≤ y ≤ 4 and x ≥ C for a sufficiently large absolute constant C, then
Ht (x + iy) = (1 + O≤(0.7))Mt
( 1 + y − ix 2
) .


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 57 of 67 31
(iii) If x = x0 + O(1) for some x0 ≥ 200, then
Ht (x + iy) = O
(
xO(1)
0
∣∣∣∣Mt
( 1 + y − ix 2
)∣∣∣∣
)
=O
(
xO(1)
0
∣∣∣∣Mt
( ix0 2
)∣∣∣∣
) .
Proof We begin with (i). Since Ht = Ht∗ and Mt = Mt∗, we may assume without loss of generality that y ≥ 0. Using (16) and (11), we may write the desired estimate as
Ht (x + iy)
Bt (x + iy) = 1 + O(x−ct ) + γ .
We apply Theorem 1.3. (Strictly speaking, the estimates there required y ≤ 1 rather than y ≤ 10; however, as remarked at the beginning of Sect. 6, all the estimates in that section would continue to hold under this weaker hypothesis if one adjusted all the numerical constants appropriately.) This gives
Ht (x + iy)
Bt (x + iy) =
N ∑
n=1
btn
ns∗ + γ
N ∑
n=1
ny btn
ns∗+κ + O≤ (eA + eB + eC,0) , (99)
where
γ = O(x−y/2)
κ = O(x−1)
Re s∗ ≥ 1 + y
2 +t
2 log x
4π − O(x−2)
eA = O
(
x−y/2
N ∑
n=1
btnn− 1−y
2 −t
2 log x
4π −O(x−1) log2 x
x
)
eB = O
( N ∑
n=1
btnn− 1+y
2 −t
2 log x
4π +O(x−1) log2 x
x
)
eC,0 = O
(
x− 1+y
4
) .
Since N = O(x1/2), we have x−y/2ny = O(1) and nO(x−1) = O(1) for all 1 ≤ n ≤ N . We conclude that
Ht (x + iy)
Bt (x + iy) = 1 + γ + O
(
log2 x
x+
N ∑
n=2
btn
n 1+y
2 +t
2 log x
4π
+ x− 1+y
4
)
so it will suffice (for c small enough) to show that
N ∑
n=2
btn
n 1+y
2 +t
2 log x
4π
= O(x−ct ).
By (15), we can write the left-hand side as
N ∑
n=2
1
n
1+y
2 +t
2 log x
4π √n
= O(x−ct ).
For 2 ≤ n ≤ N , we have
1+y
2 +t
2 log x
4π√n ≥ ct log x


 31 Page 58 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
for some absolute constant c > 0. By the integral test, the left-hand side is then bounded by
1
2ct log x +
∫∞
2
1
uct log x du
which, for x ≥ exp(C/t) and C large, is bounded by O(2−ct log x). The claim then follows after adjusting c appropriately. Now, we prove (ii). As before, we have the expansion (99). We have
γ
N ∑
n=1
ny btn
ns∗+κ = O
(
x−y/2
N ∑
n=1
btn
n 1−y
2 +t
2 log x
4π
)
=O
(
x−y/2
N ∑
n=1
n y−1
2
)
=O
(
x− y−1
4
) ;
similar arguments give eA = O( log2 x
x x 1−y
4 ), while
eB = O
(
log2 x x
N ∑
n=1
btnn− 1+y
2 −t
2 log x
4π
)
=O
(
log2 x x
N ∑
n=1
n−2
)
=O
(
log2 x x
)
.
We conclude that
Ht (x + yi)
Bt (x + yi) =
N ∑
n=1
btn
ns∗ + O
(
x− y−1
4
)
= 1 + O≤
( N ∑
n=2
n− 1+y
2 −t
2 log x
4π −O(x−1)
)
+ O(x− y−1
4)
= 1 + O≤
( N ∑
n=2
n−2
)
+ O(x−1/2)
= 1 + O≤
(π2
6 −1
)
+ O(x−1/2)
= 1 + O≤(0.7)
as claimed, if x ≥ C for C large enough. Finally, we prove (iii). Again our starting point is (99). The right-hand side can be bounded crudely by O(xO(1)) = O(xO(1)
0 ); hence,
Ht (x + iy) = O
(
xO(1)
0
∣∣∣∣Mt
( 1 + y + ix 2
)∣∣∣∣
) .


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 59 of 67 31
However, from (10), (6), (9) it is not hard to see that the log-derivative of Mt (s) is of size O(log x0) in the region s = ix0
2 + O(1). Thus,
∣∣∣∣Mt
( 1 + y + ix 2
)∣∣∣∣ = O
(
xO(1)
0
∣∣∣∣Mt
( ix0 2
)∣∣∣∣
) ,
giving the claim.
To understand the behavior of Mt (x + iy), we make the following simple observations:
Lemma 9.2 (Behavior of Mt ) Let 0 < t ≤ 1/2, let x∗ > 0 be sufficiently large, and let x + iy = x∗ + O(1). Then,
Mt
( 1+y+ix 2
)
= Mt
( 1+ix∗ 2
)
exp
(
(i(x−x∗)+y)
(1
4 log x∗
4π + πi
8
)
+O
( log x∗
x∗
)) .
Also, there is a continuous branch of argMt
( 1+ix∗ 2
)
for all large real x∗ such that
argMt
( 1 + ix∗ 2
)
= tπ
16 log x∗
4π + 7π
8 + x∗
4 log x∗
4π − x∗
4 +O
( log x∗
x∗
) .
Proof By (10) and (8), the log-derivative of Mt is given by
Mt′
Mt
=α+ t
2 αα′. (100)
For s = ix∗
2 + O(1), we have from (9) that
α(s) = 1
2 log x∗
4π + πi
4 +O
(1
x∗
)
(101)
and from this and (43) we conclude that
Mt′ (s)
Mt (s) = 1
2 log x∗
4π + πi
4 +O
( log x∗
x∗
)
whenever s = ix∗
2 +O(1). The first claim then follows by applying the fundamental theorem of calculus to a branch of log Mt . For the second claim, we calculate
argMt
( 1 + ix∗ 2
)
=t
4 Im
(
α
( 1 + ix∗ 2
)2)
+ π − x∗
4 log π
+ Im
( −1 + ix∗
4 log 1 + ix∗
4 − 1 + ix∗
4
)
=t
4
(π
4 log x∗
4π + O
( log x∗
x∗
))
+ π − x∗
4 log π
+ Im
( −1 + ix∗ 4
(
log x∗
4 + iπ
2−i
x∗
+O
(1
x∗2
)))
− x∗
4 = tπ
16 log x∗
4π +π − x∗
4 log π − x∗
4 + x∗
4 log x∗
4 −π
8 +O
( log x∗
x∗
)
= tπ
16 log x∗
4π + 7π
8 + x∗
4 log x∗
4π − x∗
4 +O
( log x∗
x∗
)
as desired.


 31 Page 60 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Now, we can prove Theorem 1.5. We begin with (ii). Let n ≥ exp( C
t ), and suppose that x + iy = xn + O(1). By Proposition 9.1(i) and Lemma 9.2, we have
Ht (x + iy) = Mt
( 1 + ixn 2
)
exp
(
(−i(x − xn) + y)
(1
4 log xn
4π − πi
8
)
+ O(xn−ct )
)
+ Mt
( 1 + ixn 2
)
exp
(
(i(x − xn) − y)
(1
4 log xn
4π + πi
8
)
+ O(xn−ct )
) .
(102)
From Lemma 9.2 and (26), one has
argMt
( 1 + ixn 2
)
= −π
2 +O
( log xn
xn
)
mod π
and hence
Mt
( 1 + ixn 2
)
= − exp
( O
( log xn
xn
))
Mt
( 1 + ixn 2
)
. (103)
If we now make the further assumption y = O
(1 log xn
)
, we can thus simplify the above approximation as
Ht (x + iy) = −Mt
( 1 + ixn 2
)
e−π (x−xn )/8
× exp
(
(−i(x − xn) + y) 1
4 log xn
4π + O(|y| log xn + xn−ct )
)
+ Mt
( 1 + ixn 2
)
e−π (x−xn )/8
× exp
(
(i(x − xn) − y) 1
4 log xn
4π + O(|y| log xn + xn−ct )
)
= 2iMt
( 1 + ixn 2
)
e−π (x−xn )/8
×
(
sin
( x + iy − xn
4 log xn
4π
)
+ O(|y| log xn + xn−ct )
) .
(104)
In particular, if x + iy traverses the circle {xn + c
log n eiθ : 0 ≤ θ ≤ 2π } once anticlockwise and c is small enough, the quantity Ht (x + iy) will wind exactly once around the origin, and hence by the argument principle there is precisely one zero of Ht inside this circle. As the zeroes of Ht are symmetric around the real axis, this zero must be real. This proves (ii). Now, we prove (i). Suppose that Ht (x + iy) = 0 and x ≥ exp( C
t ). We can assume |y| ≤ 1 since it is known (e.g., from [9, Theorem 13]) that there are no zeroes with |y| > 1. Let n be a natural number that minimizes |x − xn|, then x = xn + O
(1 log xn
)
since the derivative of the left-hand side of (26) in xn is comparable to log xn. From (102), we have
0 = Mt
( 1 + ixn 2
)
exp
(
(−i(x − xn) + y)
(1
4 log xn
4π − πi
8
)
+ O(xn−ct )
)
+ Mt
( 1 + ixn 2
)
exp
(
(i(x − xn) − y)
(1
4 log xn
4π + πi
8
)
+ O(xn−ct )
) .


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 61 of 67 31
Thus, both summands on the right-hand side have the same magnitude, which on taking logarithms and canceling like terms implies that
y1
4 log xn
4π + O(xn−ct ) = −y 1
4 log xn
4π + O(xn−ct )
and hence y = O
( xn−ct log xn
)
. We can now apply (104) to conclude that
sin
( x + iy − xn
4 log xn
4π
)
+ O(xn−ct ) = 0
which (when combined with the hypothesis that |x − xn| is minimal) forces x − xn = O
( xn−ct log xn
)
. This gives the claim. Next, we prove (iii). In view of parts (i) and (ii), and adjusting C if necessary, we may assume that X takes the form X = xn + c
log xn for some n ≥ exp( C
t ). By the argument
principle, Nt (X) is equal to −1
2π times the variation in the argument of Ht on the boundary of the rectangle {x + iy: 0 ≤ x ≤ X; −3 ≤ y ≤ 3} traversed clockwise, since there are no zeroes with imaginary part of magnitude greater than one. By compactness, the variation on the left edge {iy: − 3 ≤ y ≤ 3} is O(1), and similarly for any fixed portion {x + 3i: 0 ≤ x ≤ C} of the upper edge. From Proposition 9.1 [and (102)], we see that the variation of Ht (x + iy)/Mt ( 1+y−ix
2 ) on the remaining upper edge {x + 3i: C ≤ x ≤ X} and that on the top half {X + iy: 0 ≤ y ≤ 3} of the right edge are both equal to O(1). Since Ht = Ht∗, the variation on the lower half of the rectangle is equal to that of the upper half. We thus conclude that
Nt (X) = − 1
π argMt
( 1 − iX 2
)
+ O(1),
where we use a continuous branch of the argument of Mt
( 1−iX 2
)
that is bounded at 3i.
The claim now follows from Lemma 9.2 (using Mt = Mt∗ to work with 1+iX
2 instead of
1−iX
2 ). Finally, we prove (iv). From the Hadamard factorization theorem as in the proof of Proposition 3.1, we have
Ht′(z)
Ht (z) = ∑
n>0
(1
z − zn
+1
z + zn
)
(105)
where the zeroes of Ht are indexed in pairs ±zn. Setting z = X + 4i, we see from Proposition 9.1 and the generalized Cauchy integral formula that the logarithmic derivative of Ht (x+iy)/Mt
( 1+y−ix 2
)
is equal to O(1) at X +4i for all sufficiently large X, and hence for all X by symmetry and compactness. On the other hand, from Stirling’s formula (or the logarithmic growth of the digamma function) one easily verifies that the logarithmic derivative of Mt
( 1+y−ix 2
)
is equal to O(log(2+X)) at X +4i. Hence, Ht′(X+4i)
Ht(X+4i) = O(log(2+X)). Taking
imaginary parts, we conclude that ∑
n>0
− 4 − yn
(X − xn)2 + (4 − yn)2 − 4 + yn
(X + xn)2 + (4 + yn)2 = O(log(2 + X))
where we write zn = xn + iyn; equivalently, one has ∑
n
(4 − yn)
(X − xn)2 + (4 − yn)2 = O(log(2 + X)),
where the sum now ranges over all zeroes, including any at the origin. Since |yn| ≤ 1, every zero in [X, X + 1] makes a contribution of at least 1
100 (say). As the summands are


 31 Page 62 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
all positive, the first part of claim (iv) follows. To prove the second part, we may assume by compactness that x ≥ C. Repeating the proof of (iii), we reduce to showing that the variation of argHt on the short vertical interval {X + iy : 0 ≤ y ≤ 3} is O(log X). If we let θ be a phase such that eiθ Ht (X + 3i) is real and positive, we see that this variation is at most π (m + 1), where m is the number of zeroes of Re (eiθ Ht (X + yi)) for 0 ≤ y ≤ 3, since every increment of π in argeiθ Ht must be accompanied by at least one such zero. As Ht = Ht∗, this is also the number of zeroes of eiθ Ht (X + yi) + e−iθ Ht (2X − (X + yi)). On the other hand, from Proposition 9.1(ii), (iii) and Jensen’s formula we see that the number of such zeroes is O(log X), and the claim follows.
Remark 9.3 Theorem 1.5 gives good control on Ht (x + iy) whenever x ≥ exp(C/t). As a consequence (and assuming for the sake of argument that the Riemann hypothesis holds), then for any Λ0 > 0, the bound Λ ≤ Λ0 should be numerically verifiable in time O(exp(O(1/Λ0))), by applying the arguments of previous sections with t and y set equal to small multiples of Λ0. We leave the details to the interested reader.
Remark 9.4 Our discussion here will be informal. In view of the results of [8], it is expected that the zeroes zj(t) of Ht (x + iy) should evolve according to the system of ordinary differential equations:
d
dt zk (t) = 2
′ ∑
j=k
1
zk (t) − zj(t) ,
where the sum is evaluated in a suitable principal value sense, and one avoids those times where the zero zk (t) fails to be simple; see [8, Lemma 2.4] for a verification of this in the regime t > Λ. In view of the Riemann–von Mangoldt formula (as well as variants such Corollary 1.5, it is expected that the number of zeroes in any region of the form {x + iy: x + iy = x∗ + O(1)} for large x∗ should be of the order of log x∗. As a consequence, we expect a typical zero zk (t) to move with speed O(log |zk (t)|), although one may occasionally move much faster than this if two zeroes are exceptionally close together, or less than this if the zeroes are close to being evenly spaced. As a consequence, if the Riemann hypothesis fails and there is a zero x + iy of H0 with y comparable to 1, it should take time comparable to 1
log x for this zero to move toward the real axis, leading to
the heuristic lower bound Λ 1
log x . Thus, in order to obtain an upper bound Λ ≤ Λ0, it will probably be necessary to verify that there are no zeroes x + iy of H0 with y comparable to 1 and |x| ≤ c log 1
Λ for some small absolute constant c > 0. This suggests that the time complexity bound in Remark 9.3 is likely to be best possible (unless one is able to prove the Riemann hypothesis, of course). In [8, Lemma 2.1], it is also shown that the velocity of a given zero z(t) is given by the formula
d
dt z(t) = Ht′′(z(t))
Ht′(z(t)) ,
assuming that the zero is simple. By using the asymptotics in Proposition 9.1 and Corollary 1.5 together with the generalized Cauchy integral formula to then obtain asymptotics for Ht′ and Ht′′, it is possible to show that for the zeroes x(t) that are real and larger than exp(C/t), and move leftward with velocity


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 63 of 67 31
d
dt x(t) = − π
4 + O(x−ct );
we leave the details to the interested reader.
10 Further numerical results
By Theorem 1.5, one can verify the second hypothesis of Theorem 1.2 when X ≥ exp(C/t0) for a large constant C. If we ignore for the sake of discussion the third hypothesis of Theorem 1.2 (which turns out to be relatively easy to verify numerically in practice), this suggests that one can obtain a bound of the form Λ ≤ O(t0) provided that one can verify the Riemann hypothesis up to a height exp(C/t0). In other words, if one has numerically verified the Riemann hypothesis up to a large height T , this should soon lead to a bound of the form Λ ≤ O
(1 log T
) .
Aside from improving the implied constant in this bound, it does not seem easy to improve this sort of implication without a major breakthrough on the Riemann hypothesis (such as a massive expansion of the known zero-free regions for the zeta function inside the critical strip). We shall justify this claim heuristically as follows. Suppose that there was a counterexample to the Riemann hypothesis at a large height T , so that H0(2T +iy) = 0 for some positive y, which for this discussion we will take to be comparable to 1. The Riemann von Mangoldt formula indicates that the number of zeroes of H0 within a bounded distance of this zero should be comparable to log T ; the majority of these zeroes should obey the Riemann hypothesis and thus stay at roughly unit distance from our initial zero 2T + iy. Proposition 3.1 then suggests that as time t advances, this zero should move at speed comparable to log T . Thus, one should not expect this zero to reach the real axis until a time comparable to 1
log T . This heuristic analysis therefore indicates that it is unlikely that
one can significantly improve the bound Λ ≤ O
(1 log T
)
without being able to exclude significant violations of the Riemann hypothesis at height T (Figs. 18, 19). Table 1 collects some numerical results verifying the second two hypotheses of Theorem 1.2 for larger values of X, and smaller values of t0, y0, than were considered in Sect. 8. This leads to improvements to the bound Λ ≤ 0.22 conditional on the assumption that the Riemann Hypothesis can be numerically verified beyond the height T ≈ 3.06 × 1010 used in Sect. 8. For instance, the final row of the table implies that one has the bound Λ ≤ 0.1 assuming that the Riemann hypothesis is verified up to the height T ≈ 4.5 × 1021. Note that this is broadly consistent with the previous heuristic that the upper bound on Λ is proportional to 1
log T .
The selection of parameters in this table proceeded as follows. One first located parameters t0, y0, N0 (with the quantity Λ = t0 + 1
2 y20 as small as possible) for which one could obtain a good lower bound for ft0 (x + iy0) when x = N0; we arbitrarily chose a target lower bound of |ft0 (x + iy0)| ≥ 0.03 to provide an adequate safety margin. From (96), one had
ft0 (x + iy0) =
N ∑
n=1
βn + O≤
(
|γ |
∣∣∣∣∣
N ∑
n=1
αn
∣∣∣∣∣
)
+ O≤
(
|γ |
N ∑
n=1
ny0 btn0
nσ (n|κ| − 1)
)
, (106)
where
βn := btn0
nσ +iT


 31 Page 64 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Fig. 18 Real zeros moving up leftwards and getting “solidified”
Fig. 19 Actual trajectories of some real and complex zeros
and
αn := ny0 btn0
nσ +iT .
The final term on the right-hand side of (106) can be estimated as in Sect. 8.5 and is negligible in practice. To control the other two terms, we use the following lemma (which roughly speaking corresponds to a simplified version of the “Euler 2 mollifier” version of the “Euler 5 mollifier” analysis in Sect. 8.5):


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 65 of 67 31
Table 1 Conditional Λ results
X t0 y0 Λ Winding number N0 |ft (x + iy)| lower bound
2 × 1012 + 129,093 0.198 0.15492 0.21 0 398,942 0.0341 5 × 1012 + 194,858 0.186 0.16733 0.20 0 630,783 0.0376 2 × 1013 + 131,252 0.180 0.14142 0.19 0 1,261,566 0.0349 6 × 1013 + 123,375 0.168 0.15492 0.18 0 2,185,096 0.0377 3 × 1014 + 188,911 0.161 0.13416 0.17 0 4,886,025 0.0369 2 × 1015 + 122,014 0.153 0.11832 0.16 0 12,615,662 0.0532 7 × 1015 + 688,86 0.139 0.14832 0.15 0 23,601,743 0.0350 6 × 1016 + 156,984 0.132 0.12649 0.14 0 69,098,829 0.0307 6 × 1017 + 88,525 0.122 0.12649 0.13 0 218,509,686 0.0347 9 × 1018 + 35,785 0.113 0.11832 0.12 0 846,284,375 0.0318 2 × 1020 + 66,447 0.102 0.12649 0.11 0 3,989,422,804 0.0305 9 × 1021 + 70,686 0.093 0.11832 0.1 0 26,761,861,742 0.0321
Lemma 10.1 Let α1, . . . , αN be complex numbers, and let β2 be a number such that whenever 1 ≤ n ≤ N is even, β2αn/2 lies on the line segment {θ αn: 0 ≤ θ ≤ 1} connecting 0 with αn. Then, we have the lower bound
|1 − β2|
∣∣∣∣∣
N ∑
n=1
αn
∣∣∣∣∣ ≥ 2|α1| − (1 − |β2|)
N ∑
n=1
|αn| − 2|β2| ∑
N /2<n≤N
|αn|
and the upper bound
|1 − β2|
∣∣∣∣∣
N ∑
n=1
αn
∣∣∣∣∣ ≤ (1 − |β2|)
N ∑
n=1
|αn| + 2|β2| ∑
N /2<n≤N
|αn|.
Proof The quantity |1 − β2|| ∑N
n=1 αn| can be written as
∣∣∣∣∣
2∑N
n=1
(1n≤N αn − 12|nαn/2β2)
∣∣∣∣∣ .
By the triangle inequality, this is bounded above by
2∑N
n=1
|1n≤N αn − 12|nαn/2β2|
and below by
2|α1| −
2∑N
n=1
|1n≤N αn − 12|nαn/2β2|.
We have
2∑N
n=1
|1n≤N αn − 12|nαn/2β2| =
N ∑
n=1
|αn| − 12|n|αn/2||β2| +
2∑N
n=N +1
12|n|αn/2||β2|
which we can rearrange as
(1 − |β2|)
N ∑
n=1
|αn| + 2|β2| ∑
N /2<n≤N
|αn|
and the claim follows.


 31 Page 66 of 67 D. H. J. Polymath Res Math Sci (2019) 6:31
Fig. 20 The envelope of potential choices of x, Λ. Note the approximate inverse relationship between Λ and 1
log x
Using this lemma to lower bound | ∑N
n=1 βn| and upper bound | ∑N
n=1 αn|, and then using the triangle inequality yields a lower bound on |ft0 (x + iy0)| when N = N0. These quantities can be readily computed for many values of t0, y0, N0, leading to an envelope for Λ and x ≈ 4π N02 that is depicted in Fig. 20. By working in intervals N ∈ [N−, N+] for some finite number of intervals [N−, N+] covering [N0, N1] for some large N1 as in Sect. 8.5, and then using a crude triangle inequality bound for N ≥ N1 as in Sect. 8.3, we thus (in view of the conservative safety margin in our lower bounds for |ft0 (x + iy0)|) expect to be able to verify the hypothesis in Theorem 1.2(iii) for any choice of parameters t0, y0, N0 as above. The main remaining difficulty is then to verify the barrier hypothesis (Theorem 1.2(ii)). This is by far the most numerically intensive step, and we proceed as in Sect. 8.4, after using the ad hoc procedure in Sect. 8.1 to select X0. The graphs in Fig. 21 illustrate that for increasing x, the number of xy-rectangles to be evaluated within the barrier, as well as the number of mesh points required per rectangle (measured at t = 0), increases exponentially. All barrier runs generated a winding number of zero for each rectangle, and the scripts completed successfully without any errors. For all barrier locations, the computations of the mesh points were calculated at 20 digits accuracy except for the highest two where 10 digits were used (to be able to compute it within a reasonable time). Checks were made before each formal run to assure the target accuracy would be achieved. The computations for X = 2 × 1020 + 66,447 and X = 9 × 1021 + 70,686 in the above table were massive and performed using a BOINC [1]-based grid computing setup,


 D. H. J. Polymath Res Math Sci (2019) 6:31 Page 67 of 67 31
Fig. 21 The left graph shows how the number mesh points of the xy-rectangle at t = 0 increases with x for each barrier. The graph on the right does the same, but now for the total number of xy-rectangles that need to be evaluated per barrier
in which a few hundred volunteers participated. Their contributions can be tracked at
anthgrid.com/dbnupperbound.
Received: 28 April 2019 Accepted: 1 August 2019 Published online: 26 August 2019
References
1. Anderson, D.P.: BOINC: a system for public-resource computing and storage. In: GRID ’04: Proceedings of the Fifth IEEE/ACM International Workshop on Grid Computing, pp. 4–10 (2004) 2. Arias de Reyna, J.: High-precision computation of Riemann’s zeta function by the Riemann–Siegel asymptotic formula, I. Math. Comput. 80, 995–1009 (2011) 3. Arias de Reyna, J., Van de lune, J.: On the exact location of the non-trivial zeroes of Riemann’s zeta function. Acta Arith. 163, 215–245 (2014) 4. Boyd, W.G.C.: Gamma function asymptotics by an extension of the method of steepest descents. Proc. Math. Phys. Sci. 447(1931), 609–630 (1994) 5. Csordas, G., Norfolk, T.S., Varga, R.S.: A lower bound for the de Bruijn–Newman constant . Numer. Math. 52, 483–497 (1988) 6. Csordas, G., Odlyzko, A.M., Smith, W., Varga, R.S.: A new Lehmer pair of zeros and a new lower bound for the De Bruijn–Newman constant Lambda. Electron. Trans. Numer. Anal. 1, 104–111 (1993) 7. Csordas, G., Ruttan, A., Varga, R.S.: The Laguerre inequalities with applications to a problem associated with the Riemann hypothesis. Numer. Algorithms 1, 305–329 (1991) 8. Csordas, G., Smith, W., Varga, R.S.: Lehmer pairs of zeros, the de Bruijn–Newman constant , and the Riemann hypothesis. Constr. Approx. 10(1), 107–129 (1994) 9. de Bruijn, N.C.: The roots of trigonometric integrals. Duke J. Math. 17, 197–226 (1950) 10. Ki, H., Kim, Y.O., Lee, J.: On the de Bruijn–Newman constant. Adv. Math. 22, 281–306 (2009) 11. Newman, C.M.: Fourier transforms with only real zeroes. Proc. Am. Math. Soc. 61, 246–251 (1976) 12. Norfolk, T.S., Ruttan, A., Varga, R.S.: A lower bound for the de Bruijn–Newman constant II. In: Gonchar, A.A., Saff, E.B. (eds.) Progress in Approximation Theory, pp. 403–418. Springer, Berlin (1992) 13. Odlyzko, A.M.: An improved bound for the de Bruijn–Newman constant. Numer. Algorithms 25, 293–303 (2000) 14. Platt, D.J.: Isolating some non-trivial zeros of zeta. Math. Comput. 86, 2449–2467 (2017) 15. Polya, G.: Über trigonometrische Integrale mit nur reelen Nullstellen. J. Reine Angew. Math. 58, 6–18 (1927) 16. Polymath, D.H.J.: http://github.com/km-git-acc/dbn_upper_bound 17. Polymath, D.H.J.: Zeroes of the heat flow evolution of the Riemann ξ function at negative times: numerical experiments and heuristic justifications, http://github.com/km-git-acc/dbn_upper_bound/blob/master/Writeup/ Sharkfin/sharkfin.pdf 18. Rodgers, B., Tao, T.: The De Bruijn–Newman constant is nonnegative, preprint. arXiv:1801.05914 19. Saouter, Y., Gourdon, X., Demichel, P.: An improved lower bound for the de Bruijn–Newman constant. Math. Comput. 80, 2281–2287 (2011)
Publisher’s Note
Springer Nature remains neutral with regard to jurisdictional claims in published maps and institutional affiliations.