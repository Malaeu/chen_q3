---
title: "Problems of the Millennium: The Riemann Hypothesis"
authors:
  - "Enrico Bombieri"
date: "2000-00-00 2000"
publication: null
doi: null
url: "https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf"
zotero:
  attachment_key: "7ZGWPCRG"
  parent_key: "ZZMPBTIQ"
  item_id: 1938
  attachment_item_id: 1985
---

Problems of the Millennium: the Riemann Hypothesis
E. Bombieri
I. The problem. The Riemann zeta function is the function of the complex variable s, defined in the half-plane1 (s) > 1 by the absolutely convergent series
ζ(s) :=
∑ ∞
n=1
1
ns ,
and in the whole complex plane C by analytic continuation. As shown by Riemann, ζ(s) extends to C as a meromorphic function with only a simple pole at s = 1 , with residue 1 , and satisfies the functional equation
π−s/2 Γ( s
2 ) ζ(s) = π−(1−s)/2 Γ( 1 − s
2 ) ζ(1 − s). (1)
In an epoch-making memoir published in 1859, Riemann [Ri] obtained an analytic formula for the number of primes up to a preassigned limit. This formula is expressed in terms of the zeros of the zeta function, namely the solutions ρ ∈ C of the equation ζ(ρ) = 0 . In this paper, Riemann introduces the function of the complex variable t defined by
ξ(t) = 1
2 s(s − 1) π−s/2Γ( s
2 ) ζ(s)
with s = 1
2 +it, and shows that ξ(t) is an even entire function of t whose zeros have
imaginary part between −i/2 and i/2 . He further states, sketching a proof, that in the range between 0 and T the function ξ(t) has about (T /2π) log(T /2π) − T /2π zeros. Riemann then continues: “Man findet nun in der That etwa so viel reelle Wurzeln innerhalb dieser Grenzen, und es ist sehr wahrscheinlich, dass alle Wurzeln reell sind.”, which can be translated as “Indeed, one finds between those limits about that many real zeros, and it is very likely that all zeros are real.” The statement that all zeros of the function ξ(t) are real is the Riemann hypothesis. The function ζ(s) has zeros at the negative even integers −2, −4, . . . and one refers to them as the trivial zeros. The other zeros are the complex numbers 1
2 + iα where α is a zero of ξ(t). Thus, in terms of the function ζ(s), we can state
Riemann hypothesis. The nontrivial zeros of ζ(s) have real part equal to 1
2.
In the opinion of many mathematicians the Riemann hypothesis, and its extension to general classes of L -functions, is probably today the most important open problem in pure mathematics.
II. History and significance of the Riemann hypothesis. For references pertaining to the early history of zeta functions and the theory of prime numbers, we refer to Landau [La] and Edwards [Ed].
1 We denote by (s) and (s) the real and imaginary part of the complex variable s . The use of the variable s is already in Dirichlet’s famous work of 1837 on primes in arithmetic progression.


 2 E. BOMBIERI
The connection between prime numbers and the zeta function, by means of the celebrated Euler product
ζ(s) =
∏
p
(1 − p−s)−1
valid for (s) > 1 , appears for the first time in Euler’s book Introductio in Analysin Infinitorum, published in 1748. Euler also studied the values of ζ(s) at the even positive and the negative integers, and he divined a functional equation, equivalent
to Riemann’s functional equation, for the closely related function ∑(−1)n−1/ns (see the interesting account of Euler’s work in Hardy’s book [Hard]). The problem of the distribution of prime numbers received attention for the first time with Gauss and Legendre, at the end of the eighteenth century. Gauss, in a letter to the astronomer Hencke in 1849, stated that he had found in his early years that the number π(x) of primes up to x is well approximated by the function2
Li(x) =
∫x
0
dt
log t .
In 1837, Dirichlet proved his famous theorem of the existence of infinitely many primes in any arithmetic progression qn+a with q and a positive coprime integers. On May 24, 1848, Tchebychev read at the Academy of St. Petersburg his first memoir on the distribution of prime numbers, later published in 1850. It contains the first study of the function π(x) by analytic methods. Tchebychev begins by taking the logarithm of the Euler product, obtaining3
−∑
p
log(1 − 1
ps ) + log(s − 1) =log ((s − 1)ζ(s)), (2)
which is his starting point. Next, he proves the integral formula
ζ(s) − 1 − 1
s−1 = 1
Γ(s)
∫∞
0
(1
ex − 1 − 1
x ) e−xxs−1 dx, (3)
out of which he deduces that (s − 1)ζ(s) has limit 1 , and also has finite derivatives of any order, as s tends to 1 from the right. He then observes that the derivatives of any order of the left-hand side of (2) can be written as a fraction in which the numerator is a polynomial in the derivatives of (s − 1)ζ(s), and the denominator is an integral power of (s − 1)ζ(s), from which it follows that the left-hand side of (2) has finite derivatives of any order, as s tends to 1 from the right. From this, he is able to prove that if there is an asymptotic formula for π(x) by means of a
finite sum ∑ akx/(log x)k , up to an order O(x/(log x)N ), then ak = (k − 1)! for k = 1, . . . , N − 1 . This is precisely the asymptotic expansion of the function Li(x), thus vindicating Gauss’s intuition. A second paper by Tchebychev gave rigorous proofs of explicit upper and lower bounds for π(x), of the correct order of magnitude. Here, he introduces the counting functions
θ(x) =
∑
p≤x
log p , ψ(x) = θ(x) + θ( 2 √x) + θ( 3 √x) + . . .
2 The integral is a principal value in the sense of Cauchy. 3 Tchebychev uses 1 + ρ in place of our s . We write his formulas in modern notation.


 PROBLEMS OF THE MILLENNIUM: THE RIEMANN HYPOTHESIS 3
and proves the identity4 ∑
n≤x
ψ( x
n ) = log [x]! .
From this identity, he finally obtains numerical upper and lower bounds for ψ(x), θ(x) and π(x). Popular variants of Tchebychev’s method, based on the integrality of suitable ratios of factorials, originate much later and cannot be ascribed to Tchebychev. Riemann’s memoir on π(x) is really astonishing for the novelty of ideas introduced. He first writes ζ(s) using the integral formula, valid for (s) > 1 :
ζ(s) = 1
Γ(s)
∫∞
0
e−x
1 − e−x xs−1 dx, (4)
and then deforms the contour of integration in the complex plane, so as to obtain a representation valid for any s. This gives the analytic continuation and the functional equation of ζ(s). Then he gives a second proof of the functional equation in the symmetric form (1), introduces the function ξ(t) and states some of its properties as a function of the complex variable t. Riemann continues by writing the logarithm of the Euler product as an integral transform, valid for (s) > 1 :
1
s log ζ(s) =
∫∞
1
∏ (x)x−s−1 dx (5)
where
∏ (x) = π(x) + 1
2 π( 2 √x) + 1
3 π( 3 √x) + . . . .
By Fourier inversion, he is able to express ∏ (x) as a complex integral, and compute it using the calculus of residues. The residues occur at the singularities of log ζ(s) at s =1 and at the zeros of ζ(s). Finally an inversion formula expressing π(x) in
terms of ∏ (x) yields Riemann’s formula. This was a remarkable achievement which immediately attracted much attention. Even if Riemann’s initial line of attack may have been influenced by Tchebychev (we find several explicit references to Tchebychev in Riemann’s unpublished Nachlass5) his great contribution was to see how the distribution of prime numbers is determined by the complex zeros of the zeta function. At first sight, the Riemann hypothesis appears to be only a plausible interesting property of the special function ζ(s), and Riemann himself seems to take that view. He writes: “Hiervon wa ̈re allerdings ein strenger Beweis zu w ̈unschen; ich habe indess die Aufsuchung desselben nach einigen flu ̈chtigen vergeblichen Versuchen vorla ̈ufig bei Seite gelassen, da er f ̈ur den na ̈chsten Zweck meiner Untersuchung entbehrlich schien.”, which can be translated as “Without doubt it would be desirable to have a rigorous proof of this proposition; however I have left this research aside for the time being after some quick unsuccessful attempts, because it appears to be unnecessary for the immediate goal of my study.”
4 Here [x] denotes the integral part of x . 5 The Nachlass consists of Riemann’s unpublished notes and is preserved in the mathematical library of the University of G ̈ottingen. The part regarding the zeta function was analyzed in depth by C.L. Siegel [Sie].


 4 E. BOMBIERI
On the other hand, one should not draw from this comment the conclusion that the Riemann hypothesis was for Riemann only a casual remark of minor interest. The validity of the Riemann hypothesis is equivalent to saying that the deviation of the number of primes from the mean Li(x) is
π(x) = Li(x) + O(√x log x);
the error term cannot be improved by much, since it is known to oscillate in both
directions to order at least Li(√x) log log log x (Littlewood). In view of Riemann’s comments at the end of his memoir about the approximation of π(x) by Li(x), it is quite likely that he saw how his hypothesis was central to the question of how good an approximation to π(x) one may get from his formula. The failure of the Riemann hypothesis would create havoc in the distribution of prime numbers. This fact alone singles out the Riemann hypothesis as the main open question of prime number theory. The Riemann hypothesis has become a central problem of pure mathematics, and not just because of its fundamental consequences for the law of distribution of prime numbers. One reason is that the Riemann zeta function is not an isolated object, rather is the prototype of a general class of functions, called L -functions, associated with algebraic (automorphic representations) or arithmetical objects (arithmetic varieties); we shall refer to them as global L -functions. They are Dirichlet series with a suitable Euler product, and are expected to satisfy an appropriate functional equation and a Riemann hypothesis. The factors of the Euler product may also be considered as some kind of zeta functions of a local nature, which also should satisfy an appropriate Riemann hypothesis (the so-called Ramanujan property). The most important properties of the algebraic or arithmetical objects underlying an L -function can or should be described in terms of the location of its zeros and poles, and values at special points. The consequences of a Riemann hypothesis for global L -functions are important and varied. We mention here, to indicate the variety of situations to which it can be applied, an extremely strong effective form of Tchebotarev’s density theorem for number fields, the non-trivial representability of 0 by a non-singular cubic form in 5 or more variables (provided it satisfies the appropriate necessary congruence conditions for solubility, Hooley), and Miller’s deterministic polynomial time primality test. On the other hand, many deep results in number theory which are consequences of a general Riemann hypothesis can be shown to hold independently of it, thus adding considerable weight to the validity of the conjecture. It is outside the scope of this article even to outline the definition of global L functions, referring instead to Iwaniec and Sarnak [IS] for a survey of the expected properties satisfied by them; it suffices here to say that the study of the analytic properties of these functions presents extraordinary difficulties. Already the analytic continuation of L -functions as meromorphic or entire functions is known only in special cases. For example, the functional equation for the L -function of an elliptic curve over Q and for its twists by Dirichlet characters is an easy consequence of, and is equivalent to, the existence of a parametrization of the curve by means of modular functions for a Hecke group Γ0(N ); the real difficulty lies in establishing this modularity. No one knows how to prove this functional equation by analytic methods. However the modularity of elliptic curves over Q has been established directly, first in the semistable case in the spectacular work


 PROBLEMS OF THE MILLENNIUM: THE RIEMANN HYPOTHESIS 5
of Wiles [Wi] and Taylor and Wiles [TW] leading to the solution of Fermat’s Last Theorem, and then in the general case in a recent preprint by Breuil, Conrad, Diamond and Taylor. Not all L -functions are directly associated to arithmetic or geometric objects. The simplest example of L -functions not of arithmetic/geometric nature are those arising from Maass waveforms for a Riemann surface X uniformized by an arithmetic subgroup Γ of PGL(2, R). They are pull-backs f (z), to the universal covering space (z) > 0 of X , of simultaneous eigenfunctions for the action of the hyperbolic Laplacian and of the Hecke operators on X . The most important case is again the group Γ0(N ). In this case one can introduce a notion of primitive waveform, analogous to the notion of primitive Dirichlet character, meaning that the waveform is not induced from another waveform for a Γ0(N ′) with N ′ a proper divisor of N . For a primitive waveform, the action of the Hecke operators Tn is defined for every n and the L -function can be defined
as ∑ λf (n)n−s where λf (n) is the eigenvalue of Tn acting on the waveform f (z). Such an L -function has an Euler product and satisfies a functional equation analogous to that for ζ(s). It is also expected that it satisfies a Riemann hypothesis. Not a single example of validity or failure of a Riemann hypothesis for an L function is known up to this date. The Riemann hypothesis for ζ(s) does not seem to be any easier than for Dirichlet L -functions (except possibly for non-trivial real zeros), leading to the view that its solution may require attacking much more general problems, by means of entirely new ideas.
III. Evidence for the Riemann hypothesis. Notwithstanding some skepticism voiced in the past, based perhaps more on the number of failed attempts to a proof rather than on solid heuristics, it is fair to say that today there is quite a bit of evidence in its favor. We have already emphasized that the general Riemann hypothesis is consistent with our present knowledge of number theory. There is also specific evidence of a more direct nature, which we shall now examine.
First, strong numerical evidence. Interestingly enough, the first numerical computation of the first few zeros of the zeta function already appears in Riemann’s Nachlass. A rigorous verification of the Riemann hypothesis in a given range can be done numerically as follows. The number N (T ) of zeros of ζ(s) in the rectangle R with vertices at −1 − iT, 2 − iT, 2 + iT, −1 + iT is given by Cauchy’s integral
N (T ) − 1 = 1
2πi
∫
∂R
−ζ′
ζ (s) ds,
provided T is not the imaginary part of a zero (the −1 in the left-hand side of this formula is due to the simple pole of ζ(s) at s =1 ). The zeta function and its derivative can be computed to arbitrary high precision using the MacLaurin summation formula or the Riemann-Siegel formula [Sie]; the quantity N (T ) − 1 , which is an integer, is then computed exactly by dividing by 2πi the numerical evaluation of the integral, and rounding off its real part to the nearest integer (this is only of theoretical interest and much better methods are available in practice for computing N (T ) exactly). On the other hand, since ξ(t) is continuous and real for real t, there will be a zero of odd order between any two points at which ξ(t) changes sign. By judiciously choosing sample points, one can detect sign changes


 6 E. BOMBIERI
of ξ(t) in the interval [−T, T ]. If the number of sign changes equals N (T ), one concludes that all zeros of ζ(s) in R are simple and satisfy the Riemann hypothesis. In this way, it has been shown by van de Lune, te Riele and Winter [LRW] that the first 1.5 billion zeros of ζ(s), arranged by increasing positive imaginary part, are simple and satisfy the Riemann hypothesis. The Riemann hypothesis is equivalent to the statement that all local maxima of ξ(t) are positive and all local minima are negative, and it has been suggested that if a counterexample exists then it should be in the neighborhood of unusually large peaks of |ζ( 1
2 + it)|. The above range for T is T ∼= 5 × 108 and is not large
enough for |ζ( 1
2 + it)| to exhibit these peaks which are known to occur eventually. However, further calculations done by Odlyzko [Od] in selected intervals show that the Riemann hypothesis holds for over 3 × 108 zeros at heights up to6 2 × 1020 . These calculations also strongly support independent conjectures by Dyson and Montgomery [Mo] concerning the distribution of spacings between zeros. Computing zeros of L -functions is more difficult, but this has been done in several cases, which include examples of Dirichlet L -functions, L -functions of elliptic curves, Maass L -functions and nonabelian Artin L -functions arising from number fields of small degree. No exception to a generalized Riemann hypothesis has been found in this way.
Second, it is known that hypothetical exceptions to the Riemann hypothesis must be rare if we move away from the line (s) = 1
2.
Let N (α, T ) be the number of zeros of ζ(s) in the rectangle α ≤ (s) ≤ 2 , 0 ≤ (s) ≤ T . The prototype result goes back to Bohr and Landau in 1914, namely N (α, T ) = O(T ) for any fixed α with 1
2 < α < 1 . A significant improvement of the result of Bohr and Landau was obtained by Carlson in 1920, obtaining the density theorem N (α, T ) = O(T 4α(1−α)+ε) for any fixed ε > 0 . The fact that the exponent here is strictly less than 1 is important for arithmetic applications, for example in the study of primes in short intervals. The exponent in Carlson’s theorem has gone through several successive refinements for various ranges of α , in particular in the range 3
4 < α < 1 . Curiously enough, the best exponent known up to date
in the range 1
2 <α≤ 3
4 remains Ingham’s exponent 3(1 − α)/(2 − α), obtained in 1940. For references to these results, the reader may consult the recent revision by Heath-Brown of the classical monograph of Titchmarsh [Ti], and the book by Ivic [Iv].
Third, it is known that more than 40 % of nontrivial zeros of ζ(s) are simple and satisfy the Riemann hypothesis (Selberg [Sel], Levinson [Le], Conrey [Conr]). Most of these results have been extended to other L -functions, including all Dirichlet L -functions and L -functions associated to modular forms or Maass waveforms.
IV. Further evidence: varieties over finite fields. It may be said that the best evidence in favor of the Riemann hypothesis derives from the corresponding theory which has been developed in the context of algebraic varieties over finite fields. The simplest situation is as follows. Let C be a nonsingular projective curve over a finite field Fq with q = pa elements, of characteristic p. Let Div(C) be the additive group of divisors on C
6 The most recent calculations by Odlyzko, which are approaching completion, will explore completely the interval [1022, 1022 + 1010] .


 PROBLEMS OF THE MILLENNIUM: THE RIEMANN HYPOTHESIS 7
defined over Fq , in other words formal finite sums a = ∑ aiPi with ai ∈ Z and Pi points of C defined over a finite extension of Fq , such that φ(a) = a where φ is the Frobenius endomorphism on C raising coordinates to the q -th power. The
quantity deg(a) = ∑ ai is the degree of the divisor a . The divisor a is called effective if every ai is a positive integer; in this case, we write a > 0 . Finally, a prime divisor p is a positive divisor which cannot be expressed as the sum of two positive divisors. By definition, the norm of a divisor a is N a = qdeg(a) . The zeta function of the curve C , as defined by E. Artin, H. Hasse and F.K. Schmidt, is
ζ(s, C) =
∑
a>0
1
N as .
This function has an Euler product
ζ(s, C) =
∏
p
(1 − N p−s)−1
and a functional equation
q(g−1)sζ(s, C) = q(g−1)(1−s)ζ(1 − s, C)
where g is the genus of the curve C ; it is a consequence of the Riemann-Roch theorem. The function ζ(s, C) is a rational function of the variable t = q−s , hence is periodic7 with period 2πi/ log q , and has simple poles at the points s = 2πim/ log q and s = 1 + 2 πim/ log q for m ∈ Z. Expressed in terms of the variable t, the zeta function becomes a rational function Z(t, C) of t, with simple poles at t = 1 and t = q−1 . The use of the variable t, rather than q−s , is more natural in the geometric case and we refer to Zeta functions, with a capital Z, to indicate the corresponding objects. The Riemann hypothesis for ζ(s, C) is the statement that all its zeros have real part equal to 1
2 ; in terms of the Zeta function Z(t, C), which has a numerator of
degree 2g , has zeros of absolute value q− 1
2.
This is easy to verify if g =0 , because the numerator is 1 . If g = 1 , a proof was obtained by Hasse in 1934. The general case of arbitrary genus g was finally settled by Weil in the early 1940s (see his letter to E. Artin of July 10, 1942 where he gives a complete sketch of the theory of correspondences on a curve [We1]); his results were eventually published in book form in 1948 [We2]. Through his researches, Weil was led to the formulation of sweeping conjectures about Zeta functions of general algebraic varieties over finite fields, relating their properties to the topological structure of the underlying algebraic variety. Here the Riemann hypothesis, in a simplified form, is the statement that the reciprocals of the zeros and poles of the Zeta function (the so-called characteristic roots) have absolute value qd/2 with d a positive integer or 0 , and are interpreted as eigenvalues of the Frobenius automorphism acting on the cohomology of the variety. After M. Artin, A. Grothendieck and J.-L. Verdier developed the fundamental tool of  ́etale cohomology, the proof of the corresponding Riemann hypothesis for Zeta functions of arbitrary varieties over finite fields was finally obtained by Deligne [Del1], [Del2]. Deligne’s theorem surely ranks as one of the crowning achievements
7 Similarly, ζ(s) is almost periodic in any half-plane (s) ≥ 1 + δ , δ > 0 .


 8 E. BOMBIERI
of twentieth century mathematics. Its numerous applications to the solution of longstanding problems in number theory, algebraic geometry and discrete mathematics are witness to the significance of these general Riemann hypotheses. In our opinion, these results in the geometric setting cannot be ignored as not relevant to the understanding of the classical Riemann hypothesis; the analogies are too compelling to be dismissed outright.
V. Further evidence: the explicit formula. A conceptually important generalization of Riemann’s explicit formula for π(x), obtained by Weil [We3] in 1952, offers a clue to what may lie still undiscovered behind the problem. Consider the class W of complex-valued functions f (x) on the positive half-line R+ , continuous and continuously differentiable except for finitely many points at which both f (x) and f ′(x) have at most a discontinuity of the first kind, and at which the value of f (x) and f ′(x) is defined as the average of the right and left limits there. Suppose also that there is δ > 0 such that f (x) = O(xδ) as x → 0+ and f (x) = O(x−1−δ) as x → +∞ . Let f ̃(s) be the Mellin transform
f ̃(s) =
∫∞
0
f (x) xs dx
x,
which is an analytic function of s for −δ < (s) < 1 + δ . For the Riemann zeta function, Weil’s formula can be stated as follows. Let Λ(n) = log p if n = pa is a power of a prime p, and 0 otherwise. We have
Explicit Formula. For f ∈ W we have
f ̃(0) − ∑
ρ
f ̃(ρ) + f ̃(1) =
∞ ∑
n=1
Λ(n){f (n) + 1
n f(1
n )} + (log 4π + γ)f (1)
+
∫∞
1
{f (x) + 1
x f(1
x) − 2
x f (1)} dx
x − x−1 .
Here the first sum ranges over all nontrivial zeros of ζ(s) and is understood as
lim
T →+∞
∑
| (ρ)|<T
f ̃(ρ).
In his paper, Weil showed that there is a corresponding formula for zeta and L -functions of number fields as well as for Zeta functions of curves over finite fields. The terms in the right-hand side of the equation can be written as a sum of terms of local nature, associated to the absolute values of the underlying number field, or function field in the case of curves over a field of positive characteristic. Moreover, in the latter case the explicit formula can be deduced from the Lefschetz fixed point formula, applied to the Frobenius endomorphism on the curve C . The three terms
in the left-hand side, namely f ̃(0), ∑ f ̃(ρ), f ̃(1), now correspond to the trace of the Frobenius automorphism on the l -adic cohomology of C (the interesting term
∑ f ̃(ρ) corresponds to the trace on H1 ), while the right-hand side corresponds to the number of fixed points of the Frobenius endomorphism, namely the prime divisors of degree 1 on C .


 PROBLEMS OF THE MILLENNIUM: THE RIEMANN HYPOTHESIS 9
Weil also proved that the Riemann hypothesis is equivalent to the negativity of the right-hand side for all functions f (x) of type
f (x) =
∫∞
0
g(xy) g(y) dy,
whenever g ∈ W satisfies the additional conditions
∫∞
0
g(x) dx
x=
∫∞
0
g(x) dx = 0.
In the geometric case of curves over a finite field, this negativity is a rather easy consequence of the algebraic index theorem for surfaces, namely:
Algebraic Index Theorem. Let X be a projective nonsingular surface defined over an algebraically closed field. Then the self-intersection quadratic form (D · D), restricted to the group of divisors D on X of degree 0 in the projective embedding of X , is negative semidefinite.
The algebraic index theorem for surfaces is essentially due to Severi8 in 1906 [Sev,§2,Teo.I]. The proof uses the Riemann-Roch theorem on X and the finiteness of families of curves on X of a given degree; no other proof by algebraic methods is known up to now, although much later several authors independently rediscovered Severi’s argument. The algebraic index theorem for nonsingular projective varieties of even dimension over the complex numbers was first formulated and proved by Hodge, as a consequence of his theory of harmonic forms. No algebraic proof of Hodge’s theorem is known, and it remains a fundamental open problem to extend it to the case of varieties over fields of positive characteristic. The work of Montgomery [Mo], Odlyzko [Od] and Rudnick and Sarnak [RS] on correlations for spacings of zeros of ξ(t) suggests that L -functions can be grouped into a few families, in each of which the spacing correlation is universal; the conjectured spacing correlation is the same as for the limiting distribution of eigenvalues of random orthogonal, unitary or symplectic matrices in suitable universal families, as the dimension goes to ∞. All this is compatible with the view expressed by Hilbert and Po ́lya that the zeros of ξ(t) could be the eigenvalues of a self-adjoint linear operator on an appropriate Hilbert space. It should also be noted that a corresponding unconditional theory for the spacing correlations of characteristic roots of Zeta functions of families of algebraic varieties over a finite field, has been developed by Katz and Sarnak [KS], using methods introduced by Deligne in his proof of the Riemann hypothesis for varieties over finite fields. Thus the problem of spacing correlations for zeros of L -functions appears to lie very deep. All this leads to several basic questions. Is there a theory in the global case, playing the same role as cohomology does for Zeta functions of varieties over a field of positive characteristic? Is there an analogue of a Frobenius automorphism in the classical case? Is there a general index theorem by which one can prove the classical Riemann hypothesis? We are
8 Severi showed that a divisor D on X is algebraically equivalent to 0 up to torsion, if it has degree 0 and (D · D) = 0 . His proof holds, without modifications, under the weaker assumption (D · D) ≥ 0 , which yields the index theorem.


 10 E. BOMBIERI
here in the realm of conjectures and speculation. In the adelic setting propounded by Tate and Weil, the papers [Conn], [Den], [Hara] offer glimpses of a possible setup for these basic problems. On the other hand, there are L -functions, such as those attached to Maass waveforms, which do not seem to originate from geometry and for which we still expect a Riemann hypothesis to be valid. For them, we do not have algebraic and geometric models to guide our thinking, and entirely new ideas may be needed to study these intriguing objects.
Institute for Advanced Study, Princeton, NJ 08540
References
[Conn] A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Selecta Math. (NS) 5 (1999), 29–106.
[Conr] J.B. Conrey, More than two fifths of the zeros of the Riemann zeta function are on the critical line, J. reine angew. Math. 399 (1989), 1–26.
[Del1] P. Deligne, La Conjecture de Weil I, Publications Math. IHES 43 (1974), 273–308.
[Del2] P. Deligne, La Conjecture de Weil II, Publications Math. IHES 52 (1980), 137–252.
[Den] C. Deninger, Some analogies between number theory and dynamical systems on foliated spaces, Proc. Int. Congress Math. Berlin 1998, Vol. I, 163186.
[Ed] H.M. Edwards, Riemann’s Zeta Function, Academic Press, New York London 1974.
[Hara] S. Haran, Index theory, potential theory, and the Riemann hypothesis, L -functions and Arithmetic, Durham 1990, LMS Lecture Notes 153 (1991), 257270.
[Hard] G.H. Hardy, Divergent Series, Oxford Univ. Press 1949, Ch. II, 23–26.
[IS] H. Iwaniec and P. Sarnak, Perspectives on the Analytic Theory of L -Functions, to appear in proceedings of the conference Visions 2000, Tel Aviv.
[Iv] A. Ivicˇ , The Riemann Zeta-Function - The Theory of the Riemann ZetaFunction with Applications, John Wiley & Sons Inc., New York - Chichester Brisbane - Toronto - Singapore 1985.
[KS] N.M. Katz and P. Sarnak, Random matrices, Frobenius eigenvalues and monodromy, Amer. Math. Soc. Coll. Publ. 49, Amer. Math. Soc., Providence RI 1999.
[La] E. Landau, Primzahlen, Zwei Bd., IInd ed., with an Appendix by Dr. Paul T. Bateman, Chelsea, New York 1953.


 PROBLEMS OF THE MILLENNIUM: THE RIEMANN HYPOTHESIS 11
[Le] N. Levinson, More than one-third of the zeros of the Riemann zetafunction are on σ = 1/2 , Adv. Math. 13 (1974), 383–436.
[LRW] J. van de Lune, J.J. te Riele and D.T. Winter, On the zeros of
the Riemann zeta function in the critical strip, IV, Math. of Comp. 46 (1986), 667–681.
[Mo] H.L. Montgomery, Distribution of the Zeros of the Riemann Zeta Function, Proceedings Int. Cong. Math. Vancouver 1974, Vol. I, 379–381.
[Od] A.M. Odlyzko, Supercomputers and the Riemann zeta function, Supercomputing 89: Supercomputing Structures & Computations, Proc. 4-th Intern. Conf. on Supercomputing, L.P. Kartashev and S.I. Kartashev (eds.), International Supercomputing Institute 1989, 348–352.
[Ri] B. Riemann, Ueber die Anzahl der Primzahlen unter einer gegebenen Gro ̈sse, Monat. der Ko ̈nigl. Preuss. Akad. der Wissen. zu Berlin aus der Jahre 1859 (1860), 671–680; also, Gesammelte math. Werke und wissensch. Nachlass, 2. Aufl. 1892, 145–155.
[RS] Z. Rudnick and P. Sarnak, Zeros of principal L -functions and random matrix theory, Duke Math. J. 82 (1996), 269–322.
[Sel] A. Selberg, On the zeros of the zeta-function of Riemann, Der Kong. Norske Vidensk. Selsk. Forhand. 15 (1942), 59–62; also, Collected Papers, SpringerVerlag, Berlin - Heidelberg - New York 1989, Vol. I, 156–159.
[Sev] F. Severi, Sulla totalita` delle curve algebriche tracciate sopra una superficie algebrica, Math. Annalen 62 (1906), 194–225.
[Sie] C.L. Siegel, U ̈ ber Riemanns Nachlaß zur analytischen Zahlentheorie, Quellen und Studien zur Geschichte der Mathematik, Astronomie und Physik 2 (1932), 45–80; also Gesammelte Abhandlungen, Springer-Verlag, Berlin - Heidelberg - New York 1966, Bd. I, 275–310.
[Ti] E.C. Titchmarsh, The Theory of the Riemann Zeta Function, 2nd ed. revised by R.D. Heath-Brown, Oxford Univ. Press 1986.
[TW] R. Taylor and A. Wiles, Ring theoretic properties of certain Hecke algebras, Annals of Math. 141 (1995), 553–572.
[We1] A. Weil, Œuvres Scientifiques–Collected Papers, corrected 2nd printing, Springer-Verlag, New York - Berlin 1980, Vol. I, 280-298.
[We2] A. Weil, Sur les Courbes Alge ́briques et les Varie ́te ́s qui s’en de ́duisent, Hermann & Cie , Paris 1948.
[We3] A. Weil, Sur les “formules explicites” de la th ́eorie des nombres premiers, Meddelanden Fra ̊n Lunds Univ. Mat. Sem. (dedi ́e `a M. Riesz), (1952), 252265; also, Œuvres Scientifiques–Collected Papers, corrected 2nd printing, SpringerVerlag, New York - Berlin 1980, Vol. II, 48–61.
[Wi] A. Wiles, Modular elliptic curves and Fermat’s Last Theorem, Annals of Math. 141 (1995), 443–551.