---
title: "Analytic number theory and algebraic asymptotic analysis"
authors:
  - "Jesse Elliott"
date: "2025-00-00 2025"
publication: "arXiv"
doi: "10.48550/arxiv.2407.17820"
url: null
zotero:
  attachment_key: "7EYGBCU6"
  parent_key: "WTJYATRX"
  item_id: 1823
  attachment_item_id: 1842
---

arXiv:2407.17820v4 [math.NT] 21 Jun 2025
Analytic Number Theory and
Algebraic Asymptotic Analysis
Jesse Elliott


 

 Table of Contents
Dedication vii
Preface ix 0.1. Overview ix 0.2. Prerequisites and target audience xiii 0.3. Outline of contents xiv 0.4. Motivation and detailed summary xvi 0.5. Notation and conventions xl 0.6. Acknowledgments xli 0.7. About the author xlii 0.8. Publication xlii
Part 1. A survey of analytic number theory 1
Chapter 1. A brief history of primes 3 1.1. The prime numbers, algebraically 3 1.2. The prime numbers, asymptotically 7 1.3. The prime numbers, analytically 22
Chapter 2. Asymptotic analysis 37 2.1. Asymptotic relations 37 2.2. Asymptotic expansions 40 2.3. The degree deg f of a real function f 48 2.4. Slowly varying and regularly varying functions 51
Chapter 3. Arithmetic functions 59 3.1. Elementary complex functions 59 3.2. Arithmetic functions and formal Dirichlet series 62 3.3. Multiplicative and additive arithmetic functions 67 3.4. Summatory functions 78 3.5. Inversion theorems 83 3.6. Asymptotics of summatory functions and prime counting functions 88 3.7. Average value and average order 95 3.8. Dirichlet series 100
Chapter 4. Special functions in analytic number theory 111 4.1. The gamma function Γ(s) 111 4.2. The Riemann zeta function ζ(s) 115 4.3. The prime zeta function P (s) 122 4.4. The functions Ein(s), Ei(s), and E1(s) 124
iii


 iv TABLE OF CONTENTS
4.5. The functions ERi(s) and Ri(x) 127
Chapter 5. The analytic theory of primes 135 5.1. The explicit formulas for π0(x), Π0(x), and ψ0(x) 135 5.2. The prime number theorem with error bound 147 5.3. The zeros of ζ(s) and the Riemann–von Mangoldt formula 150 5.4. Primes in abstract analytic number theory 172
Part 2. Algebraic asymptotic analysis 177
Chapter 6. Logexponential degree 179 6.1. The degree of a real function 179 6.2. The iterated logarithmic degree ldeg f of a real function f 187 6.3. The logexponential degree ledeg f of a real function f 196 6.4. Further results on degree and logexponential degree 228
Chapter 7. Asymptotic algebra 233 7.1. Lattice-ordered rings 233 7.2. The ring of germs of real functions at ∞ 236 7.3. Real asymptotic differential algebra: Hardy rings and Hardy fields 239 7.4. Characterizations and generalizations of the degree map 249 7.5. Logexponentially bounded Hardy fields 260 7.6. Logexponential degree of transseries 267
Chapter 8. Asymptotic continued fraction expansions 275 8.1. General asymptotic continued fraction expansions 275 8.2. Asymptotic Jacobi and Steiltjes continued fraction expansions 277 8.3. Continued fractions with polynomial terms 279 8.4. Prime counting counting functions 283 8.5. Weighted prime counting functions 290 8.6. Measure-theoretic interpretation 299
Part 3. Applications of algebraic asymptotic analysis to number theory 305
Chapter 9. The prime counting function π(x) and related functions 307 9.1. The function li(x) − π(x) 307 9.2. Riemann’s functions Π(x) and Ri(x) 314 9.3. The first and second Chebyshev functions θ(x) and ψ(x) 315 9.4. The function li(x) − π(x) on average 321
Chapter 10. Summatory functions 327 10.1. Error terms in Mertens’ theorems 327 10.2. The Mertens function M (x) and summatory Liouville function L(x) 334 10.3. The Dirichlet divisor problem and its various analogues 339 10.4. The degree and logexponential degree of a summatory function 341
Chapter 11. The Riemann zeta function ζ(s) 347 11.1. The Lindelöf hypothesis and density hypothesis 347 11.2. The nontrivial zeros of ζ(s) 351


 TABLE OF CONTENTS v
Chapter 12. Primes in intervals, the nth prime, and the nth prime gap 361 12.1. Asymptotics for prime counts in intervals 361 12.2. The nth prime pn 382 12.3. The nth prime gap gn = pn+1 − pn 394
Chapter 13. Diophantine approximation and continued fractions 403 13.1. The basics of Diophantine approximation 403 13.2. Irrationality measure 413 13.3. Markov and relativized Markov constants 419 13.4. Logexponential irrationality degree 425 13.5. Lévy and relative Lévy constants 437 13.6. Rates of convergence 439 13.7. Quadratic irrationals 449
Chapter 14. Conjectures 457 14.1. Iterated logarithmic degree statistics 457 14.2. Conjectures concerning li(x) − π(x) 462 14.3. Conjectures concerning the Mertens function 469 14.4. Conjectures concerning the Riemann zeta function 478 14.5. Conjectures on asymptotics for prime counts in intervals 486 14.6. Conjectures on prime gaps 490 14.7. Gemeralizations of the abc conjecture 494 14.8. Tables 497
Bibliography 507
Index of Symbols 517
Index 521


 

 Dedication
This book is dedicated to my mother, Nancy (Elliott) Cappello.
vii


 

 Preface
0.1. Overview
This monograph introduces a new framework for measuring and comparing the asymptotic behavior of complex functions of a real variable, one that proves especially effective within number theory. At its core is a formalism built around two invariants, degree and logexponential degree, that quantify asymptotic growth. These invariants extend classical notations such as O, o, and ∼ that were developed by du Bois-Reymond, Bachmann, Landau, Hardy, and others, into a more expressive and numerically structured analytic-algebraic language of asymptotic comparison. This framework is situated within a broader field that we refer to as algebraic asymptotic analysis: the study of asymptotic behavior using tools from both algebra and analysis. Algebraic asymptotic analysis builds on several other fields, including asymptotic analysis [57] [79] [117] [118] [226] [296]; Karamata theory [27] [148] [149] [264]; the theory of continued fractions and moments in the tradition of Stieltjes [2] [52] [274]; and asymptotic differential algebra [11] [35] [253] [67] [68] [69] [254] [126]. The book is structured in three parts. Part 1 is a survey of classical analytic number theory in both mathematical and historical contexts. Anticipating Parts 2 and 3, it includes foundational material on asymptotic analysis, arithmetic functions, Dirichlet series, special functions, and the analytic theory of primes, prioritizing conceptual breadth, clarity, and visual insight over formal proof. Part 2 presents the central theoretical framework of the book, developing the theory of logexponential degree and its interactions with asymptotic analysis and real asymptotic differential algebra—notably, through connections to ordered exponential fields, Hardy fields, Hardy’s ordered differential field of logarithmico-exponential functions [117] [118], and the ordered differential field of well-based logarithmic-exponential transseries [11, Appendix A] [67] [68] [69]. Finally, Part 3 applies Parts 1 and 2 to a broad range of functions in number theory. Specifically, it uses logexponential degree as a unifying organizing principle for analyzing asymptotic behavior and motivating conjectures related to the following: the Riemann hypothesis, the Lindelöf hypothesis, and the density hypothesis; the ordinates of the Riemann zeta function zeros and their gaps; the prime counting function, weighted prime counting functions, the Mertens function, and summatory functions more broadly; the prime listing function and prime gaps; the Dirichlet divisor problem; least primitive roots, quadratic non-residues, and primes in arithmetic progressions; Roth’s theorem on irrationality measure; and the abc conjecture. At the foundation of the new formalism is the notion of degree, which appears implicitly throughout analytic number theory. Precisely, we define the degree deg f ∈ [−∞, ∞], for any complex-valued function f defined on a subset of R that is not bounded above, to be the infimum of all t ∈ R such that |f (x)| ≪ xt as x → ∞. Equivalently, one has
deg f = lim supx→∞ Lf (x), where Lf (x) = log |f(x)|
log x is the unique function from R>0 ∩ dom f
ix


 x PREFACE
to [−∞, ∞) satisfying |f (x)| = xLf (x), where log 0 = −∞ and 0 = x−∞. The corresponding lower degree degf is the supremum of all t ∈ R such that |f (x)| ≫ xt and is given equivalently by lim infx→∞ Lf (x), and also by − deg(1/f ) if f is not eventually 0. Intuitively, degree can be seen as a degree of freedom, representing the maximal power a function can asymptotically achieve. Likewise, lower degree represents a degree of variation—the minimal power it can asymptotically maintain. A few notable examples illustrate the significance of the degree invariant. The Riemann hypothesis, for instance, is equivalent to the statement that deg(li −π) = 1
2 , where π(x) is the
prime counting function and li(x) = R x
0
dt
log t is the logarithmic integral function. Likewise,
it is equivalent to the statement that deg M = 1
2 , where M (x) = P
n≤x μ(n) is the Mertens
function. More generally, one has deg(li −π) = Θ = deg M (x), where Θ ∈ [ 1
2 , 1] is the supremum of the real parts of the nontrivial zeros of the Riemann zeta function. The equality deg(li −π) = Θ means that the bound li(x) − π(x) = O(xt) holds for all t > Θ and fails for all t < Θ. Intuitively, this says that, to first order, the prime counting function fluctuates around its smooth approximation li(x) by a Θ-power law, and thus it is like a “law of gravity” for the primes. The constant Θ, which we call the Riemann constant, thus encodes a fundamental relationship between the prime counting function and the zeros of Riemann zeta function. The best case scenario is the Riemann hypothesis, Θ = 1
2 ; the worst case scenario is Θ = 1, which we call the anti-Riemann hypothesis. Although a disproof of the anti-Riemann hypothesis would represent major progress toward a proof of the Riemann hypothesis, currently there is no guarantee that the anti-Riemann hypothesis is false, let alone that the Riemann hypothesis is true. This reveals an asymmetry in the problem of settling the Riemann hypothesis, namely, that a mere negative answer would still leave the exact value of Θ = deg(li −π) a mystery. It also hints at what is widely known but rarely stated: many statements equivalent to the Riemann hypothesis can be recast as unconditional statements about the Riemann constant Θ. This gives weight to the claim that the closer that Θ is to 1
2 , the “more true” the Riemann hypothesis is. In this respect, the Riemann hypothesis acts less like a binary proposition, and more like a fuzzy one whose truth value is a decreasing function RH(Θ) of Θ—for example, RH(Θ) = 2(1 − Θ) ∈ [0, 1], where 1 − Θ is the infimum of the real parts of the nontrivial zeros of ζ(s). Since the functions li −π and M are likely not correlated to more than first order, the equality deg(li −π) = deg M suggests the need for a finer measure of asymptotic behavior, one capable of quantifying such behavior not just relative to power functions, but more broadly to Hardy’s logarithmico-exponential functions [118]. A logarithmico-exponential function is a real function that is defined on a neighborhood of ∞ and can be built from all real constants and the functions id, exp, and log using the operations of addition, multiplication, division, and composition. On the ubiquity of such functions, Hardy remarked that “the only scales of infinity that are of any practical importance in analysis are those which may be constructed by means of the logarithmic and exponential functions” [117, p. 22]. While this assessment might be slightly overstated, the vast corpus of number theory literature reveals that logarithmico-exponential functions indeed offer natural and precise benchmarks against which to compare a vast array of asymptotic behavior. Logexponential degree captures such behavior by ordering functions naturally and linearly. It is defined precisely as follows. Let f be a real function whose domain is a subset of


 0.1. OVERVIEW xi
[−∞, ∞) that is not bounded above, and let T (f ) denote the real function
T (f )(x) =

  
  
f (ex)e−(deg f)x if deg f ̸= ±∞
max(log |f (x)|, 0) if deg f = ∞
−1
log |f (x)| if deg f = −∞,
where again we interpret log 0 = −∞. The logexponential degree of f , denoted ledeg f , is the infinite sequence
ledeg f = (deg f, deg T (f ), deg T (T (f )), deg T (T (T (f ))), . . .) ∈
∞
Y
n=0
[−∞, ∞],
where the product is equipped with the lexicographic (total) ordering. We write ledegk f for the kth coordinate of ledeg f , so in particular ledeg0 f = deg f . Note, for example, that
ledeg(x1/2(log x)−1 log log log x) = (1/2, −1, 0, 1, 0, 0, 0, . . .)
and
ledeg(xe−0.2098(log x)3/5(log log x)−1/5) = (1, −∞, −3/5, 1/5, 0, 0, 0, . . .).
Both of these logarithmico-exponential functions have appeared in the study of the asymptotic behavior of the prime counting function π(x) [185] [93]. Though seemingly ad hoc, the logexponential degree formalism lends itself to a natural axiomatic characterization: see Theorem 6.3.42. Importantly, one has the implications
ledeg f < ledeg g ⇒ f = o(g) ⇒ f = O(g) ⇒ ledeg f ≤ ledeg g,
where the first implication holds if g is logarithmico-exponential. What distinguishes this hierarchy is that o and O are qualitative and partially ordered, while ledeg is quantitative and linearly ordered—not as a single number, but a lexicographically ordered sequence encoding an infinite tower of power-law growth rates. Moreover, the transitions in the hierarchy are not arbitrary: each level in the ledeg sequence reflects a “slower” scale than the prior levels, all arbitrated by the map T . The recursive definition of ledeg reflects extensive trial and refinement; earlier versions the author attempted failed to preserve the analytic-algebraic properties necessary for global coherence across the degree hierarchy. Once established, the formalism opens a path to recasting a vast number of classical problems in more general terms. For example, it uncovers two problems that transcend the Riemann hypothesis: compute the logexponential degree ledeg(li −π) and of ledeg M . Several well-known results in the literature imply the following constraints on the constants Θ1 = ledeg1(li −π) and M1 = ledeg1 M : unconditionally, one has Θ1 ∈ [−∞, 1]; if the Riemann hypothesis is true, then Θ1 ∈ [−1, 1]; if the Riemann hypothesis is false, then Θ1 ∈ [−∞, −1]; if the anti-Riemann hypothesis is true, then Θ1 = M1 = −∞ and ledeg2(li −π) = ledeg2 M ∈ [−1, − 3
5 ]; and if the Riemann hypothesis is true and M1 = 0, then all of the zeros of ζ(s) are simple. Moreover, assuming a 1979 conjecture of Montgomery, one has ledeg(li −π) = ( 1
2 , −1, 0, 2, 0, 0, 0, . . .) [212, Conjecture, p. 16]. Likewise, assuming an unpublished conjecture of Gonek, later supported by Ng [220, (20)], one has ledeg M = (1
2 , 0, 0, 5
4 , 0, 0, 0, . . .). These inferences all motivate the conjecture—backed also by modest numerical data—that Θ1 = −1 and M1 = 0. One of the strengths of the logexponential degree formalism is its ability to express structural relationships among number-theoretic functions—relationships that are often difficult


 xii PREFACE
to formulate or prove using traditional methods. For example, one can relate the logexponential degree of various functions to that of li(x) − π(x), and vice versa. In particular, we accomplish this for each of the functions
pn − li−1(n), x − θ(x), x − ψ(x), eγ Y
p≤x
1− 1
p−1
log x ,
X
p≤x
1
p − log log x − M, e−M Y
p≤x
e1/p − log x, and log x −
X
p≤x
log p
p − B,
where θ and ψ denote the first and second Chebyshev functions, respectively, and γ, M , and B are well-known constants. The formalism also applies to Diophantine approximation. In Chapter 13, we show that the irrationality measure μ(α) of any irrational number α can be interpreted as the degree μ(α) = deg 1
μα(x) = −deg μα(x), where
μα(x) = min
n
α− a
b : a, b ∈ Z, 1 ≤ b ≤ x
o
.
It follows that Roth’s theorem is equivalent to deg 1
μα(x) = 2 for all algebraic irrationals α. Naturally, we define the logexponential irrationality degree of α to be the logexponential degree of 1
μα(x) . We show that, for almost all real numbers α, the logexponential irrationality
degree of α is equal to (2, 1, 1, 1, . . .). This leads us to speculate that this law also holds for the numbers π, γ, log 2, and any other “natural” real number for which the terms of its continued fraction is expected to obey the asymptotic running geometric mean of Khinchin’s constant—including all algebraic numbers of degree greater than two. Yet another application is to the abc conjecture: one can show that it is equivalent to the statement that the lower degree deg ABC(n) of the function
ABC(n) = min{rad(ab(a + b)) : a, b ∈ Z>0, gcd(a, b) = 1, a + b = n}
≤ rad(n − 1) rad(n)
is equal to 1, where rad(n) = Q
p|n p. Known bounds on ABC(n) put constraints and suggest conjectures on what its logexponential degree could be. Such applications demonstrate the utility of the logexponential degree formalism across a vast array of functions in number theory. To manage these effectively, we organize them around a core set of primitives, such as li(x) − π(x), M (x), and 1
μα(x) , in terms of which we express the logexponential degree of many other number-theoretic functions. This strategy both clarifies existing dependencies and reveals new ones, offering a more coherent view of how various number-theoretic functions and error terms in their natural approximations interrelate. The theoretical contributions of this monograph reveal connections between the logexponential degree formalism and real asymptotic differential algebra. For example, we apply the formalism to the study of Hardy fields, and vice versa, where a Hardy field is a subfield of the ring of germs of all real functions at ∞ that is closed under differentiation. We also define logexponential degree formally as a canonical map on the ordered differential field T of well-based logarithmic-exponential transseries. We then compute not only which sequences are equal to ledeg f some function f , but also the image of ledeg on both T and the field L of logarithmico-exponential functions (and we find that the two images coincide). As


 0.2. PREREQUISITES AND TARGET AUDIENCE xiii
one might expect, for example, the logexponential degree of any transseries, hence of any logarithmico-exponential function, ends in a trail of 0s. At its core, algebraic asymptotic analysis retains those aspects of real asymptotic differential algebra governing asymptotic growth and comparison that persist even in the absence of a derivation. Since differentiation still enters into some of its applications—particularly through Karamata theory—connections between logexponential degree and Hardy fields are not unexpected. However, although both frameworks provide canonical models of asymptotic behavior, logexponential degree isolates that behavior without relying on derivational structure. Among the many branches of mathematics, number theory is perhaps unique in that many of its central problems are simple to state yet notoriously difficult to solve. It is likely that newer and more powerful methods are needed to tackle its longstanding problems. Even the slightest improvement in an error bound often demands extraordinary ingenuity. Rather than attempting to sharpen such bounds directly, this text offers a framework for relating them—so that an improvement in one may yield corresponding improvements in others. While our results are unconditional, they also reflect and organize the best known error bounds to date, drawing on the accumulated knowledge of analytic number theory, both classical and contemporary. As a result, the degree framework serves not merely as a technical tool, but as a language for measuring both mathematical and epistemological uncertainty. More precisely, it provides a structure for quantifying, relating, and tracking asymptotic errors across a network of approximations, treating them as functionally and relationally dependent, often in ways previously expressed only heuristically. Ultimately, this offers a refinement in how we describe asymptotic behavior: not merely as a set of binary outcomes, but as a structured space of epistemic and metaphysical possibilities that expresses much of what we understand and seek to understand in precise numerical form.
0.2. Prerequisites and target audience
The target audience for this book is anyone interested in analytic number theoryparticularly those with the equivalent of a Bachelor’s degree in mathematics—as well as researchers and graduate students in analytic number theory, asymptotic analysis, and asymptotic differential algebra. This book connects those three fields but does not assume prior knowledge of any of them. The mathematical prerequisites are elementary number theory, abstract algebra, real and complex analysis, and topology, all at the beginning graduate or advanced undergraduate level. Many standard results from analytic number theory are stated without proof, with citations provided. These results are used as black boxes: techniques like contour integration are rarely unpacked in detail. The goal is not to reconstruct known results, but to develop a complementary framework focused on asymptotic structure. Part 1 of the text is an extenstive introductory survey of analytic number theory written for the non-specialist. It is included not only to make the text more accessible, but also to lay out the results our theory relies on. Classical proofs appear in standard graduate or advanced undergraduate textbooks (e.g., [18] [32] [56] [113] [157] [215] [216] [228] [236] [280] [304]), and proofs of more recent results are always referenced in the bibliography. Table 1.3.2 in Section 1.3 lists several important classical theorems concerning the distribution of the primes, with extensive references to proofs showcasing diverse methods and levels of


 xiv PREFACE
generality. This helps guide the reader into the deeper theory with less risk of privileging one methodological tradition over others.
0.3. Outline of contents
This text is divided into three parts. Part 1 (A survey of analytic number theory) is a survey of analytic number theory at the advanced undergraduate or beginning graduate level. The expert in analytic number theory may skip this part of the book.
Ch. 1. A brief history of primes. Topics include: prime and composite numbers, the fundamental theorem of arithmetic, Mersenne primes, twin primes, prime k-tuples conjecture, Riemann zeta function, arithmetic functions, summatory functions, Dirichlet series, prime listing function pn, prime counting function π(x), prime number theorem, Euler–Mascheroni constant, harmonic numbers, Meissel–Mertens constant, Riemann hypothesis, logarithmic integral function li(x), Riemann’s function Ri(x), Riemann–von Mangoldt explicit formula, prime number theorem with error bound, Riemann constant Θ. Ch. 2. Asymptotic analysis. Topics include: asymptotic relations (O, o, ≍, ∼, Ω+, Ω−, Ω±), asymptotic expansions, asymptotic expansions of π(x), Euler–Maclaurin formula, Stirling’s approximation, the degree deg f of a real function f , slowly varying and regularly varying functions, Karamata’s integral representation theorem and integral theorem. Section 2.3 introduces the new notion of the degree of a real function, and Section 2.4 relates it to the study of regularly varying functions. Ch. 3. Arithmetic functions. Topics include: elementary complex functions, formal Dirichlet series, Dirichlet convolution, ring of arithmetic functions, the rings of multiplicative and additive arithmetic functions, Möbius inversion theorem, Bell series, summatory functions, inversion theorems, Abel’s summation formula, partial summation, Mertens function M (x), first Chebyshev function θ(x), second Chebyshev function ψ(x), Riemann’s prime counting function Π(x), von Mangoldt function Λ(n), average value and average order, Dirichlet hyperbola method, Dirichlet series, abscissa of convergence, Euler products.
Ch. 4. Special functions in analytic number theory. Topics include: the gamma function Γ(s), log-gamma function log Γ(s), digamma function Ψ(s), Riemann zeta function ζ(s), functional equation, zeros of ζ(s), Riemann hypothesis, Riemann xi function ξ(s), prime zeta function P (s), and special functions Ein(s), Ei(s), E1(s), ERi(s), and Ri(x).
Ch. 5. The analytic theory of primes. Topics include: Riemann von–Mangoldt explicit formulas for π0(x), Π0(x) and ψ0(x), prime number theorem with error bound, Riemann–Siegel theta function and Z function, nontrivial zeros of ζ(s), the functions N (T ) and S(T ), Riemann–von Mangoldt formula, Lambert W function, Montgomery’s pair correlation conjecture, abstract analytic number theory, arithmetic semigroup, Dedekind zeta function.
Part 2 (Algebraic asymptotic analysis) extends results in algebraic asymptotic analysis, introduces the notion of logexponential degree, and studies asymptotic continued fraction expansions and their applications to analytic number theory. Most of the results in Part 2 are new.
Ch. 6. Logexponential degree. The results in Chapter 6 comprise the main new analyticalgebraic tools introduced in this book and form the basis for the investigation in


 0.3. OUTLINE OF CONTENTS xv
Parts 2 and 3. The chapter introduces the iterated logarithmic degree and logexponential degree formalisms and states and proves many of their properties, relating them to the various asymptotic relations O, o, ≍, ∼, etc., to the operations +, −, ·, /, and ◦, on functions, and to Hardy’s ordered field L of all logarithmico-exponential functions [117] [118]. Section 6.1 furthers our study of the notions of the degree deg f and lower degree deg f of a real function f and provides some further uses of degree in real and complex analysis. Section 6.3 establishes various fundamental properties of logexponential degree that are used in the remainder of the text. Ch. 7. Asymptotic algebra. Chapter 7 explores applications of the field of asymptotic algebra, e.g., asymptotic differential algebra, to the study of logexponential degree, and vice versa. We use logexponential degree to provide universal properties for some important Hardy fields, including Hardy’s ordered differential field L, and we introduce the notion of the logexponential degree of a logarithmic-exponential transseries. We also provide several axiomatic characterizations of the degree map. Chapter 7 is not used in any later chapters, the only exceptions being the definitions in Section 7.3 of a Hardian function and of the ordered differential field H ⊋ L of all universally Hardian functions, along with Theorem 7.3.19 and Propositions 7.3.14 and 7.5.14. Ch. 8. Asymptotic continued fraction expansions. Chapter 8, which is based on [73] and [74], is a discussion of asymptotic continued fraction expansions and their applications to the prime counting function and related functions. We show, for example, that, for each positive integer n, two well-known continued fraction expansions of the exponential integral function En(z) correspondingly yield two (divergent) asymptotic continued fraction expansions of the prime counting function. Chapter 8 is not used in any later chapters, with the sole exception of Proposition 8.5.5.
Part 3 (Applications of algebraic asymptotic analysis to number theory) applies Parts 1 and 2 to the study of various important functions arising in number theory. The main goal of Part 3 is to expess the logexponential degree of the various functions of arising in number theory in terms of the logexponential degree of f for as few “logexponential primitives” f (e.g., f = li −π) as possible.
Ch. 9. The prime counting function π(x) and related functions. Chapter 9 uses the degree formalisms to study the prime counting function π(x) and various functions closely related to π(x), including the first and second Chebyshev functions θ(x) and ψ(x) and Riemann’s prime counting function Π(x). Ch. 10. Summatory functions. Chapter 10 uses the degree formalisms to study the summatory function P
n≤x f (n) of various arithmetic functions f (n), including the Möbius function μ(n), the Liouville lambda function λ(n), the divisor function d(n), and Euler’s totient φ(n). Ch. 11. The Riemann zeta function ζ(s). Chapter 11 uses the degree formalisms to study the Riemann zeta function ζ(s), the Riemann zeta zero counting functions N (T ) and S(T ), the ordinates γn of the zeros of ζ(s), and the gaps γn+1 − γn between them.
Ch. 12. Primes in intervals, the nth prime, and the nth prime gap. Chapter 12 uses the degree formalisms to study primes in intervals, the prime listing function pn, the prime gap function gn = pn+1 − pn, and the maximal prime gap function G(x) = maxpk≤x gk. Section 12.1 explores the problem of determining which real functions
h satisfy π(x + h(x)) − π(x) ∼ h(x)
log x (x → ∞).


 xvi PREFACE
Ch. 13. Diophantine approximation and continued fractions. Chapter 13 provides applications of degree and logexponential degree to Diophantine approximation and regular continued fractions, e.g., to the study of irrationality measure, Markov constants, Lévy constants, Q-order of convergence, rates of convergence, quadratic irrationals, badly approximable numbers, well approximable numbers, and very well approximable numbers. We show, for example, that the irrationality measure of any irrational number α is equal to deg n
∥nα∥ , where ∥x∥ denotes the distance from x ∈ R to the nearest integer, and we provide several equivalent characterizations of the logexponential degree of n
∥nα∥ . We also pose some conjectures generalizing Roth’s theorem concerning the rational approximation of algebraic numbers. No prior knowledge of Diophantine approximation is assumed in this chapter. Ch. 14. Conjectures. Chapter 14, which is largely data-driven, uses the degree formalisms to express evidence, both numerically and graphically, and in a novel way, for some of the conjectures discussed in this book, including the Riemann hypothesis and various extensions of the Riemann hypothesis.
0.4. Motivation and detailed summary
In this somewhat lengthy technical section, we provide a detailed summary of the text, along with our primary motivations for introducing the notions of degree and logexponential degree. Let π : R≥0 −→ R denote the function that for any x ≥ 0 counts the number of primes less than or equal to x:
π(x) = #{p ≤ x : p is prime}, ∀x ≥ 0.
The function π(x) is known as the prime counting function. The celebrated prime number theorem, proved by de la Vallée Poussin [61] and Hadamard [114] in 1896, states that
π(x) ∼ x
log x (x → ∞),
where log x is the natural logarithm. It is known, however, that the logarithmic integral function
li(x) =
Zx
0
dt
log t , ∀x ≥ 0,
where the Cauchy principal value of the integral is assumed, provides a better approximation to π(x) than any algebraic function of log x. The prime number theorem with error bound, proved by de la Vallée Poussin in 1899 [62], states that the error li(x) − π(x) in the approximation π(x) ≈ li(x) is bounded above by
li(x) − π(x) = O x
eC√log x (x → ∞) (0.4.1)
for some constant C > 0. This has since been improved to
li(x) − π(x) = O x
eA(log x)3/5(log log x)−1/5 (x → ∞), (0.4.2)
where A = 0.2098 [93], which is the strongest known O bound on the error li(x)−π(x) to date. Proofs of such bounds on the error are based on the Riemann–von Mangoldt explicit formula for π(x) in terms of the zeros of the Riemann zeta function ζ(s) [248] and rather sophisticated


 0.4. MOTIVATION AND DETAILED SUMMARY xvii
methods for verifying zero-free regions for ζ(s) in the critical strip {s ∈ C : 0 ≤ Re s ≤ 1}. As is well known, Riemann proved, in his landmark paper [248] of 1859, that the zeros of ζ(s), besides the negative even integers, are all non-real and lie in the critical strip. The non-real zeros of ζ(s), or, equivalently, the zeros of ζ(s) that lie in the critical strip, are known as the nontrivial zeros of ζ(s). The celebrated Riemann hypothesis, conjectured by Riemann in his paper, states that all nontrivial zeros of ζ(s) lie on the critical line {s ∈ C : Re s = 1
2 }. The problem of settling the Riemann hypothesis is widely regarded as one of the most important, if not the most important, unsolved problems in mathematics today. One reason for this is that there are hundreds of statements known to be equivalent to the Riemann hypothesis (many of which are collected in [38] [39]). Thus far, none of them stand out as a “correct” approach, i.e., as an approach that is most likely to lead to an eventual proof or disproof of the conjecture. Many avenues that were once thought promising ultimately were found to be just another reformuation of the same longstanding problem. (In more recent times, mathematicians and physicists have been seeking ways to think about the zeros of ζ(s) from the perspective of quantum physics [23] [25] [209, Part 5] [292] [294].) Probably the most important known equivalent of the Riemann hypothesis was found in 1901, when von Koch proved [153] that the Riemann hypothesis is equivalent to the error bound
li(x) − π(x) = O(√x log x) (x → ∞), (0.4.3)
which to date is the strongest bound on the error li(x) − π(x) that is widely conjectured to hold. Now, let
Θ = sup{Re ρ : ρ ∈ C\R, ζ(ρ) = 0} (0.4.4)
denote the supremum of the real parts of the nontrivial zeros of ζ(s). Well-known results from Riemann’s paper [248] concerning the zeros of ζ(s) imply that
1
2 ≤ Θ ≤ 1,
and that the Riemann hypothesis is equivalent to Θ = 1
2 . It is also well known [215, Theorem 15.2 and Exercise 13.1.1.1] that von Koch’s equivalent (0.4.3) of the Riemann hypothesis generalizes to the fact that Θ is given by
Θ = min t ∈ R : li(x) − π(x) = O(xt log x) (x → ∞) (0.4.5)
and also by
Θ = inf t ∈ R : li(x) − π(x) = O(xt) (x → ∞) . (0.4.6)
Thus, the constant Θ carries vital information about both the Riemann zeta function and the distribution of the prime numbers. Indeed, many known equivalents of the Riemann hypothesis can be generalized to unconditional results concerning the constant Θ, e.g., quintessentially, the Riemann hypothesis equivalent (0.4.3) generalizes to the expressions (0.4.5) and (0.4.6) for Θ. Throughout this book, and following several other authors, like Ingham in [136], we use Θ to denote the constant defined by (0.4.4) above. Because Θ is such an important constant, we also give it a name: the Riemann constant. The results noted above form the basis for the following research program, which is one of our main concerns in Part 3.
Problem 0.4.1. Given a known equivalent of the Riemann hypothesis, generalize the equivalence to an unconditional statement regarding the Riemann constant Θ.


 xviii PREFACE
The results above also serve to motivate a very natural notion of the degree of a real function. Let f : X −→ R be any real function whose domain X is a subset of R that is not bounded above. We define the degree of f to be the extended real number
deg f = inf{t ∈ R : f (x) = O(xt) (x → ∞)} ∈ R = [−∞, ∞],
which, equivalently, can be defined by
deg f = lim sup
x→∞
log |f (x)|
log x .
This notion of degree extends the usual definition of the degree of a polynomial. Given the definition of degree above, statement (0.4.6) concerning the Riemann constant Θ is equivalent to
Θ = deg(li −π).
Statements of the form
f (x) = O(xd+ε) (x → ∞), ∀ε > 0,
and of the form
f (x) = o(xd+ε) (x → ∞), ∀ε > 0,
appear throughout analytic number theory, and it is common but unstated knowledge to analytic number theorists that both of the statements above are equivalent to
lim sup
x→∞
log |f (x)|
log x ≤ d.
Thus, according to our definition of degree, all three of the above statements are equivalent to deg f ≤ d. Loosely speaking, deg f is a measure of the degree of freedom of f , and thus the Riemann constant Θ is a measure of the degree of freedom of li(x) − π(x), i.e., of the degree of freedom that π(x) has relative to li(x). The smaller the Riemann constant, the less the degree of freedom, and the more constrained π(x) is. Another important example of a generalization of a Riemann hypothesis equivalent to a statement about the Riemann constant Θ concerns the Mertens function
M (x) =
X
n≤x
μ(n), ∀x ≥ 0.
It is widely known [38, Theorem 4.16] that the Riemann hypothesis is equivalent to
M (x) = O(x1/2+ε) (x → ∞)
for all ε > 0, which, using our degree terminology, is equivalent to deg M ≤ 1
2 . More generally, it is known, but seldom disclosed in the literature, that
deg M = Θ.
See Theorem 10.2.1 for a sketch of the proof. Yet another illustrative example concerns the Riesz function
F (x) =
∞
X
k=1
(−1)k−1xk
(k − 1)!ζ(2k) = x
∞
X
k=1
μ(k)
k2 e−x/k2 ,
which is an analytic function on all of R, as the given Taylor series has radius of convergence ∞. In [251], Riesz proved that the Riemann hypothesis is equivalent to deg F ≤ 1
4 , which is


 0.4. MOTIVATION AND DETAILED SUMMARY xix
known as the Riesz criterion. A careful reading of the proof reveals that, unconditionally, one has
deg F = Θ
2,
which, of course, implies Riesz’s equivalence. A theme of this book is that the degree formalism and its generalizations to iterated logarithmic degree and logexponential degree are useful for motivating and investigating important questions about various well-studied number-theoretic functions, including the prime counting function π(x), the prime listing function pn, the prime gap function gn = pn+1 − pn, the Möbius function μ(n), the Liouville lambda function λ(n), the divisor function d(n), the prime Omega function Ω(n), the prime omega function ω(n), Euler’s totient φ(n), the Riemann zeta function ζ(s), the Riemann zeta function zero ordinate listing function γn, and the Riemann zeta zero ordinate gap function γn+1 − γn. The degree formalism alone is useful for formulating and gathering numerical and graphical evidence for conjectures. When one is uncertain what the degree of a given function f is (e.g., see Example 0.4.8), it can be helpful to compute or to graph the function
Lf (x) = log |f (x)|
log x
(which is the unique function g(x) satisfying |f (x)| = xg(x)) for as many and as large values of x ∈ dom f as is feasible. Based on such information, one can then try to conjecture what the value of
deg f = lim sup
x→∞
Lf (x)
might be. Let us apply this method to the function li(x) − π(x). Let Ri(x) denote Riemann’s approximation
Ri(x) =
∞
X
n=1
μ(n)
n li(x1/n)
to π(x) [248], which is studied in Section 4.5, where μ(n) denotes the Möbius function. One
has Ri(x) ∼ li(x) (x → ∞) and li(x) − Ri(x) ∼
√x
log x (x → ∞). In Figure 0.4.1 below, we provide graphs of the functions
Lli −π(ex) = log | li(ex) − π(ex)|
x and Lli − Ri(ex) = log | li(ex) − Ri(ex)|
x,
which are just the graphs of the functions Lli −π(x) and Lli − Ri(x) but on a lin-log scale. The constant Θ is exactly the lim sup of the blue curve as x → ∞, that is, one has
Θ = lim sup
x→∞
Lli −π(ex).
Since li(x) − Ri(x) ∼
√x
log x (x → ∞), one has limx→∞ Lli − Ri(ex) = 1
2 . Thus, the black
curve in Figure 0.4.1 tends to 1
2 as x → ∞. Since the Riemann hypothesis is equivalent to
deg(li −π) = 1
2 , the Riemann hypothesis holds if and only if the blue curve has a lim sup
of 1
2 , if and only if the blue curve minus the black curve has a lim sup of 0, as x → ∞. This provides a new way to visualize the Riemann constant Θ, along with the Riemann hypothesis.


 xx PREFACE
Figure 0.4.1. Graphs of Lli −π(ex) and Lli − Ri(ex)
It should be stressed that, at the writing of this book, there is no guarantee that the Riemann hypothesis is true, i.e., that Θ = 1
2 . If the Riemann hypothesis is false, then the most obvious next best guess for Θ is Θ = 1, which we dub the anti-Riemann hypothesis. This hypothesis holds that the prime number theorem with error bound is nearly the best of its kind, and thus the hypothesis seems to be the most compelling alternative to the Riemann hypothesis. A third alternative is that the truth is somewhere in between, i.e.,
1
2 < Θ < 1—perhaps, say, Θ = 2
3 or Θ = π
4 —and the closer Θ is to 1
2 , the closer the Riemann hypothesis is to being true. In particular, the problem of computing the Riemann constant Θ is a natural generalization of the problem of settling the Riemann hypothesis (which asks only whether or not Θ = 1
2 ).
Let us assume for the moment that the Riemann hypothesis is true. Based on values of π(x) that have been either computed or estimated, it might appear that the error bound (0.4.3) from von Koch’s Riemann hypothesis equivalent should be improved (conjecturally)
to li(x)−π(x) = O
√x
log x (x → ∞). In 1910, for example, Hardy wrote that “there is reason
to anticipate that” this error bound holds [117, p. 48]. More recently, in 1994, Riesel wrote: “Judging only from the values [given in a table] we might even try to estimate the order of
magnitude of li(x) − π(x) and find it to be about √x/ log x. However, for large values of x, this is completely wrong!” [250, p. 52]. Indeed, the O bound above fails to hold because of Littlewood’s 1914 result [185] that
li(x) − π(x) = Ω±
√x log log log x
log x (x → ∞), (0.4.7)
where one writes f (x) = Ω±(g(x)) (x → a) if lim supx→a
f (x)
|g(x)| is positive and lim infx→a
f (x) |g(x)|
is negative (both possibly infinite). Today, Littlewood’s result stands as one of a great number of occurrences of iterated logarithms in analytic number theory. Another example, proved by Rankin in 1938 [244], is the result that
pn+1 − pn ̸= o log n log log n log log log log n
(log log log n)2 (n → ∞),
which was strengthened to
pn+1 − pn ̸= o log n log log n log log log log n
log log log n (n → ∞) (0.4.8)
in 2016 by Ford, Green, Konyagin, Maynard, and Tao [96].


 0.4. MOTIVATION AND DETAILED SUMMARY xxi
One of the surprising consequences of Littlewood’s result is that li(x) − π(x) changes sign an infinite number of times, even though no one knows any specific value of x ≥ 2 for which li(x) − π(x) < 0. Even Gauss had been misled into believing that li(x) − π(x) is positive for all x ≥ 2. We now know that the infimum of all x ≥ 2 such that li(x) − π(x) < 0, known as Skewes’ number, is at least 1020 and at most s = 1.3971671494 · 10316 [162]. A lesson one learns from this is that numerical considerations sometimes mean very little in analytic number theory, and this is especially true when iterated logarithms are lurking in the background. Nevertheless, despite these warnings, we make the following conjecture (albeit contingently upon the Riemann hypothesis).
Conjecture 0.4.2. For any real number t, one has
li(x) − π(x) = o √x (log x)t (x → ∞)
if (and only if) t > −1.
The conjecture above expresses the feeling that, if the Riemann hypothesis is true, then the magnitude of li(x) − π(x) should be sufficiently close to
√x
log x without contradicting Littlewood’s result. We also assert, with somewhat less confidence, the following generalization of Conjecture 0.4.2.
Conjecture 0.4.3. For any real number t, one has
li(x) − π(x) = o
√x (log log x)t
log x (x → ∞)
if (and only if) t > 0. Consequently, there exists a δ3 ∈ [1, ∞] such that
li(x) − π(x) = o
√x (log log log x)t
log x (x → ∞)
for all t > δ3 but for no t < δ3.
It is easy to see that Conjecture 0.4.3 implies Conjecture 0.4.2 and, by von Koch’s 1901 result, either conjecture implies the Riemann hypothesis. We should thus qualify these conjectures as contingent on the Riemann hypothesis. The idea motivating Conjectures 0.4.2 and 0.4.3 is that there is an infinite sequence
Θ = δ0, δ1, δ2, δ3, . . . ∈ R
of invariants of li(x) − π(x), where δk, roughly, is the “degree of log◦k x occurring in li(x) − π(x).” Conjecture 0.4.2 (resp., Conjecture 0.4.3) is equivalent to the statement that the sequence δ0, δ1, δ2, δ3, . . . begins 1
2 , −1, δ2, δ3, . . . (resp., 1
2 , −1, 0, δ3, . . .). Here, one has
δk = ldegk(li −π),
where we define ldegk f recursively for any real function f whose domain is a subset of R that is not bounded above, as follows. First, we let f[0] = f . Suppose that f[k] is defined, and set dk = ledegk f = deg f[k]. We then let
f[k+1](x) =
(
f[k](ex)e−dkx if dk ̸= ±∞
f[k](x) if dk = ±∞.
This defines f[k] and ldegk f ∈ R for all nonnnegative integers k. We call ldegk f the (iterated) logarithmic degree of f of order k.


 xxii PREFACE
By definition, the constant δ1 = ldeg1(li −π) is the infimum of all t ∈ R such that
li(x) − π(x) = O xΘ(log x)t (x → ∞),
and (0.4.5) implies that δ1 ≤ 1. If the Riemann hypothesis is true, then Littlewood’s result (0.4.7) requires that δ1 ≥ −1. Thus, Conjecture 0.4.2 is equivalent to the conjecture that Θ= 1
2 (the Riemann hypothesis) and δ1 = −1. Likewise, Conjecture 0.4.3 is equivalent to
the conjecture that Θ = 1
2 , δ1 = −1, and δ2 = 0. On the other hand, it is known [112]
that, if the Riemann hypothesis is false, then li(x) − π(x) = O xΘ
log x (x → ∞) and thus
δ1 ≤ −1. It follows that, if δ1 > −1, then the Riemann hypothesis is true, while if δ1 < −1, then the Riemann hypothesis is false. Any result that were to imply δ1 ̸= −1, then, would have to settle the Riemann hypothesis. However, it is conceivable that improvements on the unconditional inequalities 1
2 ≤ Θ ≤ 1 and δ1 ≤ 1 could be proved absent a proof or disproof of the Riemann hypothesis. To address the possibility that the Riemann hypothesis (and Conjectures 0.4.2 and 0.4.3) may be false, we also assert the following conjecture.
Conjecture 0.4.4. Either the Riemann hypothesis or the anti-Riemann hypothesis is true. Equivalently, either deg(li −π) = 1
2 or deg(li −π) = 1.
In the event that the conjecture above is false, the constant Θ = deg(li −π) would be quite a noteworthy constant, indeed! In Chapter 13, we show that Conjectures 0.4.2 and 0.4.3 are modestly supported by numerical evidence. In Chapter 9, we show that a 1979 conjecture of Montgomery [212, Conjecture, p. 16], namely, that
lim sup
x→∞
x − ψ(x)
√x (log log log x)2 = 1
2π = − lim inf
x→∞
x − ψ(x)
√x (log log log x)2 ,
where
ψ(x) =
∞
X
k=1
X
pk ≤x
log p ∼ x (x → ∞)
is the second Chebyshev function, implies that Conjecture 0.4.3 holds with δ3 = 2 and that the entire sequence of iterated logarithmic degrees is given by 1
2 , −1, 0, 2, 0, 0, 0, . . .. Although Montgomery’s conjecture implies Conjecture 0.4.3 and the latter conjecture provides some support for the former, the motivations for these two conjectures are very different from one another. Indeed, we came to formulate Conjectures 0.4.2 and 0.4.3 several months before we learned of Montgomery’s conjecture, which is a far more ambitious conjecture that was motivated on very different grounds. There are uncountably many possible scenarios in which Conjecture 0.4.3 might hold while Montogomery’s conjecture fails, including the current best case scenario, implied by the conjecture [275, (11)] of Stoll and Demichel, according to which the iterated logarithmic degree sequence for li(x) − π(x) is given by
1
2 , −1, 0, 1, 0, 0, 0, . . .. Furthermore, as discussed throughout this book, whether or not Conjectures 0.4.2 and 0.4.3 are true, the degree concerns that motivate the conjecture illuminate many other fundamental questions regarding various number-theoretic functions besides the prime counting function. A fundamental example of such a problem concerns the Mertens function M (x). Unlike the situation with ldeg1(li −π), no upper bound is known for ldeg1 M , not even on condition of the Riemann hypothesis. Nevertheless, the conjecture [220, (20)] of Gonek and Ng implies


 0.4. MOTIVATION AND DETAILED SUMMARY xxiii
that the entire sequence ldegk M is given by 1
2 , 0, 0, 5
4 , 0, 0, 0, . . ., while conjectures of Good
and Churchhouse [104] and Lévy [259] imply that the sequence is given by 1
2 , 0, 1
2 , 0, 0, 0, . . .. This provides modest support for the following conjecture.
Conjecture 0.4.5. One has deg M = 1
2 and ldeg1 M = 0. Equivalently, one has M (x) =
o(√x (log x)t) (x → ∞) if (and only if) t > 0.
Note that, by Theorem 10.2.7 of Section 10.2, if Conjecture 0.4.5 holds, then the Riemann hypothesis holds and all of the zeros of the Riemann zeta function are simple. Now, let f be any real function whose domain is a subset of R that is not bounded above. In order to better handle situations where ldegk f = ±∞ for some k, we define a natural refinement ledeg f of ldeg f , as follows. Let f(0) = f . Suppose that f(k) is defined, and set dk = ledegk f = deg f(k). We then let
f(k+1)(x) =

  
  
f(k)(ex)e−dkx if dk ̸= ±∞
max(log |f(k)(x)|, 0) if dk = ∞
−1
log |f(k)(x)| if dk = −∞.
This defines ledegk f ∈ R for all nonnnegative integers k. We call ledegk f the logexponential degree of f of order k. Also, we write
ledeg f = (ledeg0 f, ledeg1 f, ledeg2 f, . . .) ∈
∞
Y
n=0
R
and
ldeg f = (ldeg0 f, ldeg1 f, ldeg2 f, . . .) ∈
∞
Y
n=0
R,
which we call the logexponential degree of f and the (iterated) logarithmic degree of f , respectively. We also endow the set Q∞
n=0 R with the lexicographic (total) ordering. Note that, if ldegk f ̸= ±∞ for all k < n, then ledegk f = ldegk f for all k ≤ n. However, if ldegn f = ±∞, then ledegn+1 f might not equal ldegn+1 f , and the definition of f(n+1)(x) as above is designed to “tame” the function f(n) by applying a log to |f(n)| appropriately. Thus, ldeg f is tantamount to the truncation of ledeg f at the nth coordinate for the smallest n, if any, such that ledegn f = ±∞. Note that
ledeg(f + g) ≤ max(ledeg f, ledeg g)
provided that dom f ∩ dom g is not bounded above. Moreover, f (x) = O(g(x)) (x → ∞) implies ledeg f ≤ ledeg g, which in turn implies ldeg f ≤ ldeg g. The seemingly ad hoc definition of ledeg is motivated by the following examples.
Example 0.4.6.
(1) For every positive integer n, let T (n) = #{ab : a, b ∈ {1, 2, 3, . . . , n}} denote the number of distinct integers in the n × n multiplication table. In 2008, Ford proved [95] that
T (n) ≍ n2
(log n)c(log log n)3/2 (n → ∞),


 xxiv PREFACE
where
c = 1 − 1 + log log 2
log 2 = 0.086071332055 . . . .
From this it follows that ledeg T = (2, −c, − 3
2 , 0, 0, 0, . . .).
(2) By (0.4.2), one has ledeg(li −π) ≤ (1, −∞, − 3
5, 1
5 , 0, 0, 0, . . .). Moreover, Littlewood’s
result (0.4.7) implies that ledeg(li −π) ≥ ( 1
2 , −1, 0, 1, 0, 0, 0, . . .). (3) Walfisz showed in [284] that
M (x) = O x
eA(log x)3/5(log log x)−1/5 (x → ∞),
for some A > 0. From this it follows that ledeg M ≤ (1, −∞, − 3
5, 1
5 , 0, 0, 0, . . .).
(4) The arithmetic function d(n) = P
d|n 1 is called the divisor function, since d(n) equals the number of positive divisors of n. [121, Theorem 317] states that
lim sup
n→∞
log d(n) log log n
log n = log 2,
which implies that ledeg d(n) = (0, ∞, 1, −1, 0, 0, 0, . . .). (5) Let f (x) be the function that on the interval [N, N + 1) assumes the value ex for even integers N and e−x2 for odd integers N . One has ledeg f = (∞, 1, 0, 0, 0, . . .), since the function max(log |f (x)|, 0) has logexponential degree (1, 0, 0, 0, . . .). The function log |f (x)|, on the other hand, has logexponential degree (2, 0, 0, 0, . . .). (6) Let f (x) be the function that on the interval [N, N +1) assumes the value e−x for even integers N and e−x2 for odd integers N . One has ledeg f = (−∞, −1, 0, 0, 0, . . .), since the function − 1
log |f(x)| has logexponential degree (−1, 0, 0, 0, . . .). The function
log |f (x)|, on the other hand, has logexponential degree (2, 0, 0, 0, . . .).
Examples (5) and (6) above provide some explanation as to why we defined f(k+1)(x) as we did in the definition of ledeg f , rather than, say, as log |f (x)|, when deg f(k) = ±∞. Our results in Chapter 6, which comprise the main new analytic-algebraic tools introduced in this book, demonstrate that the logexponential degree formalism is quite natural, and, in some sense, inevitable. Theorem 6.3.42, for example, provides a natural axiomatization of logexponential degree. In Chapter 7, we characterize the degree map “universally” in various ways, and we apply logexponential degree to the study of Hardy fields, logarithmic-exponential transseries, and real asymptotic differential algebra more broadly. In the remainder of this section, we provide some evidence for the main thesis of this text, namely, that the degree and logexponential degree formalisms are useful in analytic number theory. Our quintessential example concerns the prime counting function, to which we associate the invariants
Θk = ledegk(li −π) ∈ R
for all k. The Riemann constants Θk provide fine-tuned information about the difference li −π, more so than do the constants δk = ldegk(li −π). For several important numbertheoretic functions f , we are able to express all of the constants ledegk f in terms of the constants Θk and vice versa. Examples include the following.
Example 0.4.7. Let k be a nonnegative integer.


 0.4. MOTIVATION AND DETAILED SUMMARY xxv
(1) One has
ledegk(x − ψ(x)) =
(
Θk if k ̸= 1
Θk + 1 if k = 1,
where ψ(x) is the second Chebyshev function. (2) Let pn for every positive integer n denote the nth prime. It is well known that the prime number theorem is equivalent to pn ∼ n log n (n → ∞). However, the function li−1 n ∼ n log n is a much better approximation to pn than is n log n, where li−1 : R −→ (1, ∞) is the inverse of the restriction of the logarithmic integral function li to the interval (1, ∞). We show in Section 12.2 that
ledegk(pn − li−1 n) =
(
Θk if k ̸= 1
Θk + Θ + 1 if k = 1,
and thus, in particular, Θ = deg(pn − li−1 n). (3) In Section 10.1, we prove that
ledegk
X
p≤x
1
p − log log x − M
!
=
(
Θk − 1 if k = 0
Θk if k ≥ 1,
where
M = xli→m∞
X
p≤x
1
p − log log x
!
= 0.261497212847 . . . (0.4.9)
is the Meissel–Mertens constant. Similarly, we prove that
ledegk eγ Y
p≤x
1− 1
p−1
log x
!
=
(
Θk − 1 if k ≤ 1
Θk if k ≥ 2.
(4) Since one has Ri(x) ∼ li(x) (x → ∞) and li(x)−Ri(x) ∼
√x
log x (x → ∞), Littlewood’s
theorem (0.4.7) yields
ledegk(li −π) = ledegk(Ri −π)
for all k. Thus, although numerical evidence suggests that Riemann’s function Ri(x) is a better approximation of π(x) than is li(x), it is no better in the long run, at least with respect to the logexponential degree formalism.
The operations ldeg and ledeg not only facilitate the proofs of various degree relationships, as in the examples above, but they also yield some new relations between functions: one has the irreversible implications
ldeg f < ldeg g =⇒ ledeg f < ledeg g
=⇒ f (x) = o(g(x)) (x → ∞)
=⇒ f (x) = O(g(x)) (x → ∞)
=⇒ ledeg f ≤ ledeg g
=⇒ ldeg f ≤ ldeg g,
where the second implication holds provided that the function g is sufficiently nice, e.g., if g can be can be built from all real constants and the functions id, exp, and log using the


 xxvi PREFACE
operations +, ·, /, and ◦. Examples throughout this text, including Example 0.4.7 above, show that the six relations above are all distinct. For example, one has
ledeg(li −π) = ledeg(Ri −π) = ledeg pn − li−1 n
(log n)Θ+1 = ledeg x
X
p≤x
1
p − x log log x − M x
!
,
but none of these four functions is O of the others. Thus, the notions of degree, iterated logarithmic degree, and logexponential degree serve not only to quantify the asymptotic growth of real functions, including those arising prominently in number theory, but they also provide natural benchmarks for comparing the asymptotic behavior of such functions. The following examples provide further indication that computing the degree, no less the logexponential degree, of a given number-theoretic function is quite often a difficult problem.
Example 0.4.8.
(1) Let gn = pn+1 − pn denote the nth prime gap. It is known [15] that
gn = O((n log n)21/40) (n → ∞).
In [53], Cramér proved on condition of the Riemann hypothesis that
gn = O(n1/2(log n)3/2) (n → ∞).
Thus, one has
ledeg gn ≤ ( 21
40 , 21
40 , 0, 0, 0, . . .),
while also
ledeg gn ≤ ( 1
2, 3
2 , 0, 0, 0, . . .)
on condition of the Riemann hypothesis. It is conjectured, however, that gn = O((log n)t) (n → ∞) for all t > 2, or, equivalently, that deg gn = 0 and ledeg1 gn ≤ 2. Computing deg gn, no less ledegk gn for all k, is a difficult open problem.
(2) Let L(r) equal the number of lattice points in Z2 lying on or inside the circle in R2 of radius r centered at the origin. It is straightfoward to show that L(r) ∼ πr2 (r →
∞). Let H(r) = L(r) − πr2. Gauss proved that |H(r)| ≤ 2√2πr for all r and therefore H(r) = O(r) (r → ∞). The Gauss circle problem is (equivalent to) the problem of computing deg H. Hardy and Landau proved that
H(r) ̸= o(r1/2(log r)1/4) (r → ∞),
from which it follows that
ledeg H ≥ ( 1
2, 1
4 , 0, 0, 0, . . .).
In 2003, Huxley proved [134] that H(r) = O(r131/208(log r)18627/8320) (r → ∞) and therefore deg H ∈ [ 1
2 , 131
208 ] and
ledeg H ≤ ( 131
208 , 18627
8320 , 0, 0, 0, . . .).
It is widely conjectured that deg H = 1
2.
(3) Using what we now call the Dirichlet hyperbola method (Proposition 3.7.4), Dirichlet proved that
X
n≤x
d(n) = x log x + (2γ − 1)x + O(xt) (x → ∞)


 0.4. MOTIVATION AND DETAILED SUMMARY xxvii
for t = 1
2 . The Dirichlet divisor problem is the problem of determining the infimum of all such t for which the O bound above holds, which is equal to the degree deg D of the function D(x) = P
n≤x d(n) − x log x − (2γ − 1)x. Hardy proved in 1914 that
D(x) = Ω±(x1/4) (x → ∞).
It follows that deg D ∈ [ 1
4, 1
2 ] and
ledeg D ≥ ( 1
4 , 0, 0, 0, . . .).
In 2003, Huxley used the same methods in his approach to the Gauss circle problem to show [134] that
D(x) = O(x131/416(log x)26947/8320) (x → ∞)
and therefore deg D ∈ [ 1
4 , 131
416 ] and
ledeg D ≤ ( 131
416 , 26947
8320 , 0, 0, 0, . . .).
It is widely conjectured that deg D = 1
4.
(4) An integer a is said to be a primitive root modulo p, where p is prime, if a generates the (cyclic) group (Z/pZ)∗ of units in the field Z/pZ. Let g(p) denote the smallest positive primitive root mod p. In 1962, Burgess proved [42] that
deg g(p) ≤ 1
4.
Moreover, Fridlander (1949) and Salié (1950) proved that g(p) ̸= o(log p) (p → ∞), and therefore
ledeg g(p) ≥ (0, 1, 0, 0, 0, . . .).
Shoup, in 1990–92, proved that g(p) = O((log p)6) (p → ∞), and therefore
ledeg g(p) ≤ (0, 6, 0, 0, 0, . . .),
provided that the extended Riemann hypothesis is true [266, Theorem 1.3]. It is thus widely conjectured that deg g(p) = 0. (5) An integer a not divisible by p, where p ̸= 2 is prime, is said to be a quadratic residue modulo p if there exists an integer x such that x2 ≡ a (mod p), and a quadratic non-residue modulo p if a is not a quadratic residue modulo p. The smallest positive quadratic non-residue np modulo p is always a prime number less than p. In 1957, Burgess proved [41] that
deg np ≤ 1
4√e .
Vinogradov’s conjecture is (equivalent to) the statement that deg np = 0. In 2001, Wedeniwski proved in his doctoral thesis that np < 3
2 (log p)2 for all primes p > 3, provided that the generalized Riemann hypothesis is true. A lower bound for the growth of np, due to Chowla, is
np ̸= o(log p) (p → ∞),
which Montgomery, in 1971, proved can be strengthened to
np ̸= o(log p log log p) (p → ∞)


 xxviii PREFACE
on condition of the generalized Riemann hypothesis. Thus, under the generalized Riemann hypothesis, one has
(0, 1, 1, 0, 0, 0, . . .) ≤ ledeg np ≤ (0, 2, 0, 0, 0, . . .).
See [205] for an account of these results, in historical context, along with some explicit inequalities for np. (6) Given relatively prime positive integers a and d with 1 ≤ a ≤ d, let p(a, d) denote the smallest prime in the arithmetic progression a, a + d, a + 2d, a + 3d, a + 4d, . . .. Linnik’s theorem states that there exist positive constants C and L such that p(a, d) ≤ CdL for all relatively prime positive integers a and d with 1 ≤ a ≤ d [188] [189]. Equivalently, it says that the function
p(d) = max{p(a, d) : 1 ≤ a ≤ d, gcd(a, d) = 1}
is O(dL) for some L, that is, deg p(d) is finite. It is known that L = 5 is admissible, and thus
ledeg p(d) ≤ (5, 0, 0, 0, . . .).
According to [246, p. 282], in 1961–62, Prachar and Schinzel proved that
p(d) ̸= o d log d log log d log log log log d
(log log log d)2 (d → ∞),
from which it follows that
ledeg p(d) ≥ (1, 1, 1, −2, 1, 0, 0, 0, . . .).
The constant deg p(d) ∈ [1, 5] is known as Linnik’s constant [246, p. 279]. In 1934, Chowla conjectured that deg p(d) = 1 [47]. In 1963, Kanold conjectured that p(d) ≤ d2 for all d, or equivalently that, for all positive integers a and d with gcd(a, d) = 1, there is at least one prime among the numbers a, a + d, a + 2d, . . . , a + (d − 1)d [147]. According to [246, pp. 280–283], Schinzel and Sierpiński (in 1958) and Kanold (in 1963) conjectured that deg p(d) = 2, while Heath-Brown (in 1978) conjectured that p(d) = O(d(log d)2) (d → ∞) and therefore ledeg p(d) ≤ (1, 2, 0, 0, 0, . . .). In 1992, Heath-Brown proved [124] that the generalized Riemann hypothesis implies that p(d) = O(φ(d)2(log d)2) (d → ∞), where φ is Euler’s totient, and therefore that ledeg p(d) ≤ (2, 2, 0, 0, 0, . . .). Thus, the conjecture that deg p(d) ≤ 2 is implied by any of the conjectures noted above. In 1990, Granville and Pomerance conjectured the lower bound p(d) ≫ φ(d)(log d)2 (d → ∞) [109], which, if true, would yield ledeg p(d) ≥ (1, 2, 0, 0, 0, . . .).
(7) The irrationality measure μ(α) of an irrational number α is the infimum of all t > 0 such that there are only finitely many pairs (a, b) of integers a and b with b > 0 and
α− a
b <1
bt .
We show in Section 13.2 that, for any irrational number α, one has
μ(α) = deg n
∥nα∥ = deg 1
min α − a
b : a, b ∈ Z and 1 ≤ b ≤ x < ∞,
where ∥x∥ for any x ∈ R is the distance from x to the nearest integer. Although it is known that μ(α) = 2 for all irrationals α outside a set of Lebesgue measure 0, and also that μ(α) = 2 for all algebraic numbers α and for α = e, the irrationality


 0.4. MOTIVATION AND DETAILED SUMMARY xxix
measure of many important transcendental numbers, like π and log 2, is unknown. The tightest known bounds for μ(π), for example, are μ(π) ∈ [2, 7.103205334137 . . .] [303]. In Section 13.4, we prove several equivalent characterizations of the logexponential degree ledeg n
∥nα∥ = ledeg 1
min{|α− a
b |:a, b ∈ Z and 1 ≤ b ≤ x} , which we prove is equal to (2, 1, 1, 1, . . .) for all irrationals α outside a set of Lebesgue measure 0. (8) The radical of a positive integer n, denoted rad(n), is the product Q
p|n p of the distinct prime factors of n. The abc conjecture states that, for every t > 1, there exist only finitely many triples (a, b, c) of mutually prime positive integers such that a + b = c > rad(abc)t. It is an extremely important conjecture in Diophantine analysis and has many deep consequences, both known and conjectured. Let ABC(n) denote the maximal value of c = a + b over all relatively prime positive integers a, b such that rad(abc) = n; that is, let
ABC(n) = max{a + b : a, b ∈ Z>0, gcd(a, b) = 1, rad(ab(a + b)) = n}.
It is known that ABC(n) < ∞ for all n. Moreover, the abc conjecture is equivalent to deg ABC = 1 and thus also to
ledeg ABC ≤ (1, ∞, 1, 0, 0, 0, . . .).
To date, the tightest known bounds for ledeg ABC are
(1, 0, ∞, 1
2 , −1, 0, 0, 0, . . .) ≤ ledeg ABC ≤ (∞, 1
3 , 3, 0, 0, 0, . . .),
A conjecture of van Frankenhuysen (1995), supported by Robert, Stewart, and Tenenbaum (2014), along with heuristics and numerical evidence, implies that
ledeg ABC = (1, 0, ∞, 1
2, −1
2 , 0, 0, 0, . . .).
This leads us to conjecture, more modestly, that deg ABC(n) = 1 and ledeg1 ABC(n) = 0, that is, that
ABC(n) = O(n(log n)t) (n → ∞)
if (and only if) t > 0. Equivalently, this conjecture states that
ledeg ABC(n) ≤ (1, 0, ∞, 1, 0, 0, 0, . . .),
or, equivalently still, that for every ε > 0, there exist only finitely many triples (a, b, c) of mutually (or pairwise) relatively prime positive integers with a + b = c > rad(abc) · (log rad(abc))ε. Note that the abc conjecture is also equivalent to deg 1
ABC(n) = −1, where
ABC(n) = min{rad(abc) : a, b ∈ Z>0, gcd(a, b) = 1, a + b = c = n}.
One moral to be drawn from these examples is that, in number theory, an unknown logexponential degree is usually expected to be much closer to its best known lower bound than its best known upper bound, to several terms. In other words, we expect that our current machinery is better at saying how bad our best approximations are than it is in saying how good they truly are; intuitively, this means that we expect that lots of “cancellations” are happening in our equations and inequalities that we do not yet know how to explain. A research program initiated in Part 3 of this text is to express the logexponential degree of the various real functions arising in number theory in terms of ledeg f for as few “logexponential primitives” f as possible. Additionally, given a real number-theoretic


 xxx PREFACE
function f , one seeks a “nice” function g, i.e., a function g within a specified class F of “wellbehaved” functions defined in a neighborhood of ∞, so that ledeg(f − g) < ledeg g, which is a stronger condition than f (x) ∼ g(x) (x → ∞). Ideally, one would like to find a g ∈ F that minimizes ledeg(f − g), but, currently, most such problems of interest are intractable. One might rightfully demand an explanation as to why logexponential degree is relevant to number theory at all. One explanation for this is that the notion of logexponential degree is intimately connected to Hardy’s field of all logarithmico-exponential functions [117] [118], that is, the field of all germs of real functions that are defined on a neighborhood of ∞ and can be can be built from all real constants and the functions id, exp, and log using the operations +, ·, /, and ◦. Indeed, several of our results in Chapters 6 and 7 (e.g., Theorem 6.3.26 and Proposition 7.5.14) show that the logexponential degree of a real function captures information about the asymptotic growth rate of the function in comparison to the logarithmico-exponential functions. Moreover, as suggested by Hardy [117, p. 22], the logarithmico-exponential functions offer precise benchmarks against which to compare the order of growth of nearly any function in number theory that one might be interested in. Nevertheless, how well such functions can approximate the more complicated functions of number theory, such as li −π and pn+1 − pn, remains to be seen. Broadly speaking, occurrences of iterated logarithms in analytic number theory asymptotics can be classified into one of two types: those that are essential, and those that are artifacts of our existing machinery for bounding various number-theoretic functions. Essential occurrences of the two-fold iterated logarithm log log abound. Examples include the law of the iterated logarithm [88], Example 3.7.2(3), Remark 3.7.6, the asymptotic expansion of
pn
log n in Example 2.2.7, examples (1) and (4) of Example 0.4.6, examples (4), (7), (10), and
(11) of Example 6.3.2, and the definition (0.4.9) of the Meissel–Mertens constant M . The occurrence of log log in the last of these examples is motivated by Cramér’s model of the primes, a heuristic model of the primes in which the “probability” that an integer n > 1 is prime is 1
log n . Indeed, Cramér’s model suggests that the sum P
p≤x
1
p can be approximated by
P
1<n≤x
1
n log n , hence also by R x
e
dt
t log t = log log x. Cramér’s model also suggests two readily verified essential occurrences of log log log, namely, that the limit
xli→m∞
X
p≤x
1
p log log p − log log log x
!
,
and thus also the limit
xli→m∞
X
p≤x
1
p
P
p′≤p
1 p′
− log log log x
!
,
exists. Likewise, the limits
xli→m∞
X
p≤x
1
p log log p log log log p − log log log log x
!


 0.4. MOTIVATION AND DETAILED SUMMARY xxxi
and
xli→m∞

  
X
p≤x
1
p
P
p′≤p
1 p′
P
p′≤p
1 p′ P
p′′≤p′ 1
p′′
− log log log log x

  
exist, and so on. Admittedly, these last examples are somewhat artificial. Some natural occurrences of log log log, on the other hand, are conjectured to be essential, e.g., by Montgomery’s conjecture [212, Conjecture, p. 16] and by the conjecture [220, (20)] of Gonek and Ng. However, the majority of currently known occurrences of log log log, log log log log, and beyond are unlikely to be essential occurrences (although Example 6.3.2(11) is another exception). P. Nielsen notes in [221] that the iterated logs in (0.4.8), for example, come from “the current state of the art sieve methods, together with bounding techniques. When you solve for the best fit functions to undo some of the exponentiation that occurs in calculations, the logs just fall out. In these types of problems, it is not inconceivable (and actually occurs quite regularly) that one new idea is applied to the problem, and the asymptotic changes (sometimes involving more multi-log factors, to account for the small additional room for improvement that was gained).” Although the logexponential degree formalism does not explain why iterated logarithms arise in analytic number theory, or why logarithmico-exponential functions are so prevalent, it at least provides a new way of delineating such occurrences and establishing their various interrelationships in order to explain how they proliferate. Perhaps neither degree nor logexponential degree have been defined or studied before because our ignorance even of deg f is so great for so many number-theoretic functions f that we care about. Such problems draw attention to the rather humbling fact that our ignorance is much greater than that revealed by problems like the Riemann hypothesis, the Dirichlet divisor problem, and the Gauss circle problem. One at least can be hopeful that future solutions to these difficult problems may at the same time shed light on the accompanying logexponential degress of higher order—as would happen, for example, if something close to Montgomery’s conjecture [212, Conjecture, p. 16] or the conjecture [220, (20)] of Gonek and Ng were someday to be resolved in the positive.
Remark 0.4.9 (The ANTEDB). In late January 2025, the author learned of a recent project of Terence Tao, Timothy Trudgian, and Andrew Yang, namely, the Analytic Number Theory Exponent Database, or ANTEDB (currently housed at https://github.com/teorth/expdb), which they describe as an “ongoing project to systematically record known theorems for various exponents appearing in analytic number theory, as well as the relationships between them.” Their notion of exponent is more general, though informal, than our notion of degree. While this book relates asymptotic invariants regardless of tractability, the ANTEDB project catalogs and improves the best known explicit bounds on invariants that are amenable to study with our current machinery.
Key properties of logexponential degree. Below we state the key properties of ledeg that are proved in Sections 6.3, 7.5, and 7.6 and that are used throughout Part 3. Since the proofs in Part 2 are somewhat technical, the reader may choose to take these properties as given and read Part 3 after just skimming, or even skipping, Part 2.


 xxxii PREFACE
First, we require some notation. The set Q∞
n=0 R is equipped with the lexicographic order and endowed with the product topology where each factor R has the discrete topology. Let
∞∗
Y
n=0
R⊊
∞
Y
n=0
R
denote the set of all sequences d = (di) in Q∞
n=0 R satisfying the following four conditions for all nonnegative integers n.
(1) If dn = ∞, then d ≥ (d0, d1, . . . , dn, 0, 1, 0, 0, 0, . . .). (2) If dn = −∞, then d ≤ (d0, d1, . . . , dn, 0, −1, 0, 0, 0, . . .).
(3) If dn is finite and dn+1 = ∞, then d ≤ (d0, d1, . . . , dn+1, 1, 0, 0, 0, . . .). (4) If dn is finite and dn+1 = −∞, then d ≥ (d0, d1, . . . , dn+1, −1, 0, 0, 0, . . .).
For all d, e ∈ Q∞
n=0 R, we define:
d⊕e=d+e
if dk and ek are finite for all k, and
d ⊕ e = (d0 + e0, . . . , dn−1 + en−1, f0, f1, f2, . . .)
if n is the smallest nonnegative integer such that dn and en are not both finite, where
(f0, f1, f2, . . .) =
(
max((dn, dn+1, . . .), (en, en+1, . . .)) if dn = ∞ or en = ∞
min((dn, dn+1, . . .), (en, en+1, . . .)) otherwise
as computed in Q∞
n=0 R. The operation ⊕ is a binary operation on Q∞
n=0 R and restricts to
a binary operation on Q∞∗
n=0 R.
We say that f has exact degree if limx→∞
log |f (x)|
log x exists or is ±∞. We say that f has
exact logexponential degree if T ◦n(f ) has exact degree for all n. If f is not eventually zero, we let ledeg f = − ledeg(1/f ); otherwise, we let ledeg f = (−∞, −∞, −∞, . . .). Let f and g be real functions with dom f ∩ dom g containing a subset X of R that is not bounded above. One has the following.
(1) Degree compatibility: If ledeg f = d, then d0 = deg f .
(2) Exp shifting: Let d = ledeg f . If deg f = 0, then ledeg(f ◦ exp) = (d1, d2, . . .). If deg f > 0 and limx→∞ f (x) = ∞, then ledeg(exp ◦f ) = (∞, d0, d1, . . .). (3) Log shifting: Let d = ledeg f , and let log+ x = max(log x, 0). If deg f = ∞, then ledeg(log+ ◦|f |) = (d1, d2, d3, . . .). If deg f = −∞, and ledeg(1/ log ◦|f |) = (d1, d2, d3, . . .). If deg f ∈ R, then ledeg(f ◦ log) = (0, d0, d1, d2, . . .).
(4) Exactness equivalence: f has exact logexponential degree if and only if ledeg f = ledeg f .
(5) Exactness of L: One has T (f ) ∈ L for all f ∈ L, and every f ∈ L has exact degree; thus, every f ∈ L has exact logexponential degree.
(6) O compatibility: If f (x) = O(g(x)) (x → ∞), then ledeg f ≤ ledeg g.
(7) o compatibility: Suppose that g is eventually defined on dom f . If ledeg f < ledeg g and g has exact logexponential degree, then f (x) = o(g(x)) (x → ∞). More generally, if ledeg f < ledeg g, then f (x) = o(g(x)) (x → ∞).
(8) Nonarchimedean property: One has ledeg(f + g) ≤ max(ledeg f, ledeg g). (9) Submultiplicativity: One has ledeg(f g) ≤ ledeg f ⊕ ledeg g.


 0.4. MOTIVATION AND DETAILED SUMMARY xxxiii
(10) Exact multiplicativity: If g has exact logexponential degree, and if exactly one of ledegn f and ledegn g is finite for the least n, if any, for which at least of them is finite, then ledeg(f g) = ledeg f ⊕ ledeg g.
(11) Composition: Suppose that f and g are both defined on a neighborhood of ∞ and satisfy the following conditions. (a) f has finite degree d. (b) g has positive degree and is eventually positive. (c) g(x) ≍ r(x) (x → ∞) for some r ∈ L. (d) Either f has exact logexponential degree or g is eventually continuous and increasing. Then one has
ledeg(f ◦ g) = ledeg f ⊕ d · ledeg g + (−1, 0, 0, 0, . . .) .
(12) Compositional inversion: If f is increasing and unbounded of finite positive degree with ledeg f = d (resp., ledeg f = d), then the inverse function f −1 exists, is increasing and unbounded, and has lower logexponential degree ledeg(f −1) = d′ (resp., logexponential degree ledeg f −1 = d′) given by
d′ = 1
d0 , − d1
d0 , − d2
d0 , − d3
d0 , . . . ,
where each coordinate is given as above until the first k, if any, such that dk = ±∞, after which tail of d′ is exactly the negated tail of d, that is, d′
j = −dj for all j ≥ k. (13) Restriction compatibility: ledeg f |X ≤ ledeg f .
(14) Arithmetic function extendibility: If f is an arithmetic function, then ledeg f = ledeg f (⌊x⌋) = ledeg f (⌈x⌉).
(15) Majoration: Suppose that f is unbounded, but bounded on [N, x] ∩ X for all x ≥ N , and let
fe(x) = sup
t∈[N,x]∩X
|f (t)|, ∀x ∈ [N, ∞) ∩ X.
Then ledeg fe = ledeg f .
(16) Admissibility: One has ledeg RR∞ = Q∞∗
n=0 R. In fact, for any sequence d ∈
Q∞
n=0 R, one has d = ledeg f for some f ∈ RR∞ if and only if d ∈ Q∞∗
n=0 R, if and only if d = ledeg f for some positive, monotonic, infinitely differentiable function f on R>0 of exact logexponential degree. (17) Completeness and denseness: The poset ledeg RR∞ is order-wise dense and complete, and ledeg L>0 is both order-wise dense and topologically dense in ledeg RR∞. (18) Reducibility to L: One has
ledeg f = inf{ledeg r : r ∈ L>0, f (x) = O(r(x)) (x → ∞)}
= inf{ledeg r : r ∈ L>0, ∀x ≫ 0 |f (x)| ≤ r(x)}
= inf{ledeg r : r ∈ L>0, f (x) = o(r(x)) (x → ∞)}
= inf{ledeg r : r ∈ L>0, ledeg f < ledeg r},
where the infima (exist and) are computed in Q∞∗
n=0 R.
(19) Stabilization on L: If f ∈ L, then ledeg f eventually stabilizes to (0, 0, . . .), that is, there exists an N such that ledegk f = 0 for all k ≥ N .


 xxxiv PREFACE
See Tables 0.4.1 and 0.4.2 for a list of some important symbols and terms defined and used in this text. Tables 0.4.3, 0.4.4, and 0.4.5 provide a list of many of the degree theorems and conjectures in analytic number theory that are discussed in this book. Note that, if the third column in a given row is empty, then the given result is unconditional. Functions in the tables whose degrees are unknown include li(x) − π(x), the Mertens function M (x), the functions P
n≤x d(n) − x log x − (2γ − 1)x, P
n≤x μ2(n) − 6
π2 x, and P
n≤x φ(n) − 3
π2 x2, the function ζ(σ + ix) for a fixed σ ∈ R, and the prime gap function gn = pn+1 − pn. The logexponential degrees of all other functions appearing in the tables are expressed in terms of the logexponential degrees of those particular functions, along with the Riemann zeta zero ordinate gap function γn+1 − γn and the function S(T ).


 0.4. MOTIVATION AND DETAILED SUMMARY xxxv
Table 0.4.1. Definitions of some important symbols and terms
Symbol Definition Name
R R ∪ {∞, −∞} set of all extended real numbers RR∞ the set of all real functions f with sup dom f = ∞ L the field of (germs at ∞ of) all real functions that can the field of (germs at ∞ of) all be built from all constants and the functions id, exp, logarithmico-exponential functions and log using the operationas +, ·, /, and ◦ F ◦k kth iterate of F f (x) = O(g(x)) ∃M > 0 : |f (x)| ≤ M |g(x)| for all x in the intersection f (x) is big O of g(x) as x → a (x → a) of dom f with some punctured neighborhood of a f (x) ≪ g(x) f (x) = O(g(x)) (x → a) (x → a)
f (x) ≫ g(x) ∃M > 0 : |f (x)| ≥ M |g(x)| for all x in the intersection (x → a) of dom f with some punctured neighborhood of a f (x) ≍ g(x) f (x) ≪ g(x) (x → a) and f (x) ≫ g(x) (x → a) (x → a)
f (x) = o(g(x)) ∀M > 0 : |f (x)| ≤ M |g(x)| for all x in the intersection f (x) is little o of g(x) as x → a (x → a) of dom f with some punctured neighborhood of a
f (x) ∼ g(x) f (x) − g(x) = o(g(x)) (x → a) f (x) is asymptotic to g(x) as x → a (x → a)
f (x) = Ω+(g(x)) ∃M > 0 : for all x in a punctured neighborhood of a f (x) is Omega plus of g(x) as x → a (x → a) ∃y ̸= a closer to a than x such that f (y) > M |g(y)| f (x) = Ω−(g(x)) ∃M > 0 : for all x in a punctured neighborhood of a f (x) is Omega minus of g(x) as x → a (x → a) ∃y ̸= a closer to a than x such that f (y) < −M |g(y)|
f (x) = Ω±(g(x)) f (x) = Ω+(g(x)) (x → a) and f (x) is Omega plus minus of g(x) (x → a) f (x) = Ω−(g(x)) (x → a) as x → a deg f inf{t ∈ R : f (x) = O(xt) (x → ∞)} degree of f = lim supx→∞
log |f (x)| log x
deg f sup{t ∈ R : f (x) ≫ xt (x → ∞)} lower degree of f = lim infx→∞ log |f (x)|
log x deg f limx→∞ log |f (x)|
log x exact degree of f
T (f )

   
   
f (ex)e−(deg f)x if deg f ̸= ±∞ max(log |f (x)|, 0) if deg f = ∞
−1
log |f (x)| if deg f = −∞
ledeg f (deg f, deg T (f ), deg T (T (f )), deg T (T (T (f ))), . . .) logexponential degree of f ledegk f deg T ◦k(f ) = kth coordinate of ledeg f logexponential degree of f of order k f(k) T ◦k(f ) f (x) ≃ P∞
n=1 anφn(x) f (x) = Pn
k=1 akφk(x) + o(φn(x)) (x → a) for all f (x) has the asymptotic expansion (x → a) n ∈ Z>0
P∞
n=1 anφn(x) at a with respect to {φn} Sf (x) P
n≤x f (n) summatory function of f
Df (X) P∞
n=1 f (n)n−X formal Dirichlet series of f Df (s) P∞
n=1
f (n)
ns Dirichlet series of f
(f ∗ g)(n) P
ab=n f (a)g(b) Dirichlet convolution of f and g
ζ(s) meromorphic continuation of P∞
n=1
1
ns to C Riemann zeta function P (s) P
p
1
ps prime zeta function
Γ(s) meromorphic continuation of R ∞
0 xse−x dx
x to C gamma function
Ψ(s) Γ′(s)
Γ(s) digamma function
Ei(s) R s
−∞
ez
z dz exponential integral function
li(x) R x
0
dt
log t = Ei(log x) logarithmic integral function
ERi(s) P∞
n=1
μ(n)
n Ei s
n Ri(x) P∞
n=1
μ(n)
n li(x1/n) = ERi(log x) Riemann’s function
W (x) inverse of the restriction of xex to [−1, ∞) Lambert W function π(x) P
p≤x 1 = #{p ≤ x : p is prime} prime counting function p(x) π(x)
x prime density function
θ(x) P
p≤x log p first Chebyshev function ψ(x) P∞
k=1
P
pk≤x log p = P∞
k=1 θ(x1/k) second Chebyshev function pn nth prime number (= inf{x ∈ R : π(x) ≥ n}) prime listing function gn pn+1 − pn nth prime gap G(x) maxpk≤x gk = maxk≤π(x) gk maximal prime gap function


 xxxvi PREFACE
Table 0.4.2. Definitions of some important symbols and terms
Symbol Definition Name
γn ordinate of the nth nontrivial zero of ζ(s)
τn γn
2π
γbn τn log τn
e + 11
8
N (T ) #{ρ ∈ C : ζ(ρ) = 0, Im ρ ∈ (0, T ]} S(T ) 1
π arg ζ 1
2 + iT , where the argument is chosen to be 0 at ∞ + iT and to vary continuously on the line from ∞ + iT to 1/2 + iT vp(n) exponent of p in the prime factorization of n p-adic valuation Ω(n) P
p|n vp(n) prime Omega function ω(n) P
p|n 1 prime omega function
μ(n)
(
(−1)Ω(n) = (−1)ω(n) if n is squarefree
0 if n is not squarefree Möbius function λ(n) (−1)Ω(n) Liouville function φ(n) #(Z/nZ)∗ = #{k ∈ Z>0 : k ≤ n, gcd(k, n) = 1} Euler’s totient σa(n) P
d|n da generalized sum of divisors function d(n) σ0(n) = #{d ∈ Z>0 : d | n} divisor function σ(n) σ1(n) = P
d|n d sum of divisors function
Hn
Pn k=1
1
n nth harmonic number
M (x) P
n≤x μ(n) Mertens function L(x) P
n≤x λ(n) summatory Liouville function Θ sup{Re s : s ∈ C, ζ(s) = 0} = deg(li −π) Riemann constant
Θk ledegk(li −π) kth Riemann constant
Θ−1 sup
n
t ∈ R : li(x) − π(x) ≪ xe−(log x)t (x → ∞)
o
anti-Riemann constant
γ limx→∞
P
n≤x
1
n − log x = lims→1 ζ(s) − 1
s−1 Euler–Mascheroni constant
M limx→∞
P
p≤x
1
p − log log x Meissel–Mertens constant
H −P
p
1
p + log 1 − 1
p = R∞
1
li(t)−π(t)
t2 dt = γ − M Mertens constant
B limx→∞ log x − P
p≤x
log p p
μ unique positive zero of li(x) Ramanujan–Soldner constant ⌊α⌋ max{n ∈ Z : n ≤ α} floor of α ⌈α⌉ min{n ∈ Z : n ≥ α} ceiling of α {α} α − ⌊α⌋ fractional part of α ∥α∥ min{|α − n| : n ∈ Z} = min({α}, 1 − {α}) distance from α to the nearest integer
S(α)
(1
α−⌊α⌋ if α ∈/ Z ∪ {∞}
∞ if α ∈ Z ∪ {∞}. regular continued fraction operator
an(α) S◦n(α) nth term of regular continued fraction of α pn(α), qn(α) pn(α)
qn(α) = [a0(α), a1(α), . . . , an(α)], gcd(pn(α), qn(α)) = 1, qn(α) > 0
ord1 α #((1, α)Z/Z) order of α modulo 1 |α|1 1
ord1 α = inf (1, α)Z ∩ R>0
α ≫1 f |α − r| < f (ord1 r) for only finitely many r ∈ Q μ(α) inf{t ∈ R : α ≫1 n−t} irrationality measure of α M (α) inf t ∈ R>0 : α ≫1 1
t n−2 Markov constant of α
m(α) inf t ∈ R>0 : α ≫1 1
t n−μ(α) relativized Markov constant of α
λ(α) limn→∞ 1
n log qn(α) Lévy constant of α
λ(α; β) lim supn→∞
log qn(α)
log qn(β) upper relative Lévy constant of α with respect to β λ(α; β) lim infn→∞ log qn(α)
log qn(β) lower relative Lévy constant of α with respect to β Q{αn}n sup{c ∈ [1, ∞) : |α − αn+1| = O (|α − αn|c) (n → ∞)} Q-order of convergence of {αn}n
Q(α) Q
n pn(α) qn (α)
o
n
R(α) lim supn→∞
α− pn(α)
qn (α)
α− pn+1(α)
qn+1 (α)
Bk(α) lim supn→∞
qn+k (α) qn (α)
μμμ(α) inf{ledeg f : f ∈ L>0 and α ≫1 1/f |Z>0 } logexponential irrationality degree of α


 0.4. MOTIVATION AND DETAILED SUMMARY xxxvii
Table 0.4.3. Degree theorems and conjectures in analytic number theory
Degree Equals Assuming
deg(li −π) Θ = supρ: ζ(ρ)=0 Re ρ ∈ [ 1
2 , 1]
deg(li −π) 1
2 RH (Riemann hypothesis) deg(li −π) 1 ARH (Anti-Riemann hypothesis) ledeg1(li −π) ≤ 1 ledeg1(li −π) ∈ [−1, 1] RH ledeg1(li −π) ∈ [−∞, −1] ¬RH ledeg1(li −π) −∞ ARH
ledeg2(li −π) ∈ [−1, − 3
5 ] ARH
ledeg(li −π) ≥ ( 1
2 , −1, 0, 1, 0, 0, 0, . . .) ledeg(li −π) ≤ (Θ, 1, 0, 0, 0, 0, . . .) ledeg(li −π) ≤ (1, −∞, − 3
5, 1
5 , 0, 0, 0, . . .)
ledeg(li −π) ≤ (Θ, −1, 0, 0, 0, . . .) ¬RH ledeg(li −π) (Θ, −1, 0, 0, 0, . . .) ¬RH, and ∃ρ : ζ(ρ) = 0, Re ρ = Θ ledeg(li −π) ≥ (1, −∞, −1, 0, 0, 0, . . .) ARH ledeg(li −π) ( 1
2 , −1, Θ2, Θ3, . . .), Θ2 ≥ 0 Conjecture 0.4.2
ledeg(li −π) ( 1
2 , −1, 0, Θ3, Θ4, . . .), Θ3 ≥ 1 Conjecture 0.4.3 ledeg(id −θ) ledeg(li −π) + (0, 1, 0, 0, . . .) ledeg(id −ψ) ledeg(id −θ) ledeg(P
ρ
xρ
ρ ) ledeg(id −ψ) ledeg(ψ − θ) ( 1
2 , 0, 0, 0, . . .)
ledeg(li − Ri) ( 1
2 , −1, 0, 0, 0, . . .) ledeg(Ri −π) ledeg(li −π) ledeg(li −Π) ledeg(li −π) ledeg(Ri −Π) ledeg(li −π) ledeg(id −ψ) ( 1
2 , 0, 0, 2, 0, 0, 0, . . .) (9.3.5) (Montgomery)
ledeg(li −π) ( 1
2 , −1, 0, 2, 0, 0, 0, . . .) (9.3.5) (Montgomery)
ledeg(li −π) ( 1
2 , −1, 0, 1, 0, 0, 0, . . .) (9.1.1) (Stoll and Demichel) deg M deg(li −π)
ledeg1 M ∈ [m − 1, ∞] RH, and ζ(s) has a zero of order m
ledeg M ≥ ( 1
2 , 0, 0, 0, . . .)
ledeg M ≤ (1, −∞, − 3
5, 1
5 , 0, 0, 0, . . .)
ledeg M ≥ (1, −∞, −1, 0, 0, 0, . . .) ARH ledeg M ( 1
2 , 0, 0, 5
4 , 0, 0, 0, . . .) (14.3.1) (Gonek and Ng)
ledeg M ( 1
2 , 0, 1
2 , 0, 0, 0, . . .) (14.3.2) (Good, Churchhouse, Lévy)
ledeg M ≥ ( 1
2 , 0, 0, 1
2 , 0, 0, . . .) (14.3.5) (Kotnik and van de Lune)
ledeg M ( 1
2 , 0, d2, d3, . . .) Conjecture 0.4.5
ledeg


X
ρ
xρ
ρζ ′ (ρ)

 ledeg M RH, and the zeros of ζ(s) are simple
ledeg

π(etn) −
X
μe−t ≤k<n
et
Hk − γ + t

, t ∈ R ledeg(li −π)
ledeg


X
p≤x
1
p − log log x − M

 ledeg(li −π) + (−1, 0, 0, 0, . . .)
ledeg


X
p≤x
log 1 − 1
p + log log x + γ

 ledeg(li −π) + (−1, 0, 0, 0, . . .)
ledeg


1 s
X
p≤x
log 1 − s
p + log log x + G(s)

 ledeg(li −π) + (−1, 0, 0, 0, . . .)
ledeg

eγ Y
p≤x
1− 1
p−1
log x

 ledeg(li −π) + (−1, −1, 0, 0, 0, . . .)
ledeg

e−γ Y
p≤x
1− 1
p
−1
− log x

 ledeg(li −π) + (−1, 1, 0, 0, 0, . . .)


 xxxviii PREFACE
Table 0.4.4. Degree theorems and conjectures in analytic number theory
Degree Equals Assuming
ledeg

log x −
X
p≤x
log p
p −B

 ledeg(li −π) + (−1, 1, 0, 0, 0, . . .)
ledeg

e−M Y
p≤x
e1/p − log x

 ledeg(li −π) + (−1, 1, 0, 0, 0, . . .)
ledeg


X
n≤x
d(n) − x log x − (2γ − 1)x

 ≥ (1
4 , 0, 0, 0, . . .)
ledeg


X
n≤x
d(n) − x log x − (2γ − 1)x

 ≤ ( 131
416 , 26947
8320 , 0, 0, 0, . . .)
deg


X
n≤x
d(n) − x log x − (2γ − 1)x


1
4 widely conjectured
deg


X
n≤x
μ2(n) − 6
π2 x

 ∈ [1
4, 1
2]
deg


X
n≤x
μ2(n) − 6
π2 x

 ∈ [1
4 , 11
35 ] RH
ledeg


X
n≤x
φ(n) − 3
π2 x2

 ≥ (1, 0, 1
2 , 0, 0, 0, . . .)
ledeg


X
n≤x
φ(n) − 3
π2 x2

 ≤ (1, 2
3, 1
3 , 0, 0, 0, . . .)
ledeg


X
n≤x
φ(n) − 3
π2 x2

 (1, 0, 1, 0, 0, 0, . . .) (10.3.1) and (10.3.2) (Montgomery)
ledeg


X
n≤x
φ(n)
n −6
π2 x

 ledeg


X
n≤x
φ(n) − 3
π2 x2

 + (−1, 0, 0, 0, . . .)
deg ζ(σ + ix), σ ∈ R 0 if σ ≥ 1
2 , and 1
2 − σ if σ ≤ 1
2 Lindelöf hypothesis
deg ζ( 1
2 + it) ≤ 13
84
deg ζ( 1
2 + it) 0 Lindelöf hypothesis
ledeg ζ( 1
2 + it) ≥ (0, ∞, 1
2,−1
2, 1
2 , 0, 0, 0, . . .)
ledeg ζ( 1
2 + it) ≤ (0, ∞, 1, −1, 0, 0, 0, . . .) RH
ledeg ζ( 1
2 + it) (0, ∞, 1
2, 1
2 , 0, 0, 0, . . .) (11.1.1) (Farmer, Gonek, Hughes) ledeg ζ(1 + it) ≥ (0, 0, 1, 0, 0, 0, . . .) ledeg ζ(1 + it) (0, 0, 1, 0, 0, 0, . . .) RH ledeg S ≤ (0, 1, 0, 0, 0, . . .) ledeg S ≥ (0, 1
3,−1
3 , 0, 0, 0, . . .)
ledeg S ≤ (0, 1, −1, 0, 0, . . .) RH ledeg S ≥ (0, 1
2,−1
2, 1
2 , 0, 0, 0, . . .) RH
ledeg S (0, 1
2, 1
2 , 0, 0, 0, . . .) (14.4.1) (Farmer, Gonek, Hughes) ledeg S(γn) ledeg S ledeg(n − γbn) ledeg S ledeg(2πrn − γn) ledeg S + (0, −1, 0, 0, 0, . . .) ledeg(γn+1 − γn) ≥ (0, −1, 0, 0, 0, . . .) ledeg(γn+1 − γn) ≤ (0, 0, 0 − 1, 0, 0, 0, . . .) ledeg(γn+1 − γn) ≤ (0, 0, −1, 0, 0, 0, . . .) RH ledeg(γn+1 − γn) (0, − 1
2 , 0, 0, 0, . . .) (14.4.3) (Arous and Bourgade) ledeg1(γn+1 − γn) > −1 Conjecture 14.4.2 ledeg δn ledeg(γn+1 − γn) + (0, 1, 0, 0, 0, . . .) ledeg(γbn+1 − γbn) ledeg(γn+1 − γn) + (0, 1, 0, 0, 0, . . .) ledeg(pn − li−1 n) ledeg(li −π) + (0, Θ + 1, 0, 0, 0, . . .) ledeg(pn − Ri−1 n) ledeg(li −π) + (0, Θ + 1, 0, 0, 0, . . .)


 0.4. MOTIVATION AND DETAILED SUMMARY xxxix
Table 0.4.5. Degree theorems and conjectures in analytic number theory
Degree Equals Assuming
ledeg(li(pn) − n) ledeg(li −π) + (0, Θ, 0, 0, 0, . . .) ledeg(Ri(pn) − n) ledeg(li −π) + (0, Θ, 0, 0, 0, . . .) ledeg(x − pli(x)) ledeg(li −π) + (0, 1, 0, 0, 0, . . .) ledeg(x − pRi(x)) ledeg(li −π) + (0, 1, 0, 0, 0, . . .) deg gn ≤ 1
2 density hypothesis deg gn 0 Conjecture 12.3.5 (Piltz) ledeg gn ≤ ( 21
40 , 21
40 , 0, 0, 0, . . .)
ledeg gn ≥ (0, 1, 1, −1, 1, 0, 0, 0, . . .) ledeg gn ≤ ( 1
2, 3
2 , 0, 0, 0, . . .) RH
ledeg gn ≤ (0, 2, ∞, 1, 0, 0, 0, . . .) (14.6.4) (Pintz) ledeg G ledeg gn + (0, − deg gn, 0, 0, 0, . . .)
deg G(ex) 2 Conjecture 14.6.3 (Maynard) ledeg(x − pπ(x)) ledeg G deg n
∥nα∥ μ(α) ledeg n
∥nα∥ μμμ(α)
deg 1
min α − a
b : a, b ∈ Z and 1 ≤ b ≤ x μ(α)
ledeg 1
min α − a
b : a, b ∈ Z and 1 ≤ b ≤ x μμμ(α) − sup{deg f : f : Z>0 −→ R>0 and α ≫1 f } μ(α) − sup{ledeg f : f : Z>0 −→ R>0 and α ≫1 f } μμμ(α)
μμμ(α) = (2, 1, 1, 1, . . .) for almost all α ∈ R μμμ(α) ≥ (2, 0, 0, 0, . . .) for all irrational α μμμ(α) = (2, 0, 0, 0, . . .) for all real algebraic numbers α of degree 2 μμμ(e) (2, 1, −1, 0, 0, 0, . . .) μμμ(π), μμμ(log 2), μμμ(γ) (2, 1, 1, 1, . . .) Conjecture 13.4.21 μμμ(α) ≤ (2, 1, 1, 1, . . .) for all real algebraic Conjecture 13.4.25 numbers α μμμ(α) = (2, 1, 1, 1, . . .) for all real algebraic Conjecture 13.4.30 numbers α of degree > 2
deg min{rad(ab(a + b)) : a, b ∈ Z>0, 1 abc conjecture gcd(a, b) = 1, a + b = n} ledeg min{rad(ab(a + b)) : a, b ∈ Z>0, ≤ (1, 0, −∞, − 1
2 , 1, 0, 0, 0, . . .) gcd(a, b) = 1, a + b = n} ledeg min{rad(ab(a + b)) : a, b ∈ Z>0, ≥ (−∞, − 1
3 , −3, 0, 0, 0, . . .) gcd(a, b) = 1, a + b = n} ledeg min{rad(ab(a + b)) : a, b ∈ Z>0, (1, 0, −∞, − 1
2, 1
2 , 0, 0, 0, . . .) 1995 conjecture of gcd(a, b) = 1, a + b = n} van Frankenhuysen


 xl PREFACE
0.5. Notation and conventions
In this section, we discuss some notation and conventions that are assumed throughout the text. An index of symbols and an index of terms appear at the end of the book.
Numbers. As is standard, we let Z, Q, R, and C denote the ring of all integers, the field of all rational numbers, the field of all real numbers, and the field of all complex numbers, respectively. We let Z≥0 denote the set of all nonnegative integers, and we let Z>0 denote the set of all positive integers. We also use self-explanatory notations like R≥1, Q<0, and so on. We also let P denote the set of all prime numbers. For any x ∈ R, a neighborhood of x is a subset of R containing an interval of the form (a, b) for some a, b ∈ R with a < x < b, while a punctured neighborhood of x is a subset of R containing an interval of the form (a, b)\{x} = (a, x) ∪ (x, b) for some a, b ∈ R with a < x < b. A (punctured) neighborhood of ∞ is a subset of R containing the interval (a, ∞) for some a ∈ R, while a (punctured) neighborhood of −∞ is a subset of R containing the interval (−∞, a) for some a ∈ R. The structure
R = R ∪ {∞, −∞} = [−∞, ∞]
of all extended real numbers ordered by ≤ is complete as a totally ordered set. Endowed with the order topology, it is a compact topological space, isomorphic to [0, 1] ⊊ R. It is “almost” a field, with exceptions made for the usual indeterminate forms, e.g., ∞ + (−∞), 0 · ∞, and ∞
∞ , which are undefined. If X is a subset of R or R, then we write X for the
closure of X in R. Thus, for example, one has ∞ ∈ X if and only X contains an unbounded set of positive real numbers (i.e., sup X = ∞) or ∞ ∈ X. If X ⊆ R is nonempty, then X is the union of the closure of X in R with {sup X, inf X}. We use the expression “for all x ≫ 0” to mean “for all sufficiently large x,” i.e., “there exists an N > 0 such that for all x ≥ N .” Also, we say that a given property expressed in terms of x holds “eventually” if it holds for all x ≫ 0. However, in some contexts these notions are also used relativized to the domain of any of the functions involved.
Sets and functions. The cardinality of a set X is denoted #X. For any sets X and Y , we let Y X denote the set of all functions from X to Y . The identity function on a set X is denoted id = idX. We write dom f , codom f and im f for the domain, codomain, and range of a function f . The expression “f is defined on X” means that X is a subset of the domain of f . If f is defined on X, then we write f |X for the restriction f |X : X −→ codom f of f to the set X. We sometimes abuse notation by writing f = g when f and g are functions with dom g ⊇ dom f and f (x) = g(x) for all x ∈ dom f . If f and g are functions, then we assume that the composition f ◦ g has domain {x ∈ dom g : g(x) ∈ dom f } = g−1(dom f ∩ codom g) = g−1(dom f ∩ im g) and codomain codom f . For all nonnegative integers k, we denote the kth iterate f ◦ f ◦ · · · ◦ f of a function f by f ◦k. Thus, for example, the kth iterate log◦k of log has domain (exp◦(k−1)(0), ∞) for all positive integers k. If the compositional inverse f −1 of f exists, then we write f ◦(−k) = (f −1)◦k. If ∗ is an associative binary operation, written multiplicatively, on a set S, then for all x ∈ S we denote by x∗n the n-fold ∗-product x ∗ x ∗ · · · ∗ x. A real function is a function with domain a subset of R and codomain a subset of R; a complex function is a function with domain a subset of C and codomain a subset of C; and a complex-valued function of a real variable is a function with domain a subset of R and codomain a subset of C. For any such functions f and g, unless otherwise stated,


 0.6. ACKNOWLEDGMENTS xli
we assume that the functions f + g, f − g, and f · g have domain dom f ∩ dom g, and the function f /g has domain dom f ∩ {x ∈ dom g : g(x) ̸= 0} = (dom f ∩ dom g)\g−1({0}).
For functions f of a real variable, we often require the assumption ∞ ∈ dom f , or equivalently, sup dom f = ∞, i.e., the domain of f is a subset of R that is not bounded above. We also let RR∞ denote the set of all real functions f with ∞ ∈ dom f . More generally, for any a ∈ R, we let RRa denote the set of all real functions f such that a is a limit point of dom f . We consider all limits, limits superior, and limits inferior to be relativized to the domain of the function involved. Thus, for example, for all f ∈ RR∞ we write limx→∞ f (x) = L if for every ε > 0 there exists an N > 0 such that |f (x) − L| < ε for all x ∈ dom f with x > N . Specifically for the purpose of studying degree, we extend the definitions of limx→a f (x), lim supx→a f (x), and lim infx→a f (x) to functions f of a real variable having values in R. The extended definitions for “extended real valued functions” still require that a ∈ dom f , but where dom f may include values of x such that f (x) = ±∞. Thus, for example, if f (x) = ∞ for some unbounded set of values of x > 0, then lim supx→∞ f (x) = ∞.
We also set the conventions log |0| = log(0+) = −∞, log ∞ = ∞, and e−∞ = 0. Thus, if f is a real function, then log |f (x)| is a function of a real variable, with the same domain as f , that assumes values in the extended reals, where log |f (x)| is finite if and only if f (x) ̸= 0. For all x ∈ R, the floor of x, denoted ⌊x⌋, is the largest integer less than or equal to x, the ceiling of x, denoted ⌈x⌉, is the smallest integer greater than or equal to x (and is equal to −⌊−x⌋), and the fractional part of x, denoted {x}, is equal to x − ⌊x⌋.
Other conventions. All rings are assumed commutative with identity. If R is a ring, then R+ denotes the group R under addition, while R× denotes the monoid R under multiplication and R∗ denotes the group of units of R under multiplication. We use the bold letters, like d and e, to denote tuples with coordinates dn and en, respectively, indexed by the nonnegative integers. In all finite or infinite sums and products with dummy variable “p,” the values of p are restricted to the primes, taken in succession. Thus, for example, P
p
1
p2 represents the sum
1
22 + 1
32 + 1
52 + 1
72 + 1
112 + · · · .
A term (or phrase) that is being defined precisely is written in boldface. Technical terms for which we do not provide the definition are written in italics, and in such cases their definition can be found in Wikipedia. A term is also written in italics if it is defined precisely later in the text (in which case it will appear in the index), or if it is being singled out for emphasis. Ultimately, theorems, propositions, lemmas, and corollaries are all theorems, and their labelling as such is a matter of taste. A “Remark” is a relevant but parenthetical comment that can be skipped over without loss of continuity. A “Problem” is a newly posed problem that the author was unable to solve, while an “(Outstanding) Problem” is also a Problem, but its solution necessitates the solution of some longstanding open problem, such as the Riemann hypothesis.
0.6. Acknowledgments
I would like to thank my family, especially my mother, Nancy (Elliott) Cappello, for all of their support through some difficult times. This book would not have been possible without them. I would also like to thank my former teachers who helped inspire my passion for


 xlii PREFACE
mathematics, writing, and teaching, most especially, John Foley and Jean Jonker of Holyoke High School, and my former MIT professors James Munkres, Michael Artin, Haynes Miller, Gian-Carlo Rota, and George Boolos. I would like to thank the late Doug Stoll for assisting me with some of the data analysis and graphs concerning the function V (x) provided in Sections 1.3 and 13.2, for correcting some of my miscalculations in Mathematica regarding the function G(s) in Section 8.5, and for carrying out several time-consuming computations. I would also like to thank Grant Molnar for reading and providing corrections and extensive comments on an early draft of the book. Finally, I would like to thank the following former students of mine for collecting and analyzing data and for creating some of the graphs in Section 5.3 and Chapter 14, as a part of semester-long undergraduate research classes in Spring 2022: Noah Browne and Paul Kime at CSU Channel Islands, and Alexa Alcala, Aditya Baireddy, Sudhanva Kulkarni, Lucas Salim, Christopher Silbermann, and Haolin Zhang at UC Berkeley. All graphs in this book were created using Mathematica.
0.7. About the author
Jesse Elliott is a professor of mathematics and philosophy at California State University, Channel Islands. He was born and raised in Massachusetts and received a BS in Mathematics in 1995 from the Massachusetts Institute of Technology. In 2003, he completed a PhD in Mathematics from the University of California, Berkeley, under the advisorship of Hendrik W. Lenstra, Jr. His areas of research are algebra, number theory, and the foundations and philosophy of mathematics. His first book, Rings, Modules, and Closure Operations, published by Springer in 2019, is a research monograph on the applications of closure operations to the study of rings and modules.
0.8. Publication
This book is scheduled to be published as Volume 13 of World Scientific’s Monographs in Number Theory Series. Due to a severe illness, I am not certain that I will be able to complete the lengthy publication process. World Scientific has graciously agreed to allow me to post this unofficial draft to the arXiv. Once the process (hopefully) is complete, the book will be available at the link below.
https://www.worldscientific.com/worldscibooks/10.1142/13521#/t=aboutBook.


 Part 1
A survey of analytic number theory


 

 CHAPTER 1
A brief history of primes
In this chapter, we provide a brief history of the mathematical study of the prime numbers. Nearly all of the results described in this chapter are well known by analytic number theorists and are stated without proof. In subsequent chapters, some of these results are proved.
1.1. The prime numbers, algebraically
A positive integer is said to be prime if it is greater than 1 and has two and only two positive divisors, namely, 1 and itself, and a positive integer is said to be composite if it is greater than 1 but not prime and thus has a positive divisor other than 1 and itself. Prime numbers have been the subject of intense study for at least two millenia. In Book 7 of Euclid’s Elements, for example, one finds an ingenious proof of the fundamental theorem of arithmetic, and another of the infinitude of the set of all primes. The fundamental theorem of arithmetic is the statement that every positive integer N can be written as a product of primes (an empty product in the case N = 1, and a product of one prime in the case where N is prime), and, moreover, the prime factorization of N is unique if the prime factors are listed in nondecreasing order. The prime numbers, therefore, are like “multiplicative atoms,” and positive integers are like “molecules” that can be built up uniquely from such atoms. In other words, the prime numbers are the “multiplicative building blocks” of the positive integers. The list of positive integers in terms of their prime factorizations proceeds as follows:
1, 2, 3, 2 · 2, 5, 2 · 3, 7, 2 · 2 · 2, 3 · 3, 2 · 5, 11, 2 · 2 · 3, 13, 2 · 7, 3 · 5, 2 · 2 · 2 · 2, 17,
2 · 3 · 3, 19, 2 · 2 · 5, 3 · 7, 2 · 11, 23, 2 · 2 · 2 · 3, 5 · 5, 2 · 13, 3 · 3 · 3, 2 · 2 · 7, 29, 2 · 3 · 5, . . . .
Analogously, the number 1 is the one and only “additive atom” of the nonnegative integers, and the list of the nonnegative integers in terms of their “additive building blocks” proceeds as follows:
0, 1, 1 + 1, 1 + 1 + 1, 1 + 1 + 1 + 1, 1 + 1 + 1 + 1 + 1, . . . .
The 25 prime numbers less than 100 are
2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97.
The number 1 is neither prime nor composite: it is not considered to be prime, because if it were prime then the number 2 could be factored as a product 2 · 1 · 1 of three primes, or four primes, etc., which would invalidate the fundamental theorem of arithmetic. Of course, 2 is the only even prime, just as 3 is the only prime divisible by 3, and 5 is the only prime divisible by 5, and so on. It follows that 2 and 3 are the only consecutive integers both of which are prime. Since among any three consecutive odd integers, exactly one is divisible by 3, the numbers 3, 5, and 7 are the only three consecutive odd integers all three of which are prime.
3


 4 1. A BRIEF HISTORY OF PRIMES
See The PrimePages: prime number research & records (https://t5k.org) for the latest records concerning the prime numbers. A Mersenne number is a number of the form 2k − 1 for some positive integer k, or, equivalently, a number whose binary expansion is a sequence of all 1s. Currently, the largest known and verified prime number, found in 2018, is the Mersenne prime 282589933 − 1, which has 24862048 digits, or, in binary, 82589933 bits. Note that, if the Mersenne number 2k − 1 is prime, then k must be prime, since 2a − 1 divides 2ab − 1 for all a, b ∈ Z>0. Note also that 82589933 is the 4811740th prime. Fast algorithms are known for testing Mersenne numbers for primality, so much so that the size of known Mersenne primes vastly outstrips the size of known non-Mersenne primes. Currently there are 51 known Mersenne primes, the smallest 18 of which are 2p − 1 for p equal to
2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607, 1279, 2203, 2281, 3217.
The 17 largest known Mersenne primes were all discovered by the Great Internet Mersenne Prime Search (GIMPS), a distributed computing projec founded in 1996. The first and smallest of these 17 Mersenne primes, namely, 21398269 − 1, was discovered on November 13, 1996. To this day, no one has yet proved or disproved Mersenne’s conjecture that there are infinitely many Mersenne primes. Nevertheless, the consensus among number theorists is that Mersenne’s conjecture is very likely to be true. One reason that the prime numbers are so fascinating is the fact that, not only are there infinitely many of them, but various statements as to how they are distributed are extremely beautiful and profound, and yet, more often than not, are extremely difficult to prove. There are many easily formulated conjectures about the prime numbers, such as Mersenne’s conjecture, that have been open for centuries. The centuries-old twin prime conjecture is the statement that there are infinitely many twin primes, where twin primes are pairs of consecutive odd integers both of which are prime. Examples of small twin primes are 11 and 13, and 101 and 103. Currently, the largest known twin primes, discovered in 2016, are
2996863034895 · 21290000 ± 1,
which have 388342 digits. Very little progress was made on the twin prime conjecture until J. R. Chen proved in 1966 that there are infinitely many prime numbers p such that p + 2 is either prime or semiprime, where a semiprime is a positive integer that is a product of two primes. More recently, in 2013, the groundbreaking work of Y. Zhang, along with subsequent work by J. Maynard, T. Tao and others, resulted in a proof that there are infinitely many primes that differ at most by 246, or, in analytic terms,
2 ≤ lim inf
n→∞ (pn+1 − pn) ≤ 246,
where pn denotes the nth prime. The twin prime conjecture, on the other hand, is equivalent to the statement that
lim inf
n→∞ (pn+1 − pn) = 2.
Not only is the twin prime conjecture widely believed true, but it is believed also that there are infinitely many prime triplets, that is, triples of primes of the form (p, p+2, p+6) or (p, p + 4, p + 6). For example, the six prime triplets of the first form are
(5, 7, 11), (11, 13, 17), (17, 19, 23), (41, 43, 47), (101, 103, 107), (107, 109, 113),
and the first six prime triplets of the second form are
(7, 11, 13), (13, 17, 19), (37, 41, 43), (67, 71, 73), (97, 101, 103), (103, 107, 109).


 1.1. THE PRIME NUMBERS, ALGEBRAICALLY 5
As of October 2020, the largest known proven prime triplet contains primes with 20008 digits, namely the primes (p, p + 2, p + 6) with
p = 411128692197 · 266420 − 1.
One can generalize the notions of twin primes and prime triplets as follows. If a given k-tuple has infinitely many translations whose coordinates are all prime, then there cannot exist a prime p such that the set of all of the k-tuple’s coordinates contains every possible residue modulo p: if such a prime p were to exist, then, for any positive integer n, one of the coordinates formed by adding n to the k-tuple would be divisible by p, so there could only be finitely many translations whose coordinates are all prime, namely, only those that include p. A k-tuple that satisfies this condition is said to be admissible. The prime k-tuples conjecture states that, for any admissible k-tuple (m1, m2, . . . , mk) (e.g., (0, 2), (0, 2, 6), (0, 4, 6), and (0, 2, 6, 8)), there are infinitely many positive integers n such that the k-tuple (n + m1, n + m2, . . . , n + mk) is a k-tuple of primes, or prime k-tuple. Besides the celebrated Gödel’s incompleteness theorems, there are many reasons why some questions about the integers are so easy to formulate and yet so difficult to settle. One such reason can be explicated as follows. Note first that the concept of primality, for example, is a purely multiplicative concept in that it is defined solely in terms of multiplication, i.e., in terms of the monoid Z>0 under multiplication. By contrast, an additive concept is one that is defined solely in terms of addition, i.e., in terms of the monoid Z≥0 under addition. Of course, some concepts, like being even, are both additive and multiplicative, and multiplication itself can be defined recursively in terms of addition via the distributive law. Nevertheless, this distinction persists, since the monoids Z>0 and Z≥0 are not even close to being isomorphic to one another, despite the fact that their respective operations are related via the distributive law. Notice, then, that the notion of a twin prime combines an additive concept (differing by ±2) with a multiplicative concept (primality), and the twin prime conjecture thus asks how a particular set of multiplicative concepts relate to a particular set of additive concepts. Other famous examples of this type of problem include Mersenne’s conjecture, Goldbach’s conjecture, and the abc conjecture (all still open), as well as the Taylor–Wiles theorem (formerly Fermat’s last theorem), Mihăilescu’s theorem (formerly Catalan’s conjecture), and the Green–Tao theorem and its generalization, the Tao–Ziegler theorem. Many important questions about the distribution of primes are of this type, e.g., questions about how the prime numbers are distributed additively, or linearly, across the number line. Thus, our understanding—and lack thereof—of how multiplicative properties of the integers relate to additive properties of the integers goes far beyond the distributive law. Somewhat ironically, one has group isomorphisms exp : R −→ R>0 and log : R>0 −→ R, where R is a group under addition and R>0 is a group under multiplication, so that profound questions of this particular sort do not arise in the realm of the real numbers.
Remark 1.1.1 (Euclid’s proof of the fundamental theorem of arithmetic). The existence part of the fundamental theorem of arithmetic is easy to establish using the fact that the ordered set Z>0 of all positive integers is well-ordered, that is, every nonempty set of positive integers has a smallest element. The wellorderedness of the ordered set Z>0 is known as the well-ordering principle, and it is equivalent to the principle of induction, given the other axioms of arithmetic. Suppose, to obtain a contradiction, that not every positive integer is a product of prime numbers. Then, since Z>0 is well-ordered, there must exist a smallest positive integer N that is not a product of prime numbers. Since we allow products of zero or one primes, the integer N must be greater than 1 and not prime. It follows that N is composite, and so it must have a positive integer divisor d other than 1 and N , so that 1 < d < N . The complementary divisor of a positive divisor a of an integer n is the integer n/a, which is also a positive divisor of n, since n = (n/a)a.


 6 1. A BRIEF HISTORY OF PRIMES
Clearly the complementary divisor N/d of the divisor d of N also satisfies 1 < N/d < N . Thus, since d and N/d are both positive integers less than N , they must both be equal to a product of prime numbers. But then N = (N/d)d is a product of two numbers that are expressible as a product of prime numbers. It follows that N itself is expressible as a product of prime numbers, and this is our desired contradiction. Euclid’s proof of the uniqueness of prime factorizations rests crucially on Euclid’s lemma, which states that, if a positive integer d divides the product ab of two integers a and b, and if gcd(d, a) = 1, then the integer d must divide b. From Euclid’s lemma one can deduce that an integer p > 1 is prime if and only if, for all integers a and b, if p divides the product ab, then p must divide a or p must divide b. This property of primes is exactly what is needed to show that if one has two prime factorizations q1q2 · · · qm = N = q′1q′2 · · · q′n
of the same positive integer N , then q1 must equal q′
i for some i = 1, 2, . . . , n, whence it can be cancelled from both sides of the equation, and the argument repeated, to deduce that the prime factorizations of a given integer are essentially unique. Finally, the proof of Euclid’s lemma rests on the fact that, for any integers a and b, there exist integers s and t such that gcd(a, b) = sa + tb, which has a simple constructive proof called the extended Euclidean algorithm.
Remark 1.1.2 (The infinitude of the primes). If q1, q2, . . . qn is any finite list of primes, not necessarily distinct, then the integer N = 1 + q1q2 · · · qn > 1 leaves a remainder of 1 when divided by qi for any i, and thus N is not divisble by any of the primes q1, q2, . . . qn. However, every number greater than 1 is divisible by some prime, which follows from the existence of prime factorizations. Thus, N has a prime factor p, and any such prime factor p of N (e.g., the smallest prime factor of N ) cannot be among the list of primes q1, q2, . . . qn, because none of those primes divide N . This is Euclid’s ingenious “constructive” proof that, for any finite list of primes, there is a prime that is not on that list. Such a proof is preferable to a proof by contradiction, which is not constructive, but which is often given in textbooks. It is also worth noting that, around Euclid’s time, an actual infinity had been regarded by many influential thinkers, including Zeno of Elea and Aristotle, with much suspicion, but a potential infinity had been deemed acceptable, which is probably why Euclid phrased his proposition (Book IX Proposition 20) as “Prime numbers are more than any assigned multitude of prime numbers” (English translation) rather than as the modern paraphrase “There are infinitely many prime numbers.”
In the terminology of abstract algebra, the fundamental theorem of arithmetic states that the commutative monoid Z>0 of all positive integers under multiplication is the free commutative monoid generated by the set of all prime numbers. Similarly, the group Q>0 of all positive rational numbers under multiplication is the free abelian group generated by the set of all prime numbers. Analogously, the commutative monoid Z≥0 of all nonnegative integers under addition is the free commutative monoid generated by 1. In category theory, a universal property of an object is a property that uniquely characterizes the object up to isomorphism as an object of some category. For example, the ring Z of all integers is characterized uniquely up to isomorphism as an initial object in the category of rings, that is, for any ring R (with identity), there is a unique ring homomorphism from Z to R, and any ring Z′ with the same property is isomorphic to Z via a unique isomorphism Z −→ Z′. Similarly, the field Q is characterized uniquely up to isomorphism as an initial object in the category of fields of characteristic 0, or as an initial object in the category of ordered fields, and the ordered field R of all real numbers is characterized uniquely up to isomorphism as a terminal object in the category of archimedean ordered fields. Generally speaking, a universal property of a mathematical object offers evidence that the given object is worthy of study.
Remark 1.1.3 (Rings, prime ideals, and unique factorization domains). Let R be a commutative ring (with identity). The ring R is an integral domain if R is a subring of some field, or, equivalently, if 0 is the one and only zerodivisor of R. An ideal p of R is maximal if the quotient ring R/p is a field, and an ideal p is prime if R/p is an integral domain. Equivalently, a maximal ideal of R is an ideal that is contained by exactly two ideals, namely, itself and (1) = R, while a prime ideal of R is equivalently an ideal p of R properly contained in (1) such that p ⊇ ab implies p ⊇ a or p ⊇ b, for all ideals a and b of R. For example,


 1.2. THE PRIME NUMBERS, ASYMPTOTICALLY 7
the ideal (0) is prime if and only if R is an integral domain, and the ideal (0) is maximal if and only if R is a field, if and only if R has exactly two ideals, namely, (1) ⊋ (0). The maximal ideals of the integral domain Z are precisely the principal ideals (p) generated by p for some prime number p, and Z has exactly one other prime ideal, namely, (0). An element p of R is said to be prime if the principal ideal (p) of R generated by p is a prime ideal of the ring R, or, equivalently, if the quotient ring R/(p) is an integral domain, or equivalently still, if p is a nonunit of R such that p divides a product in R if and only if it divides at least one of the factors. For example, the prime elements of the integral domain Z are precisely 0 and ±p for p prime. Prime factorizations of a given non-zerodivisor of R, when such a factorization exists, are always unique up to reordering and associates, where two elements of R are said to be associates if they generate the same principal ideal. An element r of an integral domain R is said to be irreducible if it is a nonzero non-unit and if r = ab implies either a or b is a unit of R, for all a, b ∈ R. In an arbitrary integral domain, a nonzero element may not have a factorization as a product of irreducibles, and such factorizations need not be unique up to reordering and associates when they do exist. For example, the two factorizations 2 · 2 = (2i) · (−2i) of 4 in the integral domain Z[2i] are distinct irreducible factorizations of 4, since none of the four numbers can be factored any further (except by using a factor of ±1, which are the only units in Z[2i]), and since 2 is associate to nether 2i nor −2i in the ring Z[2i], since i ∈/ Z[2i]. A unique factorization domain is an integral domain R in which every nonzero nonunit element factors (necessarily uniquely up to reordering and associates) as a product of primes. The fundamental theorem of arithmetic is equivalent to the statement that the ring Z is a unique factorization domain.
1.2. The prime numbers, asymptotically
Analytic number theory is the branch of number theory that uses methods from real and complex analysis to deepen our understanding of the integers. Its mere existence is a startling testament to the interconnectedness of mathematics. Historically, one of the first applications of analysis to number theory was unveiled in 1737, when Euler related the study of prime numbers to what is now known as the Riemann zeta function
ζ(x) =
∞
X
n=1
1
nx ,
which Euler studied as a function defined for all real x > 1. Essentially, Euler showed that the fundamental theorem of arithmetic is equivalent to the Euler product representation
ζ(x) =
Y
p prime
1
1− 1
px
, ∀x > 1,
of ζ(x). Thus, Euler translated a fundamental algebraic property of the monoid Z>0 into a particular analytic property of the function ζ : R>1 −→ R>1. As a consequence of Euler’s result, if there were only finitely many primes, then the product
Y
p prime
1
1− 1
p
= ζ(1)
would be finite, but that would contradict
ζ(x) → ζ(1) =
∞
X
n=1
1
n = ∞ as x → 1+.
This provided the first analytic proof of the infinitude of the primes. In the same year, Euler proved that the sum P
p prime
1
p of the reciprocals of all prime numbers diverges, which yielded yet another analytic proof of the infinitude of the primes.


 8 1. A BRIEF HISTORY OF PRIMES
A modernization of Euler’s argument shows that
lim
x−→1+
P (x)
log ζ(x) = 1, (1.2.1)
where
P (x) =
X
p prime
1
px
for x > 1 is the prime zeta function, and where log denotes the logarithm to the base e. This in particular implies that P (1) = P
p prime
1
p diverges.
Figure 1.2.1. Graphs of ζ(x) (in black), 1 + P (x) (in blue), and 1 + 2−x (in red) on [0, 10]
Figure 1.2.1 provides a graph of the functions ζ(x), 1 + P (x), and 1 + 2−x on the interval [0, 10]. Notice from the graphs that it appears that one has
xli→m∞ ζ(x) = 1
and
xli→m∞ P (x) = 0,
which are not difficult statements to prove. One can prove, more generally, that
ζ(x) − 1 ∼ P (x) ∼ 2−x (x → ∞),
where one writes
f (x) ∼ g(x) (x → a)
whenever f (x) and g(x) are functions such that
lxi→ma
f (x)
g(x) = 1.
Equivalently, the condition f (x) ∼ g(x) (x → a) means that f (x) is a “good approximation” for g(x) for x near a (or for large x if a = ∞) in the sense that the percentage error of this
approximation, given as a fraction by the ratio f(x)−g(x)
g(x) , tends to 0 as x → a:
lxi→ma
f (x) − g(x)
g(x) = lxi→ma
f (x)
g(x) − 1 = 0.
Note that the symbols “f (x) ∼ g(x) (x → a)” are read “f (x) is asymptotic to g(x) as x approaches a.” The asymptotic notation ∼ is used routinely in analytic number theory. One also writes
f (x) = o(g(x)) (x → a)


 1.2. THE PRIME NUMBERS, ASYMPTOTICALLY 9
whenever
lxi→ma
f (x)
g(x) = 0.
This means that f (x) is “infinitely smaller” than g(x) for x near a (or for large x if a = ∞). Note, in particular, that
f (x) ∼ g(x) (x → a) ⇐⇒ f (x) − g(x) = o(g(x)) (x → a).
It is also convenient to write
f (x) = O(g(x)) (x → a)
whenever
lim sup
x→a
f (x)
g(x) < ∞,
or, equivalently, whenever the function f(x)
g(x) is bounded on some punctured neighborhood
of a. More general definitions of these relations are provided in Section 2.1, but for this chapter the definitions above suffice. The symbols “f (x) = o(g(x)) (x → a)” are read “f (x) is little o of g(x) as x approaches a,” and the symbols “f (x) = O(g(x)) (x → a)” are read “f (x) is big O of g(x) as x approaches a.” In the notations defined above, (1.2.1) is expressed as
P (x) ∼ log ζ(x) (x → 1+).
In fact, the approximation
P (x) ≈ log ζ(x)
is excellent for all x > 1, as can be witnessed from the graph in Figure 1.2.2 of the difference log ζ(x) − P (x), which decreases rapidly to 0 on the interval (1, ∞), and where the limit
H = lim
x→1+ (log ζ(x) − P (x)) = 0.315718452053 . . .
is an important constant, which we call the Mertens constant, discussed further later in this section.
Figure 1.2.2. Graph of log ζ(x) − P (x) on (1, 5]
Euler was interested in the function ζ(x) in part because of the renowned Basel problem, posed by P. Mengoli in 1650, which was the problem of computing the exact value of the


 10 1. A BRIEF HISTORY OF PRIMES
convergent series P∞
n=1
1
n2 . In 1734, Euler solved the problem by proving, non-rigorously by today’s standards, that
ζ(2) =
∞
X
n=1
1
n2 = π2
6 = 1.644934066848 . . . .
From the Euler product representation of ζ(x), which Euler proved just three years later, it follows that
π2
6=
Y
p prime
p2
(p − 1)(p + 1) = 2
1·2
3·3
2·3
4·5
4·5
6·7
6·7
8 · 11
10 · 11
12 · 13
12 · 13
14 · 17
16 · 17
18 · · · .
After Euler’s work, another giant leap occurred in 1837, with Dirichlet’s proof of Dirichlet’s theorem on primes in arithmetic progression [65], which many say kickstarted rigorous analytic number theory.
Theorem 1.2.1 (Dirichlet’s theorem on primes in arithmetic progression [65]). For any positive integers a and b, there are infinitely many primes of the form a + bn for n ∈ Z>0 if (and only if ) a and b are relatively prime.
Actually, Dirichlet proved a much stronger theorem: if a and b are relatively prime positive integers, then the proportion of all prime numbers less than or equal to x that are congruent to a modulo b tends to 1
φ(b) as x tends to ∞. Here, φ(n) denotes Euler’s totient, which equals the number of positive integers from 1 to n that are relatively prime to n. Thus, Dirichlet’s theorem says that the primes for any integer b are equally distributed modulo b among the φ(b) distict congruence classes of integers relatively prime to b. A well-known generalization of Dirichlet’s theorem is that the sum
X
p prime p≡a (mod b)
1
p
diverges, and in fact the limit
xli→m∞

 
X
p≤x
p≡a (mod b)
1
p− 1
φ(b)
X
p≤x
1
p

 
converges (and both terms in the limit differ from 1
φ(b) log log x by a limiting constant), for all relatively prime positive integers a and b. Dirichlet proved his theorem by studying a certain class of Dirichlet series, where the Dirichlet series of a function f : Z>0 −→ C is the function
Df (s) =
∞
X
n=1
f (n)
ns ,
of a complex variable s. Specifically, Dirichlet’s proof employed the Dirichlet series of functions f called Dirichlet characters, whose corresponding Dirichlet series are called Dirichlet L-functions. Although Dirichlet considered Dirichlet series and Dirichlet L-functions as functions of a real variable, Riemann was the first to study a particular Dirichlet series as a


 1.2. THE PRIME NUMBERS, ASYMPTOTICALLY 11
function of a complex variable, namely, the series
ζ(s) =
∞
X
n=1
1
ns ,
which converges (absolutely) to an analytic function, called the Riemann zeta function, on the right half plane {s ∈ C : Re s > 1} [248]. Dirichlet’s and Riemann’s work later inspired Jensen (in 1884 and 1888) and Cahen (in 1894) to undertake the general study of Dirichlet series of a complex variable. Today, Dirichlet series are a highly-developed tool for studying functions f : Z>0 −→ C and are one of the main topics of Chapter 3. On a more simplistic level, using functions to study the primes is possible for the basic reason that there are numerous functions in number theory that carry all of the information about the primes. Perhaps the most obvious example is the prime listing function p− : Z>0 −→ Z>0, where pn for all n denotes the nth prime, so that, for example, p1 = 2 and p25 = 97. Another obvious example is the characteristic function χP : Z>0 −→ {0, 1} of the set P of all prime numbers, where for any subset X of Z>0 the characteristic function χX : Z>0 −→ {0, 1} of X is the function defined by
χX(n) =
(
1 if n ∈ X
0 if n ∈ Z>0\X.
Both of the examples above are discrete functions, defined on Z>0. Functions f : Z>0 −→ C, as those above, are called arithmetic functions. Essentially, they are just sequences of complex numbers indexed by the positive integers. Besides forming its Dirichlet series Df (s), another way to “analysis-ize” an arithmetic function f is to form its summatory function Sf , which is the function Sf : R≥0 −→ C defined by
Sf (x) =
X
n≤x
f (n), ∀x ≥ 0.
The summatory function Sf of f is a step function that is constant on the interval [n − 1, n), and changes by the value +f (n) at n, for every positive integer n. In many ways, to be made apparent in Chapter 3, the association f 7−→ Sf is a discrete analogue of integration. The summatory function SχP of the characteristic function χP of the set P of all primes is called the prime counting function π(x). Specifically,
π(x) =
X
p≤x p is prime
1 = #{p ≤ x : p is prime}
for any x ≥ 0 is equal to the number of primes less than or equal to x. For example, one has π(100) = 25 because there are 25 primes less than or equal to 100, the largest being p25 = 97. The function π(x) is a nondecreasing step function, continuous from the right, that jumps up by 1 at every prime and is constant, assuming the value n, over the interval [pn, pn+1), for all n. Thus, the nth prime pn can be recovered from π(x) as the nth smallest discontinuity of π(x), or as the smallest real number x such that π(x) ≥ n, and one has
pn = inf{x ∈ R : π(x) ≥ n} = min{x ∈ R : π(x) ≥ n}
for all positive integers n. Since π(pn) = n for all n, the function π(x) : R≥0 −→ Z≥0 is a left inverse to the function pn : Z≥0 −→ R≥0, where one defines p0 = 0. In the reverse direction, the composition pπ(x) for any x equals the largest prime number less than or equal to x, e.g.,


 12 1. A BRIEF HISTORY OF PRIMES
pπ(100) = 97. Generally speaking, information about one of the two functions pn and π(x) yields corresponding information about the other. Other “primes-equivalent” functions worth mentioning are the prime density function
p(x) = π(x)
x , ∀x > 0,
and the related prime probability function
p(⌊x⌋) = π(x)
⌊x⌋ , ∀x ≥ 1.
For any x ≥ 1, the number p(⌊x⌋) equals the probability that a randomly selected positive integer less than or equal to x is prime. Thus, for example, one has
p(100) = 25
100 = 1
4.
Given that larger primes are rarer than smaller primes, one might expect that
xli→m∞ p(x) = 0, (1.2.2)
or, equivalently,
π(x) = o(x) (x → ∞),
and indeed this is true. If X is any set of positive integers, then one defines the natural density δ(X) of X to be the limit
δ(X) = xli→m∞
#{n ∈ X : n ≤ x}
#{n ∈ Z>0 : n ≤ x} = xli→m∞
#{n ∈ X : n ≤ x}
⌊x⌋ = xli→m∞
#{n ∈ X : n ≤ x}
x,
provided that any of the limits above exist. Thus, (1.2.2) states that the natural density of the set of all primes is 0. (By contrast, if a and b are positive integers, then the natural density of the set of all positive integers congruent to a modulo b is equal to 1
b > 0.) Note also that (1.2.2) implies that
nli→m∞
n
pn
= nli→m∞
π(pn)
pn
= 0.
Below is a relatively simple proof of (1.2.2).
Proof of (1.2.2). Let n be a fixed positive integer, and let x ≥ 1. Since all prime numbers are either less than or equal to n or relatively prime to n, and since there are at most x
n φ(n) integers less than or equal to x that are relatively prime to n, one has
π(x) ≤ n +
lx
n
m
φ(n),
and therefore
π(x)
x ≤n
x+1
x
lx
n
m
φ(n),
whence
0 ≤ lim sup
x→∞
π(x)
x ≤ xli→m∞
n
x+1
x
lx
n
m
φ(n) = φ(n)
n = ρ(n),
where
ρ(n) = φ(n)
n=
Y
p|n
1− 1
p


 1.2. THE PRIME NUMBERS, ASYMPTOTICALLY 13
is equal to the probability that a randomly chosen integer from 1 to n is relatively prime to n. But one has
ρ(n!) =
Y
p|n!
1− 1
p=
Y
p≤n
1− 1
p
and therefore
nli→m∞ ρ(n!) = nli→m∞
Y
p≤n
1− 1
p=
Y
p
1− 1
p= 1
Q
p 1− 1
p
−1 = 1
ζ(1) = 1
∞ = 0,
where the limits above can be made rigorous. It follows that
0 ≤ lim sup
x→∞
π(x)
x ≤ nli→m∞ ρ(n!) = 0,
which immediately implies (1.2.2). □
As of the writing of this book, the record for computing π(x) is for x = 1029. For x = 1029, it is known (On-Line Encyclopedia of Integer Sequences, February 2022) that the exact value of p(x) is
p(x) = 1520698109714272166094258063
1029 = 1
65.759271587961 . . . ,
which is much larger than one might naively expect: the odds that a randomly chosen positive integer having at most 29 digits is prime are better than 1 in 66. Thus, although the function p(x) tends to 0, apparently it does so very slowly. In analysis, when a given limit converges, it is natural to ask how fast it converges. Thus, (1.2.2) raises a more refined question: How quickly does p(x) tend to 0? Like 1/x? Like
1/√x? An answer to this challenging question is provided by the celebrated prime number theorem.
Theorem 1.2.2 (Prime number theorem [61] [114]). One has
π(x) ∼ x
log x (x → ∞),
or, equivalently,
p(x) ∼ 1
log x (x → ∞).
Since 1
log x tends to 0 as x → ∞, the prime number theorem is a precise mathematical
statement to the effect that p(x) tends to 0 like 1
log x , as x tends to ∞. The prime number theorem is easily seen to be equivalent to each of the following statements.
(1) xli→m∞
π(x)
x log x
= 1.
(2) xli→m∞
p(x)
1 log x
= 1.
(3) π(x) ∼ x
log x − 1 (x → ∞).
(4) p(x) ∼ 1
log x − 1 (x → ∞).
(5) xli→m∞ xp(x) = e.


 14 1. A BRIEF HISTORY OF PRIMES
The last of these statements reveals that famous constant e, which was discovered by Bernoulli in 1683 and is given by
e = xli→m∞ 1 + 1
x
x
=
∞
X
n=0
1
n! = 2.718281828459 . . . ,
“encodes” information about the asymptotic distribution of the primes. The (informal) approximation π(x) ≈ x
log x was first conjectured by Gauss in 1792 or 1793 at the age 15 or 16, according to his own recollection in his famous letter to the astronomer Encke in 1849 [99, pp. 444–447]. The first actual published statement of such an approximation was made by Legendre in 1798, which he refined further in 1808 [101]. Legendre’s and Gauss’ speculations are discussed further in Remark 1.3.8. Chebyshev (if not Gauss) seems to have been the first to have come close to a precise statement of the theorem. In 1848, he proved a result, namely, [46, II-éme Théorème], that immediately implies that
lim inf
x→∞
π(x)
x log x
≤ 1 ≤ lim sup
x→∞
π(x)
x log x
,
and, therefore, if the limit limx→∞
π(x) x log x
exists, then it must equal 1. Then, in 1850, he proved
[46] that
c1
x
log x < π(x) < c2
x
log x , ∀x ≫ 0, (1.2.3)
for all
c1 < A = log(21/231/351/530−1/30) = 0.9212920229 . . .
and for
c2 = 6
5 A = 1.1055504275 . . . ,
and thus
A ≤ lim inf
x→∞
π(x)
x log x
≤ 1 ≤ lim sup
x→∞
π(x)
x log x
≤6
5 A.
Of course, the prime number theorem itself is equivalent to
lim inf
x→∞
π(x)
x log x
= 1 = lim sup
x→∞
π(x)
x log x
and to
C1
x
log x < π(x) < C2
x
log x, ∀x ≫ 0,
for all C1 and C2 with C1 < 1 < C2. Thus, Chebyshev came very close to proving the prime number theorem, and there is little doubt that he had conjectured the theorem in its precise form. In 1896, almost 100 years after Legendre’s aforementioned published work, the prime number theorem was finally proved, by de la Vallée Poussin [61] and Hadamard [114]. Although it is has been claimed many times that de la Vallée Poussin and Hadamard proved the theorem “independently,” “separately” is a more accurate description, as the two proofs were very far from being independent from one another: just one year prior, in 1895, von Mangoldt had rigorously proved [199] several unproved assertions that Riemann made in his landmark paper [248] of 1859, and it was those results that finally made the proofs of


 1.2. THE PRIME NUMBERS, ASYMPTOTICALLY 15
the prime number theorem attainable. Specific details of these developments are discussed in the next section. Today, many “effective” versions of the prime number theorem are known. For example, in 1961, Rosser and Schoenfeld proved [255] that
x
log x − 1
2
< π(x) < x
log x − 3
2
, ∀x ≥ 67,
which is easily seen to imply the prime number theorem. See [136, p. 36] and [6, Theorem 4.5] for simple proofs that the prime number theorem is equivalent to
pn ∼ n log n (n → ∞),
where pn denotes the nth prime.
Figure 1.2.3. Graphs of p(x) (in black), 1
log x (in blue), and 1
log x−1 (in red) on [1, 2000]
A graphical illustration of the prime number theorem is provided in Figure 1.2.3, which provides the graph of the functions p(x), 1
log x , and 1
log x−1 . As Figure 1.2.3 suggests, the
function 1
log x−1 is in fact a much better approximation to p(x) than is 1
log x . In simple terms, one can show that
p(x) − 1
log x − 1 < p(x) − 1
log x , ∀x ≥ 97.
More dramatically, one has
p(x) − 1
log x ∼ 1
(log x)2 (x → ∞),
while
p(x) − 1
log x − 1 ∼ 1
(log x)3 (x → ∞),
so that the error in the latter approximation is substantially less than the error in the former for large x. For example, one has 1
log(1029) = 1
66.774967... , so that 1
log(1029)−1 = 1
65.774967... , while,
as we noted earlier, p(1029) = 1
65.759271... . Figure 1.2.4 provides graphs of the functions
p(x) − 1
log x , 1
(log x)2 , p(x) − 1
log x−1 , and 1
(log x)3 on [1, 10000].
One of the morals that one draws from the numerical examples above is that numbers even as large as 1029 are small when it comes to the study of the primes and that the true “size” of a prime p for the purpose of studying prime asymptotics is better measured by log p


 16 1. A BRIEF HISTORY OF PRIMES
Figure 1.2.4. Graphs of p(x) − 1
log x (in blue), 1
(log x)2 (in red), p(x) − 1
log x−1 (in black),
and 1
(log x)3 (in green) on [1, 10000]
than by p itself. This is in large part due to the prime number theorem p(x) ∼ 1
log x (x → ∞) and the remarkable fact that it is only the zeroth term in the infinite “asymptotic expansion”
p(x) −
n−1
X
k=0
k!
(log x)k+1 ∼ n!
(log x)n+1 (x → ∞), ∀n ≥ 0, (1.2.4)
of p(x). Also, more practically, with respect to computers, the “size” of a prime p is measured by how many bits it has in its binary expansion, which is given exactly by ⌊log2 p⌋ + 1 and
which is larger than log p asymptotically by a factor of 1
log 2 = 1.4426950408 . . .. A random
prime number in the interval [1, 1029] can be expressed using at most 97 bits, and 97 is not a very large number, so, by this measure, neither is 1029. As mentioned earlier, the largest known prime, 282589933 − 1, has 24862048 digits, and, expressed in binary notation, is the sequence (111 . . . 1)2 of 82589933 bits. In fact, there is a deterministic algorithm to test if an integer n is prime that runs on O((log n)t) operations for any t > 6, which is “polynomial time” in the number of bits of n, not in n itself. The best known algorithms to compute pn, π(n), and p(n), on the other hand, are polynomial time in n, which is “exponential time” in the number of bits of n. Unfortunately, this makes analyzing these functions from a purely computational perspective rather difficult. As we have noted, the number e encodes information about the distribution of the primes, and, as we have also seen, so does the number ζ(2) = π2
6 . There are many other such constants, including the Mertens constant H mentioned earlier. After e and π, arguably the most important in analytic number theory is the Euler–Mascheroni constant
γ = xli→m∞
X
n≤x
1
n − log x
!
= 0.577215664901 . . . ,
discovered by Euler in 1735, and the related constant
eγ = nli→m∞
1
n exp Hn = xli→m∞
1
x
Y
n≤x
e1/n
!
= 1.781072417990 . . . ,
where Hn is the nth harmonic number
Hn =
n
X
k=1
1
k.


 1.2. THE PRIME NUMBERS, ASYMPTOTICALLY 17
To prove that the limits above exist and are so related is a straightforward calculus exercise. The harmonic numbers satisfy
Hn − γ − log n ∼ 1
2n (n → ∞)
and in fact 1
2n + 1 < Hn − γ − log n < 1
2n, ∀n ≥ 1,
and thus γ + log n is an excellent approximation of Hn for large n. In particular, since
Hn ∼ log n (n → ∞),
the prime number theorem is equivalent to
π(n) ∼ n
Hn
(n → ∞),
where
n
Hn
= 1−1 + 2−1 + 3−1 + · · · + n−1
n
−1
is the harmonic mean of the numbers 1, 2, 3, . . . , n. See [72], Proposition 9.1.18, and Remark 9.1.19 for further relationships between the prime counting function and the harmonic numbers. The Euler–Mascheroni constant γ also features prominently in Mertens’ theorems, which are three well-known theorems that were proved by Mertens in 1874 [207], twenty-two years before the first proofs of the prime number theorem. Mertens’ third theorem is the identity
xli→m∞
X
p≤x
log 1 − 1
p + log log x
!
= −γ,
or, equivalently,
eγ Y
p≤x
1− 1
p∼1
log x (x → ∞).
From Mertens’ third theorem, it follows immediately that the prime number theorem (which in 1874 was a mere conjecture) is equivalent to the asymptotic relation
p(x) ∼ eγ Y
p≤x
1− 1
p (x → ∞),
or, equivalently,
eγ = xli→m∞
p(x)
Q
p≤x 1 − 1
p
.
These reformulations of the prime number theorem are profoundly beautiful. The function
P(x) =
Y
p≤x
1− 1
p
approximates the probability that a randomly selected number is not divisible by any prime less than or equal to x, but assuming, erroneously of course, that these are independent


 18 1. A BRIEF HISTORY OF PRIMES
events. The constant eγ is therefore an asymptotic measure of how independent these events aren’t. Moreover, P(x) for any x > 0 is the limit
P(x) = tli→m∞
#{n ∈ (0, t] : all prime factors of n are > x}
t,
which is also the limit as N → ∞ of the proportion of the integers in the interval [1, N ] having no prime factor less than or equal to x [166]. Mertens’ second theorem states that the limit
M = xli→m∞
X
p≤x
1
p − log log x
!
= 0.261497212847 . . . ,
known as the Meissel–Mertens constant, exists. This theorem is much stronger than Euler’s result that the sum P
p
1
p diverges. Moreover, it suggests the following analogy: the
relationship between the divergent series P∞
n=1
1
n , the function log x, and the constant γ is
analogous to the relationship between the divergent series P
p
1
p , the function log log x, and the constant M . Mertens’ second theorem is one of the first appearances, if not the first appearance, of an iterated logarithm function in number theory. It has, as a consequence, the estimates
X
p≤10100
1
p ≈ log log(10100) + M = log 100 + log log 10 + M ≈ 5.700699 . . .
and
X
p≤1010100
1
p ≈ log log(1010100) + M = 100 log 10 + log log 10 + M ≈ 231.354038 . . . ,
the values of which are miniscule when compared to a googol 10100 and a googolplex 1010100, respectively. Thus, although the series P
p≤x
1
p diverges, it does so extraordinarily slowly. This is one of the first instances in analytic number theory of a result showing that some patterns that emerge among the primes do so only at astronomically large numbers. Moreover, the “culprit” in this particular instance is the iterated logarithm log log x. The occurrence of log log x in Mertens’ second theorem can be motivated by Cramér’s model of the primes, which, in very loose terms, uses the prime number theorem to model the “probability” that an integer n > 1 is prime as 1
log n [53]. Under Cramér’s model, the sum
P
p≤x
1
p is approximated by the sum P
1<n≤x
1
n log n , and a straightforward calculus exercise,
using the fact that
Zx
e
dt
t log t = log log x, ∀x > 1,
shows that the limit
R = xli→m∞
X
1<n≤x
1
n log n − log log x
!
exists, where the constant
R = 0.794678645452 . . .
has its sequence of digits given by Sequence A361972 of the On-Line Encyclopedia of Integer Sequences (OEIS). It follows that Mertens’ second theorem is equivalent to the existence of


 1.2. THE PRIME NUMBERS, ASYMPTOTICALLY 19
the limit
xli→m∞
X
1<n≤x
1
n log n −
X
p≤x
1
p
!
= R − M = 0.533181432605 . . . .
It is clear that Mertens’ second theorem is also equivalent to
e−M Y
p≤x
e1/p ∼ log x (x → ∞).
Thus, given Mertens’ second theorem, the prime number theorem is equivalent to
p(x) ∼ eM Y
p≤x
e−1/p (x → ∞),
where eM = 1.371244130303 . . .. Mertens’ first theorem states that
log x −
X
p≤x
log p
p < 2, ∀x ≥ 2. (1.2.5)
In fact, it is known that the limit
B = xli→m∞ log x −
X
p≤x
log p
p
!
= 1.332582275733 . . .
exists, which in turn implies the prime number theorem. It is also known that
γ = xli→m∞ log x −
X
p≤x
log p
p−1
!
,
and therefore
B=γ+
X
p
log p
p(p − 1) = γ +
∞
X
n=2
X
p
log p
pn = γ −
∞
X
n=2
P ′(n).
As noted previously, another important constant relating to the prime numbers that was introduced by Mertens is the Mertens constant H, which is also given by
H =−
X
p
1
p + log 1 − 1
p
=
X
p
1
2p2 + 1
3p3 + 1
4p4 + · · ·
=
∞
X
n=2
P (n)
n
= 0.315718452053 · · · ,
where also
e−H =
Y
p
1− 1
p e1/p = 0.729264744257 . . . .
An immediate consequence of Mertens’ third theorem and the first expression above for the constant H is the relationship
γ = M + H.


 20 1. A BRIEF HISTORY OF PRIMES
These three constants encode important information about the primes, and they crop up in many seemingly unrelated contexts in analytic number theory—much how the constants e and π make appearances in many seemingly unrelated contexts, as, for instance, in the normal distribution. Notably, for example (see Section 3.6), one has
γ = lim
x→1+ ζ(x) − 1
x−1 =
∞
X
n=2
(−1)n ζ (n)
n=
Z∞
1
1 − {x}
x2 dx
and
H = lim
x→1+ log 1
x − 1 − P (x) =
Z∞
1
li(x) − π(x)
x2 dx.
Remark 1.2.3 (Algebraic numbers and transcendental numbers). The most remarkable example, in the author’s opinion, of an equation in mathematics that combines an assortment of fundamental constants is Euler’s equation
1 + eiπ = 0,
which follows immediately from the well-known Euler’s formula
eix = cos x + i sin x, ∀x ∈ R,
by plugging in x = π. (See Remark 3.1.1 for a “Calculus 1” proof of Euler’s formula.) Arguably, the five mathematical constants appearing in Euler’s formula are the five most fundamental constants in all of mathematics: 0 and 1 are the most important constants in arithmetic, e the most important in analysis, π the most important in geometry, and i is one of the most important constants in both algebra and complex analysis. Another startling aspect of Euler’s equation 1 + eiπ = 0 is that it uses each of the three fundamental arithmetical operations—addition, multiplication, and exponentiation—exactly once. The renowned physicist Richard Feynman wrote in his Lectures on Physics that Euler’s formula is “our jewel” and is “one of the most remarkable, almost astounding, formulas in all of mathematics” [90, pp. 22-1, 22-10], and a poll of readers conducted in 1990 by The Mathematical Intelligencer named Euler’s equation as the “most beautiful theorem in mathematics” [287]. More importantly, Euler’s equation is useful for deriving an important property of the number π: the equation, along with the proof of the transcendence of the number e in 1873 by Hermite, formed the bases for the first proof of the transcendence of π by Lindemann in 1882. Here, a complex number is said to be transcendental if is not algebraic, where a complex number is said to be algebraic if it is a root of a nonzero polynomial with rational coefficients. For example, trivially
every rational number is algebraic, and √2, though irrational, is algebraic since it is a root of the polynomial x2 − 2. One can show that the set Q of all algebraic numbers is a countable subfield of the field C, and the transcencence of both e and π can then be expressed simply as e, π ∈/ Q. Note that a complex number α is transcendental if and only if the unique surjective ring homomorphism Q[X] −→ Q[α] sending X to α is an isomorphism, if and only if the field extension Q(α) of Q is infinite dimensional as a vector space over Q. More generally, complex numbers α1, α2, . . . , αn are said to be algebraically independendent if the unique ring homomorphism Q[X1, X2, . . . , Xn] −→ C sending Xi to αi for all i is injective, that is, if f (α1, α2, . . . , αn) ̸= 0 for all nonzero polynomials f ∈ Q[X1, X2, . . . , Xn] with rational coefficients in n variables. It is an important open problem in the field of transcendental number theory—whose primary goal is develop techniques for proving that various collections of constants in mathematics are algebraically dependent or independent—to prove or disprove the conjecture that the numbers e and π are algebraically independent. It is also believed that the three constants γ, M , and H are transcendental, but, in fact, no one has yet proved that any of the three constants is irrational, much less transcendental.
Remark 1.2.4 (Mathematical constants in physics). The mathematical constants e, π, and i are important not only in mathematics, but also in other sciences, physics especially. The constants π and i, for example, appear in Schrödinger’s equation Hˆ |Ψ(t)⟩ = i h
2π
d
dt |Ψ(t)⟩, which is the quantum counterpart of
Newton’s second law ⃗F = d
dtp⃗ , where h = 6.62607015·10−34 J · Hz−1 is a universal physical constant known as Planck’s constant. Even the constant γ arises in physics, as, for example, in dimensional regularization of Feynman diagrams in quantum field theory. For applications of special values of the Riemann zeta function to physics, see Remark 1.3.7.


 1.2. THE PRIME NUMBERS, ASYMPTOTICALLY 21
Remark 1.2.5 (Mersenne primes). The Lenstra–Pomerance–Wagstaff conjecture, conjectured independently by Lenstra and Pomerance [239], modifying a prior conjecture of Gillies [100], states that the number of Mersenne primes less than or equal to x is asymptotic to eγ log2 log2 x, or, equivalently, that the
number of Mersenne primes 2p − 1 with p ≤ x is asymptotic to eγ log2 x. Equivalently still, the conjecture
states that the proportion of primes p ≤ x for which 2p − 1 is also prime is asymptotic to eγ
log 2
(log x)2
x.
Remark 1.2.6 (Twin primes and Sophie Germain primes). The Hardy–Littlewood conjecture for prime k-tuples, applied to the twin primes, states that
π2(x) ∼ 2C2
x
(log x)2 ∼ 2C2
Zx
0
dt
(log t)2 (x → ∞),
where π2(x) denotes the number of primes p ≤ x such that p + 2 is also prime, where
C2 =
Y
p prime p̸=2
1− 1
(p − 1)2 = 0.660161815846 . . .
is the twin prime constant, and where 2C2 = 1.320323631693 . . .. The conjecture is equivalent to
qn ∼ 1
2C2
n(log n)2 (n → ∞),
where qn is the sequence that enumerates in succession the first of each twin prime pair, so that the sequence is 3, 5, 11, 17, 29, 41, . . .. By the prime number theorem, the conjecture is also equivalent to
π2(x)
π(x) ∼ 2C2
log x ∼ 2C2p(x) (x → ∞),
which means that the probability π2(x)
π(x) that a randomly chosen prime number less than or equal x is the smaller of two twin primes is asymptotic to 2C2p(x), i.e., 2C2 times the probability that a randomly chosen number less than or equal to x is prime. In other words, the conjecture says that the likelihood that n + 2 is prime is increased asymptotically by a factor of 2C2 if it is known also that n is prime, and thus, if the conjecture is true, then 2C2 can be thought of as a “prime coupling constant.” The Hardy–Littlewood conjecture for twin primes is the likely analogue of the prime number theorem for twin primes, but since it implies that there are infinitely many twin primes, the proof is likely to be far more difficult, perhaps involving new methods that have not been discovered yet. However, in 2007, J. Wu made some progress on the conjecture by proving [297] that
π2(x) ≤ 3.3996 · 2C2
x
(log x)2 , ∀x ≫ 0.
Wu’s theorem is a partial analogue for π2(x) of Chebyshev’s 1850 result (1.2.3). Wu’s result improved upon a 1914 result of V. Brun, which had implied that the sum
B2 =
X
p : p+2∈P
1
p+ 1
p+2 = 1
3+1
5+1
5+1
7+ 1
11 + 1
13 + · · · ,
known now as Brun’s constant, is finite, which stands in sharp contrast to the divergence of the sum of the reciprocals of the primes. It is known that 1.8304 < B2 < 2.347, and various heuristic estimates of B2 have been made, e.g., in 2002, P. Sebah and P. Demichel used all twin primes up to 1016 to extrapolate the estimate B2 ≈ 1.902160583.
A prime p is a Sophie Germain prime if 2p + 1 is also prime. It is conjectured that the number of Sophie Germain primes less than or equal to x is asymptotic to
2C2
x
(log x)2 ∼ 2C2
Zx
0
dt
(log t)2 ∼ π2(x) (x → ∞).
Both of these asymptotics, as well as the Hardy–Littlewood conjecture for prime k-tuples, follow from the far more general Bateman–Horn conjecture [19].


 22 1. A BRIEF HISTORY OF PRIMES
1.3. The prime numbers, analytically
The prime number theorem is one of the major mathematical achievements of the 19th century. The fact that the theorem was proved by two mathematicians both in the same year (1896) was no coincidence. As mentioned earlier, much progress had been made by Chebyshev in 1848 and 1850. Nine years later, major groundwork for the eventual 1896 proofs was laid down by Riemann in his landmark eight-page paper of 1859 [248], which was the only work he ever wrote on number theory. Riemann first was able to show that the function
ζ(s) =
∞
X
n=1
1
ns
on the right half plane {s ∈ C : Re s > 1} extends (uniquely) to a meromorphic function on all of C with a single (simple) pole at s = 1 with residue 1. In fact, the extended function ζ(s) − 1
s−1 is entire, with limiting value
lsi→m1 ζ(s) − 1
s−1 =γ
at s = 1. Note that 1
s−1 is the meromorphic continuation to C of the function
Z∞
1
dx
xs = 1
s−1
on {s ∈ C : Re s > 1}, where the given integral is employed in the integral test from calculus
to determine the region of absolute convergence of the sum P∞
n=1
1
ns . In particular, one has
γ = lsi→m1
Re s>1
∞
X
n=1
1
ns −
Z∞
1
dx
xs
!
.
Today, it is the meromorphic function ζ(s) on all of C that we refer to as the Riemann zeta function. One may think of the Riemann zeta function as a simultaneously arithmetic, algebraic, and analytic generating function for the sequence of positive integers. Both proofs of the prime number theorem involved very deep results and conjectures from Riemann’s paper, specifically concerning a remarkable explicit formula that Riemann conjectured for the prime counting function π(x), expressed in terms of zeros of the Riemann zeta function ζ(s). One of the most important outstanding open problems in all of mathematics today is to prove or disprove the famous Riemann hypothesis, conjectured by Riemann in his 1859 paper, which is the statement that the zeros of ζ(s) besides the negative even integers −2, −4, −6, −8, . . . all have real part 1
2 , that is, they all lie on the critical line
{s ∈ C : Re s = 1
2} = {1
2 + it : t ∈ R}.
Riemann was able to show in his paper that the real zeros of ζ(s) are precisely the negative even integers and that all of the non-real zeros of ζ(s) lie in the criticial strip {s ∈ C : 0 ≤ Re s ≤ 1}. He also showed that they are discretely ordered in the critical strip, occur in conjugate pairs ρ and ρ (which are reflections of each other over the real axis), as well as in pairs ρ and 1 − ρ (which are reflections of each other over the critical line). Thus, the non-real zeros of ζ(s), also called the nontrivial zeros of ζ(s), can be listed in order of nondecreasing absolute imaginary part. In 1914, Hardy proved that there are infinitely many zeros of ζ(s) on the critical line [119]. In more recent times, mathematicians, using


 1.3. THE PRIME NUMBERS, ANALYTICALLY 23
sophisticated computers and algorithms, have calculated at least the first ten trillion zeros of ζ(s) to very high precision, and they all lie on the critical line [106]. This provides some evidence, though circumstantial, that the Riemann hypothesis is true.
Table 1.3.1. Some noteworthy real values of ζ(s)
s ζ(s)
2n, where n ∈ Z>0
(−1)n+1 B2n (2π )2n 2(2n)!
−n, where n ∈ Z≥0
(−1)n Bn+1 n+1
−2n, where n ∈ Z>0 0 −2n + 1, where n ∈ Z>0 − B2n
2n
0 −1
2
1∞
2 π2
6 = 1.644934 . . . 3 1.202056 . . .
4 π4
90 = 1.082323 . . . 5 1.036927 . . .
6 π6
945 = 1.017343 . . . 7 1.008349 . . .
8 π8
9450 = 1.004077 . . .
−1 − 1
12
−2 0 −3 1
120
−4 0 −5 − 1
252
−6 0 −7 1
240
−8 0
1
2 ± 14.134725 . . . i 0
1
2 ± 21.022040 . . . i 0
1
2 ± 25.010858 . . . i 0
1
2 ± 30.424876 . . . i 0
1
2 ± 32.935062 . . . i 0
1
2 ± 37.586178 . . . i 0
1
2 ± 40.918719 . . . i 0
1
2 ± 43.327073 . . . i 0
1
2 ± 48.005150 . . . i 0
1
2 ± 49.773832 . . . i 0
Some noteworthy real values of ζ(s), discovered by Euler, Riemann, and others, are provided in Table 1.3.1, including the (exactly) 20 nontrivial zeros of ζ(s) with absolute imaginary part less than or equal to 50. In the table, Bn for all nonnegative integers n denotes the nth Bernoulli number, which can be defined via their generating function
∞
X
n=0
Bn
n! Xn = X
eX − 1 =
∞
X
n=0
1
(n + 1)! Xn
!−1
,
or explicitly by
Bn =
n
X
k=0
1
k+1
k
X
j=0
(−1)j k
j jn,


 24 1. A BRIEF HISTORY OF PRIMES
whence the Bn are rational numbers for all n. Moreover, one has Bn = 0 if and only if n is an odd integer greater than 1, and Bn > 0 if and only if n = 0 or n is congruent to 2 modulo 4. The Bernoulli numbers have importance in mathematics well beyond just the Riemann zeta function, e.g., they are employed in the Euler–Maclaurin formula (Theorem 2.2.8). Figure 1.3.1 is a graph of the function ζ(t) on [−25, 25]. Figure 1.3.2 is a graph of the function |ζ( 1
2 + it)|, to be contrasted with the graphs of |ζ( 2
3 + it)| and |ζ(1 + it)| in Figure 1.3.3, on [−50, 50]. Note that ζ(s) = 0 if and only if |ζ(s)| = 0, so that these graphs provide a “snapshot” visualization of the Riemann hypothesis. A better visualization would be a moving graph of |ζ(a + it)| with a “draggable” parameter a ∈ [0, 1], but since we cannot provide such a graph here, instead we provide the 3D graph of |ζ(a + it)| for (a, t) ∈ [−25.010858 . . . , 25.010858 . . .] × [ 1
2 , 1] as in Figure 1.3.4, whose domain contains the first six nontrivial zeros of ζ(s), i.e., the first three with positive imaginary part and the first three with negative imaginary part. Figure 1.3.5 is a 3D plot of the graph of (t, ζ( 1
2 + it)) on [−100, 100], and Figure 1.3.6 is its projection onto the complex plane. These graphs provide a way of visualizing the function ζ(s) and its zeros. Further graphs for this purpose are provided in Section 4.2.
Figure 1.3.1. Graph of ζ(t) on [−25, 25]
Figure 1.3.2. Graph of |ζ( 1
2 + it)| on [−50, 50]
To describe the explicit formula for π(x) in terms of the zeros of ζ(s), we first travel back a little to 1838, when Dirichlet observed that π(x) can be well approximated by the


 1.3. THE PRIME NUMBERS, ANALYTICALLY 25
Figure 1.3.3. Graph of |ζ(1 + it)| (in black) and |ζ( 2
3 + it)| (in red) on [−50, 50]
Figure 1.3.4. Graph of |ζ(a + it)| on [−25.010858 . . . , 25.010858 . . .] × [ 1
2 , 1]
logarithmic integral function
li(x) =
Zx
0
dt
log t,
where the Cauchy principal value of the integral is assumed. The function li(x) is a particular antiderivative of 1
log x . Figure 1.3.7 provides graphs on the interval [0, 10] of both li(x) and
its derivative 1
log x . Since
d
dx
x
log x = log x − 1
(log x)2 ∼ 1
log x = d
dx li(x) (x → ∞),
L’Hôpital’s rule implies that
li(x) ∼ x
log x (x → ∞).
It follows that the prime number theorem is equivalent to
π(x) ∼ li(x) (x → ∞).


 26 1. A BRIEF HISTORY OF PRIMES
Figure 1.3.5. Graph of (t, ζ( 1
2 + it)) and (t, 0 + i0) on [−100, 100]
Figure 1.3.6. Parametric plot of ζ( 1
2 + it) on [−100, 100]
However, li(x) is a significantly better approximation to π(x) than is x
log x or any other known
rational function of x and log x. Note that the logarithmic integral approximation of π(x) is motivated by Cramér’s model of the primes, since, under that model, π(x) is approximated by P
1<n≤x
1
log n , and an easy calculus exercise shows that the limit
nli→m∞ li(x) −
X
1<n≤x
1
log n
!
>0
exists: see Figure 1.3.8 for a graph of the “logarithmic sum” function P
1<n≤x
1
log n in compar
ison to li(x). However, it was Riemann’s brilliant insight, described below, that explained more precisely how the functions π(x) and li(x) are related to one another. Let
π0(x) = lεi→m0
π(x + ε) + π(x − ε)
2 = π(x+) + π(x−)
2 , ∀x ≥ 0.
The function π0(x) is equal to the prime counting function π(x) except at its discontinuities (namely, at the primes), where π0(x) assumes the average of the limit from the right and the limit from the left of π(x). The Riemann–von Mangoldt explicit formula for π0(x)


 1.3. THE PRIME NUMBERS, ANALYTICALLY 27
Figure 1.3.7. Graph of li(x) (in black) and its derivative 1
log x (in red) on [0, 10]
Figure 1.3.8. Graph of li(x) (in black) and the “logarithmic sum” function P
1<n≤x
1 log n
(in red) on [0, 20]
states that
π0(x) = Ri(x) −
∞
X
n=1
X
ρ
μ(n)
n Ei ρ log x
n , ∀x > 1, (1.3.1)
where the inner sum is over all of the zeros ρ of the Riemann zeta function, with the nontrivial zeros taken in order of increasing absolute value of the imaginary part and repeated to multiplicity, and with the real zeros summed in the natural order −2, −4, −6, −8, . . .. Here, μ(n) is the Möbius function and Ei(s) is the complex exponential integral function, defined in Sections 3.3 and 4.5, respectively, and Riemann’s function Ri(x) is defined by
Ri(x) =
∞
X
n=1
μ(n)
n li(x1/n) =
∞
X
n=1
μ(n)
n Ei log x
n,
where the latter equality follows from the fact that li(x) = Ei(log x) for all x > 0. In particular, the Riemann–von Mangoldt explicit formula implies that all of the information about the prime numbers is encoded by the zeros of ζ(s), along with the functions Ei(s) and μ(n). See [132] for an implementation of the Riemann von–Mangoldt explicit formula in Sage. A more in-depth discussion of the formula and its relation to the prime number theorem is provided in Sections 5.1 and 5.2. In his landmark paper, Riemann wrote down an equivalent form of the explicit formula (1.3.1) (specifically, (5.1.4)). However, Riemann’s formula was not proved rigorously until 1895, by von Mangoldt. Then, just one year later, the prime number theorem was finally proved. Both 1896 proofs of the prime number theorem relied on showing that the prime number theorem is equivalent to ζ(s) having no zeros on the line {s ∈ C : Re s = 1}, and then


 28 1. A BRIEF HISTORY OF PRIMES
proving that in fact ζ(s) has no such zeros. The Riemann–von Mangoldt explicit formula is precisely what made the first part of those proofs possible. Thus, both Riemann and von Mangoldt played major roles in the eventual proofs of the prime number theorem. The “main term” of the explicit formula (1.3.1) for π0(x) is the smooth function Ri(x), which captures the “size” of π(x) in the sense that
π(x) ∼ π0(x) ∼ Ri(x) ∼ li(x) (x → ∞)
The terms μ(n)
n Ei ρ log x
n + Ei ρ log x
n , grouped together in conjugate pairs, are smooth
oscillatory terms. Along with the somewhat neglible terms μ(n)
n Ei −2k log x
n over the real zeros ρ = −2k, together they precisely capture all of the deviations of π0(x) from Ri(x), in that their sum over all n and ρ is equal to Ri(x) − π0(x). Figure 1.3.9 provides a graph of the functions π(x), li(x), and Ri(x) on the interval [1, 250]. Figure 1.3.10 compares the differences li(x) − Ri(x), Ri(x) − π(x) and li(x) − π(x) on the interval [1, 100000]. One has the relationship
li(x) − π(x) = (Ri(x) − π(x)) + (li(x) − Ri(x)),
where the smooth function
li(x) − Ri(x) ∼ li(x1/2)
2 ∼ x1/2
2 log(x1/2) =
√x
log x (x → ∞) (1.3.2)
tracks the function li(x) − π(x) much more closely than it does the function Ri(x) − π(x), at least for small x.
Figure 1.3.9. Graph of π(x) (in black), Ri(x) (in red), and li(x) (in blue) on [1, 250]
In 1899, just a few years after his proof of the prime number theorem, de la Vallée Poussin proved a much stronger version of the prime number theorem [62], which we call the prime number theorem with error bound.
Theorem 1.3.1 (Prime number theorem with error bound [62]). There exists a constant C > 0 such that
li(x) − π(x) = O x
eC√log x (x → ∞)
Since xt = o(ec√x) (x → ∞) for all t ∈ R and all c > 0, the prime number theorem with error bound implies that
li(x) − π(x) = o x
(log x)t (x → ∞) (1.3.3)


 1.3. THE PRIME NUMBERS, ANALYTICALLY 29
Figure 1.3.10. Graph of li(x) − Ri(x) (in black), Ri(x) − π(x) (in red) and li(x) − π(x) (in blue) on [1, 100000]
for all t ∈ R. By contrast, the prime number theorem is equivalent to
li(x) − π(x) = o(li(x)) (x → ∞),
and thus to
li(x) − π(x) = o x
log x (x → ∞).
Thus, the prime number theorem with error bound is a substantial improvement over the prime number theorem.
li(x) − π(x) = O(√x log x) (x → ∞). (1.3.4)
In 1976 [262], Schoenfeld proved an effective version of von Koch’s result, namely, that the Riemann hypothesis is equivalent to
| li(x) − π(x)| ≤ 1
8π
√x log x, ∀x ≥ 2657.
Of course, there is no guarantee that the Riemann hypothesis is true. Thus, we follow an unspoken tradition (following Ingham in [136], for example) and let
Θ = sup{Re ρ : ρ ∈ C\R, ζ(ρ) = 0}
denote the supremum of the real parts of the nontrivial zeros of the Riemann zeta function, which we call the Riemann constant. Equivalently, one has
Θ = inf{t ∈ R : ∀s ∈ C\R (Re s > t ⇒ ζ(s) ̸= 0)}.
Since ζ(s) has zeros (in fact, infinitely many) on the critical line, and all of its nontrivial zeros lie in the critical strip and are symmetric about the critical line, one has
1
2 ≤Θ≤1
and
0 ≤ 1 − Θ = inf{Re ρ : ρ ∈ C\R, ζ(ρ) = 0} ≤ 1
2.
It follows that the vertical strip {s ∈ C : Re s ∈ [1−Θ, Θ]} is the smallest closed vertical strip containing all of the nontrivial zeros of ζ(s). Note also that Θ − 1
2 is the supremum of the distances of the nontrivial zeros of ζ(s) to the critical line. It follows from these observations that Riemann hypothesis is equivalent to Θ = 1
2 , to 1 − Θ = 1
2 , and to Θ = 1 − Θ. In particular, the problem of settling the Riemann hypothesis generalizes as follows.


 30 1. A BRIEF HISTORY OF PRIMES
(Outstanding) Problem 1.3.2. Compute the Riemann constant Θ.
One of the main reasons that the Riemann constant is of fundamental importance in number theory is that von Koch’s Riemann hypothesis equivalent (1.3.4) generalizes to the following unconditional result.
Theorem 1.3.3 ([136, Theorems 30 and 31] [141, Theorem 12.3] [215, Theorem 15.2 and Exercise 13.1.1.1]). One has
Θ = inf t ∈ R : li(x) − π(x) = O(xt) (x → ∞)
and
Θ = min t ∈ R : li(x) − π(x) = O(xt log x) (x → ∞) .
It follows from Theorem 1.3.3 that the Riemann constant is the unique real number Θ such that the O bound li(x) − π(x) = O(xt) (x → ∞) holds for all t > Θ and fails for all t < Θ. Therefore, since Θ ≥ 1
2 , one has
li(x) − π(x) ̸= O(xt) (x → ∞), ∀t < 1
2.
It also follows that, if the Riemann hypothesis is false, that is, if some zero ρ of ζ(s) lies to the right of the critical line, then Θ ≥ Re ρ > 1
2 and therefore
li(x) − π(x) ̸= O(xt) (x → ∞)
for all t < Re ρ, including t = 1
2 and the uncountably many real numbers strictly between 1
2
and Re ρ. Thus, the Riemann hypothesis says that the approximation li(x) of π(x) is about as close to π(x) as is prima facie possible. More generally, the Riemann constant Θ sets precise limits on how well li(x) approximates π(x) for large x, and, moreover, the smaller Θ is, the better the approximation. The worst case scenario for the error function li(x) − π(x), then, is Θ = 1, which we dub the anti-Riemann hypothesis. In spirit opposite to the Riemann hypothesis, the anti-Riemann hypothesis says that de la Vallée Poussin’s prime number theorem with error bound is close to the best error bound possible. To this day, proofs of the strongest known bounds on the error li(x) − π(x) are based on the Riemann–von Mangoldt explicit formula for certain functions related to π(x) and rather sophisticated methods for verifying zero-free regions for ζ(s) in the critical strip. Even the most current of methods have not proved Θ < 1 and allow us only to bound the zeros of ζ(s) asymptotically away from the line {s ∈ C : Re s = 1} The largest known zero-free region of the critical strip yields the following best known error bound to date.
Theorem 1.3.4 (Prime number theorem with error bound [93]). One has
li(x) − π(x) = O xe−A(log x)3/5(log log x)−1/5 (x → ∞),
where A = 0.2098.
Any such result superceding de la Vallée Poussin’s prime number theorem with error bound (Theorem 1.3.1) of 1899 is also called a prime number theorem with error bound. Note that the exponent 1 of x appearing in the O bound is precisely the best known upper
bound of Θ, and the improvement over de la Vallée Poussin’s O bound O xe−C√log x is
due to an enlargement of the zero-free region of ζ(s). Such improvements are extraordinarily difficult to carry out, and yet, by some measures, they have not brought us much closer to proving the Riemann hypothesis since 1899. Thus, it would seem that either newer and


 1.3. THE PRIME NUMBERS, ANALYTICALLY 31
substantially stronger techniques are needed, or the Riemann hypothesis is false (or both, even, if 1
2 < Θ < 1).
Nevertheless, the situation is not hopeless, as, subsequent to von Koch’s 1901 result, hundreds of other statements have been shown to be equivalent to the Riemann hypothesis, e.g., those collected in [38] [39]. Thus, even if the Riemann hypothesis is eventually proved false, the negation of hundreds of statements will immediately have been proved true. For these and other reasons, the problem of settling the Riemann hypothesis is widely regarded as one of the most important, if not the most important, unsolved problems in mathematics today. Absent a solution to Problem 1.3.2, the following research program is therefore warranted.
Problem 1.3.5. Given a known equivalent of the Riemann hypothesis, generalize the equivalence to an unconditional statement regarding the Riemann constant Θ.
Several widely known examples of such unconditional statements, along with several new ones, are discussed in Part 3. Let us assume, for the moment, that the Riemann hypothesis is true. It might appear, then, based on values of π(x) that have been computed or estimated, that the conjectural
error bound (1.3.4) can be improved to li(x) − π(x) = O
√x
log x (x → ∞). For example,
Hardy wrote in 1910 that “there is reason to anticipate that” this error bound holds [117, p. 48]. However, as Riesel noted in 1994:
Judging only from the values [given in a table] we might even try to estimate
the order of magnitude of li(x) − π(x) and find it to be about √x/ log x. However, for large values of x, this is completely wrong!” [250, p. 52].
Indeed, although the big O estimate above is suggested by numerical data, it is known to be false because of Littlewood’s celebrated 1914 result, Theorem 1.3.6 below, which we call Littlewood’s theorem [185] [136, Theorem 35] [215, Theorem 15.11] [216, Theorem 6.20]
[236, Theorem 6.3]. One writes f (x) = Ω±(g(x)) (x → a) if lim supx→a
f (x)
|g(x)| is positive and
lim infx→a
f (x)
|g(x)| is negative (both possibly infinite).
Theorem 1.3.6 (Littlewood’s theorem [185]). One has
li(x) − π(x) = Ω±
√x log log log x
log x (x → ∞).
As a consequence of Littlewood’s theorem, one has
li(x) − π(x) ̸= o
√x log log log x
log x (x → ∞),
and therefore also
li(x) − π(x) ̸= O
√x
log x (x → ∞).
Littlewood’s theorem is unconditional and provides the strongest known lower bound on li(x) − π(x) to date.
Back in 1914, Littlewood’s result was astonishing, not only because it was quite possibly the first occurrence of the function log log log x in relationship to the prime numbers, but


 32 1. A BRIEF HISTORY OF PRIMES
also because it had the immediate consequence that
li(x) − π(x) = Ω±(1) (x → ∞)
and therefore the function li(x) − π(x) changes sign an infinite number of times. To this day, no one knows any specific value of x ≥ μ for which li(x) − π(x) < 0, where μ = 1.451369234883 . . . is the unique positive zero of li(x), known as the Ramanujan–Soldner constant. (It is easy to see that li(x) − π(x) < 0 for 0 < x < μ.) It is currently known that the infimum s of all x ≥ μ such that li(x) − π(x) < 0, known as Skewes’ number, is at least 1020 and at most e727.9513. For x ≈ s, or for any other number x where li(x) − π(x) is approximately 0, the function Ri(x) − π(x) is approximately equal to Ri(x) − li(x) ≈
−
√x
log x ≪ 0. Thus, the trend observed earlier in Figures 1.3.9 and 1.3.10 that Ri(x) is a
better approximation of π(x) than li(x) is violated whenever li(x) − π(x) ≈ 0, or more generally, precisely when
li(x) − π(x)
li(x) − Ri(x) < 1
2,
that is,
Ri(x) − π(x)
li(x) − Ri(x) < −1
2,
where the difference between the two functions above is equal to 1, and where we assume also that x > ν, where ν = 2.68945880489 . . . is the largest positive root of li(x) − Ri(x). Figure 1.3.11 provides a graph of the two functions on a lin-log scale, that is, with ex substituted for x, on the interval [2, 30], where the first function is graphed in blue and the second in red. By Littlewood’s theorem, the functions in blue and red attain arbitrarily large positive and large negative values, even when further divided by log log log x. Skewes’ number is the precise point at which the blue graph first dips down below the x-axis, i.e., when the red graph first dips down below the line y = −1. Moreover, li(ex) is a better approximation of π(ex) than is Ri(ex) precisely for those x for which the blue graph lies below the line y = 1
2 , which is also where the red graph lies below the line y = − 1
2 . One
can see from the graph that, at least on the interval [2, 30], the function Ri(ex) is the overall “winner” in this competition to approximate π(x). A search on Mathematica carried out by D. Stoll [276] reveals that the first interval for x > ν on which li(x) is a better approximation to π(x) is [3445027, 3445031.758 . . .), where 3445027 = p246588 = e15.052442... is a prime number with subsequent prime p246589 = 3445093, and therefore the function
li(x)−π(x)
li(x)−Ri(x) is continuous and increasing on the interval [3445027, 3445093), attaining the value 0.498060 . . . at the left endpoint and approaching the value 0.524956 . . . at the right endpoint (from the left). The next interval on which li(x) wins over Ri(x) is the rather small interval [3445649, 3445649.000498 . . .), where 3445649 = p246629 = e15.052622... is prime. Figure 1.3.12
provides a graph of the function li(x)−π(x)
li(x)−Ri(x) on the interval [3444800, 3446300], which includes
the first eight intervals, including the first two mentioned above, on which li(x) wins over Ri(x).
Unlike the number 3445027, Skewes’ number is extremely difficult to calculate, not only because it is very large with respect to our ability to compute π(x), but also because of the following surprising result. Let X denote the set
X = {x ∈ [log 2, ∞) : Li(ex) ≥ π(ex)} ,


 1.3. THE PRIME NUMBERS, ANALYTICALLY 33
Figure 1.3.11. Graphs of Ri(ex)−π(ex)
li(ex)−Ri(ex) (in red) and li(ex)−π(ex)
li(ex)−Ri(ex) = 1 + Ri(ex)−π(ex)
li(ex)−Ri(ex) (in
blue) and 1, 1
2 , and − 1
2 (in green) on [2, 30]
Figure 1.3.12. Graph of li(x)−π(x)
li(x)−Ri(x) (in blue) and 1
2 (in green) on [3444800, 3446300]
where
Li(x) =
Zx
2
1
log t dt = li(x) − li(2) = li(x) − 1.045163780117 . . . .
It is known [258] that
xli→m∞
1
x − log 2
Z
t∈[log 2,x]∩X
dt = 0.99999973 . . . .
In other words, the asymptotic density of the set X of all x ≥ log 2 such that li(ex) − li(2) ≥ π(ex) is equal to 0.99999973 . . .. Thus, counterexamples to li(x) − li(2) ≥ π(x), hence also counterexamples to li(x) ≥ π(x), are extremely rare. A general lesson one learns from this is that numerical considerations sometimes do not carry much weight in analytic number theory, especially when iterated logarithms might be lurking in the background. See Table 1.3.2 for a list of some major classical theorems in analytic number theory concerning the distribution of the primes, with their original sources, along with references to more recent proofs in the literature. The uninitiated reader seeking expertise in analytic number theory should consider undertaking a careful study of some of those proofs.
Remark 1.3.7 (The Riemann zeta function in physics). The Riemann zeta function has several applications to physics, most notably, to zeta function regularization in quantum field theory. For example, the value ζ(−3) = 1
120 is used in the derivation of the Casimir effect, and ζ(s) more broadly is used in the regularization of the energy–momentum tensor in curved spacetime, e.g., in the calculation of the vacuum expectation value of the energy of a particle field. Additionally, the constant ζ(4) = π4
90 arises in the theory


 34 1. A BRIEF HISTORY OF PRIMES
Table 1.3.2. Proofs of classical theorems concerning the distribution of the primes
Theorem Proofs
Prime number theorem [6, Chapters 4 and 13] [18, Chapter 5] [70, Chapter 4] [61] [114] [60, Chapters 4 and 5] [113, Chapter 9] [136, Chapter II] [152, Chapter 6] [154] [215, Chapter 8] [216, Chapter 5] [219, Chapter VII] [236, Chapter 5] [280, Chapter III] [301] [304, Chapter 2] Prime number theorems [18, Chapter 8] [32, Section 3.5] [58] [56, Chapter 18] with error bound [62] [70, Chapter 5] [93] [136, Chapter III] [141, Chapter 12] [157, Chapter 8] [194] [215, Chapter 6] [216, Chapters 5 and 6] [228, Chapter 6] [230, Chapter 4] Riemann–von Mangoldt [18, Chapter 8] [32, Section 3.5] [56, Chapter 17] explicit formulas [70, Chapter 3] [136, Chapter IV] [141, Chapter 12] [248] [199] [157, Chapters 5 and 8] [216, Chapter 6] [228, Chapter 10] [230, Chapter 3] Littlewood’s theorem [18, Chapter 11] [38, Theorem 4.13] [136, Theorem 35] [185] [215, Theorem 15.11] [216, Theorem 6.20] [236, Chapter 6] Dirichlet’s theorem on [6, Chapter 7] [18, Chapter 9] [32, Section 3.4] primes in arithmetic [56, Chapter 22] [60, Chapters 13 and 14] progression [65] [140, Chapter 16] [215, Chapters 4 and 11] [216, Chapter 2] [228, Chapter 7] [265, Chapter VI] [304, Chapter 5]
of black-body radiation, in the derivation of the Stefan–Boltzmann law from Planck’s law, where
σ = 2π5k4
15h3c2 = 5.670374 . . . · 10−8 W m−2 K−4
is the Stefan–Boltzmann constant, and where k = 1.380649 . . .·10−23 J · K−1 is the Boltzmann constant and c = 299792458 m · s−1 is the speed of light in a vacuum. An extensive list of appearances of the Riemann zeta function in physics can be found at http://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/physics1.htm (accessed by the author on 1 April 2024).
Remark 1.3.8 (Legendre’s constant). The first actual published statement of something close to the prime number theorem was made by Legendre in 1798 [177, p. 19], which he refined further in 1808 [178, pp. 394–398]. Legendre expressed his 1798 conjecture as follows (English translation):
It is probable that the strict formula which gives the value of b [i.e., π(a)] when a is very large is of the form a
A log a+B , A and B denoting constant coefficients and log a denoting a hyperbolic logarithm. The exact determination of these coefficients would be a curious problem and worthy of exercising the astuteness of analysts.
In 1808, he wrote (English translation):
Although the sequence of prime numbers is extremely irregular, one can however find, with a very satisfying precision, how many of these numbers there are from 1 to a given limit x. The formula that resolves this question is
y= x
log x − 1.08366 .
. . . [Table of values of π(x) given and each compared with y] . . . It is impossible that a formula could represent a series of numbers of such a great extent, and one subject to frequent anomalies, [completely] accurately. There is therefore no doubt, not only that the general law is represented by a function of the form x
A log x+B , but that the coefficients A and B indeed have values very close to A = 1 . . ., B = −1.08366.
Due to a lack of rigor by today’s standards, it is difficult to give a faithful and precise interpretation of Legendre’s conjectures.


 1.3. THE PRIME NUMBERS, ANALYTICALLY 35
Following Chebyshev and Gauss, we let A denote the unique function [2, ∞) −→ R such that
π(x) = x
log x − A(x)
for all x ≥ 2, so that
A(x) = log x − 1
p(x) .
A generous interpretation of Legendre’s 1808 conjecture is that the limit
L = xli→m∞ A(x)
exists and is approximately equal to 1.08366. The limit L is now referred to as Legendre’s constant. Clearly, the existence of the limit L implies the prime number theorem. In 1848, Chebyshev proved [45] that if Legendre’s constant exists then it must equal 1; more specifically, he proved that
lim inf
x→∞ A(x) ≤ 1 ≤ lim sup
x→∞
A(x).
In fact, the asymptotic relation (1.2.4) for n = 1, that is, the relation
p(x) − 1
log x ∼ 1
(log x)2 (x → ∞),
is equivalent to
A(x) = p(x) − 1
log x
log x
p(x) ∼ 1
(log x)2 (log x)2 ∼ 1 (x → ∞)
and thus to the existence of L, and each of these equivalent statements implies the prime number theorem. According to F. L. Bauer, “Legendre’s mistake can be explained easily: the largest tables of primes were those of J. H. Lambert (1770), going up to 105, and of G. Vega (1796), going up to 4 · 105” [20]. Using Riemann’s approximation Ri(x) to π(x), we can provide a more detailed explanation for Legendre’s approximation 1.08366 of the constant L = 1. Figure 1.3.13 compares the functions A(ex) = x − ex
π (ex )
and x − ex
Ri(ex) on the interval [3, 25], and Figure 1.3.14 compares the two functions on a smaller interval.
It is likely not a mere coincidence that the function log x − x
Ri(x) appears to attain a global maximum
of approximately 1.08356 at x ≈ 216811 ≈ e12.2871, with a very small derivative nearby that appears to attain a local (and perhaps even global) minimum of only about −3.68 · 10−9 somewhat near the point (4.75 · 105, 1.0828). See Figure 1.3.15 for a graph of the derivative of log x − x
Ri(x) near its apparent local minimum. Since log x − x
Ri(x) approximates the “center” of the graph of A(x), the misleading features of the
function log x − x
Ri(x) described above would explain why Legendre arrived at something close to 1.08356,
namely, his approximation 1.08366, as an approximation of the constant L. Even at x = 1029 one has A(x) = 1.015696108866115 . . . and log x − x
Ri(x) = 1.015696108866137 . . ., thus indicating that convergence of A(x) to the limit 1 is slow. Regarding this very matter, in his 1849 letter to Encke [99, pp. 444–447], Gauss made some prescient remarks, based on his extensive calculations (English translation):
It appears that, with increasing n, the (average) value of A decreases; however, I dare not conjecture whether the limit as n approaches infinity is 1 or a number different from 1. I cannot say that there is any justification for expecting a very simple limiting value; on the other hand, the excess of A over 1 might well be a quantity of the order of 1
log n .
Gauss’ speculations turned out to be correct, in that
A(x) − 1 ∼ 1
log x (x → ∞), (1.3.5)


 36 1. A BRIEF HISTORY OF PRIMES
and this explains why the convergence of A(x) to Legendre’s constant is so slow. Indeed, by the prime number theorem and the asymptotic relation (1.2.4) for n = 3, one has
A(x) − 1 = ((log x − 1) p(x) − 1) 1
p(x)
= (log x − 1) 1
log x + 1
(log x)2 + 2
(log x)3 + O 1
(log x)4 − 1 1
p(x)
=1
(log x)2 + O 1
(log x)3
1 p(x)
=1
log x + O 1
(log x)2 (x → ∞),
which implies (1.3.5).
Figure 1.3.13. Graph of x − ex
π(ex) and x − ex
Ri(ex) on [3, 25]
Figure 1.3.14. Graph of x − ex
Ri(ex) and x − ex
π(ex) on [log(104), log(107)]
Figure 1.3.15. Graph of d
dx log x − x
Ri(x) on [420000, 550000]


 CHAPTER 2
Asymptotic analysis
In this chapter, we discuss asymptotic relations and asymptotic expansions. We introduce the notion of the degree of a real function (which we study in much greater detail in Section 6.1), and we apply it to the study of slowly varying functions and regularly varying functions, two natural notions that have applications to analysis, probability theory, and analytic number theory. We also discuss the Euler–Maclaurin formula, Karamata’s integral representation theorem, and Karamata’s insttegral theorem.
2.1. Asymptotic relations
Let a ∈ R, and let f, g ∈ RRa (where RRa denotes the set of all real functions f such that a is a limit point of dom f ). Assume also that dom g contains the intersection of dom f with some punctured neighborhood of a. One defines the following.
(1) f (x) = O(g(x)) (x → a), also written f (x) ≪ g(x) (x → a), if for some M > 0 one has |f (x)| ≤ M |g(x)| for all x in the intersection of dom f with some punctured neighborhood of a. (2) f (x) ≫ g(x) (x → a) if for some M > 0 one has |f (x)| ≥ M |g(x)| for all x in the intersection of dom f with some punctured neighborhood of a.
(3) f (x) ≍ g(x) (x → a) if f (x) ≪ g(x) (x → a) and f (x) ≫ g(x) (x → a).
(4) f (x) = o(g(x)) (x → a) if for all M > 0 one has |f (x)| ≤ M |g(x)| for all x in the intersection of dom f with some punctured neighborhood of a. (5) f (x) ∼ g(x) (x → a) if f (x) − g(x) = o(g(x)) (x → a).
(6) f (x) = Ω+(g(x)) (x → a) if there exists an M > 0 such that for every x in a punctured neighborhood of a there exists a y ̸= a closer to a than x such that f (y) > M |g(y)|.
(7) f (x) = Ω−(g(x)) (x → a) if there exists an M > 0 such that for every x in a punctured neighborhood of a there exists a y ̸= a closer to a than x such that f (y) > −M |g(y)|.
(8) f (x) = Ω±(g(x)) (x → a) if f (x) = Ω+(g(x)) (x → a) and f (x) = Ω−(g(x)) (x → a).
Note that both of the conditions f (x) = o(g(x)) (x → a) and f (x) ∼ g(x) (x → a) are stronger than the condition f (x) = O(g(x)) (x → a), and all three conditions require that dom g contains the intersection of dom f with some punctured neighborhood of a. The relations ∼, O, and o are transitive, in the obvious sense. Moreover, if f (x) = O(g(x)) (x → a) and g(x) = o(h(x)) (x → a), or if f (x) = o(g(x)) (x → a) and g(x) = O(h(x)) (x → a), then f (x) = o(h(x)) (x → a). The relations ≍ and ∼ are symmetric on functions f, g ∈ RRa such that U ∩ dom f = U ∩ dom g for some punctured neighborhood U of a. Moreover, a function f ∈ RRa satisfies f (x) ∼ 0 (x → a) if and only if f is zero on the intersection of dom f with some punctured neighborhood of a. Note, also, that, if f (x) = Ω+(g(x)) (x → a) or if f (x) = Ω−(g(x)) (x → a), then f (x) ̸= o(g(x)) (x → a).
37


 38 2. ASYMPTOTIC ANALYSIS
As above, let f, g ∈ RRa, where dom g contains the intersection of dom f with some punctured neighborhood of a. If also g is nonzero on the intersection of dom f with some punctured neighborhood of a, then the relations (1)–(8) defined above simplify as in the following proposition.
Proposition 2.1.1. Let f, g ∈ RRa, where g is defined and nonzero on the intersection of dom f with some punctured neighborhood of a. One has the following.
(1) f (x) = O(g(x)) (x → a) if and only if
lim sup
x→a
f (x)
g(x) < ∞.
(2) f (x) ≫ g(x) (x → a) if and only if
lim inf
x→a
f (x)
g(x) > 0.
(3) f (x) ≍ g(x) (x → a) if and only if
lim sup
x→a
f (x)
g(x) < ∞ and lim inf
x→a
f (x)
g(x) > 0.
(4) f (x) = o(g(x)) (x → a) if and only if
lxi→ma
f (x)
g(x) = 0,
if and only if
lim sup
x→a
f (x)
g(x) = 0.
(5) f (x) ∼ g(x) (x → a) if and only if
lxi→ma
f (x)
g(x) = 1.
(6) f (x) = Ω+(g(x)) (x → a) if and only if
lim sup
x→a
f (x)
|g(x)| > 0.
(7) f (x) = Ω−(g(x)) (x → a) if and only if
lim inf
x→a
f (x)
|g(x)| < 0.
(8) f (x) = Ω±(g(x)) (x → a) if and only if
lim sup
x→a
f (x)
|g(x)| > 0 and lim inf
x→a
f (x)
|g(x)| < 0.
When we write f (x) ̸= O(g(x)) (x → a), or f (x) ̸≍ g(x) (x → a), etc., for any of the relations above, we mean not only that the negation of the given relation holds, but also that dom g contains the intersection of dom f with some punctured neighborhood of a. Thus, for example, if f is defined on all of R, then f |Z(x) = O(f (x)) (x → ∞), but it is neither the case that f (x) = O(f |Z(x)) (x → ∞) nor that f (x) ̸= O(f |Z(x)) (x → ∞). We follow the convention that O(g(x)) (resp., o(g(x))) denotes some function f such that


 2.1. ASYMPTOTIC RELATIONS 39
f (x) = O(g(x)) (x → a) (resp., f (x) = o(g(x)) (x → a)), assuming that a is understood by context. Our domain conventions can be summarized by stipulating that a given asymptotic relation must make sense for all x ̸= a near a in the domain of the function appearing on the left of the given relation. The rationale for this convention is that it is natural to interpret any asymptotic relation as expressing a property of the function appearing on the left. Thus, for example, when we write f (x) = h(x) + O(g(x)) (x → a), we mean that f (x) − h(x) = O(g(x)) (x → a) and that both dom g and dom h contain the intersection of dom f with some punctured neighborhood of a. In a similar vein, the relations f (x) ≪ g(x) (x → a) and g(x) ≫ f (x) (x → a) are equivalent if and only if U ∩ dom f = U ∩ dom g for some punctured neighborhood U of a, and likewise for the relations f (x) ≍ g(x) (x → a) and g(x) ≍ f (x) (x → a) and for the relations f (x) ∼ g(x) (x → a) and g(x) ∼ f (x) (x → a). Of course, if all functions involved are defined on some punctured neighborhood of a, or if they all have the same domain, then these domain restrictions are automatic.
Example 2.1.2. Let f, g ∈ RR∞ and t, u, A ∈ R with A ̸= 0. One has the following.
(1) f (x) = O(1) (x → ∞) if and only if f (x) is eventually bounded. (2) f (x) = o(1) (x → ∞) if and only if limx→∞ f (x) = 0. (3) sin x = O(1) (x → ∞). (4) sin x ̸= o(1) (x → ∞). (5) sin x = Ω±(1) (x → ∞).
(6) xt = O(xu) (x → ∞) if and only if t ≤ u. (7) xt = o(xu) (x → ∞) if and only if t < u. (8) xt = o(ex) (x → ∞) for all t ∈ R. (9) log x = o(xt) (x → ∞) if and only if t > 0, if and only if log x = O(xt) (x → ∞). (10) If f and g are polynomials, then f (x) = O(g(x)) (x → ∞) if and only if deg f ≤ deg g.
(11) If f and g are polynomials, then f (x) = o(g(x)) (x → ∞) if and only if deg f < deg g. (12) If f and g are polynomials, then f (x) ∼ g(x) (x → ∞) if and only if f and g have the same leading term. (13) f (x) ∼ Axn (x → ∞) if f is a polynomial of degree n with leading term Axn. (14) f (x) ∼ A (x → ∞) if and only if limx→∞ f (x) = A.
We note the following properties of the O and o relations.
Proposition 2.1.3. Let a ∈ R, let f1, f2, g1, g2, g ∈ RRa with a a limit point of dom f1 ∩ dom f2, and let r1, r2 ∈ R. One has the following.
(1) If
f1(x) = O(g1(x)) (x → a) and f2(x) = O(g2(x)) (x → a),
then
f1(x) + f2(x) = O(max(|g1(x)|, |g2(x)|)) (x → a)
and
f1(x)f2(x) = O(g1(x)g2(x)) (x → a).
(2) If
f1(x) = O(g(x)) (x → a) and f2(x) = O(g(x)) (x → a),
then
r1f1(x) + r2f2(x) = O(g(x)) (x → a).


 40 2. ASYMPTOTIC ANALYSIS
(3) If
f1(x) = o(g1(x)) (x → a) and f2(x) = o(g2(x)) (x → a),
then
f1(x) + f2(x) = o(max(|g1(x)|, |g2(x)|)) (x → a)
and
f1(x)f2(x) = o(g1(x)g2(x)) (x → a).
(4) If
f1(x) = o(g(x)) (x → a) and f2(x) = o(g(x)) (x → a),
then
r1f1(x) + r2f2(x) = o(g(x)) (x → a).
In this book, we are interested primarily in the case where a = ∞. However, we also require generalizations of the O, o, ≍, and ∼ relations to complex functions, where we then assume that a ∈ C ∪ {∞}. To obtain these definitions, one replaces the real absolute value in the definitions above with the complex absolute value, and one replaces punctured real neighborhoods with punctured complex neighborhoods, and then appropriate analogues of the results above hold for complex functions defined on a subset of C containing a as a limit point.
2.2. Asymptotic expansions
Let a ∈ R (resp, a ∈ C ∪ {∞}). An asymptotic sequence at a is a sequence {φn}∞
n=1
of real (resp., complex) functions φn such that
φn+1(x) = o(φn(x)) (x → a)
for all n ≥ 1 (so a is a limit point of dom φn for each n). Let {φn} be an asymptotic sequence at a, let f be a real (resp., complex) function, and let {an} be a sequence of real (resp., complex) numbers. The function f is said to have the asymptotic expansion
f (x) ≃
∞
X
n=1
anφn(x) (x → a) (2.2.1)
(at a with respect to {φn}) if
f (x) =
n
X
k=1
akφk(x) + o(φn(x)) (x → a) (2.2.2)
for all positive integers n (which requires that φn for each positive integer n be defined on the intersection of dom f with some punctured neighborhood of a).
Remark 2.2.1.
(1) It is clear that, for a given positive integer n, condition (2.2.2) implies that
f (x) =
n−1
X
k=1
akφk(x) + O(φn(x)) (x → a), (2.2.3)
which in turn implies that f (x) = Pn−1
k=1 akφk(x) + o(φn−1(x)) (x → a) if n ≥ 2. Consequently, the asymptotic expansion (2.2.1) holds if and only if either (2.2.2) or (2.2.3) holds for infinitely many integers n ≥ 1, if and only if (2.2.3) holds for all n ≥ 1.


 2.2. ASYMPTOTIC EXPANSIONS 41
(2) For any positive integer n, if an ̸= 0 and φk for each k < n is defined on the intersection of dom f with some punctured neighborhood of a, then (2.2.2) is equivalent to
f (x) −
n−1
X
k=1
akφk(x) ∼ anφn(x) (x → a).
Example 2.2.2.
(1) Important examples of asymptotic expansions over R and C follow from Taylor’s theorem: if f is real or complex function defined in a neighborhood of some number a, then one has an asymptotic expansion f (x) ≃ P∞
n=0 an(x − a)n (x → a) of f at
a with respect to the asymptotic sequence {(x − a)n} if f is infinitely differentiable
at a, in which case an = f(n)(a)
n! for all n. This also applies to f over C at ∞ (resp.,
over R at ∞, over R at −∞) by considering the function f ( 1
x ) with respect to the
asymptotic sequence 1
xk at 0 (resp., at 0+, at 0−). (2) One can generalize the notion of an asymptotic expansion (of infinite order) to the notion of an asymptotic expansion of finite order N , and then f has an asymptotic expansion f (x) ≃ PN
n=0 an(x − a)n (x → a) of order N + 1 at a with respect to the
asymptotic sequence {(x − a)n} if f is N -times differentiable at a, in which case
an = f (n)(a)
n! for all n ≤ N .
(3) Two asymptotic expansions at a with respect to {(x − a)n} or at ∞ with respect to
1
xn can be added, subtracted, multiplied, divided, and composed just like formal power series.
Excellent references on the theory of asymptotic expansions include [76] [79] [226] [296]. The following result provides some necessary and sufficient conditions for two functions to have the same asymptotic expansion with respect to a given asymptotic sequence.
Proposition 2.2.3 ([73, Lemma 2.4]). Let a ∈ C ∪ {∞}, let {φn} be an asymptotic sequence at a, and let f and g be complex functions such that dom f contains the intersection of dom g with some punctured neighborhood of a. A given asymptotic expansion of f at a with respect to {φn} is also an asymptotic expansion of g at a with respect to {φn} if and only if
g(x) = f (x) + o(φn(x)) (x → a)
for all (or, equivalently, for infinitely many) positive integers n, if only if
g(x) = f (x) + O(φn(x)) (x → a)
for all (or, equivalently, for infinitely many) positive integers n.
Proof. Suppose that f (x) ≃ P∞
n=1 anφn(x) (x → a) is an asymptotic expansion of
f , or, equivalently, that f (x) = Pn
k=1 akφk(x) + o(φn(x)) (x → a) for all positive integers
n. Let n be any positive integer. If one has g(x) = Pn
k=1 akφk(x) + o(φn(x)) (x → a), then subtracting we see that g(x) − f (x) = o(φn(x)) (x → a) on dom g, and therefore g(x) = f (x) + o(φn(x)) (x → a). The converse is also clear. Similar statements hold for the O relation. The proposition follows. □
The following result provides a natural condition under which two asymptotic sequences can be viewed as asymptotically equivalent.


 42 2. ASYMPTOTIC ANALYSIS
Proposition 2.2.4 ([73, Lemma 2.5]). Let a ∈ C ∪ {∞}, let {φn} be an asymptotic sequence at a, and let {ψn} be a sequence of complex functions such that, for all positive integers n, one has ψn(x) − φn(x) = o(φN (x)) (x → a) for all N ≥ n and Un ∩ dom φn = Un ∩ dom ψn for some punctured neighborhood Un of a. Then {ψn} is an asymptotic sequence at a with φn(x)−ψn(x) = o(ψN (x)) (x → a) for all positive integers n and N ≥ n. Moreover, any asymptotic expansion
f (x) ≃
∞
X
n=1
anφn(x) (x → a)
of a complex-valued function f at a with respect to {φn} is equivalent to the asymptotic expansion
f (x) ≃
∞
X
n=1
anψn(x) (x → a)
of f at a with respect to {ψn}.
Proof. Let N be a positive integer. For all n one has ψn(x) − φn(x) = o(φn(x)) (x → a) and therefore ψn(x) ∼ φn(x) (x → a). It follows that φn(x) − ψn(x) = o(φN (x)) = o(ψN (x)) (x → a) for all n ≤ N and that {ψn} is an asymptotic sequence at a. If the first asymptotic expansion of f holds, then one has
f (x) −
N
X
n=1
anψn(x) = f (x) −
N
X
n=1
anφn(x)
!
+
N
X
n=1
an(ψn(x) − φn(x))
= o(φN (x)) (x → a)
= o(ψN (x)) (x → a),
for all N , and therefore second asymptotic expansion of f also holds. By symmetry, the reverse implication holds as well. The proposition follows. □
In 1848 [45, p. 153], Chebyshev noted the asymptotic expansion
li(x)
x≃
∞
X
n=0
n!
(log x)n+1 (x → ∞) (2.2.4)
of the function li(x)
x with respect to the asymptotic sequence
n
1
(log x)n+1
o
. This asymptotic
expansion is now well known (see [277, Section 10.3], for example) and follows from the fact that
li(x) −
n−1
X
k=0
k!x
(log x)k+1 =
Zx
e
n! dt
(log t)n+1 + Cn ∼ n!x
(log x)n+1 (x → ∞) (2.2.5)
for all nonnegative integers n, where Cn is a constant and the given equality is proved by repeated integration by parts. (Since d
dx
x
(log x)n+1 = log x−n−1
(log x)n+2 ∼ 1
(log x)n+1 (x → ∞), the
asymptotic relation in (2.2.5) above follows from L’Hôpital’s rule.) From (1.3.3), (2.2.4), and
Proposition 2.2.3, we see that p(x) has the same asymptotic expansion as li(x)
x , namely,
p(x) ≃
∞
X
n=0
n!
(log x)n+1 (x → ∞). (2.2.6)


 2.2. ASYMPTOTIC EXPANSIONS 43
In fact, assuming (2.2.4), it follows easily that (1.3.3) and (2.2.6) are equivalent. Thus, the asymptotic expansion (2.2.6) carries essentially the same information as the weak version (1.3.3) of the prime number theorem with error bound. Note that the series P∞
k=0
k!
(log x)k+1
is divergent for all x, and the definition of asymptotic expansions equates (2.2.6) with the statement
p(x) −
n−1
X
k=0
k!
(log x)k+1 ∼ n!
(log x)n+1 (x → ∞), ∀n ≥ 1.
It is noteworthy that one can “rationalize” the asymptotic expansion (2.2.6) by substituting ex for x: one has
p(ex) −
n−1
X
k=0
k!
xk+1 ∼ n!
xn+1 (x → ∞), ∀n ≥ 1,
and therefore the function p(ex) has the asymptotic expansion
p(ex) ≃
∞
X
n=0
n!
xn+1 (x → ∞)
with respect to the asymptotic sequence 1
xn+1 . For this and many other reasons, we
consider the function p(ex) = π(ex)
ex ∼ 1
x (x → ∞) to be a “rationalized” version of the function π(x).
Example 2.2.5 ([73]). Let n be a nonnegative integer. The number Dn = n! Pn
k=0
(−1)k
k!
is equal to the number of derangements of any n-element set, and the number An =
n! Pn
k=0
1
k! is equal to the number of arrangements of any n-element set. The sequence Dn is 1, 0, 1, 2, 9, 44, 265, 1854, . . ., and the sequence An is 1, 2, 5, 16, 65, 326, 1957, 13700, . . ., and they are Sequences A000166 and A000522, respectively, of the On-Line Encyclopedia of Integer Sequences (OEIS). Using the binomial theorem, one can show that the following asymptotic expansions are equivalent to (2.2.6):
(1) p(x) ≃
∞
X
n=0
Dn
(log x − 1)n+1 (x → ∞).
(2) p(ex) ≃
∞
X
n=0
Dn
(log x)n+1 (x → ∞).
(3) p(x) ≃
∞
X
n=0
An
(log x + 1)n+1 (x → ∞).
(4) p(x/e) ≃
∞
X
n=0
An
(log x)n+1 (x → ∞).
In particular, one has the asymptotic expansion
p(x/e) ≃ 1
log x + 2
(log x)2 + 5
(log x)3 + 16
(log x)4 + 65
(log x)5 + · · · (x → ∞).
At the same time, squaring the asymptotic expansion (2.2.6) of p(x) yields
p(x)2 ≃ 1
(log x)2 + 2
(log x)3 + 5
(log x)4 + 16
(log x)5 + 64
(log x)6 + · · · (x → ∞),


 44 2. ASYMPTOTIC ANALYSIS
It follows that
p(x/e) − p(x)2 log x ∼ 1
(log x)5 (x → ∞).
Consequently, one has p(x)2 log x < p(x/e) for all sufficiently large x, which is equivalent to Ramanujan’s famous inequality
π(x)2 < ex
log x π(x/e), ∀x ≫ 0.
It is known [12] that the Riemann hypothesis implies that the smallest integer N such that Ramanujan’s inequality holds for all x ≥ N is equal to 38358837683, and, moreover, the inequality holds unconditionally for all x ≥ e9032. For any sequence an of complex numbers and any z ∈ C, the sequence bn = Pn
k=0
n
k akzn−k is called the z-binomial transform of an. The 0-binomial transform of the sequence n! is the sequence n!, which is equal to the number of permutations of any n-element set. The sequence Dn is the (−1)-binomial transform of the sequence n!, and sequence An is the 1binomial transform of the sequence n!. For every nonnegative integer n, let rn(X) denote the monic integer polynomial
rn(X) = n!
n
X
k=0
Xk
k! =
n
X
k=0
n!
k! Xk ∈ Z[X].
For any z ∈ C, the sequence rn(z) is the z-binomial transform of the sequence n!, and one has rn(0) = n!, rn(−1) = Dn, and rn(1) = An for all n, so the family of sequences rn(z) interpolates those three sequences. For all t ∈ R, one has the asymptotic expansion
p(e−tx) ≃
∞
X
n=0
rn(t)
(log x)n+1 (x → ∞).
Note that, since rn(X) ∈ Z[X], one has rn(k) ∈ Z for all n and all k ∈ Z. The integer sequence rn(2) is OEIS Sequence A010842, and thus, for example, rn(2) is the number of ways to split the set {1, 2, . . . , n} into two disjoint subsets S and T and linearly order S and then choose a subset of T . Also, the integer sequence rn(−2) is OEIS Sequence A000023. Note also that rn(z) ∼ n!ez = rn(0)ez (n → ∞) for all z ∈ C. Thus, for example, one has Dn ∼ n!e−1 (n → ∞) and An ∼ n!e (n → ∞), which are well-known asymptotics for the sequences Dn and An.
Example 2.2.6 ([229]). Another interesting reformulation of the asymptotic expansion (2.2.6) is a result proved by Panaitopol in 2000: reciprocating the asymptotic expansion of p(x) yields the asymptotic expansion
A(x) = log x − 1
p(x) ≃
∞
X
n=0
kn
(log x)n (x → ∞),
where {kn} is the sequence with generating function
∞
X
n=0
knXn = 1
X− 1
X
P∞
n=0 n!Xn ,
and where A(x) is the unique function defined on [2, ∞) such that
π(x) = x
log x − A(x), ∀x ≥ 2.


 2.2. ASYMPTOTIC EXPANSIONS 45
It follows that {kn} is OEIS Sequence A233824, and therefore kn for any n ≥ 0 is the number of subgroups of index n of the free group on two generators, and the sequence {kn} has its first several terms given by 0, 1, 3, 13, 71, 461, 3447, 29093, . . .. It also follows that kn = In+1 for all n, where {In} is OEIS Sequence A003319 and In for any nonnegative integer n is equal to the number of indecomposable permutations of {1, 2, 3 . . . , n}, where a permutation of {1, 2, 3, . . . , n} is said to be indecomposable if it does not fix {1, 2, 3, . . . , j} for any 1 ≤ j < n.
Example 2.2.7 ([8]). The function pn
n log n , where pn denotes the nth prime, has a (diver
gent) asymptotic expansion of the form
pn
n log n ≃ 1 +
n
X
k=1
Pk(log log n)
(log n)k (n → ∞),
starting
1 + log log n − 1
log n + log log n − 2
(log n)2 − (log log n)2 − 6 log log n + 11
2(log n)3 + O (log log n)3
(log n)4 ,
where P0 = 1, P1(x) = x − 1, and Pk(x) for all k ≥ 2 is a polynomial of degree at most k − 1 that can be computed recursively as in [8].
Recall that Bn denotes the nth Bernoulli number (which equals 0 if n > 1 is odd, since the defining generating function X
eX−1 , plus X
2 − 1, of the Bernoulli numbers is an even function). For every nonnegative integer n, let Bn(T ) denote the nth Bernoulli polynomial, which are defined collectively by their generating function
∞
X
n=0
Bn(T ) Xn
n! = XeT X
eX − 1 .
Explicitly, one has
Bn(T ) =
n
X
k=0
n
k Bn−kT k
for all n, and thus Bn(T ) has constant term Bn(0) = Bn for all n. Moreover, one has Bn(1) = Bn for all n ̸= 1 and B1(1) = −B1 = 1
2 . The first six Bernoulli polynomials, for example, are given by
B0(T ) = 1
B1(T ) = T − 1
2
B2(T ) = T 2 − T + 1
6
B3(T ) = T 3 − 3
2T2 + 1
2T
B4(T ) = T 4 − 2T 3 + T 2 − 1
30
B5(T ) = T 5 − 5
2T4 + 5
3T3 − 1
6T.
The following theorem is known as the Euler–Maclaurin formula.
Theorem 2.2.8 (Euler–Maclaurin formula [60, Proposition 1.3] [141, (A.24)]). Let f be an N -times continuously differentiable complex-valued function on [a, b], where a, b ∈ Z with


 46 2. ASYMPTOTIC ANALYSIS
a < b and N is a positive integer. One has
b
X
k=a
f (k) =
Zb
a
f (x) dx + f (b) + f (a)
2+
⌊N/2⌋
X
k=1
B2k
(2k)! f (2k−1)(b) − f (2k−1)(a) + R,
where
R = (−1)N+1 1
N!
Zb
a
BN ({x})f (N)(x) dx
and
|R| ≤ 2ζ(N )
(2π)N
Zb
a
|f (N)(x)| dx.
Corollary 2.2.9. Let f be an infinitely differentiable complex-valued function on [a, ∞), where a ∈ Z. Suppose that f (n) has a constant sign on (a, ∞) for infinitely many nonnegative integers n. Then one has the asymptotic expansion
b
X
k=a
f (k) ≃
Zb
a
f (x) dx + f (b) + f (a)
2+
∞
X
k=1
B2k
(2k)! f (2k−1)(b) − f (2k−1)(a) (b → ∞).
Loosely speaking, the Euler–Maclaurin formula can be viewed as an extension of the trapezoid rule by the inclusion of correction terms. The combinatorist G.-C. Rota described the Euler–Maclaurin formula as “one of the most remarkable formulas of mathematics” that “has proved very useful for over 200 years” [256, p. 11]. It is particularly useful for deriving asymptotic expansions of functions that are important in analytic number theory and combinatorics.
Example 2.2.10. For any s ∈ C with Re s > 1, the Euler–Maclaurin formula can be shown to yield the asymptotic expansion
n
X
k=1
1
ks ≃ ζ(s) + n1−s
1−s + 1
2 n−s −
∞
X
k=1
(s)2k−1 ns
B2k
(2k)!
1
n2k−1 (n → ∞),
where
(s)n = s(s + 1)(s + 2) · · · (s + n − 1)
denotes the Pochhammer symbol. For s = 2, this simplifies to
n
X
k=1
1
k2 ≃ ζ(2) − 1
n+ 1
2n2 −
∞
X
k=1
B2k
n2k+1 (n → ∞).
For s = 1, the Euler–Maclaurin formula yields the asymptotic expansion
Hn ≃ log n + γ + 1
2n −
∞
X
k=1
B2k
2kn2k (n → ∞),
where Hn = Pn
k=1
1
k denotes the nth harmonic number.
Example 2.2.11 ([217]). Stirling’s approximation is the asymptotic relation
n! ∼ √2πn n
e
n
(n → ∞)


 2.2. ASYMPTOTIC EXPANSIONS 47
for the factorial function n!. The Euler–Maclaurin formula yields the asymptotic expansion
log(n!) ≃ n log n − n + 1
2 log 2πn +
∞
X
k=1
B2k
2k(2k − 1)n2k−1 (n → ∞),
whose first few terms are
log(n!) ≃ n log n − n + 1
2 log 2πn + 1
12n − 1
360n3 + 1
1260n5 − 1
1680n7 + · · · (n → ∞).
(The constant 1
2 log 2π is derived from the Wallis product for π.) From this one obtains the asymptotic expansion
n!
√2πn n
e
n ≃1+ 1
12n + 1
288n2 − 139
51840n3 − 571
2488320n4 + · · · (n → ∞).
An explicit but rather complicated formula for the coefficients in the expansion above is provided in [217].
Remark 2.2.12 (Conventions regarding the Bernoulli number B1 [196]). Numerous results, including the Euler–Maclaurin formula, suggest that the alternative convention B1 = 1
2 is more natural than the
standard convention B1 = − 1
2 that we have employed [196]. The Bernoulli numbers so revised are denoted
Bn+ (where Bn+ = Bn(1) for all n, so that B+
1 = −B1 and Bn+ = Bn for all n ̸= 1) and have generating function ∞
X
n=0
Bn+
n! Xn = X
1 − e−X .
The most pursuasive of the various arguments presented in [196] in favor of the alternative convention is that the Bernoulli function
B(s) = −sζ(1 − s)
is entire, with B(0) = 1, and one has B(n) = Bn+ for all nonnegative integers n, and thus the Bernoulli
function interpolates the revised Bernoulli numbers Bn+. Moreover, one has
ζ(s) = − B(1 − s)
1−s for all s ∈ C\{1}, and therefore
ζ(−n) = − B+
n+1
n + 1 , ∀n ≥ 0,
which is slightly cleaner than the formula
ζ(−n) = (−1)n Bn+1
n + 1 , ∀n ≥ 0.
See Figure 2.2.1 for a graph of the Bernoulli function on [−1, 15]. Note that B(−1) = ζ(2).
Figure 2.2.1. Graph of the Bernoulli function B(x) = −xζ(1 − x) on [−1, 15]


 48 2. ASYMPTOTIC ANALYSIS
2.3. The degree deg f of a real function f
Let f ∈ RR∞, that is, let f be a real function defined on a subset of R that is not bounded above. We define
deg f = inf{t ∈ R : f (x) = o(xt) (x → ∞)} ∈ R.
We call deg f the (upper) degree of f .
The following proposition provides an equivalent definition of degree.
Proposition 2.3.1. For all f ∈ RR∞, one has
deg f = lim sup
x→∞
log |f (x)|
log x .
Proof. Let t ∈ R. One has f (x) = o (xs) (x → ∞) for all s > t if and only if for all
s > t there exists an N > 0 such that |f (x)| ≤ xs, or equivalently log |f(x)|
log x ≤ s, for all x ≥ N
in dom f , where our convention is that log |0| = −∞. The proposition follows readily from this (and from our convention that a lim sup of an extended real valued function is defined even if the values are ±∞ for any set of values of x). □
Using the proposition, one can easily verify the following examples of degree for some functions arising in calculus.
Example 2.3.2. Let a, b, c ∈ R.
(1) If f ∈ R[x] is any real polynomial, then deg f coincides with the ususal degree of f as a polynomial. (2) If f /g ∈ R(x) is a rational function, where f, g ∈ R[x] and g is nonzero, then deg(f /g) = deg f − deg g. (3) deg xa = a. (4) deg (xa + c)b = b max(a, 0). (5) deg exp = ∞. (6) deg (log)a = 0. (7) deg (sin)a = deg (cos)a = 0. (8) deg tan = ∞.
(9) deg ea√x is equal to ∞ if a > 0, and to −∞ if a < 0.
(10) deg ea√log x = 0.
Statements of the form
f (x) = o(xd+ε) (x → ∞), ∀ε > 0,
and of the form
f (x) = O(xd+ε) (x → ∞), ∀ε > 0,
appear throughout analytic number theory, and it is common but unstated knowledge to analytic number theorists that both of the statements above are equivalent to
lim sup
x→∞
log |f (x)|
log x ≤ d.
By our definition of degree, then, all three of the above statements are equivalent to deg f ≤ d. Expressions of the form lim supx→∞
log |f (x)|
log x appear in the study of Dirichlet series, as


 2.3. THE DEGREE deg f OF A REAL FUNCTION f 49
shown in Theorem 3.8.3, and a great many other examples are provided throughout this book. The following corollary of Proposition 2.3.1 implies that the notions of limit superior, limit inferior, and degree are all interdefinable.
Corollary 2.3.3. For all f ∈ RR∞, one has
lim sup
x→∞
f (x) = deg xf(x)
and
lim inf
x→∞ f (x) = − lim sup
x→∞
(−f (x)) = − deg x−f(x).
We note the following proposition, whose proof is straightforward.
Proposition 2.3.4. Let f, g ∈ RR∞. One has the following.
(1) deg f is the unique d ∈ R such that f (x) = o(xt) (x → ∞) for all t > d but for no t < d.
(2) deg f is the unique d ∈ R such that f (x) = O(xt) (x → ∞) for all t > d but for no t < d.
(3) deg f = ∞ if and only if f (x) ̸= o(xt) (x → ∞) for all t ∈ R, if and only if f (x) ̸= O(xt) (x → ∞) for all t ∈ R.
(4) deg f = −∞ if and only if f (x) = o(xt) (x → ∞) for all t ∈ R, if and only if f (x) = O(xt) (x → ∞) for all t ∈ R.
(5) If f is eventually bounded (on its domain), then deg f ≤ 0. (6) If deg f < 0, then xli→m∞ f (x) = 0 (on its domain).
(7) If f (x) = O(g(x)) (x → ∞), then deg f ≤ deg g. (8) If f (x) = O(g(x)) (x → ∞) and g(x) = O(f (x)) (x → ∞), then deg f = deg g.
Let f ∈ RR∞. The exact degree of f , written deg f , is the limit
deg f = xli→m∞
log |f (x)|
log x ,
provided that the limit exists or is ±∞, in which case we say that f has exact degree. Note that if deg f = −∞, then f has exact degree. We also define the lower degree deg f of f to be
deg f = lim inf
x→∞
log |f (x)|
log x .
Clearly one has deg f ≤ deg f , with equality if and only if f has exact degree. If f is not eventually nonzero (on its domain), then deg f = −∞; otherwise, f is eventually nonzero (on its domain), and then one has
deg f = − lim sup
x→∞
− log |f (x)|
log x = − deg(1/f ).
The following are some number-theoretic examples of degree, lower degree, and exact degree.
Example 2.3.5.


 50 2. ASYMPTOTIC ANALYSIS
(1) As noted in Theorem 1.3.3 (for which some details of the proof are provided in Section 5.2), it known that the Riemann constant Θ is equal to the infimum of all t ∈ R such that
li(x) − π(x) = O(xt) (x → ∞).
In other words, one has
Θ = deg(li −π).
It follows that
1
2 ≤ deg(li −π) ≤ 1,
and the Riemann hypothesis is equivalent to deg(li −π) = 1
2 . Note, however, that li −π does have not exact degree Θ. In fact, one has li(x) − π(x) = 0 for an unbounded set of positive real numbers x, and therefore
deg(li −π) = −∞.
(2) Since
li(x) − Ri(x) ∼
√x
log x (x → ∞),
one has
deg(li − Ri) = 1
2,
that is, the function li − Ri has exact degree 1
2. (3) [121, Theorem 317] states that
lim sup
n→∞
log d(n) log log n
log n = log 2,
where
d(n) =
X
d|n
1
is the divisor function. (The lim sup is attained by the sequence p1p2 · · · pn.) By Corollary 2.3.3, this statement can be re-interpreted as
deg d(n)log log n = deg (log n)log d(n) = log 2.
On the other hand, since there are infinitely many prime numbers, one has
lim inf
n→∞ d(n) = 2
and therefore
lim inf
n→∞
log d(n) log log n
log n = 0,
whence
deg d(n)log log n = deg (log n)log d(n) = 0.
It also follows that
deg d(n) = nli→m∞
log d(n)
log n = 0.


 2.4. SLOWLY VARYING AND REGULARLY VARYING FUNCTIONS 51
(4) It is known that
lim sup
n→∞
σ(n)
n log log n = eγ,
where
σ(n) =
X
d|n
d
is the sum of divisors function and γ is the Euler–Mascheroni constant [111, (25)]. (The lim sup is attained by the sequence (p1p2 · · · pn)⌊log pn⌋.) By Corollary 2.3.3, the lim sup above can be re-interpreted as the statement
deg nσ(n)/(n log log n) = eγ .
Moreover, since there are infinitely many prime numbers, one has
lim inf
n→∞
σ(n)
n = lim inf
n→∞
σ(n)
1 + n = 1.
It follows that
deg σ(n) = 1.
(5) Let L denote the field of all logarithmico-exponential functions [117] [118], that is, the field of all (germs of) real functions defined on a neighborhood of ∞ that can be can be built from all real constants and the functions id, exp, and log using the operations +, ·, /, and ◦. By Proposition 6.3.23 of Section 6.3, every function in L has exact degree.
Finally, we note the following.
Proposition 2.3.6. Let f be a real function that is nonzero and differentiable on a neighborhood of ∞, and suppose that the limit
d = xli→m∞
xf ′(x)
f (x) ∈ R
exists or is ±∞. Then f has exact degree d.
Proof. By L’Hôpital’s rule, one has
deg f = xli→m∞
log |f (x)|
log x = xli→m∞
f ′(x)/f (x)
1/x = d.
□
See Section 6.1 for a more thorough study of degree, lower degree, and exact degree.
2.4. Slowly varying and regularly varying functions
In this section we study slowly varying functions and regularly varying functions, which were introduced by Karamata in [148] [149]. The study of such functions is called Karamata theory. Excellent references for Karamata theory and for the proofs of the theorems stated in this section are [27] [154, Chapter IV] [264]. When necessary, to avoid Lebesgue integration, we restrict our discussion to continuous functions.


 52 2. ASYMPTOTIC ANALYSIS
A real function f defined and either positive or negative on some neighborhood of ∞ is said to be slowly varying if
xli→m∞
f (cx)
f (x) = 1
for all c > 0.
Example 2.4.1. Let f and g be real functions defined on a neighborhood of ∞, let c, a ∈ R be nonzero, and let k and l be nonnegative integers.
(1) If limx→∞ f (x) ̸= 0 exists, then f is slowly varying. (2) sin x is of degree 0 but is not slowly varying. (3) If f is slowly varying and f (x) ∼ cg(x) (x → ∞), then g is slowly varying. (4) If f and g are slowly varying, then f g is slowly varying. (5) If f is eventually positive, then f is slowly varying if and only if cf a is slowly varying. (6) c(log◦k x)a is slowly varying (resp., of degree 0) if and only if k ≥ 1. (7) ec(log x)a is slowly varying (resp., of degree 0) if and only if a < 1. (8) exp◦l(c(log◦k x)a) is slowly varying (resp., of degree 0) if and only if k > l, or k = l and a < 1.
(9) f (x) = 2+sin log log x is slowly varying with lim supx→∞ f (x) = 3 and lim infx→∞ f (x) = 1. (10) f (x) = exp((log x)1/2 sin((log x)1/2)) is slowly varying with lim supx→∞ f (x) = ∞ and lim infx→∞ f (x) = 0.
Note that, if f is a real function that is eventually positive, and if g is defined by g(x) = log f (ex), so that f (x) = eg(log x), then f is slowly varying if and only if
xli→m∞(g(x + c) − g(x)) = 0
for all c ∈ R. This equivalence is used in proofs of the following result, which is known as the Karamata’s integral representation theorem.
Theorem 2.4.2 (Karamata’s integral representation theorem). Let f be a real function defined on a neighborhood of ∞. Then f is slowly varying and continuous on a neighborhood of ∞ if and only if there exists an N > 0 and continuous functions C and η on [N, ∞) such that limx→∞ C(x) ̸= 0 exists, limx→∞ xη(x) = 0, and
f (x) = C(x) exp
Zx
N
η(t) dt
for all x ∈ [N, ∞).
Corollary 2.4.3. Let f be a real function defined on a neighborhood of ∞. If f is slowly varying and continuous on a neighborhood of ∞, then deg f = 0.
Proof. By the theorem, L’Hôpital’s rule, and the fundamental theorem of calculus, one has
xli→m∞
log |f (x)|
log x = xli→m∞
log |C(x)| + R x
N η(t) dt
log x = xli→m∞
Rx
N η(t) dt
log x = xli→m∞ xη(x) = 0,
whence deg f = 0. □


 2.4. SLOWLY VARYING AND REGULARLY VARYING FUNCTIONS 53
Note that sufficiency of the equivalent condition in Karamata’s integral representation
theorem is easy to prove. Indeed, assuming f (x) = C(x) exp R x
N η(t) dt, where C and η are as in the theorem, one has
Z cx
x
η(t) dt ≤
Z cx
x
|η(t)| dt ≤ (cx − x) max
t∈[x,cx]
|η(t)| = o(1) (x → ∞)
for all x ≥ N and all c > 1, and therefore
xli→m∞
f (cx)
f (x) = xli→m∞
C (cx)
C(x) exp xli→m∞
Z cx
x
η(t) dt = 1 exp 0 = 1.
Let f be a real function defined and either positive or negative on some neighborhood of ∞. The function f is said to be regularly varying if the limit limx→∞
f (cx)
f(x) exists and
is finite and positive for all c > 0 (or, equivalently, for all c > 1). If there exists a constant r ∈ R such that
xli→m∞
f (cx)
f (x) = cr,
or, equivalently,
f (cx) ∼ crf (x) (x → ∞),
for all c > 0, then f is regularly varying, r is called the index of regular variation of f , and f is said to be regularly varying of index r. The following result is clear.
Proposition 2.4.4. Let f and g be real functions defined on a neighborhood of ∞, and let r, s, A ∈ R with A ̸= 0.
(1) The power function Axr is regularly varying of index r, and in fact it is the unique function f (x) on (0, ∞) with f (cx) = crf (x) for all c, x > 0 and f (1) = A. (2) If f is regularly varying (resp., regularly varying of index r), and if f (x) ∼ g(x) (x → ∞), then g is regularly varying (resp., regularly varying of index r). (3) If f is regularly varying (resp., regularly varying of index r) and g is regularly varying (resp., regularly varying of index s), then f g is is regularly varying (resp., regularly varying of index r + s).
Thus, for example, the prime number theorem implies that the prime counting function is regularly varying of index 1. Karamata’s integral representation theorem and Proposition 2.4.4 together yield the following.
Corollary 2.4.5. Let f be a real function that is nonzero and continuously differentiable on a neighborhood of ∞, and suppose that the limit
r = xli→m∞
xf ′(x)
f (x) ∈ R
exists. Then f is regularly varying of index r.
Proof. Let g(x) = x−rf (x) and η(x) = g′(x)
g(x) , so that
xli→m∞ xη(x) = xli→m∞
xg′(x)
g(x) = xli→m∞ −r + xf ′(x)
f (x) = 0,


 54 2. ASYMPTOTIC ANALYSIS
where η(x) is continuous on a neighborhood [N, ∞) of ∞, and where
g(x) = g(N ) exp
Zx
N
η(t) dt
for all x ∈ [N, ∞). From Karamata’s integral representation theorem, then, it follows that g is slowly varying, whence f is regularly varying of index r by Proposition 2.4.4. □
By the following theorem, which is known as Karamata’s characterization theorem, any eventually continuous regularly varying function is regularly varying of index r for a unique r ∈ R.
Theorem 2.4.6 (Karamata’s characterization theorem). Let f be a real function defined on a neighborhood of ∞. Then f is regularly varying and continuous on a neighborhood of ∞ if and only if there exists a (unique) r ∈ R and a slowly varying function F continuous on a neighborhood of ∞ such that f (x) = xrF (x) for all x ≫ 0. If those conditions hold, then f is regularly varying of index r.
Corollary 2.4.7. Let f be a real function defined on a neighborhood of ∞. If f is regularly varying and continuous on a neighborhood of ∞, then deg f ∈ R exists and is equal to the index of regular variation of f .
Proof. By the theorem, the function f is regularly varying of index r, and x−rf (x) is slowly varying, for some r ∈ R. By Corollary 2.4.3, then, one has −r + deg f =
deg(x−rf (x)) = 0, whence r = deg f . □
By the characterization theorem, Karamata’s integral representation theorem generalizes as follows.
Theorem 2.4.8. Let f be a real function defined on a neighborhood of ∞. Then f is regularly varying and continuous on a neighborhood of ∞ if and only if there exists an N > 0 and continuous functions C and η on [N, ∞) such that limx→∞ C(x) ̸= 0 and r = limx→∞ xη(x) exist and
f (x) = C(x) exp
Zx
N
η(t) dt
for all x ∈ [N, ∞). Moreover, if those equivalent conditions hold, then f is regularly varying of index r.
Proof. Necessity follows by applying Karamata’s integral representation theorem to f1(x) = x−rf (x), where r is as provided by Theorem 2.4.6, and sufficiency follows by applying Karamata’s integral representation theorem to η1(x) = η(x) − r
x , where r = limx→∞ xη(x).
□
The following result characterizes the eventually monotonic functions that are regularly varying.
Proposition 2.4.9. Let f be an eventually nonzero and monotonic real function defined on a neighborhood of ∞. Then f is regularly varying of index r ∈ R if and only if f (g(x)) ∼ crf (x) (x → ∞) for all c > 0 and all functions g defined on a neighborhood of ∞ with g(x) ∼ cx (x → ∞).


 2.4. SLOWLY VARYING AND REGULARLY VARYING FUNCTIONS 55
Proof. Necessity is clear. Let h(x) = g(x) − cx, so that h(x) = o(x) (x → ∞). Suppose that f is eventually nondecreasing. It follows that, for every ε > 0, one has
cr(1 − ε)r ∼ f (cx − cεx)
f (x) ≤ f (x + h(x))
f (x) ≤ f (cx + cεx)
f (x) ∼ cr(1 + ε)r (x → ∞)
for all x ≫ 0, and therefore
f (g(x))
f (x) = f (x + h(x))
f (x) ∼ cr (x → ∞).
The proof when f is eventually nonincreasing is similar, with the inequalities reversed. □
The following result, known as Karamata’s integral theorem, which we use on several occasions in Part 3, is one of the main reasons that the notions of slowly varying and regularly varying functions are so useful. It can be described as an asymptotic mean value theorem for continuous regularly varying functions.
Theorem 2.4.10 (Karamata’s integral theorem). Let f be a real function that is nonzero and continuous on [N, ∞), where N > 0.
(1) f is regularly varying of index r > −1 if and only if there is a constant s > 0 such
that
1
x
Zx
N
f (t) dt ∼ f (x)
s (x → ∞).
Moreover, if those equivalent conditions hold, then one has s = r + 1 = |r + 1|.
(2) f is regularly varying of index r < −1 if and only if the integral R ∞
N f (t) dt exists and there is a constant s > 0 such that
1
x
Z∞
x
f (t) dt ∼ f (x)
s (x → ∞).
Moreover, if those equivalent conditions hold, then one has s = −(r + 1) = |r + 1|.
(3) If f is regularly varying of index −1 and R ∞
N f (t) dt = ±∞, then
f (x) = o 1
x
Zx
N
f (t) dt (x → ∞).
(4) If f is regularly varying of index −1 and R ∞
N f (t) dt exists, then
f (x) = o 1
x
Z∞
x
f (t) dt (x → ∞).
Corollary 2.4.11. Let f be a real function that is nonzero and continuous on [N, ∞), where N > 0. Then f is slowly varying if and only if
1
x
Zx
N
f (t) dt ∼ f (x) (x → ∞).
Example 2.4.12. For all nonnegative integers n, the asymptotic relation
Zx
e
n! dt
(log t)n+1 + Cn ∼ n!x
(log x)n+1 (x → ∞)
stated previously in (2.2.5) follows from Karamata’s integral theorem and the fact that the function 1
(log x)n+1 is slowly varying.


 56 2. ASYMPTOTIC ANALYSIS
Example 2.4.13. Since the function 1
log x is slowly varying, one has
li(x) =
Zx
μ
1
log t dt ∼ x
log x (x → ∞),
where μ denotes the Ramanujan–Soldner constant. More generally, for any r > −1, the function xr
log x is regularly varying of index r > −1, and therefore
li(xr+1) − li(μr+1) =
Zx
μ
tr
log t dt ∼ xr+1
(r + 1) log x (x → ∞)
for all x > 1. For r = −1, one has
Zx
e
t−1
log t dt = log log x.
Finally, for r < −1, the function xr
log x is regularly varying of index r < −1, and therefore
li(xr+1) = −
Z∞
x
tr
log t dt ∼ xr+1
(r + 1) log x (x → ∞)
for all x > 1.
Karamata’s integral theorem can be viewed in the following broader context. Let f be a function that is Riemann integrable on [N, x] for all x > N , where N ∈ R. The average value Avgf [y, x] of f on the interval [y, x], for any x > y ≥ N , is defined by
Avgf [y, x] = 1
x−y
Zx
y
f (t) dt.
Note that the power functions f (x) = Axr for A, r ∈ R with r > −1 and A ̸= 0 are characterized as those real functions f (x), continuous and nonzero on (0, ∞), such that f (0+) ∈ {0, ±∞} and
Avgf [0, x] = f (x)
s , ∀x > 0,
for some s > 0 (where, necessarily, s = r + 1). Indeed, by the fundamental theorem of calculus, the integral equation above implies sf = (xf )′ = f + xf ′ and therefore f′
f = s−1
x. Statement (1) of Karamata’s integral theorem states that the eventually continuous regularly varying functions (of some index r > −1) are characterized as those real functions f (x), continuous and nonzero on a neighborhood [N, ∞) on ∞, such that
Avgf [N, x] ∼ f (x)
s (x → ∞)
for some s > 0 (where, necessarily, s = r + 1). Loosely speaking, then, the continuous regularly varying functions are those continuous functions whose running average asymptotically behaves like the running average of a power function. Finally, we note that all of the continuity hypotheses utilized in this section can be weakened considerably: all of the results stated in this section can be generalized to (Lebesgue) measurable functions [N, ∞) −→ R, as is typically done in the literature on Karamata theory. For example, if f : [N, ∞) −→ R is measurable, then f is regulary varying of index deg f ̸= ±∞ if f is regularly varying. Likewise, Karamata’s integral representation theorem and integral theorem extend to this more general setting, where the functions f and C are assumed measurable instead of continuous, and where the Riemann integrals are replaced


 2.4. SLOWLY VARYING AND REGULARLY VARYING FUNCTIONS 57
with Lebesgue integrals. In particular, since the derivative of a differentiable function is measurable, one need only assume in Corollary 2.4.5 that f is differentiable (rather than continuously differentiable) on a neighborhood of ∞. Note also that, if f and g are eventually measurable and regularly varying of index r and s, respectively, then |f | + |g| is regularly varying of index max(r, s), and f ◦ g is regularly varying of index rs provided that limx→∞ g(x) = ∞.