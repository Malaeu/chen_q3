---
title: "The Riemann hypothesis"
authors:
  - "J. Brian Conrey"
date: "2003-00-00 2003"
publication: "Notices of the American Mathematical Society"
doi: null
url: "https://www.ams.org/notices/200303/fea-conrey-web.pdf"
zotero:
  attachment_key: "DPRZEY6A"
  parent_key: "GC46ZTLJ"
  item_id: 1963
  attachment_item_id: 1983
---

MARCH 2003 NOTICES OF THE AMS 341
The Riemann
Hypothesis
J. Brian Conrey
H
ilbert, in his 1900 address to the Paris International Congress of Mathematicians, listed the Riemann Hypothesis as one of his 23 problems for mathematicians of the twentieth century to work on. Now we find it is up to twenty-first century mathematicians! The Riemann Hypothesis (RH) has been around for more than 140 years, and yet now is arguably the most exciting time in its history to be working on RH. Recent years have seen an explosion of research stemming from the confluence of several areas of mathematics and physics. In the past six years the American Institute of Mathematics (AIM) has sponsored three workshops whose focus has been RH. The first (RHI) was in Seattle in August 1996 at the University of Washington. The second (RHII) was in Vienna in October 1998 at the Erwin Schrödinger Institute, and the third (RHIII) was in New York in May 2002 at the Courant Institute of Mathematical Sciences. The intent of these workshops was to stimulate thinking and discussion about one of the most challenging problems of mathematics and to consider many different approaches. Are we any closer to solving the Riemann Hypothesis after these efforts? Possibly. Have we learned anything about the zeta-function as a result of these workshops? Definitely. Several of the participants from the workshops are collaborating on the website (http://
www.aimath.org/WWN/rh/) which provides an overview of the subject. Here I hope to outline some of the approaches to RH and to convey some of the excitement of working in this area at the present moment. To begin, let us examine the Riemann Hypothesis itself. In 1859 in the seminal paper “Ueber die Anzahl der Primzahlen unter eine gegebener Grösse”, G. B. F. Riemann outlined the basic analytic properties of the zeta-function
ζ(s) := 1 + 1
2s + 1
3s + · · · =
∞ ∑
n=1
1
ns .
The series converges in the half-plane where the real part of s is larger than 1. Riemann proved that ζ(s) has an analytic continuation to the whole plane apart from a simple pole at s = 1. Moreover, he proved that ζ(s) satisfies an amazing functional equation, which in its symmetric form is given by
J. Brian Conrey is director of the American Institute of Mathematics. His email address is conrey@aimath.org.
-1 1 2 3
-2
-1
1
2
Figure 1. ζ( 1
2 + it) for 0 < t < 50.


 342 NOTICES OF THE AMS VOLUME 50, NUMBER 3
ξ(s) := 1
2 s(s − 1)π − s
2Γ
(s
2
)
ζ(s) = ξ(1 − s),
where Γ (s) is the usual Gamma-function. The zeta-function had been studied previously by Euler and others, but only as a function of a real variable. In particular, Euler noticed that
ζ(s) =
(
1+ 1
2s + 1
4s + 1
8s + . . .
)
×
(
1+ 1
3s + 1
9s + . . .
)(
1+ 1
5s + . . .
)
...
=∏
p
(
1− 1
ps
)−1
,
where the infinite product (called the Euler product) is over all the prime numbers. The product converges when the real part of s is greater than 1. It
is an analytic version of the fundamental theorem of arithmetic, which states that every integer can be factored into primes in a unique way. Euler used this product to prove that the sum of the reciprocals of the primes diverges. The Euler product suggests Riemann’s interest in the zeta-function: he was trying to prove a conjecture made by Legendre and, in a more precise form, by Gauss:
π (x) := #{primes less than x} ∼
∫x
2
dt
log t .
Riemann made great progress toward proving Gauss’s conjecture. He realized that the distribution of the prime numbers depends on the distribution of the complex zeros of the zeta-function. The Euler product implies that there are no zeros of ζ(s) with real part greater than 1; the functional equation implies that there are no zeros with real part less than 0, apart from the trivial zeros at
0.4 0.6 0.8 1 1.2 1.4
99
100
101
102
103
104
105
106
0.4 0.6 0.8 1.2 1.4
100
101
102
103
104
105
106
0.4 0.6 0.8 1 1.2 1.4
99
100
101
102
103
104
105
106
Figure 2. Contour plot of ζ(s), the curves ζ(s) = 0 (solid) and ζ(s) = 0 (dotted), contour plot of ζ (s ) .
Figure 3. 3-D plot of | ζ(s)|, and the curves ζ(s) = 0 (solid) and ζ(s) = 0 (dotted). This may be the first place in the critical strip where the curves ζ(s) = 0 loop around each other.


 MARCH 2003 NOTICES OF THE AMS 343
s = −2, −4, −6, . . . . Thus, all of the complex zeros are in the critical strip 0 ≤ s ≤ 1 . Riemann gave an explicit formula for π (x) in terms of the complex zeros ρ = β + iγ of ζ(s) . A simpler variant of his formula is
ψ(x) := ∑
n≤x
Λ(n)
=x−∑
ρ
xρ
ρ − log 2π − 1
2 log(1 − x−2),
valid for x not a prime power, where the von Mangoldt function Λ(n) = log p if n = pk for some k and Λ(n) = 0 otherwise. Note that the sum is not ab
solutely convergent; if it were, then ∑
n≤x Λ(n) would have to be a continuous function of x, which it clearly is not. Consequently, there must be infinitely many zeros ρ. The sum over ρ is with multiplicity and is to be interpreted as limT→∞
∑
|ρ|<T .
Note also that |xρ| = xβ; thus it was necessary to show that β < 1 in order to conclude that
∑
n≤x Λ(n) ∼ x , which is a restatement of Gauss’s conjecture.
The functional equation shows that the complex zeros are symmetric with respect to the line s = 1
2. Riemann calculated the first few complex zeros
1
2 + i14.134 . . ., 1
2 + i21.022 . . . and proved that the number N(T ) of zeros with imaginary parts between 0 and T is
N(T ) = T
2π log T
2π e + 7
8 + S(T ) + O(1/T ),
where S(T ) = 1
π arg ζ(1/2 + iT ) is computed by
continuous variation starting from arg ζ(2) = 0 and proceeding along straight lines, first up to 2 + iT and then to 1/2 + iT. Riemann also proved that S(T ) = O(log T ) . Note for future reference that at a height T the average gap between zero heights is ∼ 2π / log T. Riemann suggested that the number N0(T ) of zeros of ζ(1/2 + it) with 0 < t ≤ T seemed to be about
T
2π log T
2π e
and then made his conjecture that all of the zeros of ζ(s) in fact lie on the 1/2-line; this is the Riemann Hypothesis. Riemann’s effort came close to proving Gauss’s conjecture. The final step was left to Hadamard and de la Vallée Poussin, who proved independently in 1896 that ζ(s) does not vanish when the real part of s is equal to 1 and from that fact deduced Gauss’s conjecture, now called the Prime Number Theorem.
Initial Ideas
It is not difficult to show that RH is equivalent to the assertion that for every > 0,
π (x) =
∫x
2
dt
log t + O(x1/2+ ).
However, it is difficult to see another way to approach π (x) and so get information about the zeros. Another easy equivalent to RH is the assertion that M(x) = O(x1/2+ ) for every > 0, where
M(x) = ∑
n≤x
μ(n)
and μ(n) is the Möbius function whose definition can be inferred from its generating Dirichlet series
1/ζ :
1
ζ(s) =
∞ ∑
n=1
μ(n)
ns = ∏
p
(
1− 1
ps
)
.
Thus, if p1, . . . , pk are distinct primes, then μ(p1 . . . pk) = (−1)k; also μ(n) = 0 if p2 | n for some prime p. This series converges absolutely when s > 1. If the estimate M(x) = O(x1/2+ ) holds for every > 0, then it follows by partial summation that the series converges for every s with real part greater than 1/2; in particular, there can be no zeros of ζ(s) in this open half-plane, because zeros of ζ(s) are poles of 1/ζ(s). The converse, that RH implies this estimate for M(x) , is also not difficult to show. Instead of analyzing π (x) directly, it might seem easier to work with M(x) and prove the above estimate, perhaps by some kind of combinatorial reasoning. In fact, Stieltjes let it be known that he had such a proof. Hadamard, in his famous 1896 proof of the Prime Number Theorem, refers to Stieltjes’s claim and somewhat apologetically offers his much weaker theorem that ζ(s) does not vanish on the 1-line in the hope that the simplicity of his proof will be useful. Stieltjes never published his proof. Mertens made the stronger conjecture that
|M(x)| ≤ √x;
clearly this implies RH. However, Mertens’s conjecture was disproved by Odlyzko and te Riele in
1985. The estimate M(x) = O(√x ) is also likely to
Figure 4. Explicit formula for ψ(x) using the first 100 pairs of zeros.


 344 NOTICES OF THE AMS VOLUME 50, NUMBER 3
even used RH as a defense: he once sent a postcard to his colleague Harald Bohr prior to crossing the English Channel one stormy night, claiming that he had solved RH. Even though Hardy was an atheist, he was relatively certain that God, if he did exist, would not allow the ferry to sink under circumstances so favorable to Hardy! Hilbert seems to have had somewhat contradictory views about the difficulty of RH. On one occasion he compared three unsolved problems: the transcendence of 2
√2, Fermat’s Last Theorem, and the Riemann Hypothesis. In his view, RH would likely be solved in a few years, Fermat’s Last Theorem possibly in his lifetime, and the transcendence question possibly never. Amazingly, the transcendence question was resolved a few years later by Gelfond and Schneider, and, of course, Andrew Wiles recently proved Fermat’s Last Theorem. Another time Hilbert remarked that if he were to awake after a sleep of five hundred years, the first question he would ask was whether RH was solved. Near the end of his career, Hans Rademacher, best known for his exact formula for the number of partitions of an integer, thought he had disproved RH. Siegel had checked the work, which was based on the deduction that a certain function would absurdly have an analytic continuation if RH were true. The mathematics community tried to get Time magazine interested in the story. It transpired that Time became interested and published an article only after it was discovered that Rademacher’s proof was incorrect.
Evidence for RH
Here are some reasons to believe RH. • Billions of zeros cannot be wrong. Recent work by van de Lune has shown that the first 10 billion zeros are on the line. Also, there is a distributed computing project organized by Sebastian Wedeniwski—a screen-saver type of program—that many people subscribe to, which claims to have verified that the first 100 billion zeros are on the line. Andrew Odlyzko has calculated millions of zeros near zeros number 1020, 1021 , and 1022 (available on his website). • Almost all of the zeros are very near the 1/2line. In fact, it has been proved that more than 99 percent of zeros ρ = β + iγ satisfy
|β − 1
2 | ≤ 8/ log |γ| . • Many zeros can be proved to be on the line. Selberg got a positive proportion, and N. Levinson showed at least 1/3; that proportion has been improved to 40 percent. Also, RH implies that all zeros of all derivatives of ξ(s) are on the 1/2-line. It has been shown that more than 99 percent of the zeros of the third derivative ξ′′′(s) are on the 1/2-line. Near the end of his life, Levinson thought he had a method that allowed for a converse to Rolle’s theorem in
Figure 5. 1/|ζ(x + iy)| for 0 < x < 1 and 16502.4 < y < 16505 .
be false, but a proof of its falsity has not yet been found.
Subsequent Efforts
In England in the early 1900s the difficulty of the question was not yet appreciated. Barnes assigned RH to Littlewood as a thesis problem. Littlewood independently discovered some of the developments that had already occurred on the continent. Hardy, Littlewood, Ingham, and other British mathematicians were responsible for many of the results on the zeta-function in the first quarter of the century. Hardy and Littlewood gave the first proof that infinitely many of the zeros are on the 1/2line. They found what they called the approximate functional equation for ζ(s). Later, Siegel uncovered a very precise version of this formula while studying Riemann’s notes in the Göttingen library; the formula is now called the Riemann-Siegel formula and gives the starting point for all large-scale calculations of ζ(s) . Hardy and Littlewood gave an asymptotic evaluation of the second moment of ζ(1
2 + it); Ingham proved the asymptotics for the fourth moment. Much effort has also been expended on the unproved Lindelöf hypothesis, which is a consequence of RH. The Lindelöf hypothesis asserts that for every > 0,
ζ(1/2 + it) = O(t ) as t → ∞.
Hardy and Littlewood proved that ζ(1/2 + it) = O(t1/4+ ) . This bound is now called the “convexity bound”, since it follows from the functional equation together with general principles of complex analysis (the maximum modulus principle in the form of the Phragmén-Lindelöf theorem). Weyl improved the bound to t1/6+ with his new ideas for estimating special trigonometrical sums, now called Weyl sums. Hardy grew to love the problem. He and Littlewood wrote at least ten papers on the zetafunction. Hardy once included proving RH on a list of New Year’s goals he set for himself. Hardy


 MARCH 2003 NOTICES OF THE AMS 345
this situation, implying that if ξ′(s) has at least a certain proportion of zeros on the line, then so does ξ and similarly for ξ′′ to ξ′ and so on. However, no one has been able to make this argument work. • Probabilistic arguments. For almost all random sequences of −1’s and +1’s, the associated summatory function up to x is bounded by x1/2+ . The Möbius sequence appears to be fairly random. • Symmetry of the primes. RH tells us that the primes are distributed in as nice a way as possible. If RH were false, there would be some strange irregularities in the distribution of primes; the first zero off the line would be a very important mathematical constant. It seems unlikely that nature is that perverse!
Various Approaches
There is an often-told story that Hilbert and Pólya independently suggested that the way to prove RH was to interpret the zeros spectrally, that is, to find a naturally occurring Hermitian operator whose eigenvalues are the nontrivial zeros of ζ(1/2 + it). Then RH would follow, since Hermitian operators have real eigenvalues. This idea has been one of the main approaches that has been tried repeatedly. We describe an assortment of other interesting approaches to RH.
Pólya’s Analysis
Pólya investigated a chain of ideas that began with Riemann: namely, studying the Fourier transform of Ξ(t) := ξ( 1
2 + it) , which as a consequence of the functional equation is real for real t and an even function of t. RH is the assertion that all zeros of Ξ are real. The Fourier transform can be computed explicitly:
Φ(t) :=
∫∞
−∞
Ξ(u)eitu du
=
∞ ∑
n=1
(2n4π 2 exp(9t/2) − 3n2π exp(5t/2))
× exp (−π n2e2t ) .
It can be shown that Φ and Φ′ are positive for positive t. One idea is to systematically study classes of reasonable functions whose Fourier transforms have all real zeros and then try to prove that Ξ(t) is in the class. A sample theorem in this direction is due to de Bruijn:
Let f (t) be an even nonconstant entire function of t such that f (t) ≥ 0 for real t and f ′(t) = exp(γt2)g(t), where γ ≥ 0 and g(t) is an entire function of genus ≤ 1 with purely imaginary
zeros only. Then Ψ (z) = ∫ ∞
−∞ exp {−f (t)}eizt dt has real zeros only.
In particular, all the zeros of the Fourier transform of a first approximation (see Titchmarsh for details)
φ(t) =(2π cosh 9t
2 − 3 cosh 5t
2
)
× exp(−2π cosh 2t)
to Φ(t) are real. These ideas have been further explored by de Bruijn, Newman, D. Hejhal, and others. Hejhal (1990) has shown that almost all of the zeros of the Fourier transform of any partial sum of Φ(t) are real.
Probabilistic Models
Researchers working in probability are intrigued by the fact that the ξ-function arises as an expectation in a moment of a Brownian bridge:
2ξ(s) = E(Y s )
where Y :=
√ 2 π
(
max
t ∈[0,1]
bt − min
t∈[0,1] bt
)
with bt = βt − tβ1 where βt is standard Brownian motion. See a paper of Biane, Pitman, and Yor (Bull. Amer. Math. Soc. (N.S.) 38 (2001), 435–65).
Functional Analysis: The Nyman-Beurling Approach
This approach begins with the following theorem of Nyman, a student of Beurling.
RH holds if and only if
spanL2(0,1){ηα, 0 < α < 1} = L2(0, 1)
where
ηα(t) = {α/t} − α{1/t}
and {x} = x − [x] is the fractional part of x.
This has been extended by Baez-Duarte, who showed that one may restrict attention to integral values of 1/α. Balazard and Saias have rephrased this in a nice way:
RH holds if and only if
inAf
∫∞
−∞
∣∣∣1 − A( 1
2 + it)ζ( 1
2 + it)
∣∣∣2 dt
1
4 + t2 = 0,
where the infimum is over all Dirichlet polynomials A.
Let dN be the infimum over all Dirichlet polynomials
A(s) =
N ∑
n=1
an n−s
of length N. They conjecture that dN ∼ C/ log N ,
where C = ∑
ρ 1/|ρ|2. Burnol has proved that
dn ≥ 1
log N
∑
ρ on the line
m2
ρ
|ρ|2 ,


 346 NOTICES OF THE AMS VOLUME 50, NUMBER 3
Figure 6. Duality: The Fourier transform of the error term in the Prime Number Theorem (note the spikes at
ordinates of zeros) and the sum over zeros − ∑ xρ with |ρ| < 100 (note the peaks at primes and prime powers).
where mρ is the multiplicity of the zero ρ. If RH holds and all the zeros are simple, then clearly these two bounds are the same.
Weil’s Explicit Formula and Positivity Criterion
André Weil proved the following formula, which is a generalization of Riemann’s formula mentioned above and which specifically illustrates the dependence between primes and zeros. Suppose h is an even function that is holomorphic in the strip | t| ≤ 1/2 + δ and that satisfies h(t) = O((1 + |t|)−2−δ) for some δ > 0, and let
g(u) = 1
2π
∫∞
−∞
h(r )e−iur dr .
Then we have the following duality between primes and zeros of ζ : ∑
γ
h(γ) =2h( i
2 ) − g(0) log π
+1
2π
∫∞
−∞
h(r ) Γ ′
Γ (1
4+1
2ir) dr
−2
∞ ∑
n=1
Λ(n)
√n g(log n).
In this formula, a zero is written as ρ = 1/2 + iγ where γ ∈ C; of course RH is the assertion that every γ is real. Using this duality Weil gave a criterion for RH:
RH holds if and only if ∑
γ
h(γ) > 0
for every (admissible) function h of the form h(r ) = h0(r )h0(r ) .
Xian-Jin Li has given a very nice criterion which, in effect, says that one may restrict attention to a specific sequence hn:
The Riemann Hypothesis is true if and only if λn ≥ 0 for each n = 1, 2, . . . where
λn = ∑
ρ
(1 − (1 − 1/ρ)n).
As usual, the sum over zeros is limT→∞
∑
|ρ|<T .
Another expression for λn is
λn = 1
(n − 1)!
dn
dsn (sn−1 log ξ(s))
∣∣∣∣s=1
.
It would be interesting to find an interpretation
(geometric?) for these λn, or perhaps those asso
ciated with a different L-function, to make their pos
itivity transparent.
Selberg’s Trace Formula
Selberg, perhaps looking for a spectral interpreta
tion of the zeros of ζ(s) , proved a trace formula
for the Laplace operator acting on the space of
real-analytic functions defined on the upper half
plane H = {x + iy : y > 0} and invariant under
the group SL(2, Z) of linear fractional transforma
tions with integer entries and determinant one,
which acts discontinuously on H . This invariance
is expressed as
f
( az + b cz + d
)
= f (z);
the Laplace operator in this case is
∆ = −y2
( ∂2
∂x2 + ∂2
∂x2
)
.
The spectrum of ∆ splits into a continuous part and
a discrete part. The eigenvalues λ are all positive
and, by convention, are usually expressed as
λ = s(1 − s). The continuous part consists of all
s = 1/2 + it , t ≥ 0, and we write the discrete part
as sj = 1
2 + irj. Then


 MARCH 2003 NOTICES OF THE AMS 347
Some Other Equivalences of Interest
Here are a few other easy-to-state equivalences of RH: • Hardy and Littlewood (1918): RH holds if and only if
∞ ∑
k=1
(−x)k
k! ζ(2k + 1) = O(x−1/4) as x → ∞.
• Redheffer (1977): RH holds if and only if for every > 0 there is a C( ) > 0 such that | det(A(n))| < C( )n1/2+ , where A(n) is the n × n matrix of 0’s and 1’s defined by A(i, j) = 1 if j = 1 or if i divides j, and A(i, j) = 0 otherwise. It is known that A(n) has n − [n log 2] − 1 eigenvalues equal to 1. Also, A has a real eigenvalue
(the spectral radius) which is approximately √n, a negative eigenvalue which is approximately
−√n, and the remaining eigenvalues are small. • Lagarias (2002): Let σ (n) denote the sum of the positive divisors of n. RH holds if and only if
σ (n) ≤ Hn + exp(Hn) log Hn
for every n, where Hn = 1 + 1
2+1
3 +···+ 1
n.
Other Zeta- and L-Functions
Over the years striking analogies have been observed between the Riemann zeta-function and other zeta- or L-functions. While these functions are seemingly independent of each other, there is growing evidence that they are all somehow connected in a way that we do not fully understand. In any event, trying to understand, or at least classify, all of the objects which we believe satisfy RH is a reasonable thing to do. The rest of the article will give a glimpse in this direction and perhaps a clue to the future. First, some examples of other functions that we believe satisfy RH. The simplest after ζ is the Dirichlet L-function for the nontrivial character of conductor 3:
L(s, χ3) = 1 − 1
2s + 1
4s − 1
5s + 1
7s − 1
8s + . . . .
Figure 7. The eigenvalues of a random 40 x 40 unitary matrix, 40 consecutive zeros of ζ(s) scaled to wrap once around the circle, and 40 randomly chosen points on the unit circle.
∞ ∑
j =1
h(rj ) = − h(0) − g(0) log π
2− 1
2π
∫∞
−∞
h(r )G(r ) dr
+2
∞ ∑
n=1
Λ(n)
n g(2log n)
+∑
P
∞ ∑
:=1
g(: log P ) log P
P :/2 − P −:/2
where g, h, and Λ are as in Weil’s formula and
G(r ) = Γ ′
Γ (1
2 + ir) + Γ′
Γ (1 + ir ) − π
6 r tanh π r
+π
cosh π r ( 1
8+
√3
9 cosh πr
3 ).
The final sum is over the norms P of prime geodesics of SL(2, Z)\H. The values taken on by P
are of the form (n + √n2 − 4 )2/4 , n ≥ 3 , with certain multiplicities (the class number h(n2 − 4)). H. Haas was one of the first people to compute the eigenvalues r1 = 9.533 . . . , r2 = 12.173 . . ., r3 = 13.779 . . . of SL(2, Z) in 1977 in his University of Heidelberg Diplomarbeit. Soon after, Hejhal was visiting San Diego, and Audrey Terras pointed out to him that Haas’s list contained the numbers 14.134 . . ., 21.022 . . .: the ordinates of the first few zeros of ζ(s) were lurking amongst the eigenvalues! Hejhal discovered the ordinates of the zeros of L(s, χ3) (see section 7) on the list too. He unraveled this perplexing mystery about six months later. It turned out that the spurious eigenvalues were associated to “pseudo cusp forms” and appeared because of the method of computation used. If the zeros had appeared legitimately, RH would have followed because λ = ρ(1 − ρ) is positive. (The 1979 IHÉS preprint by P. Cartier and Hejhal contains additional details of the story.) The trace formula resembles the explicit formula in certain ways. Many researchers have attempted to interpret Weil’s explicit formula in terms of Selberg’s trace formula.


 348 NOTICES OF THE AMS VOLUME 50, NUMBER 3
This can be written as an Euler product ∏
p≡1 mod 3
(1 − p−s )−1 ∏
p≡2mod 3
(1 + p−s )−1,
it satisfies the functional equation
ξ(s, χ3) :=
(π 3
)− s
2 Γ ( s+1
2 )L(s, χ3) = ξ(1 − s, χ3),
and it is expected to have all of its nontrivial zeros on the 1/2-line. A similar construction works for any primitive Dirichlet character. Dedekind, Hecke, Artin, and others developed the theory of zeta-functions associated with number fields and their characters. These have functional equations and Euler products, and are expected to satisfy a Riemann Hypothesis. Ramanujan’s taufunction defined implicitly by
x
∞ ∏
n=1
(1 − xn)24 =
∞ ∑
n=1
τ (n)xn
also yields an L-function. The associated Fourier se
ries ∆(z) := ∑∞
n=1 τ(n) exp(2π inz) satisfies
∆
( az + b cz + d
)
= (cz + d)12∆(z)
for all integers a, b, c, d with ad − bc = 1. A function satisfying these equations is called a modular form of weight 12. The associated L-function
L∆(s) :=
∞ ∑
n=1
τ (n)/n11/2 ns
=∏
p
(
1 − τ(p)/p11/2
ps + 1
p2s
)−1
satisfies the functional equation
ξ∆ := (2π )−s Γ (s + 11/2)L∆(s) = ξ∆(1 − s),
and all of its complex zeros are expected to be on the 1/2-line. Another example is the L-function associated to an elliptic curve E : y2 = x3 + Ax + B, where A and B are integers. The associated L-function, called the Hasse-Weil L-function, is
LE(s) =
∞ ∑
n=1
a(n)/n1/2 ns
=∏
pN
(
1 − a(p)/p1/2
ps + 1
p2s
)−1
×∏
p|N
(
1 − a(p)/p1/2
ps
)−1
,
where N is the conductor of the curve. The coefficients an are constructed easily from ap for prime p; in turn the ap are given by ap = p − Np , where Np is the number of solutions of E when considered modulo p. The work of Wiles and others proved that
these L-functions are associated to modular forms of weight 2. This modularity implies the functional equation
ξE(s) := (2π /√N )−s Γ (s + 1/2)LE(s) = ξE(1 − s).
It is believed that all of the complex zeros of LE(s) are on the 1/2-line. A similar construction ought to work for other sets of polynomial equations, but so far this has not been proved. What is the most general situation in which we expect the Riemann Hypothesis to hold? The Langlands program is an attempt to understand all L-functions and to relate them to automorphic forms. At the very least a Dirichlet series that is a candidate for RH must have an Euler product and a functional equation of the right shape. Selberg has given a set of four precise axioms which are believed to characterize the L-functions for which RH holds. Examples have been given that show the necessity of most of the conditions in his axioms.
L-Functions and Random Matrix Theory
An area of investigation which has stimulated much recent work is the connection between the Riemann zeta-function and Random Matrix Theory (RMT). This work does not seem to be leading in the direction of a proof of RH, but it is convincing evidence that the spectral interpretation of the zeros sought by Hilbert and Pólya is an idea with merit. Moreover, the connection between zeta theory and RMT has resulted in a very detailed model of ζ(s) and its value distribution.
Montgomery’s Pair Correlation Conjecture
In 1972 Hugh Montgomery was investigating the spacings between zeros of the zeta-function in an attempt to solve the class number problem. He formulated his Pair Correlation Conjecture based in part on what he could prove assuming RH and in part on RH plus conjectures for the distribution of twin primes and other prime pairs. This conjecture asserts that ∑
2π α
log T <γ−γ′≤ 2πβ
log T
1 ∼ N(T )
∫β
α
(
1−
( sin π u πu
)2)
du.
The sum on the left counts the number of pairs 0 < γ, γ′ < T of ordinates of zeros with normalized spacing between positive numbers α < β. Montgomery had stopped in Princeton on his way from St. Louis, where he had presented this result at an AMS symposium, to Cambridge University, where he was a graduate student. Chowla persuaded him to show this result to Freeman Dyson at afternoon tea at the Institute for Advanced Study. Dyson
immediately identified the integrand 1 −
( sin πu πu
)2
as the pair correlation function for eigenvalues of large random Hermitian matrices measured with a Gaussian measure—the Gaussian Unitary Ensemble that physicists had long been studying


 trix explanation for these numbers. By 1998 Gonek and I had found a number-theoretic way to conjecture the answer for the eighth moment, namely g4 = 24024 . At RHII in Vienna, Keating announced that he and Snaith had a conjecture for all of the moments which agreed with g1 , g2 , and g3 . Keating, Snaith, and I—moments before Keating’s lecture—checked (amid great excitement!) that the Keating and Snaith conjecture also produced g4 = 24024 . The idea of Keating and Snaith was that if the eigenvalues of unitary matrices model zeta zeros, then perhaps the characteristic polynomials of unitary matrices model zeta values. They were able to compute—exactly—the moments of the characteristic polynomials of unitary matrices averaged with respect to Haar measure by using Selberg’s integral, which is a formula found in the 1940s by Selberg that vastly generalizes the integral for the beta-function. Keating and Snaith proposed that
gk = k2!
k− ∏1
j =0
j!
(j + k)! .
Farmer and I (2000) proved that gk is always an integer and found that it has an interesting prime factorization. Families
At RHI in Seattle, Sarnak gave a lecture on families of L-functions based on work that he and Katz were doing. They discovered a way to identify a symmetry type (unitary, orthogonal, or symplectic) with various families of L-functions. Their work was based on studying families of zeta-functions over finite fields (for which RH was already proved by Weil for curves and by Deligne for general varieties). For these zeta-functions, Katz and Sarnak proved that the zeros of the family were distributed exactly
in connection with the distribution of energy levels in large systems of particles. With this insight, Montgomery went on to conjecture that perhaps all the statistics, not just the pair correlation statistic, would match up for zeta-zeros and eigenvalues of Hermitian matrices. This conjecture is called the GUE conjecture. It has the flavor of a spectral interpretation of the zeros, though it gives no indication of what the particular operator is. Odlyzko’s Calculations
In the 1980s Odlyzko began an intensive numerical study of the statistics of the zeros of ζ(s) . Based on a new algorithm developed by Odlyzko and Schönhage that allowed them to compute a value of ζ(1/2 + it) in an average time of t steps, he computed millions of zeros at heights around 1020 and spectacularly confirmed the GUE conjecture.
Moments of Zeta
More recently, RMT has led to a conjecture for moments of ζ on the critical line. Let
Ik(T ) = 1
T
∫T
0
|ζ(1/2 + it)|2k dt.
Asymptotic formulas for I1 and I2 were found by Hardy and Littlewood and Ingham by 1926. In 1995 Ghosh and I formulated a conjecture for I3 and set up a notation to clarify the part missing from our understanding of Ik. After scaling out the arithmetic parts, we identified a factor gk which we could not predict. The factor is g1 = 1 and g2 = 2 for the second and fourth moments and conjecturally g3 = 42 for the sixth moment. At RHI in Seattle, Sarnak proposed to Keating that he find a random ma
MARCH 2003 NOTICES OF THE AMS 349
Figure 8a. The nearest neighbor spacing for GUE (solid) and for 7.8 × 107 zeros of ζ(s) near the 1020 zero (scatterplot). Graphic by A. Odlyzko.
Figure 8b.The pair-correlation function for GUE (solid) and for 8 × 106 zeros of ζ(s) near the 1020 zero (scatterplot). Graphic by A. Odlyzko.


 350 NOTICES OF THE AMS VOLUME 50, NUMBER 3
Figure 10. The second zero for L(s, χd) as compared to the RMT prediction. Graphic by M. Rubinstein.
Figure 11. The distribution of values of |ζ(1/2 + it)| near t = 106 compared with the distribution of values of characteristic polynomials of 12 × 12 unitary matrices. Graphic by N. Snaith.
Figure 9. A comparison of the distribution of the lowest lying zero for two families of L-functions. In each case one first needs to suitably normalize the zeros. The first figure compares the distribution of the lowest zero of L(s, χd), Dirichlet L-functions, for several thousand d’s of size 1012, against the distribution of the zero closest to 1 for large unitary symplectic matrices. In the second picture we show the same statistic, but for several thousand even quadratic twists d of size 500,000, of the Ramanujan τ cusp form L-function. This is compared to the distribution of the zero closest to 1 for large orthogonal matrices with even characteristic polynomial (in the latter family, one needs to distinguish between even and odd twists). Graphics by M. Rubinstein.
as the RMT distributions of the monodromy group associated with the family. Katz and Sarnak stress that the proofs of Weil and Deligne use families of zeta-functions over finite fields to prove RH for an individual zetafunction. The modelling of families of L-functions by ensembles of random matrix theory gives evidence for a spectral interpretation of the zeros, which may prove important if families are ultimately used to prove RH. At this point, however, we do not know what plays the role of the monodromy groups in this situation.
RMT and Families
Keating and Snaith extended their conjectures to moments of families of L-functions by computing moments of characteristic polynomials of symplectic and orthogonal matrices, each with their own Haar measure. (It should be mentioned that the orthogonal and symplectic circular ensembles used by the physicists do not use Haar measure and so have different answers. Katz and Sarnak figured out that Haar measure must be used to model L-functions.) Further works by Farmer, Keating, Rubinstein, Snaith, and this author have led to precise conjectures for all of the main terms in moments for many families of L-functions. These results are so precise that they lead to further conjectures about the distribution of values of the L-functions. We can even predict how frequently we find double zeros at the center of the critical strip of L-functions within certain families.


 MARCH 2003 NOTICES OF THE AMS 351
The Conspiracy of L-Functions
There is a growing body of evidence that there is a conspiracy among L-functions—a conspiracy which is preventing us from solving RH! The first clue that zeta- and L-functions even know about each other appears perhaps in works of Deuring and Heilbronn in their study of one of the most intriguing problems in all of mathematics: Gauss’s class number problem. Gauss asked whether the number of equivalence classes of binary quadratic forms of discriminant d < 0 goes to ∞ as d goes to −∞. The equivalence class of a quadratic form Q(m, n) = am2 + bmn + cn2 of discriminant d = b2 − 4ac consists of all of the quadratic forms obtained by a linear substitution m → αm + βn, n → γm + δn, where α, β, γ, δ are integers with αδ − βγ = 1 . The number h(d) of these equivalence classes is called the class number and is known to be finite. Equivalently, h(d) is the number of ideal classes of the imaginary quadratic field
Q(√d ). The history of Gauss’s problem is extremely interesting; it has many twists and turns and is not yet finished—we seem to be players in the middle of a mystery novel. Deuring and Heilbronn were trying to solve Gauss’s problem. The main tool they were using was the beautiful class number formula of Dirichlet,
h(d) = √|d| L(1, χd)/π (|d| > 4 ), which gives the class number in terms of the value of the L-function at 1, which is at the edge of the critical strip. So the question boils down to giving a lower bound for L(1, χd); this question, in turn, can be resolved by proving that there is no real zero of L(s, χd) very near to 1. Hecke had shown that the truth of RH for L(s, χd) implies that h(d) → ∞. Then Deuring proved that the falsity of RH for ζ(s) implies that h(d) > 1 for large |d|. Finally, Heilbronn showed that the falsity of RH for L(s, χ) for any χ implied that h(d) → ∞. These results together proved Gauss’s conjecture and gave a first indication of a connection between the zeros of ζ(s) and those of L(s, χd)! Later Landau showed that a hypothetical zero of L(s, χd1 ) very near to 1 implies that no other L(s, χd), d = d1, could have such a zero, further illustrating that zeros of L(s, χd) know about each other. Siegel strengthened this approach to show that for every > 0 there is a c( ) > 0 such that no zero β of L(s, χd) satisfies β > 1 − c( )|d|− . The problem with the arguments of Landau and Siegel is that the constant c( ) cannot be effectively computed, and so the bound cannot be used to actually calculate the list of discriminants d with a given class number, which presumably is what Gauss wanted. The ineffectivity comes about from the assumption that some L-function actually has a real zero near 1. Such a hypothetical zero of
some L-function, which no one believes exists, is called a Landau-Siegel zero. In fact, one can show that if there is some d1 such that L(s, χd1 ) has a zero at β < 1, then it follows that h(d) > c|d|β−1/2/ log |d| for all other d, where c > 0 can be effectively computed. Thus, the closer to 1 the hypothetical zero is, the stronger the result. But note also that any zero bigger than 1/2 would give a result. The basic idea behind this approach is that if there is an L(s, χd) with a zero near 1, then χd(p) = −1 for many small primes. In other words, χd mimics the Möbius function μ(n) for small n. This is consistent with the fact that
∞ ∑
n=1
μ(n) ns
has a zero at s = 1 (since ζ(s) has a pole at s = 1). The Landau-Siegel Zero
Much effort has gone toward trying to eliminate the Landau-Siegel zero described above and so find an effective solution to Gauss’s problem. However, the L-function conspiracy blocks every attempt exactly at the point where success appears to be in sight. We begin to suspect that the battle for RH will not be won without getting to the bottom of this conspiracy. Here are some tangible examples which give a glimpse of this tangled web.
The Brun-Titchmarsh theorem. Let π (x; q, a) denote the number of primes less than or equal to x that lie in the arithmetic progression a mod q . Sieve methods can show that for any 1 ≤ q < x the inequality
π (x; q, a) ≤ 2 x
φ(q) log(x/q)
holds, where φ is Euler’s phi-function. It is believed that the same theorem should be true with 2 replaced by any number larger than 1 and sufficiently large x. Any lowering of the constant 2 would eliminate the Landau-Siegel zero. In particular, Motohashi [1979] proved that if 1 − δ is a real zero of L(s, χq), then if for x ≥ qc the Brun-Titchmarsh theorem is valid in the form π (x; q, a) ≤ (2 − α)x/(φ(q) log(x/q)) , where α > 0 is an absolute constant, then δ ≥ c′ξ/ log q , where c and c′ are certain numerical constants.
The Alternative Hypothesis. This is an alternative to the GUE model for the distribution of zeros. It proposes the existence of a function f (T ) that goes to 0 as T → ∞ such that if any two consecutive ordinates γ and γ′ of zeros of ζ larger than some T0 are given, then the normalized gap 2π (γ log γ − γ′ log γ′) between γ and γ′ is within f (T0) of half of an integer. This hypothesis is clearly absurd! However, ruling this out would eliminate the Landau-Siegel zero (Conrey–Iwaniec (2002)), and so for all we know it could be true.


 352 NOTICES OF THE AMS VOLUME 50, NUMBER 3
L-functions is to look at elliptic curves with many rational points.
Iwaniec’s Approach
Iwaniec, in his lecture at RHIII, proposed a way to take advantage of the above ideas. In a nutshell, his idea is to take a family of L-functions having a multiple zero at 1/2 and use this family to obtain useful approximations for the Möbius function μ(n) as a linear combination of the coefficients of the L-functions from the family. In this way, the Möbius function is tamed. One example of a family considered by Iwaniec is the family of L-functions associated to the elliptic curves
EA,B2 : y 2 = x3 + Ax + B2,
which have a rational point (B, 0) and so have rank at least one. Considering A and B in certain arithmetic progressions shows that the associated L-function must have a double zero at the center. Iwaniec presented three conjectures which together would eliminate the Landau-Siegel zero. The main two theorems needed to complete his program are a bound for the second moment ∑
A≈X1/3, B≈X1/4
LA,B2 (1/2)2 = O(X7/12(log X)C )
of this family together with a good estimate (squareroot cancellation uniform in M, N, and q) for the incomplete exponential sum
∑
M <m<2M ,N <n<2N
χq(mn) exp
(
2π i m3n−4
q
)
,
the kind of estimate that for a completed exponential sum follows from the RH for varieties proved by Deligne. Iwaniec has similar, but more complicated, constructions that would lead to a quasi-Riemann hypothesis, producing a concrete β < 1 such that there are no zeros to the right of the line through β . Iwaniec’s approach will likely reduce the question of RH, which is ostensibly about zeros or poles, into several subsidiary questions that have a much different flavor, such as finding upper bound estimates for moments and values of L-functions. This approach offers hope of attack by methods from analytic number theory.
Conclusion
A major difficulty in trying to construct a proof of RH through analysis is that the zeros of L-functions behave so much differently from zeros of many of the special functions we are used to seeing in mathematics and mathematical physics. For example, it is known that the zeta-function does not satisfy any differential equation. The functions which do arise as solutions of some of the classical differential equations, such as Bessel functions, hypergeometric
If one could prove, for example, that there is a δ > 0 such that for all sufficiently large T there is a pair of consecutive zeros with ordinates between T and 2T whose distance apart is less than 1/2 − δ times the average spacing, then the alternative hypothesis would be violated. Random matrix theory predicts the exact distribution of these neighbor spacings and shows that we should expect that about 11 percent of the time the neighbor gaps are smaller than 1/2 of the average. These ideas were what led Montgomery to consider the paircorrelation of the zeros of ζ(s) mentioned above. He showed that there are arbitrarily large pairs of zeros that are as close together as 0.68 of the average spacing. Later works have gotten this bound down to 0.5152. There are indications that using work of Rudnick and Sarnak on higher correlations of the zeros of ζ , one might be able to reach 0.5, but 0.5 is definitely a limit (more like a brick wall!) of all of the known methods.
Vanishing of modular L-functions. The most spectacular example is the work of Iwaniec and Sarnak. They showed that if one could prove that there is a δ > 0 such that more than 1/2 + δ of the modular L-functions of a fixed weight, large level, and even functional equation do not vanish, then the Landau-Siegel zero could be eliminated. It is predicted that all but an infinitesimal proportion of these values are nonzero; they just needed one-half plus δ of them to be nonzero. They can prove that 50 percent do not vanish, but despite their best efforts they cannot get that extra little tiny bit needed to eliminate the Landau-Siegel zero.
A Clue and a Partial Victory
The only approach that has made an impact on the Landau-Siegel zero problem is an idea of Goldfeld. In 1974 Goldfeld, anticipated somewhat by Friedlander, realized that while a zero at 1/2 would barely fail to produce a lower bound for the class number tending to infinity, a multiple zero at 1/2 would produce a lower bound which, while not a positive power of |d|, still goes to ∞. Moreover, it was believed—by virtue of the Birch and Swinnerton-Dyer conjecture—that zeros of high multiplicity do exist and the place to look for them is among L-functions associated to elliptic curves with large rank. However, it was not until 1985 that Gross and Zagier demonstrated conclusively that there exist L-functions with triple zeros at 1/2. This led to the lower bound that for any > 0 there is an effectively computable c1( ) > 0 such that h(d) > c1( )(log |d|)1− . This is a long way from the ex
pected h(d) > c√|d|/ log |d| , but it did solve Gauss’s problem. The clue that it gave us was to study exotic L-functions, or extremal L-functions, which have zeros of high multiplicity at the center. At present, our best hope for finding these


 MARCH 2003 NOTICES OF THE AMS 353
functions, etc., have zeros which are fairly regularly spaced. A similar remark holds for the zeros of solutions of classical differential equations regarded as a function of a parameter in the differential equation. For instance, in the Pólya theorem above comparing φ(t) with Φ(t), the zeros are actually zeros of a Bessel function of fixed argument regarded as a function of the index. Again the zeros are regularly spaced. On the other hand, the zeros of L-functions are much more irregularly spaced. For example, the RMT models predict that for any > 0 there are infinitely many pairs of zeros ρ and ρ′ such that |ρ − ρ′| < |ρ|−1/3+ . Generally it is believed that all zeros of all L-functions are linearly independent (in particular, simple), except that certain L-functions can have a zero at s = 1/2 of high multiplicity. The conjecture of Birch and Swinnerton-Dyer asserts that the multiplicity of the zero of the L-function associated with a given elliptic curve is equal to the rank of the group of rational points on the elliptic curve. It is known that the latter can be as large as 26, and it is generally believed to get arbitrarily large. None of the methods from analysis seem capable of dealing with such exotic phenomena. It is my belief that RH is a genuinely arithmetic question that likely will not succumb to methods of analysis. There is a growing body of evidence indicating that one needs to consider families of L-functions in order to make progress on this difficult question. If so, then number theorists are on the right track to an eventual proof of RH, but we are still lacking many of the tools. The ingredients for a proof of RH may well be moment theorems for a new family of L-functions not yet explored; modularity of Hasse-Weil L-functions for many varieties, like that proved by Wiles and others for elliptic curves; and new estimates for exponential sums, which could come out of arithmetic geometry. The study of L-functions is still in its beginning stages. We only recently learned the modularity of the L-functions associated to elliptic curves; it would be very helpful to understand the L-functions for more complicated curves and generally for varieties. It would be useful to systematically compute many new examples of L-functions to get a glimpse of what is out there waiting to be discovered. The exotic behavior of the multiple zeros of L-functions associated to elliptic curves with many rational points could be just the beginning of the story.
Acknowledgements
I would like to thank David Farmer, K. Soundararajan, Roger Heath-Brown, Brianna Conrey, and Harold Boas for their valuable comments during the preparation of this article. Also, I thank Andrew Odlyzko, Michael Rubinstein, Nina Snaith,
and Sandra Frost for their assistance with the graphics in the article.
—J.B.C.
References
• E. BOMBIERI, Problems of the Millennium: The Riemann Hypothesis, http://claymath.org/prizeproblems/ riemann.htm.
• HAROLD DAVENPORT, Multiplicative Number Theory, third edition, revised and with a preface by Hugh L. Montgomery, Grad. Texts in Math., vol. 74, Springer-Verlag, New York, 2000.
• P. A. DEIFT, Orthogonal Polynomials and Random Matrices: A Riemann-Hilbert Approach, Courant Lecture Notes in Math., vol. 3, New York University, Courant Institute of Mathematical Sciences, New York; Amer. Math. Soc., Providence, RI, 1999.
• HENRYK IWANIEC, Introduction to the Spectral Theory of Automorphic Forms, Bibl. Rev. Mat. Iberoamericana [Library of the Revista Matemática Iberoamericana], Rev. Mat. Iberoamericana, Madrid, 1995.
• ———, Topics in Classical Automorphic Forms, Grad. Stud. Math., vol. 17, Amer. Math. Soc., Providence, RI, 1997. • NICHOLAS M. KATZ and PETER SARNAK, Random Matrices, Frobenius Eigenvalues, and Monodromy, Amer. Math. Soc. Colloq. Publ., vol. 45, Amer. Math. Soc., Providence, RI, 1999. • MADAN LAL MEHTA, Random Matrices, second edition, Academic Press, Inc., Boston, MA, 1991.
• A. M. ODLYZKO, http://www.dtc.umn.edu/ ~odlyzko/.
• ATLE SELBERG, Old and New Conjectures and Results about a Class of Dirichlet Series, Collected Papers, Vol. II, with a foreword by K. Chandrasekharan, SpringerVerlag, Berlin, 1991.
• E. C. TITCHMARSH, The Theory of the Riemann ZetaFunction, second edition, edited and with a preface by D. R. Heath-Brown, The Clarendon Press, Oxford University Press, New York, 1986.