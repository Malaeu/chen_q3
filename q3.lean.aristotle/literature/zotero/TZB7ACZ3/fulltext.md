---
title: "Primes in tuples I"
authors:
  - "Daniel A. Goldston"
  - "J\u00e1nos Pintz"
  - "Cem Y. Y\u0131ld\u0131r\u0131m"
date: "2009-00-00 2009"
publication: "Annals of Mathematics"
doi: "10.4007/annals.2009.170.819"
url: null
zotero:
  attachment_key: "U7GQPYVD"
  parent_key: "TZB7ACZ3"
  item_id: 2308
  attachment_item_id: 2317
---

ANNALS OF
MATHEMATICS
anmaah
SECOND SERIES, VOL. 170, NO. 2
September, 2009
Primes in tuples I
By Daniel A. Goldston, J ́anos Pintz, and Cem Y. Yıldırım


 

 Annals of Mathematics, 170 (2009), 819–862
Primes in tuples I
By DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
Abstract
We introduce a method for showing that there exist prime numbers which are very close together. The method depends on the level of distribution of primes in arithmetic progressions. Assuming the Elliott-Halberstam conjecture, we prove that there are infinitely often primes differing by 16 or less. Even a much weaker conjecture implies that there are infinitely often primes a bounded distance apart. Unconditionally, we prove that there exist consecutive primes which are closer than any arbitrarily small multiple of the average spacing, that is,
lim inf
n!1
pnC1 pn
log pn
D 0:
We will quantify this result further in a later paper.
1. Introduction
One of the most important unsolved problems in number theory is to establish the existence of infinitely many prime tuples. Not only is this problem believed to be difficult, but it has also earned the reputation among most mathematicians in the field as hopeless in the sense that there is no known unconditional approach for tackling the problem. The purpose of this paper, the first in a series, is to provide what we believe is a method which could lead to a partial solution for this problem. At present, our results on primes in tuples are conditional on information about the distribution of primes in arithmetic progressions. However, the information needed to prove that there are infinitely often two primes in a given k-tuple for sufficiently large k does not seem to be too far beyond the currently known results. Moreover, we can gain enough in the argument by averaging over many tuples to obtain unconditional results concerning small gaps between primes which go
Goldston was supported by NSF grant DMS-0300563, the NSF Focused Research Group grant 0244660, and the American Institute of Mathematics; Pintz by OTKA grants No. T38396, T43623, T49693 and the Balaton program; Yıldırım by TÜB ̇ITAK.
819


 820 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
far beyond anything that has been proved before. Thus, we are able to prove the existence of very small gaps between primes which, however, go slowly to infinity with the size of the primes. The information on primes we utilize in our method is often referred to as the level of distribution of primes in arithmetic progressions. Let
(1.1) .n/ D
log n if n is prime; 0 otherwise;
and consider the counting function
(1.2) .N I q; a/ D
X
nN n a.mod q/
.n/:
The Bombieri-Vinogradov theorem states that for any A > 0 there is a B D B.A/
such that, for Q D N 1
2 .log N / B ,
(1.3)
X
qQ
maax
.a;q/D1
ˇ ˇ ˇ ˇ
.N I q; a/ N
.q/
ˇ ˇ ˇ ˇ
N
.log N /A :
We say that the primes have level of distribution # if (1.3) holds for any A > 0 and any " > 0 with
(1.4) Q D N # ":
Elliott and Halberstam [5] conjectured that the primes have level of distribution 1. According to the Bombieri-Vinogradov theorem, the primes are known to have level of distribution 1=2. Let n be a natural number and consider the k-tuple
(1.5) .n C h1; n C h2; : : : ; n C hk/;
where H D fh1; h2; : : : ; hkg is a set composed of distinct non-negative integers. If every component of the tuple is a prime we call this a prime tuple. Letting n range over the natural numbers, we wish to see how often (1.5) is a prime tuple. For instance, consider H D f0; 1g and the tuple .n; n C 1/. If n D 2, we have the prime tuple .2 ; 3/. Notice that this is the only prime tuple of this form because, for n > 2, one of the numbers n or n C 1 is an even number bigger than 2. On the other hand, if H D f0; 2g, then we expect that there are infinitely many prime tuples of the form .n; n C 2/. This is the twin prime conjecture. In general, the tuple (1.5) can be a prime tuple for more than one n only if for every prime p the hi ’s never occupy all of the residue classes modulo p. This is immediately true for all primes p > k; so to test this condition we need only to examine small primes. If we denote by p.H/ the number of distinct residue classes modulo p occupied by the integers hi ,


 PRIMES IN TUPLES I 821
then we can avoid p dividing some component of (1.5) for every n by requiring
(1.6) p.H/ < p for all primes p:
If this condition holds we say that H is admissible and we call the tuple (1.5) corresponding to this H an admissible tuple. It is a long-standing conjecture that admissible tuples will infinitely often be prime tuples. Our first result is a step towards confirming this conjecture.
THEOREM 1. Suppose the primes have level of distribution # > 1=2. Then there exists an explicitly calculable constant C.#/ depending only on # such that any admissible k-tuple with k C.#/ contains at least two primes infinitely often. Specifically, if # 0:971, then this is true for k 6.
Since the 6-tuple .n; n C 4; n C 6; n C 10; n C 12; n C 16/ is admissible, the Elliott-Halberstam conjecture implies that
(1.7) lim inf
n!1
.pnC1 pn/ 16;
where the notation pn is used to denote the n-th prime. This means that pnC1 pn 16 for infinitely many n. Unconditionally, we prove a long-standing conjecture concerning gaps between consecutive primes.
THEOREM 2. We have
(1.8) Å1 WD lim inf
n!1
pnC1 pn
log pn
D 0:
There is a long history of results on this topic which we will briefly mention. The inequality Å1 1 is a trivial consequence of the prime number theorem. The first result of type Å1 < 1 was proved in 1926 by Hardy and Littlewood [18], who on assuming the Generalized Riemann Hypothesis (GRH) obtained Å1 2=3. This result was improved by Rankin [26] to Å1 3=5; also assuming the GRH. The first unconditional estimate was proved by Erd ̋os [7] in 1940. Using Brun’s sieve, he showed that Å1 < 1 c with an unspecified positive explicitly calculable constant c. His estimate was improved by Ricci [27] in 1954 to Å1 15=16: In 1965, Bombieri and Davenport [2] refined and made unconditional the method of Hardy and Littlewood by substituting the Bombieri-Vinogradov theorem for the GRH, and obtained Å1 1=2. They also combined their method with the method of Erd ̋os and obtained Å1 0:4665 : : : . Their result was further refined by Pilt’ai [25] to Å1 0:4571 : : : , Uchiyama [33] to Å1 0:4542 : : : and in several steps by Huxley [20], [21] to yield Å1 0:4425 : : : , and finally in 1984 to Å1 :4393 : : : [22]. This was further improved by Fouvry and Grupp [9] to Å1 :4342 : : : : In 1988 Maier [23] used his matrix-method to improve Huxley’s result to Å1 e 0:4425 : : : D 0:2484 : : : , where is Euler’s constant. Maier’s method by itself gives Å1 e D 0:5614 : : : . The recent version of the method


 822 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
of Goldston and Yıldırım [13] led, without combination with other methods, to Å1 1=4.
In a later paper in this series we will prove the quantitative result that
(1.9) lim inf
n!1
pnC1 pn
.log pn/ 1
2 .log log pn/2 < 1:
While Theorem 1 is a striking new result, it also reflects the limitations of our current method. Whether these limitations are real or can be overcome is a critical issue for further investigation. We highlight the following four questions.
Question 1. Can it be proved unconditionally by the current method that there are, infinitely often, bounded gaps between primes? Theorem 1 would appear to be within a hair’s breadth of obtaining this result. However, any improvement in the level of distribution # beyond 1=2 probably lies very deep, and even the GRH does not help. Still, there are stronger versions of the Bombieri-Vinogradov theorem, as found in [3], and the circle of ideas used to prove these results, which may help to obtain this result.
Question 2. Is # D 1=2 a true barrier for obtaining primes in tuples? Soundararajan [31] has demonstrated this is the case for the current argument, but perhaps more efficient arguments may be devised.
Question 3. Assuming the Elliott-Halberstam conjecture, can it be proved that there are three or more primes in admissible k-tuples with large enough k? Even under the strongest assumptions, our method fails to prove anything about more than two primes in a given tuple.
Question 4. Assuming the Elliott-Halberstam conjecture, can the twin prime conjecture be proved with a refinement of our method?
The limitation of our method, identified in Question 3, is the reason we are less successful in finding more than two primes close together. However, we are able to improve on earlier results, in particular the recent results in [13]. For 1, let
(1.10) Å D lim inf
n!1
pnC pn
log pn
:
Bombieri and Davenport [2] showed Å 1=2. This bound was later improved by Huxley [20], [21] to Å 5=8 C O.1= /, by Goldston and Yıldırım [13]
to Å .p 1=2/2, and by Maier [23] to Å e . 5=8 C O .1= //. In proving Theorem 2 we will also show, assuming the primes have level of distribution #,
(1.11) Å max. 2#; 0/;


 PRIMES IN TUPLES I 823
and hence unconditionally Å 1. However, by a more complicated argument, we will prove the following result.
THEOREM 3. Suppose the primes have level of distribution #. Then for 2,
(1.12) Å .p p2#/2:
In particular, we have unconditionally, for 1,
(1.13) Å .p 1/2:
From (1.11) or (1.12) we see that the Elliott-Halberstam conjecture implies that
(1.14) Å2 D lim inf
n!1
pnC2 pn
log pn
D 0:
We can improve on (1.13) by combining our method with Maier’s matrix method [23] to obtain
(1.15) Å e .p 1/2:
Huxley [20] generalized the results of Bombieri and Davenport [2] for Å to primes in arithmetic progressions with a fixed modulus. We are able to prove the analogue of (1.15) for primes in arithmetic progressions where the modulus can tend slowly to infinity with the size of the primes considered. Another extension of our work is that we can find primes in other sets besides intervals. Thus we can prove that there are two primes among the numbers n C ai , 1 i h, for N < n 2N and the ai ’s are given arbitrary integers in the interval Œ1; N ç if h < C plog N .log log N /2 and N is restricted to some sequence N tending to infinity, which avoids Siegel zeros for moduli near to N . It is interesting to note that such a general result can be proved regardless of the distribution of the ai values, in contrast to our present case where Gallagher’s theorem (3.7) requires the ai ’s to lie in an interval. The proofs of these results will appear in later papers in this series. While this paper is our first paper on this subject, we have two other papers that overlap some of the results here. The first paper [15], written jointly with Motohashi, gives a short and simplified proof of Theorems 1 and 2. The second paper [14], written jointly with Graham, uses sieve methods to prove Theorems 1 and 2 and provides applications for tuples of almost-primes (products of a bounded number of primes.) The present paper is organized as follows. In Section 2, we describe our method and its relation to earlier work. We also state Propositions 1 and 2 which incorporate the key new ideas in this paper. These are developed in a more general form than in [14] or [15] so as to be employable in many applications. In Section 3, we prove Theorems 1 and 2 using these propositions. The method of proof is due


 824 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
to Granville and Soundararajan. In Section 4 we make some further comments on the method used in Section 3. In Section 5 we prove two lemmas needed later. In Section 6, we prove a special case of Proposition 1 which illustrates the key points in the general case. In Section 7 we begin the proof of Proposition 1 which is reduced to evaluating a certain contour integral. In Section 8 we evaluate a more general contour integral that occurs in the proof of both propositions. In Section 9, we prove Proposition 2. In this paper we do not obtain results that are uniform in k, and therefore we assume here that our tuples have a fixed length. However, uniform results are needed for (1.9), and they will be the topic of the next paper in this series. Finally, we prove Theorem 3 in Section 10.
Notation. In the following, c and C will denote (sufficiently) small and (sufficiently) large absolute positive constants, respectively, which have been chosen appropriately. This is also true for constants formed from c or C with subscripts or accents. We unconventionally will allow these constants to be different at different occurrences. Constants implied by pure o, O, symbols will be absolute, unless otherwise stated. ŒS ç is 1 if the statement S is true and is 0 if S is false. The
symbol P[ indicates the summation is over squarefree integers, and P0 indicates the summation variables are pairwise relatively prime. The ideas used in this paper have developed over many years. We are indebted to many people, not all of whom we can mention. In particular, we would like to thank A. Balog, E. Bombieri, T. H. Chan, J. B. Conrey, P. Deift, D. Farmer, K. Ford, J. Friedlander, S. W. Graham, A. Granville, C. Hughes, D. R. Heath-Brown, A. Ledoan, H. L. Montgomery, Y. Motohashi, Sz. Gy. Revesz, P. Sarnak, J. Sivak, and K. Soundararajan.
2. Approximating prime tuples
Let
(2.1) H D fh1; h2; : : : ; hkg with 1 h1; h2; : : : ; hk h distinct integers;
and let p.H/ denote the number of distinct residue classes modulo p occupied by the elements of H.1 For squarefree integers d , we extend this definition to d .H/ by multiplicativity. We denote by
(2.2) S.H/ WD
Y
p
11
p
k
1 p.H/
p
the singular series associated with H. Since p.H/ D k for p > h, we see that the product is convergent and therefore H is admissible as defined in (1.6) if and only
1The restriction of the set H to positive integers is only for simplicity, and, if desired, can easily be removed later from all of our results.


 PRIMES IN TUPLES I 825
if S.H/ ¤ 0. Hardy and Littlewood conjectured an asymptotic formula for the number of prime tuples .n C h1; n C h2; : : : ; n C hk/, with 1 n N , as N ! 1. Let ƒ.n/ denote the von Mangoldt function which equals log p if n D pm, m 1, and zero otherwise. We define
(2.3) ƒ.nI H/ WD ƒ.n C h1/ƒ.n C h2/ ƒ.n C hk/
and use this function to detect prime tuples and tuples with prime powers in components, the latter of which can be removed in applications. The HardyLittlewood prime-tuple conjecture [17] can be stated in the form
(2.4)
X
nN
ƒ.nI H/ D N.S.H/ C o.1//; as N ! 1.
(This conjecture is trivially true if H is not admissible.) Except for the prime number theorem (1-tuples), this conjecture is unproved.2 The program the first and third authors have been working on since 1999 is to compute approximations for (2.3) with k 3 using short divisor sums and to apply the results to problems on primes. The simplest approximation of ƒ.n/ is based on the elementary formula
(2.5) ƒ.n/ D
X
d jn
.d / log n
d;
which can be approximated with the smoothly truncated divisor sum
(2.6) ƒR.n/ D
X
d jn dR
.d / log R
d:
Thus, an approximation for ƒ.nI H/ is given by
(2.7) ƒR.n C h1/ƒR.n C h2/ ƒR.n C hk/:
In [13], Goldston and Yıldırım applied (2.7) to detect small gaps between primes and proved
Å1 D lim inf
n!1
pnC1 pn
log pn
1
4:
In this paper we introduce a new approximation, the idea for which came partly from a paper of Heath-Brown [19] on almost prime tuples. His result is itself a generalization of Selberg’s proof from 1951 (see [29, pp. 233–245]) that the polynomial n.n C 2/ will infinitely often have at most five distinct prime factors, so that the same is true for the tuple .n; n C 2/. Not only does our approximation have its origin in these papers, but in hindsight the argument of Granville and
2Asymptotic results for the number of primes in tuples, unlike the existence result in Theorem 1, are beyond the reach of our method.


 826 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
Soundararajan (employed in the proof of Theorems 1 and 2) is essentially the same as the method used in these papers. In connection with the tuple (1.5), we consider the polynomial
(2.8) PH.n/ D .n C h1/.n C h2/ .n C hk/:
If the tuple (1.5) is a prime tuple then PH.n/ has exactly k prime factors. We detect this condition by using the k-th generalized von Mangoldt function
(2.9) ƒk.n/ D
X
d jn
.d / log n
d
k
;
which vanishes if n has more than k distinct prime factors.3 With this, our prime tuple detecting function becomes
(2.10) ƒk.nI H/ WD
1
kŠ ƒk.PH.n//:
The normalization factor 1=kŠ simplifies the statement of our results. As we will see in Section 5, this approximation suggests the Hardy-Littlewood type conjecture
(2.11)
X
nN
ƒk.nI H/ D N .S.H/ C o.1// :
This is a special case of the general conjecture of Bateman–Horn [1] which is the quantitative form of Schinzel’s conjecture [28]. In analogy with (2.6) (when k D 1), we approximate ƒk.n/ by the smoothed and truncated divisor sum
X
d jn dR
.d / log R
d
k
and define
ƒR.nI H/ D
1
kŠ
X
d jPH.n/ dR
.d / log R
d
k
(2.12) :
However, as we will see in the next section, this approximation is not adequate to prove Theorems 1 and 2. A second simple but crucial idea is needed: rather than only approximate prime tuples, one should approximate tuples with primes in many components. Thus, we consider when PH.n/ has k C ` or fewer distinct prime factors, where
3As with ƒ.n/, we overcount the prime tuples by including factors which are proper prime powers, but these can be removed in applications with a negligible error. The slightly misleading notational conflict between the generalized von Mangoldt function ƒk and ƒR will only occur in this section.


 PRIMES IN TUPLES I 827
0 ` k, and define
(2.13) ƒR.nI H; `/ D
1
.k C `/Š
X
d jPH.n/ dR
.d / log R
d
kC`
;
where jHj D k. If H D ∅, then k D ` D 0 and we define ƒR.nI ∅; 0/ D 1. The advantage of (2.13) over (2.7) can be seen as follows. If in (2.13) we restrict ourselves to d ’s with all prime factors larger than h, then the condition d jPH.n/ implies that we can write d D d1d2 dk uniquely with di jn C hi , 1 i k, the di ’s pairwise relatively prime, and d1d2 dk R. In our application to prime
gaps we require that R N 1
4 ". On the other hand, on expanding, (2.7) becomes a sum over di jn C hi , 1 i k, with d1 R, d2 R, : : : , dk R. The application
to prime gaps here requires that Rk N 1
4 ", and so R N 1
4k
"
k . Thus (2.7) has a more severe restriction on the range of the divisors. An additional technical advantage is that having one truncation rather than k truncations simplifies our calculations. Our main results on ƒR.nI H; `/ are summarized in the following two propositions. Suppose H1 and H2 are, respectively, sets of k1 and k2 distinct non-negative integers h. We always assume that at least one of these sets is nonempty. Let
M D k1 C k2 C `1 C `2.
PROPOSITION 1. Let H D H1 [ H2, jHi j D ki , and r D jH1 \ H2j. If
R N1
2 .log N / 4M and h RC for any given constant C > 0, then as R; N ! 1,
(2.14)
X
nN
ƒR.nI H1; `1/ƒR.nI H2; `2/
D `1C`2
`1
.log R/rC`1C`2
.r C `1 C `2/Š .S.H/CoM .1//N:
PROPOSITION 2. Let H D H1 [ H2, jHi j D ki , r D jH1 \ H2j, 1 h0 h,
and H0 D H [ fh0g. If R M N 1
4 .log N / B.M / for a sufficiently large positive constant B.M /, and h R, then as R; N ! 1,
(2.15)
X
nN
ƒR.nI H1; `1/ƒR.nI H2; `2/ .n C h0/
D
8
ˆ ˆ ˆ ˆ ˆ ˆ ˆ ˆ <
ˆ ˆ ˆ ˆ ˆ ˆ ˆ ˆ :
`1 C `2 `1
.log R/rC`1C`2
.r C `1 C `2/Š .S.H0/ C oM .1//N if h0 62 H;
`1C`2C1 `1 C 1
.log R/rC`1C`2C1
.rC`1C`2C1/Š .S.H/CoM .1//N if h0 2 H1 n H2,
`1C`2C2 `1 C 1
.log R/rC`1C`2C1
.rC`1C`2C1/Š .S.H/CoM .1//N if h0 2 H1 \ H2.


 828 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
With the assumption that the primes have level of distribution # > 1=2, i.e. (1.3)
with (1.4) holds, the asymptotics in (2.15) hold with R N #
2 " and h R", for any fixed " > 0.
By relabeling the variables, we obtain the corresponding form if h0 2 H2,
h0 62 H1.
Propositions 1 and 2 can be strengthened in several ways. We will show that the error terms oM .1/ can be replaced by a series of lower order terms and a prime number theorem type of error term. Moreover, we can make the result uniform for M ! 1 as an explicit function of N and R. This will be proved in a later paper and used in the proof of (1.9).
3. Proofs of Theorems 1 and 2
In this section we employ Propositions 1 and 2 and a simple argument due to Granville and Soundararajan to prove Theorems 1 and 2.
For ` 0, Hk D fh1; h2; : : : ; hkg, 1 h1; h2; : : : ; hk h R, we deduce
from Proposition 1, for R N 1
2 .log N / B.M / and R; N ! 1, that
(3.1)
X
nN
ƒR.nI Hk; `/2 1
.k C 2`/Š
2`
` S.Hk/N.log R/kC2`:
For any hi 2 Hk, we have from Proposition 2, for R N #
2 ", and R; N ! 1, (3.2)
X
nN
ƒR.nI Hk; `/2 .n C hi / 1
.k C 2` C 1/Š
2` C 2
` C 1 S.Hk/N.log R/kC2`C1:
Taking R D N #
2 ", we obtain4
(3.3)
S WD
2N
X
nDN C1
k
X
i D1
.n C hi / log 3N ƒR.nI Hk; `/2
k
.k C 2` C 1/Š
2` C 2
` C 1 S.Hk/N.log R/kC2`C1
log 3N 1
.k C 2`/Š
2`
` S.Hk/N.log R/kC2`
2k
k C 2` C 1
2` C 1
` C 1 log R log 3N 1
.k C 2`/Š
2`
` S.Hk/N.log R/kC2`:
4In (3.3), as well as later in (3.8), the asymptotic sign replaces an error term of size o.log N / in the parenthesis term after log 3N . We thus make the convention that the asymptotic relationship holds only up to the size of the apparent main term.


 PRIMES IN TUPLES I 829
Here we note that if S > 0 then there exists an n 2 ŒN C 1; 2N ç such that at least two of the numbers n C h1; n C h2; : : : ; n C hk will be prime. This occurs when
(3.4) k
k C 2` C 1
2` C 1
` C 1 # > 1:
If k; ` ! 1 with ` D o.k/, then the left-hand side has the limit 2#, and thus (3.4) holds for any # > 1=2 if we choose k and ` appropriately depending on #. This proves the first part of Theorem 1. Next, assuming # > 20=21, we see that (3.4) holds with ` D 1 and k D 7. This proves the second part of Theorem 1 but with k D 7. The case k D 6 requires a slightly more complicated argument and is treated later in this section. The table below gives the values of C.#/, defined in Theorem 1, obtained from (3.4). For a certain #, it gives the smallest k and corresponding smallest ` for which (3.4) is true. Here h.k/ is the shortest length of any admissible k-tuple, which has been computed by Engelsma [6] by exhaustive search for 1 k 305 and covers every value in this table and the next except h.421/, where we have taken the upper bound value from [6].
# k ` h.k/
1 7 1 20 0.95 8 1 26 0.90 9 1 30 0.85 11 1 36 0.80 16 1 60 0.75 21 2 84 0.70 31 2 140 0.65 51 3 252 0.60 111 5 634 0.55 421 10 2956
* indicates that this value could be an upper bound of the true value.
To prove Theorem 2, we modify the previous proof by considering
(3.5) Sz WD
2N
X
nDN C1
X
1 h0 h
.nCh0/ log 3N
X
1 h1;h2;:::;hk h distinct
ƒR.nI Hk; `/2;
where is a positive integer. To evaluate Sz, we need the case of Proposition 2 where h0 62 Hk:
(3.6)
X
nN
ƒR.nI Hk; `/2 .nCh0/ 1
.kC2`/Š
2`
` S.Hk[fh0g/N.log R/kC2`:


 830 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
We also need a result of Gallagher [10]: as h ! 1,
(3.7)
X
1 h1;h2;:::hk h distinct
S.Hk/ hk:
Taking R D N #
2 ", and applying (3.1), (3.2), (3.6), and (3.7), we find that
Sz
X
1 h1;h2;:::;hk h distinct
k
.k C 2` C 1/Š
2` C 2
` C 1 S.Hk/N.log R/kC2`C1
C
X
1 h0 h h0¤hi ;1 i k
1
.k C 2`/Š
2`
` S.Hk [ fh0g/N.log R/kC2`
log 3N 1
.k C 2`/Š
2`
` S.Hk/N.log R/kC2`
!
2k
kC2`C1
2` C 1
` C 1 log RCh log 3N 1
.kC2`/Š
2`
` N hk.log R/kC2`:
(3.8)
Thus, there are at least C 1 primes in some interval .n; n C hç, N < n 2N , provided that
(3.9) h > 2k
k C 2` C 1
2` C 1
`C1
#
2 " log N;
which, on letting ` D Œpk=2ç and taking k sufficiently large, gives
(3.10) h > 2# C 4" C O 1
pk log N:
This proves (1.11). Theorem 2 is the special case D 1 and # D 1=2. We are now ready to prove the last part of Theorem 1. Consider
S0 W D
2N
X
nDN C1
k
X
i D1
.n C hi / log 3N
L
X
`D0
a`ƒR.nI Hk; `/
2
(3.11)
D
2N
X
nDN C1
k
X
i D1
.n C hi / log 3N
X
0 `1;`2 L
a`1 a`2 ƒR.nI Hk; `1/ƒR.nI Hk; `2/
D
X
0 `1;`2 L
a`1 a`2 M`1;`2 ;


 PRIMES IN TUPLES I 831
where
(3.12) M`1;`2 D Mz`1;`2 .log 3N /M`1;`2 ;
say. Applying Propositions 1 and 2 with R D N #
2 ", we deduce that
M`1;`2
`1 C `2 `1
.log R/kC`1C`2
.k C `1 C `2/Š S.Hk/N
and
Mz`1;`2 k `1 C `2 C 2
`1 C 1
.log R/kC`1C`2C1
.k C `1 C `2 C 1/Š S.Hk/N:
Therefore,
M`1;`2
`1 C `2 `1
S.Hk/N .log R/kC`1C`2
.k C `1 C `2/Š
k.`1 C `2 C 2/.`1 C `2 C 1/
.`1 C 1/.`2 C 1/.k C `1 C `2 C 1/ log R log 3N :
Defining b` D .log R/`a` and b to be the column matrix corresponding to the vector .b0; b1; : : : ; bL/, we obtain
S .N; Hk; #; b/ WD
1
S.Hk/N.log R/kC1 S 0
(3.13)
X
0 `1;`2 L
b`1 b`2
`1 C `2 `1
1
.k C `1 C `2/Š
k.`1 C `2 C 2/.`1 C `2 C 1/
.`1 C 1/.`2 C 1/.k C `1 C `2 C 1/
2
#
bT Mb;
where
(3.14) M D i Cj
i
1
.kCi Cj /Š
k.i Cj C2/.i Cj C1/
.i C1/.j C1/.kCi Cj C1/
2
# 0 i;j L
:
We need to choose b so that S > 0 for a given # and minimal k. On taking b to be an eigenvector of the matrix M with eigenvalue , we see that
(3.15) S bT b D
k
X
i D0
jbi j2
will be > 0 provided that is positive. Therefore S > 0 if M has a positive eigenvalue and b is chosen to be the corresponding eigenvector. Using Mathematica we computed the values of C.#/ indicated in the following table, which may be compared to the earlier table obtained from (3.4).


 832 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
# k L h.k/
1 6 1 16 0.95 7 1 20 0.90 8 2 26 0.85 10 2 32 0.80 12 2 42 0.75 16 2 60 0.70 22 4 90 0.65 35 4 158 0.60 65 6 336 0.55 193 9 1204
In particular, taking k D 6, L D 1, b0 D 1, and b1 D b in (3.13), we get
S1
8Š 96 112
# C 2b 18 16
# C b2 4 4
#
4.1 #/
8Š# b2 2b 18# 16
4.1 #/
96# 112
4.1 #/
4.1 #/
8Š# b 18# 16
4.1 #/
2
C
15#2 64# C 48
4.1 #/2 :
Choosing b D 18# 16
4.1 #/ , we then have
S 15#2 64# C 48
8Š#.1 #/ ;
of which the right-hand side is > 0 if # 1 lies between the two roots of the
quadratic; this occurs when 4.8 p19/=15 < # 1. Thus, there are at least two primes in any admissible tuple Hk for k D 6, if
(3.16) # > 4.8 p19/
15 D 0:97096 : : : :
This completes the proof of Theorem 1.
4. Further remarks on Section 3
We can formulate the method of Section 3 as follows. For a given tuple H D fh1; h2; : : : ; hkg we define
(4.1) Q1 WD
2N
X
nDN C1
fR.nI H/2; Q2 WD
2N
X
nDN C1
k
X
i D1
.n C hi / fR.nI H/2;


 PRIMES IN TUPLES I 833
where f should be chosen to make Q2 large compared with Q1, and R D R.N / will be chosen later. It is reasonable to assume
(4.2) fR.nI H/ D
X
d jPH.n/ dR
d ;R :
Our goal is to select the d;R which maximizes
(4.3) D .N I H; f / WD
1
log 3N
Q2
Q1
for the purpose of obtaining a good lower bound for . If > for some N and positive integer , then there exists an n, N < n 2N , such that the tuple (1.5) has at least C 1 prime components. This method has much in common with the method introduced for twin primes by Selberg and for general tuples by Heath-Brown. However, they used the divisor function d.n C hi / in Q2 in place of .n C hi / and sought to minimize (4.3) to obtain a good upper bound for . Heath-Brown even chose f D ƒR.nI H; 1/. As a first example, suppose we choose f as in (2.6) and (2.7), so that
(4.4) fR.nI H/ D
k
Y
i D1
ƒR.n C hi /:
By [13], we have, as R; N ! 1,5
Q1 N S.H/.log R/k if R N 1
(4.5) 2k .1 "/;
Q2 kN S.H/.log R/kC1 if R N #
2k .1 "/:
On taking R D N
#0
2k , 0 < #0 < #, we see that, as N ! 1,
(4.6) k log R
log N
#0
2:
Notice that < 1, so that we fail to detect primes in tuples. In Section 3, we proved that on choosing f D ƒR.nI H; `/, by (3.1) and (3.2), as N ! 1,
(4.7) k
k C 2` C 1
2` C 1
` C 1 #0:
If ` D 0 this gives k
kC1 #0, which, for large k, is twice as large as (4.6), while (4.7) gains another factor of 2 when ` ! 1 slowly as k ! 1. This finally shows > 1 if # > 1=2, but just fails if # D 1=2.
5For special reasons, the validity of the formula for Q2 actually holds here for R N
#
2.k 1/ .1 "/
if k 2, but this is insignificant for the present discussion.


 834 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
In (3.11) we chose
(4.8) fR.nI H/ D
L
X
`D0
b`
.log R/` ƒR.nI Hk; `/ D
X
d jPH.n/ dR
.d /P log.R=d /
log R
where P is a polynomial with a k-th order zero at 0. The matrix procedure does not provide a method for analyzing unless L is taken fixed, but the general problem has been solved by Soundararajan [31]. In particular, he showed that < 1 if # D 1=2, so that one can not prove there are bounded gaps between primes using (4.8). The exact solution from Soundrarajan’s analysis was obtained by a calculus-of-variations argument by Conrey, which gives, as N ! 1,
(4.9) D
k.k 1/
2ˇ #0;
where ˇ is determined as the solution of the equation
(4.10) 1
ˇD
R1
0 yk 2q.y/2 dy
R1
0 yk 1q0.y/2 dy
with q.y/ D Jk 2.2pˇ/ y1 k
2 Jk 2.2pˇy/;
where Jk is the Bessel function of the first type. Using Mathematica, one can check that this gives exactly the values of k in the previous table, which is in agreement with our earlier calculations; but it provides somewhat smaller values of # for which a given k-tuple will contain two primes. Thus, for example, we can replace (3.16) by the result that every admissible 6-tuple will contain at least two primes if
(4.11) # > :95971 : : : :
5. Two lemmas
In this section we will prove two lemmas needed for the proof of Propositions 1 and 2. The conditions on these lemmas have been constructed in order for them to hold uniformly in the given variables. The Riemann zeta-function has the Euler product representation, with s D Cit,
(5.1) .s/ D
Y
p
11
ps
1
; > 1:
The zeta-function is analytic except for a simple pole at s D 1, where as s ! 1
(5.2) .s/ D
1
s 1 C C O.js 1j/:
(Here is Euler’s constant.) We need standard information concerning the classical zero-free region of the Riemann zeta-function. By Theorem 3.11 and (3.11.8) in


 PRIMES IN TUPLES I 835
[32], there exists a small constant c > 0, for which we assume c 10 2, such that . C i t / ¤ 0 in the region
(5.3) 1 4c
log.jtj C 3/
for all t . Furthermore, we have
. Cit/ 1
1 C i t log.jt j C 3/; 1
(5.4) . C i t / log.jtj C 3/;
0
. Cit/C
1
1 C i t log.jtj C 3/;
in this region. We will fix this c for the rest of the paper (we could take, for instance, c D 10 2, see [8]). Let L denote the contour given by
(5.5) s D
c
log.jt j C 3/ C i t:
LEMMA 1. For R C , k 2, B C k,
(5.6)
Z
L
.log.jsj C 3//B
ˇ ˇ ˇ ˇ
Rs
sk ds
ˇ ˇ ˇ ˇ
Ck
1 R c2 C e
pc log R=2;
where C1; c2 and the implied constant in depends only on the constant C in the formulation of the lemma. In addition, if k c3 log R with a sufficiently small c3 depending only on C , then
(5.7)
Z
L
.log.jsj C 3//B
ˇ ˇ ˇ ˇ
Rs
sk ds
ˇ ˇ ˇ ˇ
e
pc log R=2:
Proof. The left-hand side of (5.6) is, with C4 depending on C ,
(5.8)
Z1
0
R .t/ .log.jt j C 4//B
.jt j C c=2/k dt
Z C4
0
Ck
1 R c2 dt C
Z! 3
C4
R
c
log.jt jC3/
t 3=2 dt C
Z1
!3
t 3=2dt
Ck
1 R c2 C e
c log R
log ! C ! 1
2;
where now C1 is a constant depending on C . On choosing log ! D
pc log R, the first part of the lemma follows. The second part is an immediate consequence of the first part.
The next lemma provides some explicit estimates for sums of the generalized divisor function. Let !.q/ denote the number of prime factors of a squarefree integer q. For any real number m, we define


 836 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
(5.9) dm.q/ D m!.q/:
This agrees with the usual definition of the divisor functions when m is a positive integer. Clearly, dm.q/ is a monotonically increasing function of m (for a fixed q), and for real m1, m2, and y, we see that
(5.10) dm1 .q/dm2 .q/ D dm1m2 .q/; .dm.q//y D dmy .q/:
Recall that P[ indicates a sum over squarefree integers. We use the ceiling function dye WD minfn 2 ZI y ng.
LEMMA 2. For any positive real m and x 1 we have
D0.x; m/W D
X[
qx
dm.q/
(5.11) q .dme C log x/dme .m C 1 C log x/mC1;
D .x; m/W D
X[
qx
(5.12) dm.q/ x.dme C log x/dme x.m C 1 C log x/mC1:
Proof. First, we treat the case when m is a positive integer. We prove (5.11) by induction. Observe that the assertion is true for m D 1, that is, when d1.q/ D 1 by definition. Suppose (5.11) is proved for m 1. Let us denote the smallest term in a given product representation of q by j D j.q/ x1=m. Then this factor can stand at m places, and, therefore, with q D q0j.q/ D q0j ,
X[
qx
dm.q/
qm
x1=m
X
j D1
[1
j
X[
q0 x=j
dm 1.q0/
q0 m.1 C log x 1
m / .m 1 C log x/m 1
.m C log x/.m C log x/m 1 D .m C log x/m:
This completes the induction. For real m, the result holds since D0.x; m/ D0.x;dme/. We note that (5.12) follows from (5.11) because D .x; m/ xD0.x;m/.
6. A special case of Proposition 1
In this section we prove a special case of Proposition 1 which illustrates the method without involving the technical complications that appear in the general case. This allows us to set up some notation and obtain estimates for use in the general case. We also obtain the result uniformly in k. Assume H is nonempty (so that k 1), ` D 0, and ƒR.nI H; 0/ D ƒR.nI H/.
PROPOSITION 3. Suppose
(6.1) k 0 .log R/ 1
2 0 with an arbitrarily small fixed 0 > 0;


 PRIMES IN TUPLES I 837
and h RC , with C any fixed positive number; then
(6.2)
N
X
nD1
ƒR.nI H/ D S.H/N C O.Ne cplog R/ C O R.2 log R/2k :
This result motivates the conjecture (2.11).
Proof. We have
(6.3) SR.N I H/ WD
N
X
nD1
ƒR.nI H/ D
1
kŠ
X
dR
.d / log R
d
k
X
1nN d jPH.n/
1:
If for a prime p we have pjPH.n/, then among the solutions n hi .mod p/, 1 i k, there will be p.H/ distinct solutions modulo p. For d squarefree we then have by multiplicativity d .H/ distinct solutions for n modulo d which satisfy d jPH.n/, and for each solution, n runs through a residue class modulo d . Hence we see that
(6.4)
X
1nN d jPH.n/
1 D d .H/ N
d C O.1/ :
Trivially, q.H/ k!.q/ D dk.q/ for squarefree q. Therefore, we conclude that
SR.N I H/ D N
0
@
1
kŠ
X
dR
.d / d .H/
d log R
d
k
1
ACO
0
@
.log R/k
kŠ
X[
dR
d .H/
1
A
D N TR.H/ C O R.k C log R/2k ;
(6.5)
by Lemma 2. Let .a/ denote the contour s D a C i t, 1 < t < 1. We apply the formula
(6.6) 1
2i
Z
.c/
xs
skC1 ds D
0 if 0 < x 1,
1
kŠ .log x/k if x 1,
for c > 0, and have that
(6.7) TR.H/ D
1
2i
Z
.1/
F .s/ Rs
skC1 ds;
where, letting s D C i t and assuming > 0,
(6.8) F .s/ D
1
X
d D1
.d / d .H/
d 1Cs D
Y
p
1 p.H/
p1Cs :


 838 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
Since p.H/ D k for all p > h,
(6.9) F .s/ D
GH.s/
.1 C s/k ;
where by (5.1)
(6.10) GH.s/ D
Y
p
1 p.H/
p1Cs 1 1
p1Cs
k
D
Y
p
1C
k p.H/
p1Cs C Oh
k2
p2C2 ;
which is analytic and uniformly bounded for > 1=2 C ı for any ı > 0. Also, by (2.2) we see that
(6.11) GH.0/ D S.H/:
From (5.4) and (6.9), the function F .s/ satisfies the bound
(6.12) F .s/ jGH.s/j.C log.jt j C 3//k
in the region on and to the right of L. Here GH.s/ is analytic and bounded in this region, and has a dependence on both k and the size h of the components of H. We note that p.H/ D k not only when p > h, but whenever p 6 j Å, where
(6.13) Å WD
Y
1 i<j k
jhj hi j;
since then all k of the hi ’s are distinct modulo p. We now introduce an important parameter U that is used throughout the rest of the paper. We want U to be an
upper bound for log Å, and since trivially Å hk2 we choose
(6.14) U WD C k2 log.2h/
and have
(6.15) log Å U:
We now prove, for 1=4 < 1,
(6.16) jGH.s/j exp.5kU ı log log U /; where ı D max. ; 0/:
We treat separately the different pieces of the product defining GH. First, by use of the inequality log.1 C x/ x for x 0, we have


 PRIMES IN TUPLES I 839
ˇ ˇ ˇ ˇ ˇ
Y
pU
1 p.H/
p1Cs
ˇ ˇ ˇ ˇ ˇ
Y
pU
1C
k
p1 ı
D exp
X
pU
log 1 C
k
p1 ı exp
X
pU
k
p1 ı
exp kU ı X
pU
1
p exp kU ı log log U :
Second, by the same estimates and the inequality .1 x/ 1 1C3x for 0 x 2=3, we see that
ˇ ˇ ˇ ˇ ˇ
Y
pU
11
p1Cs
k
ˇ ˇ ˇ ˇ ˇ
Y
pU
11
p1 ı
1k
Y
pU
1C
3
p1 ı
k
since 1
p1 ı
1
23=4 < 2
3;
exp 3kU ı log log U :
Hence, the terms in the product for GH.s/ with p U are
exp 4kU ı log log U :
For the terms p > U , we first consider those for which pjÅ. In absolute value, they are
Y
pjÅ p>U
1C
k
p1 ı 1 C
3
p1 ı
k
exp
X
pjÅ p>U
4k
p1 ı :
Since there are fewer than .1 C o.1// log Å < U primes with pjÅ, the sum above is increased if we replace these terms with the integers between U and 2U . Therefore the right-hand side above is
exp 4k
X
U <n 2U
1
n1 ı exp 4k.2U /ı X
U <n 2U
1
n exp.4kU ı /:
Finally, if p > U
ˇ ˇ ˇ ˇ
k
p1Cs
ˇ ˇ ˇ ˇ
k
U1 ı
1
2;


 840 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
so that in absolute value the terms with p > U and p 6 j Å are
D
ˇ ˇ ˇ ˇ ˇ
Y
p6 jÅ p>U
1k
p1Cs 1 1
p1Cs
k
ˇ ˇ ˇ ˇ ˇ
D
ˇ ˇ ˇ ˇ ˇ
exp
X
p6 jÅ p>U
1
X
D1
1k
p1Cs C k
1
X
D1
11
p1Cs
!ˇ ˇ ˇ ˇ ˇ
exp
X
p>U
1
X
D2
2k
p1 ı exp
X
p>U
1
X
D2
k
p1 ı
exp 2k2 X
n>U
1
n2 2ı exp 4k2U ı
U 1 ı exp 2kU ı :
Thus, the terms with p > U contribute exp 6kU ı , from which we obtain (6.16).
In conclusion, for h RC (where C > 0 is fixed and as large as we wish) and for s on or to the right of L, we have
(6.17) F .s/ .C log.jt j C 3//k exp.5kU ı log log U /:
Returning to the integral in (6.7), we see that the integrand vanishes as jt j ! 1, 1=4 < 1. By (6.9) we see that in moving the contour from .1/ to the left to L we either pass through a simple pole at s D 0 when H is admissible (so that S.H/ ¤ 0), or we pass through a regular point at s D 0 when H is not admissible. In either case, we have by virtue of (5.2), (6.11), (6.14), (6.17), and Lemma 1, for any k satisfying (6.1),
(6.18) TR.H/ D GH.0/ C
1
2i
Z
L
F .s/ Rs
skC1 ds D S.H/ C O.e cplog R/:
Equation (6.2) now follows from this and (6.5).
Remark. The exponent 1=2 in the restriction k .log R/1=2 0 is not significant. Using Vinogradov’s zero-free region for .s/ we could replace 1=2 by 3=5.
7. First part of the proof of Proposition 1
Let
(7.1) H D H1 [ H2; jH1j D k1; jH2j D k2; k D k1 C k2;
r D jH1 \ H2j; M D k1 C k2 C `1 C `2:
Thus jHj D k r. We prove Proposition 1 in the following sharper form.


 PRIMES IN TUPLES I 841
PROPOSITION 4. Let h RC , where C is any positive fixed constant. As R; N ! 1, we have
X
nN
ƒR.nI H1; `1/ƒR.nI H2; `2/ D `1 C `2
`1
.log R/rC`1C`2
(7.2) .r C `1 C `2/Š S.H/N
CN
r C`1 C`2
X
j D1
Dj .`1; `2; H1; H2/.log R/rC`1C`2 j
C OM .N e cplog R/ C O.R2.3 log R/3kCM /;
where the Dj .`1; `2; H1; H2/’s are functions independent of R and N which satisfy the bound
(7.3) Dj .`1; `2; H1; H2/ M .log U /Cj M .log log 10h/C 0
j
where U is as defined in (6.14) and Cj and Cj0 are two positive constants depending on M .
Proof. We can assume that both H1 and H2 are nonempty since the case where one of these sets is empty can be covered in the same way we did in the case of ` D 0 in Section 6. Thus k 2 and we have
(7.4)
SR.N I H1; H2; `1; `2/ WD
N
X
nD1
ƒR.nI H1; `1/ƒR.nI H2; `2/
D
1
.k1C`1/Š.k2C`2/Š
X
d;e R
.d / .e/ log R
d
k1C`1
log R
e
k2C`2 X
1nN d jPH1 .n/ ejPH2 .n/
1:
For the inner sum, we let d D a1a12, e D a2a12 where .d; e/ D a12. Thus a1, a2, and a12 are pairwise relatively prime, and the divisibility conditions d jPH1.n/ and ejPH2.n/ become a1jPH1.n/, a2jPH2.n/, a12jPH1.n/, and a12jPH2.n/. As in Section 6, we get a1.H1/ solutions for n modulo a1, and a2.H2/ solutions for n modulo a2. If pja12, then from the two divisibility conditions we have p.H1.p/ \ H2.p// solutions for n modulo p, where
H.p/ D fh01; : : : ; h0
p.H/ W h0j hi 2 H for some i; 1 h0j pg:
Notice that H.p/ D H if p > h . Alternatively, we can avoid this definition which is necessary only for small primes by defining
(7.5) p.H1\ H2/ WD p.H1.p/ \ H2.p// WD p.H1/ C p.H2/ p.H/


 842 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
and then extending this definition to squarefree numbers by multiplicativity.6 Thus we see that
X
1nN d jPH1 .n/ ejPH2 .n/
1 D a1 .H1/ a2 .H2/ a12 .H1\ H2/ N
a1a2a12
C O.1/ ;
and have
(7.6)
SR.N I `1; `2; H1; H2/ D
N
.k1 C `1/Š.k2 C `2/Š
X
a1a12 R a2a12 R
.a1/ .a2/ .a12/2 a1 .H1/ a2 .H2/ a12 .H1\ H2/
a1a2a12
log R
a1a12
k1C`1
log R
a2a12
k2C`2
CO .log R/M X
a1a12 R a2a12 R
.a1/2 .a2/2 .a12/2 a1 .H1/ a2 .H2/ a12 .H1\ H2/
!
D N TR.`1; `2I H1; H2/ C O.R2.3 log R/3kCM /;
where P0 indicates the summands are pairwise relatively prime. Notice that by Lemma 2, the error term was bounded by
.log R/M X[
q R2
X
q Da1 a2 a12
dk.q/ D .log R/M X[
q R2
d3 .q /dk .q /
D .log R/M X[
q R2
d3k.q/ R2.3 log R/3kCM :
By (6.6), we have (7.7)
TR.`1; `2I H1; H2/ D
1
.2 i /2
Z
.1/
Z
.1/
F .s1; s2/ Rs1
s1k1C`1C1
Rs2
s2k2C`2C1 ds1 ds2;
where, by letting sj D j C i tj and assuming 1; 2 > 0,
6We are establishing a convention here that for p we take intersections modulo p.


 PRIMES IN TUPLES I 843
F .s1; s2/ D
X
1 a1;a2;a12<1
.a1/ .a2/ .a12/2 a1 .H1/ a2 .H2/ a12 .H1\ H2/
a11Cs1 a21Cs2 a121Cs1Cs2
D
Y
p
1 p.H1/
p1Cs1
p .H2 /
p1Cs2 C
p.H1\ H2/
p1Cs1Cs2 :
(7.8)
Since for all p > h we have p.H1/ D k1, p.H2/ D k2, and p.H1 \ H2/ D r, we factor out the dominant zeta-factors and write
(7.9) F .s1; s2/ D GH1;H2 .s1; s2/ .1 C s1 C s2/r
.1 C s1/k1 .1 C s2/k2 ;
where by (5.1) (7.10)
GH1;H2 .s1; s2/ D
Y
p
0
B @
1 p.H1/
p1Cs1
p .H2/
p1Cs2 C p .H1\H2/
p1Cs1Cs2 1 1
p 1Cs1 Cs2
r
11
p1Cs1
k1
11
p1Cs2
k2
1
C A
is analytic and uniformly bounded for 1; 2 > 1=4 C ı, for any fixed ı > 0. Also, from (2.2), (7.1), and (7.5) we see immediately that
(7.11) GH1;H2.0; 0/ D S.H/:
Furthermore, the same argument leading to (6.16) shows that for s1, s2 on L or to the right of L
(7.12) GH1;H2 .s1; s2/ exp.C kU ı1Cı2 log log U /;
with ıi D min. i ; 0/ and U as defined in (6.14). We define
(7.13) W .s/ WD s .1 C s/
and
(7.14) D.s1; s2/ D GH1;H2 .s1; s2/ W .s1 C s2/r
W .s1/k1 W .s2/k2 ;
so that (7.15)
TR.`1; `2I H1; H2/ D
1
.2 i /2
Z
.1/
Z
.1/
D.s1; s2/ Rs1Cs2
s1`1C1s2`2C1.s1 C s2/r ds1ds2:
To complete the proof of Proposition 1, we need to evaluate this integral. We will also need to evaluate a similar integral in the proof of Proposition 2, where the parameters k1, k2, and r have several slightly different relationships with H1 and H2, and G is slightly altered. Therefore we change notation to handle these situations simultaneously.


 844 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
8. Completion of the proof of Proposition 1: Evaluating an integral
Let
(8.1) TR.a; b; d; u; v; h/ WD
1
.2 i /2
Z
.1/
Z
.1/
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds1 ds2;
where
(8.2) D.s1; s2/ D
G.s1; s2/W d .s1 C s2/
W a.s1/W b.s2/
and W is from (7.13). We assume G.s1; s2/ is regular on L and to the right of L and satisfies the bound, with ıi D min. i ; 0/,
(8.3) G.s1; s2/ M exp.CM U ı1Cı2 log log U /; where U D CM 2 log.2h/:
LEMMA 3. Suppose that
(8.4) 0 a; b; d; u; v M; a C u 1; b C v 1; d min.a; b/;
where M is a large constant and our estimates may depend on M . Let h RC , with C any positive fixed constant. Then we have, as R ! 1,
(8.5) TR.a; b; d; u; v; h/ D u C v
u
.log R/uCvCd
.u C v C d /Š G.0; 0/
C
uCvCd
X
j D1
Dj .a; b; d; u; v; h/.log R/uCvCd j COM .e cplog R/;
where the Dj .a; b; d; u; v; h/’s are functions independent of R which satisfy the bound
(8.6) Dj .a; b; d; u; v; h/ M .log U /Cj M .log log 10h/C 0
j
for some positive constants Cj , Cj0 depending on M .
Proof. One would expect to proceed exactly as in Section 6 by moving both contours to the left to L. There is, however, a complication because the integrand now contains the function .1 C s1 C s2/ which necessitates also that s1 C s2 be restricted to the region to the right of L if we wish to use the bounds in (5.4).7 By
7This was pointed out to us by J. Sivak and also Y. Motohashi and was handled in similar ways in [30] and in [15]; we have also adopted this approach here.


 PRIMES IN TUPLES I 845
the conditions of Lemma 3, (5.4), and (8.3), we have
(8.7) D.s1; s2/
suC1
1 svC1
2 .s1 Cs2/d
M
exp.CM U ı1Cı2 log log U / log.jt1jC3/ log.jt2jC3/ 2M max.1; js1 Cs2j d /
js1jaCuC1js2jbCvC1
provided s1, s2, and s1 C s2 are on or to the right of L. We next let
(8.8) V D e
plog R
and define the contours, for j D 1 or 2,
Lj0 D
4 jc
log V D
n4 jc
log V C i t W 1 < t < 1
o
(8.9) ;
Lj D
n4 jc
log V C i t W jt j 4 j V
o
;
Lj D
n 4 jc
log V C i t W jt j 4 j V
o
;
Hj D
n
j  ̇i4 jV W j jj
4 jc
log V
o
:
By (8.7) the integrand in (8.1) vanishes as jt1j ! 1 or jt2j ! 1 provided s1 and s2 are to the right of L02. We first shift the contours .1/ for the integrals over s1 and s2 to L01 and L02, respectively. Next, we truncate these contours so that they may be replaced with L1 and L2. In doing this there are two error terms which are estimated by (8.7). For example the error term coming from L01 and the truncated piece of L02 is
M .log U /CM .log V /M V 5c
16
Z1
1
.log jt j C 3/2M
jc
4 log V C i t jaCuC1 dt
!
Z1
V =16
.log t /2M
t2 dt
!
M
.log V /6M
V 1 5c
16
M e cplog R:
Hence
(8.10) TR D
1
.2 i /2
Z
L2
Z
L1
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds1 ds2 C OM .e cplog R/:
To replace the s1-contour along L1 with the contour along L1 we consider the rectangle formed by L1, H1, and L1 which contains poles of the integrand as a function of s1 at s1 D 0 and s1 D s2. Hence we see that


 846 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
(8.11) TR D
1
2i
Z
L2
Res
s1D0
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds2
C
1
2i
Z
L2
Res
s1D s2
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds2
C
1
.2 i /2
Z
L2
Z
L1 [H1
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds1 ds2 C OM .e cplog R/:
Here the contours along L1 and H1 are oriented clockwise. In the first and third integrals we move the contour over L2 to L2 in the same fashion, but now we only pass a pole at s2 D 0. Thus we obtain
(8.12)
TR D Res
s2D0 Res
s1D0
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d
C
1
2i
Z
L2 [H2
Res
s1D0
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds2
C
1
2i
Z
L1 [H1
Res
s2D0
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds1
C
1
2i
Z
L2
Res
s1D s2
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds2
C
1
.2 i /2
Z
L2 [H2
Z
L1 [H1
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds1 ds2 C OM .e cplog N /
WD I0 C I1 C I2 C I3 C I4 C OM .e cplog R/:
We will see that the residue I0 provides the main term and some of the lower order terms, the integral I3 provides the remaining lower order terms, and the integrals I1, I2, and I4 are error terms. We consider first I0. At s1 D 0 there is a pole of order u C 1, and therefore8 by Leibniz’s rule we have
Res
s1D0
D.s1; s2/Rs1
suC1
1 .s1 C s2/d D
1
uŠ
u
X
i D0
u
i .log R/u i @i
@si
1
D.s1; s2/
.s1 C s2/d
ˇ ˇ ˇ ˇ
ˇs1D0
8If G.0; 0/ D 0 then the order of the pole is u or less, but the formula we use to compute the residue is still valid. In this situation one or more of the initial terms will have the value zero.


 PRIMES IN TUPLES I 847
and
@i
@si
1
D.s1; s2/
.s1 C s2/d
ˇ ˇ ˇ ˇ
ˇs1D0
D . 1/i D.0; s2/d.d C 1/ .d C i 1/
sd Ci
2
C
i
X
j D1
i j
@j
@sj
1
D.s1; s2/
ˇ ˇ ˇ ˇ
ˇs1D0
. 1/i j d.d C 1/ .d C i j 1/
sd Ci j
2
;
where in case of i D j (including the case when i D j D 0 and d 0 arbitrary) the empty product in the numerator is 1. We conclude that
(8.13) Res
s1D0
D.s1; s2/Rs1
suC1
1 .s1 C s2/d D
u
X
i D0
i
X
j D0
a.i; j /.log R/u i
sd Ci j
2
@j
@sj
1
D.s1; s2/
ˇ ˇ ˇ ˇ
ˇs1D0
with a.i; j / as given explicitly in the previous equations. To complete the evaluation of I0, we see that the .i; j /th term contributes to I0 a pole at s2 D 0 of order v C 1 C d C i j (or less), and therefore by Leibniz’s formula
Res
s2 D0
Rs2
svC1Cd Ci j
2
@j
@sj
1
D.s1; s2/
ˇ ˇ ˇ ˇ
ˇs1D0
D
1
.vCd Ci j /Š
vCd Ci j
X
mD0
vCd Ci j
m .log R/vCdCi j m @m
@sm
2
@j
@sj
1
D.s1; s2/
ˇ ˇ ˇ ˇ
ˇs1D0
s2 D0
:
This completes the evaluation of I0, and we conclude (8.14)
I0 D
u
X
i D0
i
X
j D0
vCd Ci j
X
mD0
b.i; j; m/ @m
@sm
2
@j
@sj
1
D.s1; s2/
ˇ ˇ ˇ ˇ
ˇs1D0
s2D0
.log R/uCvCd j m;
where (8.15)
b.i; j; m/ D . 1/i j u
i
i j
vCd Ci j m
d.d C 1/ .d C i j 1/
uŠ.v C d C i j /Š :
The main term is of order .log R/uCvCd and occurs when j D m D 0. Therefore, it is given by
G.0; 0/.log R/uCvCd 1
uŠ
u
X
i D0
u
i . 1/i d.d C 1/ .d C i 1/
.v C d C i /Š
!
:
It is not hard to prove that
(8.16) 1
uŠ
u
X
i D0
u
i . 1/i d.d C 1/ .d C i 1/
.v C d C i /Š D u C v
u
1
.u C v C d /Š ;


 848 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
from which we conclude that the main term is
(8.17) G.0; 0/ u C v
u
1
.u C v C d /Š .log R/dCuCv:
Motohashi found the following approach which avoids proving (8.16) directly and which can be used to simplify some of the previous analysis. Granville also made a similar observation. The residue we are computing is equal to
1
.2 i /2
Z
Ä2
Z
Ä1
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d ds1 ds2;
where Ä1 and Ä2 are the circles js1j D and js2j D 2 , respectively, with a small > 0. When s1 D s and s2 D sw, this is equal to
1
.2 i /2
Z
Ä3
Z
Ä1
D.s; sw/Rs.wC1/
suCvCd C1wvC1.w C 1/d ds dw;
with Ä3 the circle jwj D 2. The main term is obtained from the constant term G.0; 0/ in the Taylor expansion of D.s; sw/ and, therefore, equals
G.0; 0/ .log R/uCvCd
.u C v C d /Š
1
2i
Z
Ä3
.w C 1/uCv
wvC1 dw D G.0; 0/ .log R/uCvCd
.u C v C d /Š
uCv
v;
by the binomial expansion. To complete the analysis of I0, we only need to show that the partial derivatives of D.s1; s2/ at .0; 0/ satisfy the bounds given in the lemma. For this, we use Cauchy’s estimate for derivatives
(8.18) jf .j /.z0/j max
jz z0jD
jf .z/j
jŠ
j;
if f .z/ is analytic for jz z0j . In the application below we will choose z0 on L or to the right of L and
(8.19) D
1
C log U log T ; where T D js1j C js2j C 3:
Thus we see the whole circle jz z0 1j D will remain in the region (5.3) and the estimates (5.4) hold in this circle. (We remind the reader that the generic constants c; C take different values at different appearances.) Thus, we have for s1; s2 on L


 PRIMES IN TUPLES I 849
or to the right of L, and j M , m 2M ,
@m
@sm
2
@j
@sj
1
(8.20) D.s1; s2/
j ŠmŠ.C log U log T /j Cm max
js1 s1j ;js2 s2j
jD.s1 ; s2 /j
M exp.CM U ı1Cı2 log log U /.log T /6M max.1; js1 C s2j/d
max.1; js1j/a max.1; js2j/b ;
which, if max.js1j; js2j/ C , reduces to
(8.21) @m
@sm
2
@j
@sj
1
D.s1; s2/ M exp CM U ı1Cı2 log log U :
In particular, we have
(8.22) @m
@sm
2
@j
@sj
1
D.s1; s2/
ˇ ˇ ˇ ˇ
ˇs1D0
s2D0
M .log U /CM :
We conclude from (8.14), (8.17), and (8.22) that I0 provides the main term and some of the secondary terms in Lemma 3 which satisfy the stated bound. We now consider I1. By (8.13) and (8.20), (8.23)
I1 M .log R/u
Z
L2 [H2
eCM U ı2 log log U .log.jt2j C 3//3M max.1; js2jd /
js2jvC1Cd max.1; js2jb/ jRs2 jjds2j:
By (8.4) we have b C v 1, along H2, jRs2j ecplog R, and along both L2 and H2 we have U ı2 1. When js2j 1,
max.1; js2jd /
js2jvC1Cd max.1; js2jb/
1
js2jvC1Cb
1
js2j2 ;
and therefore the contribution from H2 to I1 is
M
.log R/7M=2 1=2
V 2 ecplog R M e cplog R:
Similarly the integral along L2 is bounded by
M .log R/2M R
c 16 log V
ZV
V
.log.jt j C 3//3M min 1
.log V / 3M ; 1
t2 dt
M .log R/3M R
c 16 log V
M e cplog R;


 850 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
and therefore I1 also satisfies this bound. The same bound holds for I2 since it is with relabeling equal to I1. Further, I4 also satisfies this bound by the same argument on applying (8.7) and noting that js1 C s2j c
log V in I4.
Finally, we examine I3, which only occurs if d 1:
Res
s1D s2
D.s1; s2/Rs1Cs2
suC1
1 svC1
2 .s1 C s2/d D lim
s1! s2
1
.d 1/Š
@d 1
@s1d 1
D.s1; s2/Rs1Cs2
s1uC1s2vC1
D
1
.d 1/Š
d1
X
i D0
Bi .s2/.log R/d 1 i ;
(8.24)
where
(8.25) Bi .s2/
Dd 1
i
i
X
j D0
i j
@i j
@si j
1
D.s1; s2/
ˇ ˇ ˇ ˇ
ˇs1D s2
. 1/j .u C 1/ .u C j /
. 1/uCj C1suCvCj C2
2
:
Therefore by (8.12), (8.24), and (8.25),
(8.26) I3 D
1
.d 1/Š
d1
X
i D0
Ci .log R/d 1 i ;
where
(8.27) Ci D
1
2i
Z
L2
Bi .s2/ ds2; 0 i d 1:
By (8.20) and (8.25) we see that for s2 to the right of L
(8.28) Bi .s2/ M exp CM U jı2j log log U log.jt2j C 3/ 4M
jt2juCvCaCbC2 max.1; jt2ji / :
In (8.27) we may shift the contour L2 to the imaginary axis with a semicircle of radius 1= log U centered at and to the right of s2 D 0. Further, we can extend this
contour to the complete imaginary axis with an error OM .e cplog R/ using (8.28) and the same argument used above (8.10). Letting
(8.29) L0 D
n
s D it W jtj
1
log U
o
[
n
sD
ei#
log U W 2 # 2
o
oriented from i 1 up to i 1, we conclude
(8.30) Ci D
1
2i
Z
L0
Bi .s2/ ds2 C OM .e cplog R/; 0 i d 1:


 PRIMES IN TUPLES I 851
The integral here is independent of R but depends on h. Therefore this provides in (8.26) some further lower order terms in Lemma 3. The contribution to Ci from the integral along the imaginary axis is
(8.31) M .log U /uCvCiCaCbC1 exp.CM log log U / M .log U /C 0M :
This expression also bounds the contribution to Ci from the semicircle contour, completing the evaluation of I3. Combining our results, we obtain Lemma 3.
9. Proof of Proposition 2
We introduce some standard notation associated with (1.2) and (1.3). Let
(9.1) .xI q; a/ WD
X
px p a.mod q/
log p D Œ.a; q/ D 1ç x
.q/ C E.xI q; a/;
where ŒS ç is 1 if the statement S is true and is 0 if S is false. Next, we define
(9.2) E0.x; q/ WD max
a; .a;q/D1 jE.xI q; a/j; E .x; q/ D max
y x E0.y; q/:
In this paper we only need level of distribution results for E0, but usually these results are stated in the stronger form for E . Thus, for some 1=2 # 1, we assume, given any A > 0 and " > 0, that
(9.3)
X
q x# "
E .x; q/ A;"
x
.log x/A :
This is known to hold with # D 1=2. We prove the following stronger version of Proposition 2. Let
CR.`1; `2; H1; H2; h0/ D
8
ˆ ˆ ˆ ˆ ˆ <
ˆ ˆ ˆ ˆ ˆ :
1 if h0 62 H,
.`1 C`2 C1/ log R
.`1 C1/.r C`1 C`2 C1/ if h0 2 H1 n H2,
.`1 C`2 C2/.`1 C`2 C1/ log R
.`1 C1/.`2 C1/.r C`1 C`2 C1/ if h0 2 H1 \ H2.
By relabeling the variables we obtain the corresponding form if h0 2 H2 n H1. We continue to use the notation (7.1).
PROPOSITION 5. Suppose h R. Given any positive A, there exists B D B.A; M / such that for
(9.4) R M;A N 1
4 =.log N /B and R; N ! 1
we have


 852 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
(9.5)
N
X
nD1
ƒR.nI H1; `1/ƒR.nI H2; `2/ .n C h0/
D
CR.`1; `2; H1; H2; h0/
.r C `1 C `2/Š
`1 C `2 `1
S.H0/N.log R/rC`1C`2
CN
r
X
j D1
Dj .`1; `2; H1; H2; h0/.log R/rC`1C`2 j C OM;A
N
.log N /A ;
where the Dj .`1; `2; H1; H2; h0/’s are functions independent of R and N which satisfy the bound
(9.6) Dj .H1; H2; h0/ M .log U /Cj M .log log 10h/C 0
j
for some positive constants Cj , Cj0 depending on M . If conjecture (9.3) holds, then
(9.5) holds for R M N #
2 " and h R", for any given " > 0.
Proof. We assume that both H1 and H2 are nonempty so that k1 1 and k2 1. The proof in the case when one of these sets is empty is much easier and may be obtained by an argument analogous to that of Section 6. We have
(9.7) SzR.N I H1; H2; `1; `2; h0/ WD
N
X
nD1
ƒR.nI H1; `1/ƒR.nI H2; `2/ .n C h0/
D
1
.k1 C `1/Š.k2 C `2/Š
X
d;e R
.d / .e/ log R
d
k1C`1
log R
e
k2C`2
X
1nN d jPH1 .n/ ejPH2 .n/
.n C h0/:
To treat the inner sum above, let d D a1a12 and e D a2a12, where .d; e/ D a12, so that a1, a2, and a12 are pairwise relatively prime. As in Section 7, the n for which d jPH1.n/ and ejPH2.n/ cover certain residue classes modulo Œd; eç. If n b .mod a1a2a12/ is such a residue class, then letting
m D n C h0 b C h0.mod a1a2a12/;
we see that this residue class contributes to the inner sum
(9.8)
X
1Ch0 m N Ch0 m bCh0 .mod a1a2a12/
.m/
D .N Ch0I a1a2a12; bCh0/ .h0I a1a2a12; bCh0/
D Œ.b C h0; a1a2a12/ D 1ç N
.a1a2a12/ C E.N I a1a2a12; bCh0/ C O.h log N /:


 PRIMES IN TUPLES I 853
We must determine the number of these residue classes where .b C h0; a1a2a12/ D 1 so that the main term is non-zero. If pja1, then b hj .mod p/ for some hj 2 H1, and therefore b C h0 h0 hj .mod p/. Thus, if h0 is distinct modulo p from all the hj 2 H1, then all p.H1/ residue classes satisfy the relatively prime condition, while otherwise h0 hj .mod p/ for some hj 2 H1 leaving p.H1/ 1 residue classes with a non-zero main term. We introduce the notation p .H10/ for this number in either case, where we define for a set H and integer h0
(9.9) p .H0/ D p.H0/ 1;
where
(9.10) H0 D H [ fh0g:
We extend this definition to d .H0/ for squarefree numbers d by multiplicativity. The function d is familiar in sieve theory; see [16]. A more algebraic discussion
of d may also be found in [14], [15]. We define d .H1\H2/0 as in (7.5). Next, the divisibility conditions a2jPH2.n/, a12jPH1.n/, and a12jPH2.n/ are handled as in Section 7 together with the above considerations. Since E.nI q; a/ .log N / if .a; q/ > 1 and q N , we conclude that
(9.11)
X
1nN d jPH1 .n/ ejPH2 .n/
.n C h0/ D a1 .H10/ a2 .H20/ a12 .H1\H2/0 N
.a1a2a12/
C O dk.a1a2a12/ max
b
.b;a1a2a12/D1
ˇ
ˇE.N I a1a2a12; b/ˇ
ˇ C h.log N / :
Substituting this into (9.7) we obtain for SzR.N I H1; H2; `1; `2; h0/ the value
N
.k1 C `1/Š.k2 C `2/Š
X
a1a12 R a2a12 R
.a1/ .a2/ .a12/2 a1 .H10/ a2 .H20/ a12 .H1\H2/0
.a1a2a12/
log R
a1a12
k1C`1
log R
a2a12
k2C`2
C O .log R/M X
a1a12 R a2a12 R
dk.a1a2a12/E0.N; a1a2a12/
!
C O.hR2.3 log N /M C3kC1/;


 854 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
that is to say,
(9.12) SzR.N I H1; H2; `1; `2; h0/ D N zTR.H1; H2; `1; `2; h0/
C O .log R/M Ek.N / C O hR2.3 log N /M C3kC1 ;
where the last error term was obtained using Lemma 2. To estimate the first error term we use Lemma 2, (1.3), and the trivial estimate E0.N; q/ .2N=q/ log N for q N to find, uniformly for k p.log N /=18, that
(9.13) jEk.N /j
X[
q R2
dk.q/ max
b
.b;q/D1
ˇ
ˇE.N I q; b/ˇ
ˇ
X
q Da1 a2 a12
1
D
X[
q R2
dk.q/d3.q/E0.N; q/
v u u t
X[
q R2
d3k .q /2
q
s X
q R2
q.E0.N; q//2
q
.log N /9k2p2N log N
s X
q R2
E0.N; q/ N.log N /.9k2C1 A/=2;
provided R2 N 1
2 =.log N /B . On relabeling, we conclude that given any positive integers A and M there is a positive constant B D B.A; M / so that for R N1
4 =.log N /B and h R, (9.14)
SzR.N I H1; H2; `1; `2; h0/ D N zTR.H1; H2; `1; `2; h0/ C OM
N
.log N /A :
Using (9.3) with any # > 1=2, we see that (9.14) holds for the longer range
R M N#
2 ", h N ".
Returning to the main term in (9.12), we have by (6.6) that
(9.15) zTR.H1; H2; `1; `2; h0/
D
1
.2 i /2
Z
.1/
Z
.1/
F .s1; s2/ Rs1
s1k1C`1C1
Rs2
s2k2C`2C1 ds1ds2;
where, by letting sj D j C i tj and assuming 1; 2 > 0,
(9.16) F .s1; s2/
D
X
1 a1;a2;a12<1
.a1/ .a2/ .a12/2 a1 .H10/ a2 .H20/ a12 .H1\H2/0
.a1/a1s1 .a2/a2s2 .a12/a12s1Cs2
D
Y
p
1 p .H10/
.p 1/ps1
p .H20/
.p 1/ps2 C
p .H1\H2/0
.p 1/ps1Cs2 :


 PRIMES IN TUPLES I 855
We now consider three cases.
Case 1. Suppose h0 62 H. Then we have, for p > h,
p .H10/ D k1; p .H20/ D k2; p .H1\H2/0 D r:
Therefore in this case we define GH1;H2.s1; s2/ by
(9.17) F .s1; s2/ D GH1;H2 .s1; s2/ .1 C s1 C s2/r
.1 C s1/k1 .1 C s2/k2 :
Case 2. Suppose h0 2 H1 but h0 62 H2. (By relabeling this also covers the case where h0 2 H2 and h0 62 H1.) Then for p > h
p .H10/ D k1 1; p .H20/ D k2; p .H1\H2/0 D r:
Therefore, we define GH1;H2.s1; s2/ by
(9.18) F .s1; s2/ D GH1;H2 .s1; s2/ .1 C s1 C s2/r
.1 C s1/k1 1 .1 C s2/k2 :
Case 3. Suppose h0 2 H1 \ H2. Then for p > h
p .H10/ D k1 1; p .H20/ D k2 1; p .H1\H2/0 D r 1:
Thus, we define GH1;H2.s1; s2/ by
(9.19) F .s1; s2/ D GH1;H2 .s1; s2/ .1 C s1 C s2/r 1
.1 C s1/k1 1 .1 C s2/k2 1 :
In each case, G is analytic and uniformly bounded for 1; 2 > c, with any c < 1=4.
We now show that in all three cases
(9.20) GH1;H2 .0; 0/ D S.H0/:
Notice that in Cases 2 and 3 we have H0 D H. By (5.1), (7.5), (9.9), and (9.16), we find in all three cases
(9.21) GH1;H2 .0; 0/
D
Y
p
1 p.H10/ C p.H20/ p..H1\H2/0/ 1
p1 1 1
p
a.H1;H2;h0/
D
Y
p
1 p.H0/ 1
p1 1 1
p
a.H1;H2;h0/
;
where a.H1; H2; h0/ D k1Ck2 r D k r in Case 1; a.H1; H2; h0/ D .k1 1/Ck2 r D k r 1 in Case 2; and a.H1; H2; h0/ D .k1 1/C.k2 1/ .r 1/ D k r 1


 856 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
in Case 3. Hence, in Case 1 we have
GH1;H2 .0; 0/ D
Y
p
p p.H0/
p1 1 1
p
.k r/
(9.22)
D
Y
p
1 p.H0/
p 11
p
.k rC1/
D S.H0/;
while in Cases 2 and 3 we have
(9.23) GH1;H2 .0; 0/ D
Y
p
p p.H/
p1 1 1
p
.k r 1/
D
Y
p
1 p.H/
p 11
p
.k r/
D S.H/ .D S.H0//:
We are now ready to evaluate TR.H1; H2; `1; `2; h0/. There are two differences between the functions F and G that appear in (9.16)–(9.19) and the earlier (7.8)–(7.10). The first difference is that a factor of p in the denominator of the Euler product in (7.8) has been replaced by p 1, which only affects the value of constants in calculations. The second difference is the relationship between k1, k2, and r, which affects the residue calculations of the main terms. However, the analysis of lower order terms and the error analysis are essentially unchanged and, therefore, we only need to examine the main terms. We use Lemma 3 here to cover all of the cases. Taking into account (9.17)–(9.19) we have in Case 1 that a D k1; b D k2; d D r; u D `1; v D `2; in Case 2 that a D k1 1; b D k2; d D r; u D `1 C 1; v D `2; and in Case 3 that a D k1 1; b D k2 1; d D r 1; u D `1 C 1; v D `2 C 1. By (9.22) and (9.23), the proof of Propositions 5 and 2 is thus complete.
10. Proof of Theorem 3
For convenience, we agree in our notation below that we consider every set of size k with a multiplicity kŠ according to all permutations of the elements hi 2 H, unless mentioned otherwise. While unconventional, this will clarify some of the calculations. To prove Theorem 3 we consider in place of (3.5)
(10.1) SR.N; k; `; h; /
WD
1
N h2kC1
2N
X
nDN C1
X
1 h0 h
.n C h0/ log 3N
X
H f1;2;:::;hg jHjDk
ƒR.nI H; `/
2
D MzR.N; k; `; h/ log 3N
h MR.N; k; `; h/;


 PRIMES IN TUPLES I 857
where
MR.N; k; `; h/ D
1
N h2k
2N
X
nDN C1
X
H f1;2;:::;hg jHjDk
ƒR.nI H; `/
2
(10.2) ;
(10.3) MzR.N; k; `; h/
D
1
N h2kC1
2N
X
nDN C1
X
1 h0 h
.n C h0/
X
H f1;2;:::;hg jHjDk
ƒR.nI H; `/
2
:
To evaluate MR and MzR we multiply out the sum and apply Propositions 1 and 2. We need to group the pairs of sets H1 and H2 according to the size of the intersection r D jH1 \ H2j, and thus jHj D jH1 [ H2j D 2k r. Let us choose now a set H and here, exceptionally, we disregard the permutation of the elements in H. (However for H1 and H2 we take into account all permutations.) Given the set H of size 2k r, we can choose H1 in 2k r
k ways. Afterwards, we can choose the
intersection set in k
r ways. Finally, we can arrange the elements both in H1 and H2 in kŠ ways. This gives
(10.4) 2k r
k
k
r .kŠ/2 D .2k r/Š k
r
2
rŠ
choices for H1 and H2, when we take into account the permutation of the elements in H1 and H2. If we consider in the summation every union set H of size j just once, independently of the arrangement of the elements, then Gallagher’s theorem (3.7) may be formulated as
(10.5)
X
H f1;2;:::;hg jHjDj
S.H/ hj
jŠ;
where P indicates every set is counted just once. Applying this, we obtain on letting
(10.6) x D
log R
h;
and using Proposition 1, that (10.7)
MR.N; k; `; h/ 1
N h2k
k
X
r D0
.2k r/Š k
r
2
rŠ 2`
`
.log R/2`Cr
.r C 2`/Š N
X
jHjD2k r
S.H/
2`
` .log R/2`
k
X
r D0
k r
2 xr
.r C 1/ .r C 2`/ :


 858 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
By Proposition 2 and (10.5),
(10.8) MzR.N; k; `; h/ 1
N h2kC1
k
X
r D0
.2k r/Š k
r
2
rŠ Zr ;
where, abbreviating a D 2`C1
`C1 D 2` C 1
`C1
2` `
1 D
1
2
2` C 2 `C1
2` `
1
, we have
Zr WD 2`
`
.log R/2`Cr
.r C 2`/Š
(
r
X
jHjD2k r
2a log R
r C 2` C 1 S.H/N
C .2k 2r/
X
jHjD2k r
a log R
r C 2` C 1 S.H/N C
X
jHjD2k r
h
X
h0 D1 h0 ...H
S.H0/N
)
N 2`
`
.log R/2`Cr
.r C 2`/Š
(
h2k r
.2k r/Š
2ak log R
r C2`C1 C
2k r C 1
.2k r C 1/Š h2k rC1
)
:
(10.9)
In the last sum we took into account which element of H0 is h0, which can be chosen in 2k r C 1 ways. Thus we obtain
(10.10) MzR.N; k; `; h/
2`
` .log R/2`
k
X
r D0
k r
2 xr
.r C 1/ .r C 2`/
2ak
r C 2` C 1x C 1 :
We conclude, on introducing the parameters
(10.11) ' D
1
` C 1 ; .so that a D 2 '/; ‚ D
log R
log 3N ; .so that R D .3N /‚/;
that
(10.12) SR.N; k; `; h; / 2`
` .log R/2`Pk;`; .x/;
where
(10.13) Pk;`; .x/ D
k
X
r D0
k r
2 xr
.r C 1/ .r C 2`/ 1 C x 4.1 '
2 /k
r C2`C1 ‚
!!
:
Let
(10.14) h D log 3N; so that x D
‚:
The analysis of when S > 0 now depends on the polynomial Pk;`; .x/. We examine this polynomial as k; ` ! 1 in such a way that ` D o.k/. In the first place, the


 PRIMES IN TUPLES I 859
size of the terms of the polynomial are determined by the factor
g.r/ D k
r
2
xr;
and since g.r/ > g.r 1/ is equivalent to
r < kC1
1 C p1x
we should expect the polynomial is controlled by terms with r close to k=.z C 1/, where
(10.15) z D
1
px :
Consider now the sign of each term. For small x, the terms in the polynomial are positive, but they become negative when
1 C x 4.1 '
2 /k
r C 2` C 1 ‚
!
< 0:
When r D k=.z C 1/ and k; ` ! 1, ` D o.k/, we have heuristically
1 C x 4.1 '
2 /k
r C 2` C 1 ‚
!
1C
1 z2
4k
k
zC1 ‚
!
D
1
z2 .z C 2/2
‚:
Therefore, the terms will be positive for r near k=.z C 1/ if z > p =‚ 2, which
is equivalent to > .p 2p‚/2. Since we can take ‚ as close to #=2 as we wish, this implies Theorem 3. To make this argument precise, we choose r0 slightly smaller than g.r/ maximal, and prove that all the negative terms together contribute less than the single term r0, which will be positive for z and thus close to the values above. For the proof, we may assume 2 and 1=2 #0 1 are fixed, with #0 < 1 in case D 2. (The case D 1 is covered by Theorem 2, and the case D 2, #0 D 1, E2 D 0 is covered by (1.11) proved in Section 3.) First, we choose "0 as a sufficiently small fixed positive number. We will choose ` sufficiently large, depending on , #0, "0, and set
(10.16) k D .` C 1/2 D ' 2; ` > `0. ; #0; "0/; so that ' < '0. ; #0; "0/:
Furthermore, we choose
(10.17) ‚ D
log R
log 3N D
#0.1 '/
2;
and (because of our assumptions on ) we can define
(10.18) z0 WD
p2 =#0 2 > 0:


 860 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
Thus, we see that
(10.19) 1 C
1
z02
4k
k z0C1
2
#0
!
D
1
z02 .z0 C 2/2 2
#0
D 0;
Let us choose now
(10.20) r0 D
kC1
z0 C 1 ; r1 D r0 C 'k D r0 C ` C 1;
and put
(10.21) z D z0.1 C "0/:
The linear factor in each term of Pk;`; .x/ is, for r0 r r1,
1 C x 4.1 '
2 /k
r C 2` C 1 ‚
!
D1C
1
z2
0 .1 C "0/2
4k.1 C O.'//
k
z0C1 C O.k'/
2
#0.1 '/
!
D1C
z2
0 C O.p '/ C O. '/
z2
0 .1 C "0/2
> c. ; #0/"0 if ' < '0. ; #; "0/;
(10.22)
where c. ; #0/ > 0 is a constant. Letting
(10.23) f .r/ WD k
r
2 xr
.r C 1/ .r C 2`/ ;
we have, for any r2 > r1,
f .r2/
f .r0/ <
Y
r0<r r2
kC1 r
r
1
z
2
<
Y
r0<r r1
kC1 r
r
1
z
2
(10.24)
< kC1
r0 C 1 1 1
z
2` z0 C 1 1
z0.1 C "0/
2`
< e "0`:
Thus, the total contribution in absolute value of the negative terms of Pk;`; .x/ will be, for sufficiently large `, at most
(10.25) k 1 C
4.k C /
z2 e "0`f .r0/ < e "0`=2f .r0/;
while that of the single term r0 will be by (10.22) at least
(10.26) c. ; #0/"0f .r0/ > e "0`=2f .r0/ if ` > `0. ; #0; "0/:
This shows that Pk;`; .x/ > 0. Hence, we must have at least C 1 primes in some interval
(10.27) ŒnC1; nChç D ŒnC1; nC log 3N ç; n 2 ŒN C1; 2N ç;


 PRIMES IN TUPLES I 861
where
(10.28) D ‚z2 < #0
2 z2
0 .1 C "0/2 D .1 C "0/2.p p
2#0/2:
Since "0 can be chosen arbitrarily small, this proves Theorem 3.
References
[1] P. T. BATEMAN and R. A. HORN, A heuristic asymptotic formula concerning the distribution of prime numbers, Math. Comp. 16 (1962), 363–367. MR 26 #6139 Zbl 0105.03302
[2] E. BOMBIERI and H. DAVENPORT, Small differences between prime numbers, Proc. Roy. Soc. Ser. A 293 (1966), 1–18. MR 33 #7314 Zbl 0151.04201
[3] E. BOMBIERI, J. B. FRIEDLANDER, and H. IWANIEC, Primes in arithmetic progressions to large moduli. III, J. Amer. Math. Soc. 2 (1989), 215–224. MR 89m:11087 Zbl 0674.10036
[4] H. DAVENPORT, Multiplicative Number Theory, second ed., Grad. Texts Math. 74, SpringerVerlag, New York, 1980, Revised by Hugh L. Montgomery. MR 82m:10001 Zbl 0453.10002
[5] P. D. T. A. ELLIOTT and H. HALBERSTAM, A conjecture in prime number theory, in Symposia Mathematica, Vol. IV (INDAM, Rome, 1968/ 69), Academic Press, London, 1970, pp. 59–72. MR 43 #1943 Zbl 0238.10030
[6] T. J. ENGELSMA, k-tuple permissible patterns, 2005. Available at http://www.opertech.com/ primes/k-tuples.html
[7] P. ERDÖS, The difference of consecutive primes, Duke Math. J. 6 (1940), 438–441. MR 1,292h Zbl 0023.29801
[8] K. FORD, Zero-free regions for the Riemann zeta function, in Number Theory for the Millennium, II (Urbana, IL, 2000), A K Peters, Natick, MA, 2002, pp. 25–56. MR 2003k:11136 Zbl 1034.11045
[9] É. FOUVRY and F. GRUPP, On the switching principle in sieve theory, J. Reine Angew. Math. 370 (1986), 101–126. MR 87j:11092 Zbl 0588.10051
[10] P. X. GALLAGHER, On the distribution of primes in short intervals, Mathematika 23 (1976), 4–9. MR 53 #13140 Zbl 0346.10024
[11] D. A. GOLDSTON, On Bombieri and Davenport’s theorem concerning small gaps between primes, Mathematika 39 (1992), 10–17. MR 93h:11102 Zbl 0758.11037
[12] D. A. GOLDSTON and C. Y. YILDIRIM, Higher correlations of divisor sums related to primes. I. Triple correlations, Integers 3 (2003), A5, 66 pp. MR 2004h:11075 Zbl 1118.11039
[13] , Higher correlations of divisor sums related to primes III: Small gaps between primes, Proc. London Math. Soc. 95 (2007), 653–686. Zbl 1134.11034
[14] D. A. GOLDSTON, S. W. GRAHAM, J. PINTZ, and C. Y. YILDIRIM, Small gaps between primes and almost primes, Trans. Amer. Math. Soc. 361 (2009), 5285–5330.
[15] D. A. GOLDSTON, Y. MOTOHASHI, J. PINTZ, and C. Y. YILDIRIM, Small gaps between primes exist, Proc. Japan Acad. Ser. A Math. Sci. 82 (2006), 61–65. MR 2007a:11135 Zbl 05123005
[16] H. HALBERSTAM and H.-E. RICHERT, Sieve Methods, London Math. Soc. Monogr., No. 4, Academic Press, New York, 1974. MR 54 #12689 Zbl 0298.10026
[17] G. H. HARDY and J. E. LITTLEWOOD, Some problems of ‘Partitio Numerorum’; III: On the expression of a number as a sum of primes, Acta Math. 44 (1923), 1–70. MR 1555183
[18] G. H. HARDY and J. E. LITTLEWOOD, unpublished manuscript, see [26].
[19] D. R. HEATH-BROWN, Almost-prime k-tuples, Mathematika 44 (1997), 245–266. MR 99a: 11106 Zbl 0886.11052


 862 DANIEL A. GOLDSTON, JÁNOS PINTZ, and CEM Y. YILDIRIM
[20] M. N. HUXLEY, On the differences of primes in arithmetical progressions, Acta Arith. 15 (1968/1969), 367–392. MR 39 #5494 Zbl 0186.36402
[21] , Small differences between consecutive primes. II, Mathematika 24 (1977), 142–152. MR 57 #5925 Zbl 0367.10038
[22] M. HUXLEY, An application of the Fouvry-Iwaniec theorem, Acta Arith. 43 (1984), 441–443. MR 85k:11043 Zbl 0542.10036
[23] H. MAIER, Small differences between prime numbers, Michigan Math. J. 35 (1988), 323–344. MR 90e:11126 Zbl 0671.10037
[24] H. L. MONTGOMERY, Topics in Multiplicative Number Theory, Lecture Notes in Math. 227, Springer-Verlag, New York, 1971. MR 49 #2616 Zbl 0216.03501
[25] G. Z. PILT’AI, On the size of the difference between consecutive primes, Issledovania po teorii chisel 4 (1972), 73–79.
[26] R. A. RANKIN, The difference between consecutive prime numbers. II, Proc. Cambridge Philos. Soc. 36 (1940), 255–266. MR 1,292i Zbl 0025.30702
[27] G. RICCI, Sull’andamento della differenza di numeri primi consecutivi, Riv. Mat. Univ. Parma 5 (1954), 3–54. MR 16,675e Zbl 0058.27602
[28] A. SCHINZEL and W. SIERPIN ́ SKI, Sur certaines hypothèses concernant les nombres premiers, Acta Arith. 4, 185–208; Erratum 5 (1958), 259. MR 21 #4936 Zbl 0082.25802
[29] A. SELBERG, Collected Papers. Vol. II, Springer-Verlag, New York, 1991. MR 95g:01032 Zbl 0729.11001
[30] J. SIVAK, Méthodes de crible appliquées aux sommes de Kloosterman et aux petits écarts entre nombres premiers, 2005, Thèse de Doctorat de l’Université Paris Sud (Paris XI). Available at http://www.math.u-psud.fr/~sivak/these.pdf
[31] K. SOUNDARARAJAN, Small gaps between prime numbers: the work of Goldston-PintzYıldırım, Bull. Amer. Math. Soc. 44 (2007), 1–18. MR 2007k:11150 Zbl 05135876
[32] E. C. TITCHMARSH, The Theory of the Riemann Zeta-Function, second ed., The Clarendon Press, Oxford University Press, New York, 1986. MR 88c:11049 Zbl 0601.10026
[33] S. UCHIYAMA, On the difference between consecutive prime numbers, Acta Arith. 27 (1975), 153–157. MR 51 #3085 Zbl 0301.10037
(Received September 27, 2005) (Revised July 22, 2006)
E-mail address: goldston@math.sjsu.edu DEPARTMENT OF MATHEMATICS, SAN JOSE STATE UNIVERSITY, ONE WASHINGTON SQUARE, SAN JOSE, CA 95192-0130, UNITED STATES
E-mail address: pintz@renyi.hu RÉNYI MATHEMATICAL INSTITUTE OF MATHEMATICS, P.O. BOX 127, 1364 BUDAPEST,
HUNGARY
E-mail address: yalciny@boun.edu.tr BOG ̃ AZIÇI UNIVERSITY, DEPARTMENT OF MATHEMATICS, BEBEK, 34342  ̇ISTANBUL, TURKEY
and
FEZA GÜRSEY ENSTITÜSÜ, KULELI MAHALLESI,  ̧SEKIP AYHAN ÖZI  ̧SIK CADDESI 44, 34684
ÇENGELKÖY,  ̇ISTANBUL, TURKEY