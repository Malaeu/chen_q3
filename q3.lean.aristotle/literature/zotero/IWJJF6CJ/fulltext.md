---
title: "Upper bounds for moments of zeta sums"
authors:
  - "Peng Gao"
date: "2026-00-00 2026"
publication: "Journal of Number Theory"
doi: "10.1016/j.jnt.2025.04.002"
url: null
zotero:
  attachment_key: "MGIZSAJI"
  parent_key: "IWJJF6CJ"
  item_id: 1821
  attachment_item_id: 1838
---

Journal of Number Theory 278 (2026) 47–63
Contents lists available at ScienceDirect
Journal of Number Theory
journal homepage: www.elsevier.com/locate/jnt
General Section
Upper bounds for moments of zeta sums
Peng Gao
School of Mathematical Sciences, Beihang University, Beijing 100191, China
article info abstract
Article history:
Received 22 May 2024 Received in revised form 7 April 2025 Accepted 13 April 2025 Available online 4 June 2025 Communicated by L. Smajlovic
MSC: 11M06
Keywords: Zeta sums Moments
We establish upper bounds for moments of zeta sums using results on shifted moments of the Riemann zeta function under the Riemann hypothesis. © 2025 Elsevier Inc. All rights are reserved, including those for text and data mining, AI training, and similar technologies.
1. Introduction
Character sums have been extensively studied in the literature as they have many important applications in number theory. In [3], A. J. Harper studied sizes of the sums given by
∑
n≤x
nit and
∑
n≤x
χ(n),
where t ∈ R and χ(n) is a non-principal Dirichlet character modulo a large prime r. Following the notation in [3], we shall refer the first sum above as a zeta sum.
E-mail address: penggao@buaa.edu.cn.
https://doi.org/10.1016/j.jnt.2025.04.002 0022-314X/© 2025 Elsevier Inc. All rights are reserved, including those for text and data mining, AI training, and similar technologies.


 48 P. Gao / Journal of Number Theory 278 (2026) 47–63
Building on his work concerning moments of random multiplicative functions, Harper [3] showed that the low moments of zeta sums (and also character sums) have “better than squareroot cancellation”. More precisely, he proved that uniformly for 1 ≤ x ≤ T and 0 ≤ k ≤ 1,
1 T
∫T
0
∣∣∣
∑
n≤x
nit
∣∣∣
2k
dt
(x
1 + (1 − k)√log log(10LT )
)k ,
where LT = min{x, T /x}. In [9], B. Szabó obtained sharp upper bounds on shifted moments of Dirichlet Lfunction at points on the critical line and then applied the results to show under the generalized Riemann hypothesis (GRH) that for a fixed real number k > 2 and a large integer q, we have for 2 ≤ Y ≤ q,
∑
χ∈Xq∗
∣∣∣∣
∑
n≤Y
χ(n)
∣∣∣∣
2k
k φ(q)Y k(min(log Y, log 2q
Y ))(k−1)2 , (1.1)
where Xq∗ denotes the set of primitive Dirichlet characters modulo q and φ denotes Euler’s totient function. A similar result is given in [2] for moments of quadratic Dirichlet character sums under GRH. We note that the zeta sums behave very much like character sums. In fact, other than periodicity, the function n → n−it for a fixed t ∈ R is totally multiplicative and is unimodular. Thus, one expects to establish results analogous to (1.1) for moments of zeta sums and it is the aim of this paper to achieve this. For this, we define for real numbers m, T, Y > 0,
Sm(T, Y ) :=
∫2T
T
∣∣∣∣
∑
n≤Y
n−it
∣∣∣∣
2m
dt.
We are interested in bounding Sm(T, Y ) from the above. We first observe that as pointed out in [3] that using [4, Lemma 1.2] that when t is large and x ≥ t, we have
∑
x<n≤2x nit = (2x)1+it−x1+it
1+it + O(1) x/t. Moreover, note that by [6, Chap. 7, (34)],
we have ∑
n≤x nit t1/2 log t when x ≤ t. As the term x/t dominates t1/2 log t when x ≥ t3/2 log t, we deduce that when T is large enough and Y ≥ T 3/2 log T , we have for any real m > 0,
Sm(T, Y ) m T 1−2mY 2m.
We may therefore focus on the case Y < T 3/2 log T . In fact, since the sum ∑
x<n≤2x nit
is well understood when x ≥ T as shown above, we may further consider on the case Y ≤ T when bounding Sm(T, Y ).


 P. Gao / Journal of Number Theory 278 (2026) 47–63 49
Throughout this paper, we shall assume that Y ≤ (1 − ε)T for any fixed ε > 0. For this case, we establish the following result concerning the size of Sm(T, Y ) under the Riemann hypothesis (RH).
Theorem 1.1. Let us use the above notation and assume RH. Fix a real number with 0 < < 1. For any real number m > 2, large real numbers T, Y such that Y ≤ (1 − ε)T , we have
Sm(T, Y ) T Y m(log T )(m−1)2 . (1.2)
We note that by Hölder’s inequality, we have for any real number n > 1,
Sm(T, Y ) T 1−1/n(Smn(T, Y ))1/n.
The above together with Theorem 1.1 then implies that Sm(T, Y ) T Y m(log T )O(1) for any m > 0, upon choosing n large enough. We remark here that it is shown in [3] that one has Sm(T, Y ) T m+1, so our result above improves this when Y is slightly smaller than T . Our proof of Theorem 1.1 follows the approaches in [9]. A key ingredient used in the proof is a result of M. J. Curran [1] on shifted moments of the Riemann zeta function ζ (s).
2. Preliminaries
In this section, we include some results concerning shifted moments of the Riemann zeta function. The first one is quoted from [1, Theorem 1.1].
Proposition 2.1. Let us use the above notation and assume RH. Fix a real number with 0 < < 1. Let k ≥ 1 be a fixed integer and a1, . . . , ak be fixed non-negative real numbers. Let T be a large real number and let b = (b1, . . . , bk) be a real k-tuple with |bj| ≤ (1−ε)T . Then
∫2T
T
k ∏
j=1
|ζ( 1
2 + i(t + bk))|ak dt
T (log T )(a2
1 +···+a2
k)/4 ∏
1≤j<l≤k
|ζ(1 + i(bj − bl) + 1/ log T )|ajal/2.
Here the implied constant depends on k and the aj but not on T or the bj.
We remark here that [1, Theorem 1.1] is stated for |bj| ≤ T /2 but an inspection of the proof indicates that it continues to hold for |bj| ≤ (1 − ε)T with any ε > 0. To be more precise, for our case, one just needs to replace the set [T /2, 5T /2] in the


 50 P. Gao / Journal of Number Theory 278 (2026) 47–63
definition of G given in [1, (2)] by [εT, (2 + ε)T ] and carry out the proof. The only subtlety is the modification of the proof of [1, Proposition 4.3], as we have now |bj −bk| ≤ 2(1 − ε)T and this requires that the proof of [1, Proposition 4.3] holds when one assumes that |αj − αk| ≤ 2(1 − ε)T there. However, this follows if one can show that the term T (log T )−A in the proof is negligible, which in turn is a consequence of the estimation |ζ(1 + 1/ log T + it)| 1/ log T for |t| ≤ 2T given in the proof of [1, Proposition 4.3]. We also note that
∣∣∣ζ(1 + 1/ log T + iα)
∣∣∣ =
∣∣∣
∑ ∞
n=1
n−(1+1/ log T +iα)
∣∣∣ ≤
∣∣∣
∑ ∞
n=1
n−(1+1/ log T )
∣∣∣
=
∣∣∣ζ(1 + 1/ log T )
∣∣∣ log T,
where the last estimation above follows from [7, Corollary 1.17]. Also by [7, Corollary 1.17], we see that for 1
log T ≤ |α| ≤ 10, we have
|ζ(1 + 1/ log T + iα)| = 1
|1/ log T + iα| + O(1) 1
|α| .
Moreover, by [7, Corollary 13.16], we see that for 10 ≤ |α| ≤ eT , we have under the RH that
log |ζ(1 + 1/ log T + iα)| ≤ log log log |α| + O(1).
Based on these observations, for T be given as in Proposition 2.1, we now introduce the function g : R≥0 → R defined by
g(x) =
⎧⎪⎪⎨
⎪⎪⎩
log T if x ≤ 1
log T or x ≥ eT ,
1
x if 1
log T ≤ x ≤ 10,
log log x if 10 ≤ x ≤ eT .
(2.1)
The above discussions together with Proposition 2.1 allow us to derive the following simplified version on shifted moments of the Riemann zeta function.
Corollary 2.2. Let us use the above notation and assume RH. Fix a real number with 0 < < 1. Let k ≥ 1 be a fixed integer and a1, . . . , ak be fixed non-negative real numbers. Let T be a large real number and let b = (b1, . . . , bk) be a real k-tuple with |bj| ≤ (1−ε)T . Then
∫2T
T
k ∏
j=1
|ζ( 1
2 + i(t + bk))|ak dt T (log T )(a2
1 +···+a2
k)/4 ∏
1≤j<l≤k
g(|bj − bl|)ajal/2.
Here the implied constant depends on k, ε and the aj but not on T or the bj.


 P. Gao / Journal of Number Theory 278 (2026) 47–63 51
We also note the following upper bounds on moments of the Riemann zeta function, which can be obtained by modifying the proof of [1, Theorem 1.1].
Lemma 2.3. Let us use the above notation and assume RH. Fix a real number with 0 < < 1. Let k ≥ 1 be a fixed integer and a1, . . . , ak be fixed non-negative real numbers. Let T be a large real number and let b = (b1, . . . , bk) be a real k-tuple with |bj| ≤ (1−ε)T . Then for large real number T and σ ≥ 1/2,
∫2T
T
k ∏
j=1
|ζ(σ + i(t + bk))|ak dt T (log T )O(1).
We end this section by including an estimation for an average of the moments of the Riemann zeta function.
Proposition 2.4. Let us use the above notation and assume RH. Fix a real number with 0 < < 1. We have for any real numbers m > 2, 10 ≤ E ≤ (1 − ε)T ,
∫2T
T
( ∫E
0
|ζ(1/2 + i(±s + t))|ds
)2m
dt
T ((log T )(m−1)2 E3(log log E)O(1) + (log T )m2−3m+3E2m(log log T )O(1)).
(2.2)
Proof. Our proof follows closely that of [9, Proposition 3]. Without loss of generality, we prove (2.2) only for the case where the sign ± in front of s is + in what follows. We have by symmetry that for each fixed t and any fixed integer k ≥ 1,
( ∫E
0
|ζ(1/2 + i(s + t))|ds
)2m
∫
[0,E]k
k ∏
a=1
|ζ(1/2 + i(ta + t))| ·
(∫
D
|ζ(1/2 + i(u + t))|du
)2m−k
dt,
(2.3)
where D = D(t1, . . . , tk) = {u ∈ [0, E] : |t1 − u| ≤ |t2 − u| ≤ . . . ≤ |tk − u|}.
We let B1 = [ − 1
log T , 1
log T
] and Bj = [ − ej−1
log T , − ej−2
log T
] ∪ [ ej−2
log T , ej−1
log T
] for 2 ≤ j <
log log T + 10 := K. We further denote BK = [−E, E] \ ⋃
1≤j<K Bj .
Observe that for any t1 ∈ [0, E], we have D ⊂ [0, E] ⊂ t1 + [−E, E] ⊂ ⋃
1≤j≤K t1 + Bj .
Thus if we denote Aj = Bj ∩ (−t1 + D), then (t1 + Aj)1≤j≤K form a partition of D. We apply Hölder’s inequality twice to deduce that for 2m ≥ k + 1,
(∫
D
|ζ(1/2 + i(u + t))|du
)2m−k


 52 P. Gao / Journal of Number Theory 278 (2026) 47–63
≤
(∑
1≤j≤K
1
j ·j
∫
t1 +Aj
|ζ(1/2 + i(u + t))|du
)2m−k
≤
(∑
1≤j≤K
j 2m−k
(∫
t1 +Aj
∣∣ζ(1/2 + i(u + t))∣∣du
)2m−k )
(2.4)
·
(∑
1≤j≤K
j −(2m−k)/(2m−k−1)
)2m−k−1
∑
1≤j≤K
j 2m−k
(∫
t1 +Aj
|ζ(1/2 + i(u + t))|du
)2m−k
≤∑
1≤j≤K
j2m−k|Bj |2m−k−1
∫
t1 +Aj
|ζ(1/2 + i(u + t))|2m−kdu.
We denote for t = (t1, . . . , tk),
ζ(t, u) =
∫2T
T
k ∏
a=1
|ζ(1/2 + i(ta + t))| · |ζ(1/2 + i(u + t))|2m−kdt.
Notice that we have [−E, E] = ⋃
1≤j≤K Bj. Thus, for each (t1, . . . , tk, u) ∈ [0, E]k+1, we may decompose the values of |ti+1 − u| − |ti − u| into unions of Bj. Applying this, we then deduce from (2.3) and (2.4) that
∫2T
T
( ∫E
0
|ζ(1/2 + i(s + t))|ds
)2m
dt
∑
1≤l0 ≤K
l2m−k
0 |Bl0 |2m−k−1
∫
[0,E]k
∫
t1 +Al0
ζ(t, u)dudt
∑
1≤l0 ,l1 ,...lk−1 ≤K
l2m−k
0 |Bl0 |2m−k−1
∫
Cl0 ,l1,··· ,lk−1
ζ(t, u)dudt,
(2.5)
where
Cl0,l1,··· ,lk−1 = {(t1, . . . , tk, u) ∈ [0, E]k+1 : u ∈ t1 + Al0 , |ti+1 − u| − |ti − u| ∈ Bli ,
1 ≤ i ≤ k − 1}.
We now distinguish two cases in the last summation of (2.5) according to the size of l0.


 P. Gao / Journal of Number Theory 278 (2026) 47–63 53
Case 1: l0 < K. First note that for any fixed u, t1 is in a fixed region of size el0
log T . For
fixed u and t1, t2 is in a fixed region of size el1
log T when l1 < K, as |t2 −u| ∈ |t1 −u|+Bl1 .
Moreover, when l1 = K, t2 is in a region of size E E el1
log T as eK
log T 1. We
thus conclude that t2 is in a fixed region of size E el1
log T regardless of the value of
l1. Similar considerations then imply that the volume of the region Cl0,l1,··· ,lk−1 is
E k el0+l1+···+lk−1
(log T )k . Also, by the definition of Cl0,l1,··· ,lk−1 , we have t1−u ∈ Al0 ⊂ Bl0 , so that
we have el0
log T |t1 − u| E ≤ T . It follows from the definition of the function g defined
in (2.1) that g(|t1 − u|) log T
el0 or g(|t1 − u|) log log E. As min( log T
el0 , log log E) 1,
we conclude that g(|t1 − u|) log T
el0 log log E. We deduce from the definition of Aj that
|t2 − u| ≥ |t1 − u|, so that E |t2 − u| = |t1 − u| + (|t2 − u| − |t1 − u|) el0
log T + el1
log T ,
which implies that g(|t2 − u|) log T
emax(l0,l1) log log E. Similarly, we have g(|ti − u|)
log T
emax(l0,l1,...,li−1) log log E for any 1 ≤ i ≤ k. Moreover, we have ∑j−1
s=i (|ts+1−u|−|ts−u|) ≤
|tj − ti| for any 1 ≤ i < j ≤ k, so that we have g(|tj − ti|) log T
emax(li,...,lj−1) log log E. We
then deduce from Corollary 2.2 that for (t1, . . . , tk, u) ∈ Cl0,l1,··· ,lk−1 ,
ζ(t, u) T (log T )((2m−k)2+k)/4(log log E)O(1)
( k∏−1
i=0
log T
emax(l0 ,l1 ,...,li )
)(2m−k)/2
·
( k∏−1
i=1
k ∏
j=i+1
log T
emax(li ,...,lj −1 )
)1/2
= T (log T )m2 (log log E)O(1)
· exp
(
− 2m − k
2
k−1
∑
i=0
max(l0, l1, . . . , li) − 1
2
k−1
∑
i=1
k ∑
j=i+1
max(li, . . . , lj−1)
) .
Here, we adopt the convention throughout the paper that any empty product is defined to be 1 and any empty sum is defined to be 0. Observe that we have |Bl0| el0
log T , so
that
∑
1≤l0 <K
1≤l1 ,...lk−1 ≤K
l2m−k
0 |Bl0 |2m−k−1
∫
Cl0,l1 ,··· ,lk−1
ζ(t, u)dudt
T (log T )(m−1)2 Ek(log log E)O(1)
·∑
1≤l0 <K
1≤l1 ,...lk−1 ≤K
l2m−k
0 exp
(
(2m − k − 1)l0 +
k−1
∑
i=0
li − 2m − k
2
k−1
∑
i=0
max(l0, l1, . . . , li)
−1
2
k−1
∑
i=1
k ∑
j=i+1
max(li, . . . , lj−1)
)
(2.6)
= T (log T )(m−1)2 Ek(log log E)O(1)


 54 P. Gao / Journal of Number Theory 278 (2026) 47–63
·∑
1≤l0 <K
1≤l1 ,...lk−1 ≤K
l2m−k
0 exp
( 2m − k
2 l0 + 1
2
k−1
∑
i=1
li − 2m − k
2
k−1
∑
i=1
max(l0, l1, . . . , li)
−1
2
k−1
∑
i=1
k ∑
j=i+2
max(li, . . . , lj−1)
) .
We now set k = 3 and our assumption that m > 2 to see that in this case deduce from the above that
2m − k
2 l0 + 1
2
k−1
∑
i=1
li − 2m − k
2
k−1
∑
i=1
max(l0, l1, . . . , li) − 1
2
k−1
∑
i=1
k ∑
j=i+2
max(li, . . . , lj−1)
= 2m − 3
2 l0 + 1
2
∑
1≤i≤2
li − 2m − 3
2
∑
1≤i≤2
max(l0, l1, . . . , li)
−1
2
∑
1≤i≤2
∑
i+2≤j≤3
max(li, . . . , lj−1)
= 2m − 3
2 l0 + 1
2
∑
1≤i≤2
li − 2m − 3
2
∑
1≤i≤2
max(l0, l1, . . . , li) − 1
2 max(l1, l2)
≤ l2
2 − 2m − 3
2 max(l0, l1, . . . , l2)
≤ − (m − 2) max(l0, . . . , l2).
We deduce from (2.6) and the above that when k = 3,
∑
1≤l0 <K
1≤l1 ,...lk−1 ≤K
l2m−k
0 |Bl0 |2m−k−1
∫
Cl0,l1 ,··· ,lk−1
ζ(t, u)dudt
T (log T )(m−1)2 E3(log log E)O(1) ∑
1≤l0 <K
1≤l1 ,...l2 ≤K
l2m−3
0 exp
(
− (m − 2) max(l0, . . . , l2)
)
T (log T )(m−1)2 E3(log log E)O(1) ∑
1≤l0 <K
1≤l1 ,...l2 ≤K
l2m−3
0 exp
(
− (m − 2)(l0 + l1 + l2)
3)
)
T (log T )(m−1)2 E3(log log E)O(1), (2.7)
where the last estimation above follows by noting that we have m > 2. Case 2: l0 = K. The volume of the region CK,l1,··· ,lk−1 is Ek+1 el1+···+lk−1
(log T )k−1 . For
each 1 ≤ i ≤ k, we have g(|ti − u|) log log E. Also, similar to Case 1, we have g(|tj − ti|) log T
emax(li,...,lj−1) for 1 ≤ i ≤ k.


 P. Gao / Journal of Number Theory 278 (2026) 47–63 55
ζ(t, u) T (log T )((2m−k)2+k)/4(log log E)O(1)
( k∏−1
i=1
k ∏
j=i+1
log T
emax(li ,...,lj −1 )
)1/2
= T (log T )((2m−k)2+k2)/4(log log E)O(1) exp
(
−1
2
k−1
∑
i=1
k ∑
j=i+1
max(li, . . . , lj−1)
) .
As |BK | E, we see that
∑
1≤l1 ,...lk−1 ≤K
K2m−k|BK |2m−k−1
∫
CK,l1,··· ,lk−1
ζ(t, u)dudt
T (log T )((2m−k)2+k2)/4−k+1E2m(log log E)O(1)(log log T )O(1)
·∑
1≤l1 ,...lk−1 ≤K
exp
( k−1
∑
i=1
li − 1
2
k−1
∑
i=1
k ∑
j=i+1
max(li, . . . , lj−1)
) .
(2.8)
We now set k = 3 to see that in this case deduce from the above that
k−1
∑
i=1
li − 1
2
k−1
∑
i=1
k ∑
j=i+1
max(li, . . . , lj−1)
= (l1 + l2) − 1
2 (l1 + max(l1, l2) + l2) ≤ (l1 + l2) − 1
2 (l1 + l2 + l2) = l1
2.
We deduce from (2.8) and the above that by setting k = 3,
∑
1≤l1 ,...lk−1 ≤K
K2m−k|BK |2m−k−1
∫
CK,l1 ,··· ,lk−1
ζ(t, u)dudt
T (log T )((2m−3)2+32)/4−2E2m(log log E)O(1)(log log T )O(1) ∑
1≤l1 ,...l2 ≤K
exp
( l1 2
)
T (log T )m2−3m+3E2m(log log T )O(1),
(2.9)
where the last estimation above follows by noting that we have E < T . We now deduce the estimation in (2.2) using (2.7) and (2.9). This completes the proof of the proposition.
3. Proof of Theorem 1.1
3.1. Initial treatments
As we explained in the paragraph below Theorem 1.1, it suffices to establish (1.2). We let ΦU (x) be a non-negative smooth function supported on (0, 1), satisfying ΦU (x) = 1 for x ∈ (1/U, 1−1/U ) with U a parameter to be chosen later and such that Φ(j)
U (x) j U j


 56 P. Gao / Journal of Number Theory 278 (2026) 47–63
for all integers j ≥ 0. We denote the Mellin transform of ΦU by ̂ΦU and we observe that repeated integration by parts gives that, for any integer i ≥ 1 and (s) ≥ 1/2,
̂ΦU (s) U i−1(1 + |s|)−i. (3.1)
Note that Hölder’s inequality implies |x+y|2m ≤ 22m−1(|x|2m+|y|2m) for any x, y ∈ C. We insert the function ΦU ( n
Y ) into the definition of Sm(T, Y ) and apply this to obtain that
Sm(T, Y )
∫2T
T
∣∣∣ ∑
n
n−itΦU ( n
Y)
∣∣∣
2m
dt +
∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
2m
dt. (3.2)
We further apply the Mellin inversion to obtain that
∫2T
T
∣∣∣
∑
n
n−itΦU ( n
Y)
∣∣∣
2m
dt =
∫2T
T
∣∣∣ 1
2πi
∫
(2)
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt.
Observe that by [5, Corollary 5.20] that under RH, we have for (s) ≥ 1/2 and any ε > 0,
ζ(s) |s|ε. (3.3)
The bounds in (3.1) and (3.3) allow us to shift the line of integration in (3.2) to (s) = 1/2 to obtain that
∫2T
T
∣∣∣ ∑
n
n−itΦU ( n
Y)
∣∣∣
2m
dt =
∫2T
T
∣∣∣ 1
2πi
∫
(1/2)
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt. (3.4)
We split the last integral above according to whether | (s)| ≤ (log T )D or not for some D > 0 to be specified later, obtaining
∫2T
T
∣∣∣
∑
n
n−itΦU ( n
Y)
∣∣∣
2m
dt
∫2T
T
∣∣∣
∫
(1/2) | (s)|≤(log T )D
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt
+
∫2T
T
∣∣∣
∫
(1/2) | (s)|>(log T )D
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt.
(3.5)


 P. Gao / Journal of Number Theory 278 (2026) 47–63 57
We now set U = (log T )C to deduce from (3.1), (3.2), (3.4) and the above that
Sm(T, Y )
∫2T
T
∣∣∣
∫
(1/2) | (s)|≤(log T )D
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt
+
∫2T
T
∣∣∣
∫
(1/2) | (s)|>(log T )D
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt
+
∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
2m
dt
Ym
∫2T
T
∣∣∣
∫
(1/2) |s|≤(log T )D
∣∣∣ζ(1/2 + i(s + t))
∣∣∣ 1
1 + |s| ds
∣∣∣
2m
dt
+
∫2T
T
∣∣∣
∫
(1/2) | (s)|>(log T )D
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt
+
∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
2m
dt.
(3.6)
It follows from the above that in order to establish Theorem 1.1, it remains to prove the following results.
Lemma 3.2. Let us use the above notation and assume RH. We have for D sufficiently large in terms of C and any real number m > 2,
∫2T
T
∣∣∣
∫
(1/2) | (s)|>(log T )D
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt T Y m. (3.7)
Lemma 3.3. Let us use the above notation and assume RH. We have for D large enough and any real number m > 2,
∫2T
T
∣∣∣
∫
(1/2) |s|≤(log T )D
∣∣∣ζ(1/2 + i(s + t))
∣∣∣ 1
1 + |s| ds
∣∣∣
2m
dt T (log T )(m−1)2 . (3.8)


 58 P. Gao / Journal of Number Theory 278 (2026) 47–63
Lemma 3.4. Let us use the above notation and assume RH. We have for C large enough and any real number m > 2,
∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
2m
dt T Y m. (3.9)
3.5. Proof of Lemma 3.2
We apply (3.1) and Hölder’s inequality to deduce that, as m ≥ 1/2,
∫2T
T
∣∣∣
∫
(1/2) | (s)|>(log T )D
ζ(s + it)Y s ̂ΦU (s)ds
∣∣∣
2m
dt
∫2T
T
(( ∫
(1/2) | (s)|>(log T )D
∣∣∣̂ΦU (s)
∣∣∣|ds|
)2m−1
·
∫
(1/2) | (s)|>(log T )D
∣∣∣ζ(s + it)Y s
∣∣∣
2m∣∣∣̂ΦU (s)
∣∣∣|ds|
) dt
Y m( ∫
(1/2) | (s)|>(log T )D
∣∣∣̂ΦU (s)
∣∣∣|ds|
)2m−1
·
∫
(1/2) | (s)|>(log T )D
∫2T
T
∣∣∣ζ(s + it)
∣∣∣
2m∣∣∣̂ΦU (s)
∣∣∣dt|ds|.
(3.10)
Now we note that by (3.1),
∫
(1/2) | (s)|>(log T )D
∣∣∣̂ΦU (s)
∣∣∣|ds|
∫
(1/2) | (s)|>(log T )D
U
1 + |s|2 |ds| D
U
(log T )D .
(3.11)
We also apply (3.3) to see that
∫
(1/2) | (s)|>(log T )D
∫2T
T
∣∣∣ζ(s + it)
∣∣∣
2m
·
∣∣∣̂ΦU (s)
∣∣∣dt|ds|
∫
|s|>(log T )D
∫2T
T
∣∣∣ζ(1/2 + i(s + t))
∣∣∣
2m
·U
1 + |s|2 dt|ds|
∫
(log T )D<|s|≤5T
∫2T
T
∣∣∣ζ(1/2 + i(s + t))
∣∣∣
2m
·U
1 + |s|2 dt|ds|


 P. Gao / Journal of Number Theory 278 (2026) 47–63 59
+
∫
|s|>5T
∫2T
T
∣∣∣ζ(1/2 + i(s + t))
∣∣∣
2m
·U
1 + |s|2 dt|ds|
∫
(log T )D<|s|≤5T
∫2T
T
∣∣∣ζ(1/2 + i(s + t))
∣∣∣
2m
·U
1 + |s|2 dt|ds|
+
∫
|s|>5T
∫2T
T
∣∣∣s + t
∣∣∣
ε
·U
1 + |s|2 dt|ds| (3.12)
∫
(log T )D<|s|≤5T
∫2T
T
∣∣∣ζ(1/2 + i(s + t))
∣∣∣
2m
·U
1 + |s|2 dt|ds| +
∫
|s|>5T
∫2T
T
∣∣∣s
∣∣∣
ε
·U
1 + |s|2 dt|ds|
∫
(log T )D<|s|≤5T
∫2T
T
∣∣∣ζ(1/2 + i(s + t))
∣∣∣
2m
·U
1 + |s|2 dt|ds| + U T ε
∫
(log T )D<|s|≤5T
∫2T
T
∣∣∣ζ(1/2 + it)
∣∣∣
2m
·U
1 + |s|2 dt|ds| + U T ε
T U (log T )O(1)(log T )−D + U T ε,
where the last estimation above follows from [8, Corollary B], which asserts that
∫2T
T
∣∣∣ζ(1/2 + it)
∣∣∣
2m
dt T (log T )O(1).
We now deduce the estimation given in (3.7) from (3.10)-(3.12), upon taking D much larger than C. This completes the proof of the lemma.
3.6. Proof of Lemma 3.3
We deduce from (3.6) by symmetry and Hölder’s inequality that,
∣∣∣
∫
|s|≤(log T )D
∣∣∣ζ(1/2 + i(s + t))| 1
1 + |s| ds
∣∣∣
2m
∣∣∣
(log T )D
∫
0
|ζ(1/2 + i(u + t))|
u + 1 du
∣∣∣
2m


 60 P. Gao / Journal of Number Theory 278 (2026) 47–63
∣∣∣
∑
n≤D log log T +1
en −1
∫
en−1 −1
|ζ(1/2 + i(u + t))|
u + 1 du
∣∣∣
2m
=
∣∣∣
∑
n≤D log log T +1
n−1 · n
en −1
∫
en−1 −1
|ζ(1/2 + i(u + t))|
u + 1 du
∣∣∣
2m
≤
(∑
n≤D log log T +1
n−2m/(2m−1)
)2m−1
·∑
n≤D log log T +1
( n
en −1
∫
en−1 −1
|ζ(1/2 + i(u + t))|
u + 1 du
)2m
∑
n≤D log log T +1
n2m
e2nm
( en−1
∫
en−1 −1
|ζ(1/2 + i(u + t))|du
)2m
,
where the last estimation above follows by noting that we have 1/(u + 1) e−n for en−1 − 1 ≤ u ≤ en − 1.
By Proposition 2.4, for any m > 2, one has
∑
n≤D log log T +1
n2m
e2nm
∫2T
T
( en−1
∫
en−1 −1
|ζ(1/2 + i(u + t))|du
)2m
dt
T
∑
n≤D log log T +1
n2m
e2nm
(
(log T )(m−1)2 e3n(log 2n)O(1)
+ (log T )m2−3m+3(log 2n)O(1)(log log T )O(1)e2mn)
T (log T )(m−1)2 .
We now deduce from the above that (3.8) holds. This completes the proof of the lemma.
3.7. Proof of Lemma 3.4
We apply the Cauchy-Schwarz inequality to see that
∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
2m
dt
≤
( ∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
2
dt
)1/2( ∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
4m−2
dt
)1/2
.
(3.13)


 P. Gao / Journal of Number Theory 278 (2026) 47–63 61
We first note that it follows from [5, Theorem 9.1] that for arbitrary complex numbers an, we have for T, Z ≥ 2,
∫2T
T
∣∣∣∣
∑
n≤Z
ann−it
∣∣∣∣
2
dt (T + Z)
∑
n≤Z
|an|2.
We apply the above to Z = Y and keep in mind our assumption that Y ≤ T to see that
∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
2
dt (T + Y )
∑
n≤Y
(1 − ΦU ( n
Y ))2
T
∑
Y (1−1/U )≤n≤Y
1+T
∑
0≤n≤Y /U
1 TY
U.
(3.14)
We next note that
∫2T
T
∣∣∣∣
∑
n≤Y
n−it(1 − ΦU ( n
Y ))∣∣∣∣
4m−2
dt
∫2T
T
∣∣∣∣
∑
n≤Y
n−it
∣∣∣∣
4m−2
dt +
∫2T
T
∣∣∣∣
∑
n≤Y
n−itΦU ( n
Y)
∣∣∣∣
4m−2
dt.
(3.15) We deduce from (3.5), Lemma 3.2 and Lemma 3.3 that
∫2T
T
∣∣∣∣
∑
n≤Y
n−itΦU ( n
Y)
∣∣∣∣
4m−2
dt T Y 2m−1(log T )O(1). (3.16)
To estimate the first expression on the right-hand side of (3.15), we apply Perron’s formula as given in [7, Corollary 5.3] to see that
∑
n≤Y
n−it = 1
2πi
1+1/ log Y +iY
∫
1+1/ log Y −iY
ζ(s + it) Y s
s ds + R1 + R2,
=1
2πi
1/2−iY
∫
1+1/ log Y −iY
+1
2πi
1/2+iY
∫
1/2−iY
+1
2πi
1+1/ log Y +iY
∫
1/2+iY
ζ(s + it) Y s
s ds + R1 + R2,
(3.17)
where


 62 P. Gao / Journal of Number Theory 278 (2026) 47–63
R1 =O
(∑
Y /2<n<2Y n=Y
min(1, 1
|n − Y | )
)
= O(log Y ),
R2 =O
( 41+1/ log Y + Y 1+1/ log Y
Y ζ(1 + 1/ log Y )
)
= O(log Y ).
(3.18)
Here the last estimation above follows from [7, Corollary 1.17]. We now consider the moments of the horizontal integrals in (3.17). We may assume that Y ≥ 10, otherwise the lemma is trivial. By symmetry we only need to consider only one of them. Note that we have |Y s/s| 1 in that range and m ≥ 1, which allows us to apply Hölder’s inequality to get
∫2T
T
∣∣∣∣
1+1/ log Y +iY
∫
1/2+iY
ζ(s + it) Y s
s ds
∣∣∣∣
4m−2
dt
∫2T
T
( 1+1/ log Y +iY
∫
1/2+iY
|ζ(s + it)||ds|
)4m−2
dt
1+1/ log Y +iY
∫
1/2+iY
∫2T
T
|ζ(s + it)|4m−2dt|ds|
T (log T )O(1), (3.19)
where the last estimation above follows from Lemma 2.3, which implies that for 1/2 ≤ (s) ≤ 1 + 1/ log Y , we have under RH,
∫2T
T
|ζ(s + it)|4m−2dt T (log T )O(1).
We treat the moments of the vertical integral in (3.17) using Hölder’s inequality (by noting that 4m − 2 > 4), Proposition 2.4 and the assumption Y ≤ (1 − ε)T to see that
∫2T
T
∣∣∣∣
1/2+iY
∫
1/2−iY
ζ(s + it) Y s
s ds
∣∣∣∣
4m−2
dt
Y 2m−1
∫2T
T
( ∫Y
0
|ζ(1/2 + i(s + t))|
s + 1 ds
)4m−2
dt
Y 2m−1 ∑
n≤log Y +2
n4m−2
e(4m−2)n
∫2T
T
( en−1
∫
en−1 −1
|ζ(1/2 + i(s + t))|ds
)4m−2
dt (3.20)
Y 2m−1T (log T )O(1)( ∑
n≤log Y +2
n4m−2
e(4m−2)n e3n +
∑
n≤log Y +2
n4m−2)


 P. Gao / Journal of Number Theory 278 (2026) 47–63 63
Y 2m−1T (log T )O(1).
We conclude from (3.17)-(3.20) that
∫2T
T
∣∣∣∣
∑
n≤Y
n−it
∣∣∣∣
4m−2
dt Y 2m−1T (log T )O(1). (3.21)
We then deduce from (3.13)-(3.16), (3.21) and recall that we have U = (log T )C , Y ≤ (1 − ε)T to see that the estimation given in (3.9) is valid. This completes the proof of the lemma.
Acknowledgments
The author is supported in part by NSFC grant 12471003. This work grows out of discussions with Changhao Chen and Nankun Hong on large sieve inequalities for Dirichlet polynomials when the author visited Anhui University in April 2024. The author is indebted to them for the inspiration of this paper and many helpful suggestions on the writing of the manuscript. The author would also like to thank the anonymous referees for their very careful inspections of the paper and many valuable suggestions.
Data availability
No data was used for the research described in the article.
References
[1] M.J. Curran, Correlations of the Riemann zeta function, Mathematika 70 (4) (2024) e12268, 14 pp. [2] P. Gao, L. Zhao, Bounds for moments of quadratic Dirichlet character sums, Bull. Aust. Math. Soc. 111 (2025) 43–47.
[3] A.J. Harper, The typical size of character and zeta sums is o(√x) (preprint), arXiv:2301.04390. [4] A. Ivić, The Riemann Zeta-Function, Theory and Applications, Dover Publications, Inc., Mineola, New York, 2003. [5] H. Iwaniec, E. Kowalski, Analytic Number Theory, American Mathematical Society Colloquium Publications, vol. 53, American Mathematical Society, Providence, 2004. [6] H.L. Montgomery, Ten lectures on the interface between analytic number theory and harmonic analysis, in: CBMS Regional Conference Series in Mathematics, vol. 84, Conference Board of the Mathematical Sciences, Washington, DC; by the American Mathematical Society, Providence, RI, 1994. [7] H.L. Montgomery, R.C. Vaughan, Multiplicative Number Theory. I. Classical Theory, Cambridge Studies in Advanced Mathematics, vol. 97, Cambridge University Press, Cambridge, 2007. [8] K. Soundararajan, Moments of the Riemann zeta function, Ann. Math. (2) 170 (2) (2009) 981–993. [9] B. Szabó, High moments of theta functions and character sums, Mathematika 70 (2) (2024) e12242, 37 pp.