---
title: "A Counterexample to the Mizohata-Takeuchi Conjecture"
authors:
  - "Hannah Cairo"
date: "2025-03-12 2025-03-12"
publication: null
doi: "10.48550/arXiv.2502.06137"
url: "http://arxiv.org/abs/2502.06137"
zotero:
  attachment_key: "JAWTUKMR"
  parent_key: "A7UPDGTE"
  item_id: 1931
  attachment_item_id: 1933
---

arXiv:2502.06137v2 [math.CA] 12 Mar 2025
A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE
HANNAH CAIRO
Abstract. We derive a family of Lp estimates of the X-Ray transform of positive measures in Rd, which we use to construct a log R-loss counterexample to the Mizohata-Takeuchi conjecture for every C2 hypersurface in Rd that does not lie in a hyperplane. In particular, multilinear restriction estimates at the endpoint cannot be sharpened directly by the Mizohata-Takeuchi conjecture.
1. Introduction
Let Σ Ă Rd be a compact C2 hypersurface with measure ds. The extension operator E : L1pΣ; dsq Ñ L8pRdq is defined by
rEf spxq :“
ż
Σ
e ́2πixx,ςyf pςqdσpςq
The Mizohata-Takeuchi conjecture can be stated as follows:
Conjecture 1.1 (Mizohata-Takeuchi). Let Σ be any C2 hypersurface in Rd with surface measure dσ. Let f P L2pΣ, dσq and let w : Rd Ñ Rě0 be a nonnegative weight. Then we have
ż
Rd
|Ef pxq|2 wpxqdx À }f }2
L2pΣ;dσq }X w}L8 (1.1)
where Xw denotes the X-Ray transform of w.
The primary result of this paper is the following counterexample to the Mizohata-Takeuchi conjecture with log R-loss:
Theorem 1.2 (Counterexample). For any C2 hypersurface Σ that is not a plane, there is some f P L2pΣ; dσq and nonnegative weight wRRd Ñ Rě0 so that the following holds.
ż
BR p0q
ˇˇEf pxqˇˇ2wpxqdx Á log R }f }2
L2pΣ;dσq sup
lĂRd a line
ż
l
w
Conjecture 1.1 originally arose in the study of well-posedness for dispersive PDE ([Tak74; Tak80; Miz85]). Since then, the Mizohata-Takeuchi conjecture has taken on an important role in Fourier restriction theory for a few reasons, which we enumerate below.
1.1. Multilinear Restriction Estimates. In 2006, the following multilinear form of the restriction conjecture was formulated by [BCT06]:
Conjecture 1.3 (Multilinear Restriction). Let tUj : j P rdsu be a collection of C2 hypersurfaces in Rd, so that the normal to Uj at any point is within 1
100 of the xj -axis. Let Ej denote the corresponding extension operators. Then, for each ε ą 0, q ě 2d
d ́1 and p1 ď qpd ́1q
d,
Date: February 2025.
1


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 2
›››››
źd
j“1
Ej gj
›››››
Lq{d pB p0,Rqq
À
źd
j“1
}gj }LppUj q
for all gj P Lp pUjq , 1 ď j ď d, and all R ě 1.
Currently, Conjecture 1.3 has been proven away from the endpoint ([Tao20]) and up to Rε losses at the endpoint ([BCT06]). In a recent paper, [CHV23] (see also [CHV18]) developed a general functional-analytic approach to dual formulations of multilinear estimates. In particular, they showed that The MizohataTakeuchi Conjecture implies Conjecture 1.3 without Rε losses, using the endpoint multilinear Kakeya inequality of Guth ([Gut10]). Theorem 1.2 therefore shows that it is not possible to use this approach to prove Conjecture 1.3.
1.2. Stein’s Conjecture. In 1978, it was suggested by Stein ([Ste79]) that Kakeya or Nikodym maximal functions may control the behavior of Bochner-Riesz multipliers (see [BCSV06] and the references therein for the history of this approach). In the 1990’s, several papers (see [CRS92; BRV97; CS97b; CS97a] and the references therein) were written on the subject, and the following conjecture has become known as Stein’s conjecture:
Conjecture 1.4 (Stein’s Conjecture). Under the hypotheses of Conjecture 1.1, the following holds:
ż
Rd
|Ef |2 wdx À
ż
Σ
|f pςq|2 sup
l‖N pςq
Xwplqdσpςq (1.2)
It is worthwhile for historical purposes to note that Stein originally posed several different forms of this inequality, and only recently has Stein’s conjecture (in the context of the extension operator) come to refer to the inequality above (see [BGNO24]). The reason why one might expect (1.2) to hold is as follows. One often expects Ef to be
controlled in some sense by square functions, maybe of the form ř
Θ| ˆ
f |Θdσ|2 where Θ ranges over some collection of Rα-caps for some α. For weighted estimates on quantities of the form
ş
Rd |E2pxq|wpxqdx, one expects the contribution from each term defining the square function to be concentrated along tubes by a parabolic rescaling argument. The norm }f }2
L2 measures the
concentration of the L2 mass of Ef along these tubes in a way that is compatible with square functions, and so we are led to consider estimates of the form (1.2). Note that Stein’s conjecture would directly imply the Mizohata-Takeuchi conjecture since
ż
Σ
|f pςq|2 sup
l‖N pςq
Xwplqdσpςq ď
ˆż
Σ
|f pςq|2dσpςq
 ̇
sup
ς PΣ
sup
l‖N pςq
Xwplqdσpςq “ }f }2
L2pΣ;dσq }X w}L8
Thus, Theorem 1.2 implies that Stein’s conjecture is false as stated in Conjecture 1.4.
1.3. The Kakeya Maximal Conjecture and the Restriction Conjecture. The counterexample is also interesting because, assuming the Kakeya maximal conjecture, Stein’s conjecture would imply the restriction conjecture ([BGNO24]). Consider a Kakeya-type maximal operator M defined on suitably regular weights w : Rn Ñ Rě0 by
Mwpωq “ sup
T ‖ω
ż
T
w, ω P Sn ́1


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 3
where T an infinitely long tube of width 1. We denote the local maximal function by MRw “ Mpw|BR q. Note that MR is equivalent to the standard Kakeya maximal operator, upon a rescaling. As such, MR is expected to satisfy the estimate
}MR}LnpRnqÑLnpSn ́1q Àε Rε (1.3)
which is equivalent to the Kakeya maximal conjecture. To see how this is related to the restriction conjecture, take some f P L 2n
n ́1 pΣq and note that
}Ef }2
L
2n
n ́1 “ sup
wPLn pRn q
}w} ́1
Ln
ż
Rd
|Ef |2 pxqwpxqdx
by Ho ̈lder’s inequality. If Stein’s conjecture were to hold, we have
}Ef }2
L
2n
n ́1 À sup
wPLnpRnq
ż
Σ
|f pξq|2MpNΣpξqqdσpξq
From here, if (1.3) holds, then the above implies
}Ef }L
2n
n ́1 pBRq Àε Rε }f }L
2n
n ́1 pΣq
if Σ has nonvanishing curvature. Note that the counterexample presented here only shows that Stein’s conjecture is false up to a logarithmic factor; if Stein’s conjecture were true locally, then the Kakeya maximal conjecture would still imply the restriction conjecture.
1.4. L2-wellposedness of first-order pertubations of the Schro ̈dinger equation. The historical value of the Mizohata-Takeuchi conjecture stems from its applications to the well-posedness of first-order pertubations of the Schr ̈odinger equation. Around 1980, Takeuchi ([Tak74],[Tak80]) was studying the Cauchy problem for operators of the form
Lpuq “ iBtu ` △u `
ÿn
j“1
bjBju ` cpxqu “ f (1.4)
The Cauchy problem for (1.4) is L2-wellposed if, given any u0 P L2pRnq and f P Ct0pL2pRnqq, there is a unique solution upx, tq to (1.4) for |t| ă T that satisfies the estimate
}up ̈, tq}L2 ÀT }u0}L2 `
ˇˇˇˇ
żt
0
}f p ̈, sq}L2 ds
ˇˇˇˇ (1.5)
Takeuchi ([Tak74; Tak80]) claimed that a sufficient condition for (1.5) to hold is the following:
Re
 ̃ż t
0
ÿn
j“1
bjpx ` sνqνj ds
 ̧
À1
where the constant is independent of px, t, νq P Rn ˆ R ˆ Sn ́1. Later, Mizohata ([Miz85]) showed that Takeuchi’s argument had an error. It is well-known that the Cauchy problem for (1.4) is closely related to weighted L2 estimates of the form (1.1).


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 4
1.5. The intrinsic value of the Mizohata-Takeuchi Conjecture. Lastly, it is worthwhile to note that there is some intrinsic value in the Mizohata-Takeuchi conjecture. As noted in [CIW24], much of the development in Fourier restriction theory has centered around the Lp-Lq mapping properties of E, and the Mizohata-Takeuchi and Stein conjectures are some of the very few attempts to understand the shape of the level sets of Ef for various f : Σ Ñ C.
1.6. Progress on the Mizohata-Takeuchi Conjecture. In this section, we present a chronological overview of some important results in the direction of Conjecture 1.1. One of the first influential results was established by Barcelo ́, Ruiz, and Vega ([BRV97]) which demonstrated the radial case of the Mizohata-Takeuchi conjecture (see also [CRS92]). This was achieved by directly estimating Bessel functions and the extension operator on spherical harmonics. In 2009, Carbery ([Car09]) studied the nature of sets U Ă Rd where Xp1U q is small. In general, the study of tube-occupancy of sets is difficult, independently of weighted Fourier extension estimates (see [DZ24]). More recently, Shayya ([Sha23]) has studied the extent to which Mizohata-Takeuchi-type estimates can be derived from decay properties of dxσ in the plane. Another important recent development was by Ortiz ([Ort23]), in which the Mizohata-Takeuchi conjecture was proven with an R
1
4 `ε-loss for the cone in 3 dimensions. Probably the most influential recent development in the direction of the Mizohata-Takeuchi conjecture is a result by Carbery, Iliopoulou, and Wang ([CIW24]), in which several special cases (for the weight) were proven, as well as the general conjecture with R n ́1
n`1 `ε-loss. The approach was based on the refined decoupling estimates of Guth, Iosevich, Ou, and Wang ([GIOW20]). The R n ́1
n`1 -losses are especially relevant when placed in the context of a recent talk given by Guth ([Gut22]), in which he demonstrates that it is not possible to prove the Mizohata-Takeuchi conjecture without R n ́1
n`1 loss using only certain decoupling axioms. More recently, Bennett, Gutierrez, Nakamura, and Oliveira ([BGNO24]) have explored connections to time-frequency analysis and have proven a related Mizohata-Takeuchi-type inequality involving Sobolev norms.
1.7. Reformulations. In light of Theorem 1.2, the following local version may be a plausible reformulation of the Mizohata-Takeuchi conjecture.
Conjecture 1.5 (Local Mizohata-Takeuchi). Under the same hypotheses as Conjecture 1.1, we have ż
BR
|Ef pxq|2 wpxqdx Àε Rε }f }2
L2pΣ;dσq sup
lĂRd a line
ż
l
w
It is unclear whether one should expect Conjecture 1.5 to hold, or to expect an R n ́1
n`1 -loss counterexample in the spirit of Guth’s argument ([Gut22]).
1.8. Outline of this paper. We begin in Section 2 by proving L2-based estimates on the X-Ray transform for positive measures. We then discuss how this can be used to formulate a weaker version of the Mizohata-Takeuchi conjecture on the Fourier side in Section 3. The construction relies on an incidence geometry Lemma, which is proven separately in Section 4.
1.9. Acknowledgments. The author would like to express her gratitude to her advisor, Ruixiang Zhang, for his generous introduction to the beautiful theory of Fourier restriction, as well as for pointing out the Mizohata-Takeuchi conjecture and reviewing earlier versions of this paper.


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 5
2. X-Ray transform estimates for positive measures
Let ν P Sd ́1. For any weight w : Rn Ñ r0, 8q, we define Xνwpzq “ ş
Rν`z w for any z P νK. For
any function μ : Rn Ñ C so that μ restricts to an Lp function on every plane perpendicular to ν, we define the restriction map Pν μ : R Ñ LppνKq by Pν μpλqpωq “ μpλν ` ωq. In this section, we prove
Theorem 2.1. Let h : Rn Ñ C be so that |ˆh|2 “ w, for a nonnegative weight w : Rn Ñ r0, 8q. Then we have the estimate
}Xν w}Lp ď ››Pν h››2
L2pLqpνKqq (2.1)
for p P r1, 8s and q “ 2p
2p ́1 . In particular, when p “ 8 we have the estimate
}Xν w}L8 ď ››Pν h››2
L2pL1pνKqq
and in this case, the estimate is sharp when h ě 0 everywhere.
Proof. The proof is relatively straightforward, once we digest the meaning of the norm appearing on the right of (2.1). We write
}Pν hpλq}LqpνKq “
ˆż
νK
|hpλν ` ωq|q
 ̇
1 q
Thus,
››Pν h››L2pLqpνKqq “
 ̃ż
R
ˆż
νK
|hpλν ` ωq|q
 ̇
2 q
 ̧
1 2
We note that Xνw “ Pνw { ˇp0q by the projection-slice theorem. We note that
Pν wˇp0q “ Pν ph  ̊  ̃ˆhqp0q “
ż
R
Pνhpλq  ̊ Pν h Čpλq
where μ ̃ denotes μ  ̋ px ÞÑ  ́xq for any function μ. Therefore, we have
Xνwpzq “
ż
R
ˇˇˇPν h {pλqpzq
ˇˇˇ
2
dλ
Minkowski’s inequality gives
}Xν w}LppνKq ď
ż
R
›››Ppν hpλq
›››
2
L2p pν K q
Applying Hausdorff-Young yields (2.1). Note that, if h ě 0 everywhere and p “ 8, then both Minkowski’s inequality and Hausdorff-Young are sharp.
3. The proof of Theorem 1.2
This section is divided into four parts:
3.1. We discuss some preliminary estimates. This part is primarily devoted to posing similar problems of Mizohata-Takeuchi-type on the Fourier side. 3.2. We present a “white lie” proof of Theorem 1.2 to help the reader understand the important points. 3.3. We explain briefly an incidence lemma, which we prove in section 4. 3.4. We present a rigorous proof of Theorem 1.2.


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 6
3.1. Some preliminaries. Let w : BR Ñ r0, 8q be a nonnegative weight. As [CIW24] notes, we are free to assume that w is locally constant at scale 1, and so w satisfies the necessary regularity conditions discussed in the previous section. We are interested in the quantity Ewpf, gq : L2pΣ; dσqˆ L2pΣ; dσq Ñ C given below.
Ewpf, gq :“
ż
Rd
Ef pxqEgpxqwpxqdx “
A w
1
2 Ef dσ, w 1
2 Egdσ
E
We should think of Ew as a quadratic form on the Hilbert space L2pΣ; dsq. The Mizohata-Takeuchi conjecture seeks an upper bound on the largest eigenvalue of Ew in terms of }Xw}L8 .
As in the previous section, let h : Rn Ñ C so that
ˇˇˇˆhpxq
ˇˇˇ
2
“ wpxq. We write
Ewpf, gq “ xh  ̊ f dσ, h  ̊ gdσy
In particular, we note Ewpf, f q “ }h  ̊ f dσ}2
L2. Therefore, to prove Theorem 1.2, it suffices to prove
the following.
Proposition 3.1. For any C2 hypersurface Σ Ă Rd, there exists for each R ě 1, a function
f P L2pΣ; dσq and a function h : Rd Ñ C with ˆh Ă BR, so that the following holds.
}h  ̊ f dσ}2
L2 Á log R }f }2
L2pΣ;dσq
››Pν h››2
L2 pL1 pν K qq
for every ν P Sd ́1
In light of Proposition 3.1, we are led to consider partial progress towards Conjecture 1.5 in the following form.
Conjecture 3.2. For any C2 hypersurface Σ Ă Rd with surface measure dσ and any functions
f P L2pΣ; dσq and h : Rd Ñ C with ˆh Ă BR, the following holds
}h  ̊ f dσ}2
L2 Àε Rε }f }2
L2pΣ;dσq
››Pν h››2
L2 pL1 pν K qq
for every ν P Sd ́1
To help the reader understand the construction of the counterexample, we present first a “white lie” version.
3.2. A white lie construction. Throughout this section, we use A « B to mean that A and B are essentially equal, in the sense that B is a suitable approximation of A in some sense that we will formalize in a later section. The reader may feel free to assume A “ B when verifying estimates, even though A “ B is generally false. The point of this notation is to avoid excess detail at the expense of rigor. Let ξ1,  ̈  ̈  ̈ , ξN Ă Σ be a R ́1-separated collection of N „ log R points in Σ. We will choose the
ξi later on. Let us set Si “
›››1BR ́1 pξiqXΣ
››› ́1
L1pΣ;dσq 1BRpξiqXΣdσ and
f“
N ÿ
i“1
Si.
We record the following for future use:
R ́d`1 }f }2
L2pΣ;dσq „ }f }L1pΣ;dσq „ N (3.1)


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 7
The key step is the construction of the following lattice:
Q“
"
~c  ̈ ξ~ : ~c P t0, 1uN , c1 `  ̈  ̈  ̈ ` cN “
ZN
2
^*
Here, ~c  ̈ ξ~ denotes c1ξ1 `  ̈  ̈  ̈ ` cN ξN by abuse of notation. We now define
h “ Rd ÿ
qPQ
1BR ́1 pqq (3.2)
Note that |Q| “ `tNN
2u
 ̆ „ N ́1
2 2N by Stirling’s approximation for the factorial.
The choice of scale R ́1 reflects the locally constant principle:
White Lie 3.3. We have supppˆhq Ă BpRq.
We would like a lower bound on }f dσ  ̊ h}2
L2. The operation h ÞÑ f dσ  ̊ h sends each ball in (3.2) to the sum of the translations of that ball by each of ξ1,  ̈  ̈  ̈ , ξN . We will need an estimate of the following type.
White Lie 3.4. We have Spξiq  ̊ 1BpR ́1q « Rd1Bpξi,R ́1q
With this, we are free to write
h ̊f «
N ÿ
i“1
ÿ
qPQ
Rd1Bpξi`q,R ́1q (3.3)
Now, note that ě 1
2 of the possible values of ξi ` q satisfy ci “ 0, if q “ ~c  ̈ ξ~. Therefore, at least 1
2
of the values of ξi ` q will lie in the lattice
Q1 “
"
~c  ̈ ξ~ : ~c P t0, 1uN , c1 `  ̈  ̈  ̈ ` cN “
ZN
2
^
`1
* ,
which is a set of size at most `t NN
2 u`1
 ̆ „ |Q|. Since there are a total of N |Q| balls in (3.3), where
each ball has an L2 norm of R d
2 , we have
}h  ̊ f }2
L2 Á N 2|Q|Rd (3.4)
We would now like to estimate ››Pν h››2
L2pL1pνKqq. We recall
››Pν h››2
L2pL1pνKqq :“
ż
R
}Pν hpλq}2
L1 dλ
Let Kνpλq denote the number of balls in the definition (3.2) of h that pass through the plane λν `νK, so that }Pνhpλq}L1 À KνpλqR. We deduce that }Pνhpλq}2
L1 À R2 }Kν }2
L2 . We use }Kν }L1 „ R ́12N to obtain
}Pν hpλq}2
L1 À }Kν }L1 }Kν }L8 „ R2N }Kν }L8 (3.5)
Combining (3.1), (3.4), and (3.5), we obtain
}h  ̊ f dσ}2
L2 }Kν }L8 Á N }f }2
L2 }Pν hpλq}2
L1
We will show that }Kν}L8 À 1 for every ν, for some choice of tξ1,  ̈  ̈  ̈ , ξN u in Lemma 3.5 below,
i.e. no plane passes through more than „ 1 balls in the definition (3.2) of h. The “white-lie” proof is now complete, contingent upon the following lemma.


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 8
3.3. An incidence geometry lemma.
Lemma 3.5. For any R ą 1 sufficiently large, there exists
 ̋ A point ξ0 P Σ  ̋ A set of N „ log R points tξ1,  ̈  ̈  ̈ , ξN u Ă Σ so that the following conditions are met.
(i) No plane passes through more than 2d ́1 balls in the collection of balls of radius R ́1 around the points c1pξ1  ́ ξ0q `  ̈  ̈  ̈ ` cN pξ1  ́ ξ0q for ~c P t0, 1uN . (ii) We have |ξm  ́ ξn| ą R ́1 for every pm, nq P rN s2.
We note that Q is a translate of tc1pξ1  ́ ξ0q `  ̈  ̈  ̈ ` cN pξ1  ́ ξ0q : ~c P t0, 1uN , řN
i“1 ci “ X N
2
\u and so the point ξ0 does not affect our estimates. The proof of this Lemma is rather involved and may be of independent interest. We postpone the proof to Section 4.
3.4. A rigorous proof of Proposition 3.1. We now present a rigorous proof of Proposition 3.1 by the means described in Section 3.2. Let ξ1,  ̈  ̈  ̈ , ξN with N „ log R be a collection of points that satisfy the conclusion of Lemma 3.5. Let η be so that ηˆ is a smooth cutoff function with 1BpC ́1q ď ηˆ ď 1BpCq for some constant C ą 1 to be determined later, so that ηˆ is supported in a ball of radius „ 1; let ηRpξq “ RdηpRξq be a rapidly decaying kernel at scale R ́1. For convenience, we assume that η is radially symmetric. We set
h0 “ ÿ
pPQ
δp,
and choose h “ h0  ̊ ηR so that ˆh Ă BCR. Note that }h0}L1 „ }h}L1 „ |Q| and }h}2
L2 „ |Q|Rd.
We set fi “ ř
i Si as in the previous section. We would like to show the following estimate.
}f dσ  ̊ h}2
L2 “ }f dσ  ̊ h0  ̊ ηR}2
L2 Á N 2|Q|Rd (3.6)
We have
}f  ̊ h0  ̊ ηR}2
L2 “
ż
ΣˆΣ
N ÿ
i,j“1
ÿ
q,q1 PQ
SipςqSjpς1qrηR  ̊ ηRspς  ́ ς1 ` q  ́ q1qdσpςqdσpς1q (3.7)
Note that ηR  ̊ ηR “ pηxRq2 is another rapidly decaying kernel at scale R ́1. We morally have ηR  ̊ ηR À 1B2R ́1 but the honest kernel has rapidly decaying oscillatory tails. If we set
H“
N ÿ
i,j“1
ÿ
q,q1 PQ
δξi ́ξj `q ́q1  ̊ Tij
where Tijpξj  ́ ξi ` ζq “ Si  ̊ S ̃jpζq, then we can rewrite (3.7) as
}f  ̊ h0  ̊ ηR}2
L2 “ xH, ηR  ̊ ηRy,
Note that if q, ξi, and ξj are randomly chosen, then there is a ě 1
4 probability that q ` ξi  ́ ξj will
lie in Q. Therefore, we deduce ż
BR ́1 p0q
H Á N 2|Q| (3.8)
Now, note that we can deduce that that points in Q are separated by at least R ́1 from Lemma 3.5, in the sense that every R ́1-ball contains À 1 of the points (in fact, their ν-projections


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 9
are separated). Since }Tij}L1 „ 1, Tij is nonnegative, and Tij is supported in B2R ́1p0q, we deduce
that ż
BR ́1 pζq
H À N 2|Q|. (3.9)
for any ζ P Rd. Combining (3.8) and (3.9), we conclude that (3.6) holds for a suitable choice of η so that η  ̊ η ě
B1p0q and ş
Rd pη  ̊ ηq ́ ă c for some sufficiently small c (here, η  ̊ η “ pη  ̊ ηq`  ́ pη  ̊ ηq ́ is a difference of nonnegative functions).
To estimate ››Pν h››2
L2pL1pνKqq, we note that the method from Section 3.2 must be modified slightly, since η has a rapidly decaying tail, and therefore we expect some interference between the different “layers” of Q. More concretely, we write
}Pν hpλq}L1 À
ż
R
Kν pλ1qμRpλ  ́ λ1qdλ1 “ Kν  ̊ μRpλq
where Kν is defined as in Section 3.2 and μRpλq “ RμpRλq is some rapidly decaying smooth kernel at scale R ́1. We write
}Pν h}2
L2pL1pνKqq À }RKν  ̊ μR}2
L2
ďR2 }Kν }L1 }Kν}L8 }μR}2
L1
ÀR2 }Kν }L1 }Kν}L8
ÀR|Q|
This completes the proof.
4. The proof of Lemma 3.5
Let Σ Ă Rd be a compact C2 hypersurface that is not a subset of a plane. We will see in section 4.4 that Lemma 3.5 will follow easily from the following Lemma.
Lemma 4.1. For any R ą 1 sufficiently large, there exists
 ̋ A point ξ0 P Σ  ̋ A set of N „ log R points tξ1,  ̈  ̈  ̈ , ξN u Ă Σ so that the following conditions are met.
(i) For any direction ν P Sd ́1, the ν-projections of the differences ξm  ́ ξ1 lie in nearly distinct dyadic intervals; that is, if un denotes the part of the partition U1p1q that contains log2p|πν pξn  ́ ξ0q|q, then we have
um “ un and m ą n ùñ n P Sν (4.1)
where Sν is called the set of bad values of n. The size of S is at most d  ́ 1. (ii) We have |ξm  ́ ξn| ą R ́1 for every pm, nq P t1, N u2.
Remark 4.2. It is much easier to see that the lemma is true if we are allowed to choose different ξn for different ν; since Σ does not lie in a hyperplane, it cannot project to a point, so πνpΣq must contain some line segment from which we can choose ξn dyadically.
Before proving Lemma 4.1, we explain the main ideas. First, the condition that Σ is a hypersurface is not necessary as long as we assume that it does not project to a point and is C2. We will also see that higher order corrections do not play an important role in the proof, so we might as


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 10
well assume that Σ is smooth. In this case, the desirable region of Σ is best approximated by the moment curve Md.
Mdptq “ pt, t2,  ̈  ̈  ̈ , tdq (4.2)
That is, we should be able to construct ξn « Mdptnq for a nice choice of tn and most of the Mdptnq will nearly lie in Σ. Note that if ν “ pν1,  ̈  ̈  ̈ , νdq was close to p1,  ̈  ̈  ̈ , 0q, say |ν1| ą c ą 0, then the projection πν pMdptqq would look like a line near t “ 0. Motivated by this, we might decide to set tn “ 2 ́n dyadically. This also works well if, e.g., ν “ p0, 1,  ̈  ̈  ̈ , 0q because then πν pMdptnqq „ 2 ́2n. It is remarkably harder to prove that the estimates are uniform over all possible choice of lines. It is, in general, difficult to work with neighborhoods of the projections πν pMdptnqq and it is usually preferable to work with neighborhoods of tn prior to projection. We might try setting Bn “ BpMdptnq, 2|Mdptn ́1q|q so that 0 R πν pBnq implies that πν pMdptnqq lies in a dyadic interval higher than Mdp|tn ́1|q, and therefore higher than πν pMdptn ́1qq. The advantage here is that the
problem reduces to showing something about how many balls lie on a hyperplane νK through the origin, which seems much more tractable. Unfortunately, this approach fails. To see why, let us choose tn “ c ́n for some c ą 1, and set d “ 2 for definiteness, so that the Bn are balls of radius „ c ́1|tn| “ c ́1 ́n. If we choose ν “ p0, 1q, then the Bn project to segments of length „ c ́1 ́n a distance „ c ́2n away from 0. As n gets large, these segments will overlap a lot because the lengths do not decay fast enough. In light of the above setback, we might be temped to choose the Bn to be rectangles instead. If we set Un “ tn ` r ́2c ́1 ́n, 2c ́1 ́ns ˆ r ́2c ́2 ́2n, 2c ́2 ́2ns, then we might hope that πν pUnq contains the origin when πν ptnq does not lie in a dyadic interval higher than πν ptn ́kq. That is,
if πν ptnq
πνptn ́kq P r ́2, 2s for some k ą 1, we would like to see if 0 P πν pUnq. If πν ptnq “ απν ptn ́kq for some α P r ́2, 2s, then we would like to show that tn  ́ αtn ́k P Un because we know that πν ptn  ́ αtn ́kq “ 0. As it turns out, it is not hard to verify that tn  ́ αtn ́k P Un from the definition of Un. When d ą 2, the main idea of the proof is to use a projection φ : Rd Ñ Rd ́1 to induct on d. We define φ below.
φpx1,  ̈  ̈  ̈ , xdq “ px2,  ̈  ̈  ̈ , xdq
x1
(4.3)
We will see that φ is useful because it reduces the dimension by 1 and it sends hyperplanes in Rd to (affine) hyperplanes in Rd ́1. This is the point where the choice (4.2) of the moment curve is essential because φ  ̋ Md “ Md ́1. After suitably defining the rectangles Und in dimension d ą 2, we will note that 0 P πν
`Und
 ̆ is equivalent to the statement that the hyperplane νK that contains 0 also passes through some point of Und. This will then imply that φpνKq meets some point of φpUndq.
However, φpνKq is just a hyperplane in Rd ́1 and we will see that φpUndq is very close to Un,d ́1 and so the problem reduces to a d  ́ 1-dimensional problem. There is one more complication which arises, namely that after applying φ, we are dealing with hyperplanes in general position. Before applying φ, we were only dealing with hyperplanes through the origin.1 To remedy this, consider fixing a scale dn „ |tn| for some n. Note that either φpνKq will be very far away from the origin, it will be very close to the origin, or it will be a moderate distance away from the origin. If φpνKq is very far from the origin at scale dn, then there is no risk of φpνKq passing through φpUndq. On the other hand, if φpνKq is very close to the origin at scale dn,
1It is notable that this is the only reason that the number of “bad” n, i.e. the constant in (4.1), is dependent on d.


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 11
then we might as well assume that it meets the origin, in which case we have reduced the problem completely to the n  ́ 1-dimensional case. For the third case, namely that the distance from φpνKq to the origin is the same scale as dn, we are truly without hope. Luckily, it is not possible for very many tn to meet this fate since there are not many scales dn that are close to the distant from φpνKq to the origin. In view of the principles above, we are ready to formalize the proof.
4.3. The proof of Lemma 4.1. We divide the proof into two lemmas. Lemma 4.3 is the main argument for the moment curve and Lemma 4.4 proves that Lemma 4.1 for an arbitrary curved C2 hypersurface Σ reduces to the moment-curve case. Recall the definition of the moment curve.
Mdptq “ pt, t2,  ̈  ̈  ̈ , tdq (4.2)
For any c ą 1, we set tc,n “ c ́n and xc,n “ Mdptc,nq. Throughout the proof, we will use the rescaling symmetry of the moment curve.
Mdpc ́1tq “ Lc  ̋ Mdptq
Here, Lcpxq is the entry-wise multiplication of x by Mdpc ́1q. Notably, we have
Lcpxc,nq “ Lcpxc,n`1q
We also recall the definition of φ : Rd.
φpx1,  ̈  ̈  ̈ , xdq “ px2,  ̈  ̈  ̈ , xdq
x1
(4.3)
At the core of the argument is the fact that φ and Lc commute:
φ  ̋ Lc “ Lc  ̋ φ
Here, we written Lc for the corresponding scaling in Rd ́1 by abuse of notation. In fact, by a similar abuse of notation, all of Lc, M, and φ mutually commute. Given any vector v, let us denote by Qpvq the axially-oriented rectangular box centered at the origin, whose dimensions are encoded in the entries of the vector 2v. We should imagine v as a corner of the box. We now define the boxes U d
b,c,n, where b ą 1 will be fixed later.
Ud
b,c,n “ xc,n ` QpMdpbtc,n`1qq (4.4)
In the notes following Remark 4.2, we took b “ 2. To digest (4.4), recall that we are looking for the smallest box so that translations xc,n ` αxc,k remain in the box, for suitably defined α. Since Q commutes with axial rescaling, the boxes U d
b,c,n are related by Lc.
LcpU d
b,c,nq “ U d
b,c,n`1 (4.5)
We are now ready to state and prove the following lemma.
Lemma 4.3. Let d be arbitrary. For c " b " 1 sufficiently large, we have the following.
(i) For any direction ν P Sd ́1 and any pn, kq P Z2 with n ă k, the projections πν
 ́
Ud
b,c,n
 ̄
and
πν
 ́
Ud
b,c,k
 ̄
do not overlap unless n P Sν. Here, Sν is called the set of bad n and |Sν| ď d ́1.
(ii) In particular, the values of logc πν pcc,nq are distinct, except for a set of as most d ́1 choices of n.


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 12
Proof. The proof is by induction on d. Note that the d “ 1 case is trivial. The first step is to note that πν
 ́
Ud
b,c,n
 ̄
and πν
 ́
Ud
b,c,k
 ̄
overlap iff νK passes through a point
of U d
b,c,n  ́ U d
b,c,k. Note that all of the boxes QpMdpbtc,k`1qq in the definition (4.4) of U d
b,c,n will fit inside QpMdpbtc,n`1qq. The points xc,k also fit inside this box, so we deduce the following.
Ud
b,c,n  ́ U d
b,c,k Ă U d
b1,c,n
Here, b1 „ b is some other scale. Therefore, it suffices to construct a set Sν of bad points so that for n R Sν, the hyperplane νK will not meet U d
b1,c,n. This is equivalent to proving that φpνKq does not meet φpU d
b1,c,nq because φpU d
b1,c,nq is well-defined if c ą b1. We observe that (4.5) in dimension d  ́ 1 implies the following:
φpU d
b1,c,nq “ Ln
c pφpU d
b1,c,1qq (4.6)
Note that φpU d
b1,c,1q fits inside a box U d ́1
b2,c,1 for some b2 „ b1 now that we are at scale b1 ˆ  ̈  ̈  ̈ ˆ b1. By (4.5) in dimension d with (4.6), we deduce that the box construction of U nearly commutes with φ. That is,
φpU d
b1,c,nq Ă U d ́1
b2,c,n
Therefore, it suffices to show that φpνKq does not meet more than d  ́ 1 of the boxes U d ́1
b2 ,c,n .
We would be done by the induction hypothesis if φpνKq were to pass through the origin, so we assume that 0 R φpνKq. Consider boxes QpMd ́1pb3tc,m`1qq and take m0 to be maximal so that φpνKq contains a point l inside such a box. Here, b3 „ b2 is so that the boxes U d ́1
b2,c,k lie in
QpMd ́1pb3tc,m`1qq for k ą m ` 1. We observe that, for n ą m0 ` 1, the hyperplane φpνKq does not meet U d ́1
b2,c,n by maximality of m0.
If n “ m0 ` 1, then it does not matter if φpνKq meets U d ́1
b2,c,n if we can show that at most d  ́ 2
of the values n ă m0 are bad. If n ă m0 ` 1, we observe that φpνKq “ l ` ν2K, where ν2 is perpendicular to φpνKq. Thus, it
suffices to show that no more than d  ́ 2 of the translated boxes U d ́1
b2,c,n  ́ l meet ν2K. However,
since l P QpMd ́1pb3tc,m`1qq, we deduce that U d ́1
b2,c,n  ́ l Ă U d ́1
b4,c,n for some b4 „ b2. Our inductive
hypothesis then implies that at most d  ́ 2 of the boxes U d ́1
b4,c,n meet ν2K. This completes the
proof.
We are now ready to handle the general case of a curved C2 hypersurface Σ. We assume that Σ is given near ξ “ 0 as the graph of a C2 function Φ : Rd ́1 Ñ R. We write
Φpωq “ Cpω, ωq ` op|ω2|q (4.7)
where C is some quadratic form. We assume additionally that the largest-magnitude eigenvalue of C corresponds to an eigenvector pointing in the η1 “ p1, 0,  ̈  ̈  ̈ , 0q direction. It is also convenient to assume by rescaling that Cpη1, η1q “ 1. We will now set
ωn “ pc ́n, c ́3n, c ́4n,  ̈  ̈  ̈ , c ́dnq
for some c ą 1. We set ξn “ Φpωnq. We are now ready to prove Lemma 4.1 for Σ.
Lemma 4.4. For sufficiently large n ą 0, each ξn as defined above lies in the box U d
b,c,n for some choice of b, c consistent with Lemma 4.3.


 A COUNTEREXAMPLE TO THE MIZOHATA-TAKEUCHI CONJECTURE 13
Proof. Suppose we set M ̃ dptq “ Φpt, t3, t4,  ̈  ̈  ̈ , tdq so that ξn “ M ̃ dpc ́nq. Note that M ̃ dptq ́Mdptq lies entirely in the p0, 1,  ̈  ̈  ̈ , 0q-direction, so it suffices to prove that this difference lies within the p0, 1,  ̈  ̈  ̈ , 0q-width of U d
b,c,n. Recall that this width is Op|t2|q, so it suffices to show that
M ̃ dptq  ́ Mdptq “ op|t2|q
However, we have
Bppt, 0,  ̈  ̈  ̈ , 0q, pt, 0,  ̈  ̈  ̈ , 0qq “ t2
and
|p0, t3, t4,  ̈  ̈  ̈ , tdq| “ Op|t|3q
Since the derivative of ω Ñ Bpω, ωq tends to zero as ω Ñ 0, we conclude that
Bppt, t3, t4,  ̈  ̈  ̈ , tdq, pt, t3, t4,  ̈  ̈  ̈ , tdqq “ Bppt, 0,  ̈  ̈  ̈ , 0q, pt, 0,  ̈  ̈  ̈ , 0qq ` op|t|3q “ t2 ` op|t|2q
by writing pt, t3, t4,  ̈  ̈  ̈ , tdq “ pt, 0,  ̈  ̈  ̈ , 0q ` p0, t3, t4,  ̈  ̈  ̈ , tdq. This completes the proof upon applying (4.7).
To finish the proof of Lemma 4.1, note that we can relabel the ξn to assume that n is sufficiently large. The pigeonholing condition (4.1) is then satisfied by choosing c sufficiently large. The only step left is then proving that R ́1 „ R ́1. The smallest separation between two values of ξn will occur when n reaches its maximum, i.e. n „ N . In particular, the minimum separation is Á |tN | „ c ́N . We can ensure that c ́N „ R ́1 by choosing the right constant in N „ log R.
Remark 4.5. There is actually another proof of Lemma 4.1 that relies on a polynomial-partitioning technique. Instead of inducting on the dimension d, one can project the moment curve onto a line to obtain a polynomial whose coefficients are suitably bounded on both sides. The problem then reduces to a problem about the shape of sets where the polynomial and its derivatives have certain signs. However, this polynomial-based approach requires some delicate estimates on the shapes of these sets and how these shapes interact with the corresponding shapes for its derivative. It is also very difficult to yield the sharp estimate of d  ́ 1 for the number of bad points using this approach, and it is unclear how to construct the sharp examples for ν. It is for these reasons that the approach included is preferred.
4.4. The proof of Lemma 3.5 using Lemma 4.1. To prove the plane condition Lemma 3.5 (i), it suffices to show that the projections πν
 ́
~c  ̈ ξ~
 ̄
are distinct at scale R ́1. Note that, even though
Lemma 4.1 gave only distinct values of log2 ξi, we can easily guarantee logK ξi for any K ą 0 using
only every log2pKqth value of ξi. Let us fix ~c1 P t0, 1uN . If
ˇˇˇπν
 ́
~c  ̈ ξ~
 ̄
 ́ πν
 ́
~c1  ̈ ξ~
 ̄ˇˇˇ ď R ́1 (4.8)
holds for more than 2d ́1 values of ~c, then (4.8) holds for at least one ~c1 so that c1m ‰ cm for some
m R Sν, that is, m is not a bad value, and c1n “ cn for all n P Sν. Let us assume that m is the value in t1,  ̈  ̈  ̈ , N u where πν pξm  ́ ξ0q is maximized. Next, note that since the values of πν pξk  ́ 0q lie in distinct logarithmic intervals of the form rα, αKs, we deduce that |πν pξm  ́ ξ0q | is more than twice the sum of all |πν pξk  ́ ξ0q | for k with ck ‰ c1k. This contradicts (4.8) by the triangle inequality
applied to ř
l  ̆πν pξl  ́ ξ0q, where the sum is over all values of l where cl ‰ c1l.


 REFERENCES 14
References
[BBC08] Juan Antonio Barcelo ́, Jonathan Bennett, and Anthony Carbery. “A note on localised weighted inequalities for the extension operator”. In: Journal of the Australian Mathematical Society 84.3 (2008), pp. 289–299. [BCSV06] Jonathan Bennett, Anthony Carbery, Fernando Soria, and Ana Vargas. “A Stein conjecture for the circle”. In: Mathematische Annalen 336 (2006), pp. 671–695. [BCT06] Jonathan Bennett, Anthony Carbery, and Terence Tao. “On the multilinear restriction and Kakeya conjectures”. In: Acta Mathematica 196.2 (Jan. 2006), pp. 261–302. doi: 10.1007/s11511-006-0006-4.
[BGNO24] Jonathan Bennett, Susana Gutierrez, Shohei Nakamura, and Itamar Oliveira. “A phasespace approach to weighted Fourier extension inequalities”. In: arXiv preprint arXiv:2406.14886 (2024). url: https://arxiv.org/pdf/2406.14886.
[BN21] Jonathan Bennett and Shohei Nakamura. “Tomography bounds for the Fourier extension operator and applications”. In: Mathematische Annalen 380 (2021), pp. 119–159. url: https://arxiv.org/pdf/2001.01674.
[BRV97] Juan Antonio Barcelo ́, Alberto Ruiz, and Luis Vega. “Weighted estimates for the Helmholtz equation and some applications”. In: journal of functional analysis 150.2 (1997), pp. 356–382. [Car09] Anthony Carbery. “Large sets with limited tube occupancy”. In: Journal of the London
Mathematical Society 79.2 (2009), pp. 529–543. doi: https://doi.org/10.1112/jlms/jdn086. eprint: https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/jlms/jdn086. url: https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/jlms/jdn086. [CHV18] Anthony Carbery, Timo S Ha ̈nninen, and Stef ́an Ingi Valdimarsson. “Multilinear Duality and Factorisation for Brascamp-Lieb-type Inequalities with applications”. In: arXiv preprint arXiv:1809.02449 (2018).
[CHV23] Anthony Carbery, Timo S Ha ̈nninen, and Stef ́an Ingi Valdimarsson. “Disentanglement, multilinear duality and factorisation for nonpositive operators”. In: Analysis & PDE 16.2 (2023), pp. 511–543. url: https://arxiv.org/abs/2003.03326v2.
[CIW24] Anthony Carbery, Marina Iliopoulou, and Hong Wang. “Some sharp inequalities of Mizohata–Takeuchi-type.” In: Revista Mathematica Iberoamericana 40.4 (2024). url: https://arxiv.org/pdf/2302.11877.
[Cor77] Antonio Cordoba. “The Kakeya maximal function and the spherical summation multipliers”. In: American Journal of Mathematics 99.1 (1977), pp. 1–22. [CRS92] Anthony Carbery, Elena Romera, and Fernando Soria. “Radial weights and mixed norm inequalities for the disc multiplier”. In: Journal of functional analysis 109.1 (1992), pp. 52–75. [CS97a] Anthony Carbery and Fernando Soria. “Pointwise Fourier inversion and localisation in R n”. In: Journal of Fourier Analysis and Applications 3 (1997), pp. 847–858.
[CS97b] Anthony Carbery and Fernando Soria. “Sets of divergence for the localization problem for Fourier integrals”. In: Comptes Rendus de l’Acade ́mie des Sciences-Series IMathematics 325.12 (1997), pp. 1283–1286. [CSV07] Anthony Carbery, Fernando Soria, and Ana Vargas. “Localisation and weighted inequalities for spherical Fourier means”. In: Journal d’Analyse Mathe ́matique 103 (2007), pp. 133–156. [DZ24] Ciprian Demeter and Ruixiang Zhang. “On the N -set occupancy problem”. In: arXiv preprint arXiv:2403.10678 (2024).


 REFERENCES 15
[GIOW20] Larry Guth, Alex Iosevich, Yumeng Ou, and Hong Wang. “On Falconer’s distance set problem in the plane”. In: Inventiones mathematicae 219.3 (2020), pp. 779–830. [Gut10] Larry Guth. “The endpoint case of the Bennett–Carbery–Tao multilinear Kakeya conjecture”. In: Acta Mathematica 205.2 (Jan. 2010), pp. 263–286. doi: 10.1007/s11511-010-0055-6. url: https://arxiv.org/abs/0811.2251.
[Gut22] Larry Guth. “An enemy scenario in restriction theory”. In: joint talk for AIM Research Com- munity Fourier restriction conjecture and related problems and HAPPY network (2022). url: https://www.youtube.com/watch?v=x-DET83UjFg.
[Miz85] Sigeru Mizohata. On the Cauchy problem. Vol. 3. Academic Press, 1985. [Ort23] Alexander Ortiz. “A sharp weighted Fourier extension estimate for the cone in R3 based on circle tangencies”. In: arXiv preprint arXiv:2307.11731 (2023). url: https://arxiv.org/pdf/2307.1173 [Sha23] Bassam Shayya. “Mizohata–Takeuchi estimates in the plane”. In: Bulletin of the Lon
don Mathematical Society 55.5 (2023), pp. 2176–2194. url: https://arxiv.org/pdf/2208.10305. [Ste79] Elias M Stein. “Some problems in harmonic analysis”. In: Harmonic analysis in Euclidean spaces, Proceedings of the Symposium in Pure Mathematics of the Amer. Math. Soc., Williams College, Mass, Proc. Sympos. Pure Math., XXXV Part I, 1979. Amer. Math. Soc. 1979, pp. 3–20. [Tak74] Jiro Takeuchi. “A necessary condition for the well-posedness of the Cauchy problem for a certain class of evolution equations”. In: Proceedings of the Japan Academy 50.2 (1974), pp. 133–137. [Tak80] Jiro Takeuchi. “On the Cauchy problem for some non-kowalewskian equations with distinct characteristic roots”. In: Journal of Mathematics of Kyoto University 20.1 (1980), pp. 105–124. [Tao20] Terence Tao. “Sharp bounds for multilinear curved Kakeya, restriction and oscillatory integral estimates away from the endpoint”. In: Mathematika 66.2 (2020), pp. 517–576. url: https://arxiv.org/abs/1907.11342.
[WZ25] Hong Wang and Joshua Zahl. “Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions”. In: arXiv preprint arXiv:2502.17655 (2025).