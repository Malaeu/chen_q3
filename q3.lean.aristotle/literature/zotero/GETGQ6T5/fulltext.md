---
title: "The entropy formula for the Ricci flow and its geometric applications"
authors:
  - "Grisha Perelman"
date: "2002-11-11 2002-11-11"
publication: null
doi: "10.48550/arXiv.math/0211159"
url: "http://arxiv.org/abs/math/0211159"
zotero:
  attachment_key: "TKW493EZ"
  parent_key: "GETGQ6T5"
  item_id: 2256
  attachment_item_id: 2268
---

arXiv:math/0211159v1 [math.DG] 11 Nov 2002
The entropy formula for the Ricci flow
and its geometric applications
Grisha Perelman∗
November 26, 2024
Introduction
1. The Ricci flow equation, introduced by Richard Hamilton [H 1], is the evolution equation d
dt gij(t) = −2Rij for a riemannian metric gij(t). In his
seminal paper, Hamilton proved that this equation has a unique solution for a short time for an arbitrary (smooth) metric on a closed manifold. The evolution equation for the metric tensor implies the evolution equation for the curvature tensor of the form Rmt = △Rm + Q, where Q is a certain quadratic expression of the curvatures. In particular, the scalar curvature R satisfies Rt = △R + 2|Ric|2, so by the maximum principle its minimum is non-decreasing along the flow. By developing a maximum principle for tensors, Hamilton [H 1,H 2] proved that Ricci flow preserves the positivity of the Ricci tensor in dimension three and of the curvature operator in all dimensions; moreover, the eigenvalues of the Ricci tensor in dimension three and of the curvature operator in dimension four are getting pinched pointwisely as the curvature is getting large. This observation allowed him to prove the convergence results: the evolving metrics (on a closed manifold) of positive Ricci curvature in dimension three, or positive curvature operator
∗St.Petersburg branch of Steklov Mathematical Institute, Fontanka 27, St.Petersburg 191011, Russia. Email: perelman@pdmi.ras.ru or perelman@math.sunysb.edu ; I was partially supported by personal savings accumulated during my visits to the Courant Institute in the Fall of 1992, to the SUNY at Stony Brook in the Spring of 1993, and to the UC at Berkeley as a Miller Fellow in 1993-95. I’d like to thank everyone who worked to make those opportunities available to me.
1


 in dimension four converge, modulo scaling, to metrics of constant positive curvature. Without assumptions on curvature the long time behavior of the metric evolving by Ricci flow may be more complicated. In particular, as t approaches some finite time T, the curvatures may become arbitrarily large in some region while staying bounded in its complement. In such a case, it is useful to look at the blow up of the solution for t close to T at a point where curvature is large (the time is scaled with the same factor as the metric tensor). Hamilton [H 9] proved a convergence theorem , which implies that a subsequence of such scalings smoothly converges (modulo diffeomorphisms) to a complete solution to the Ricci flow whenever the curvatures of the scaled metrics are uniformly bounded (on some time interval), and their injectivity radii at the origin are bounded away from zero; moreover, if the size of the scaled time interval goes to infinity, then the limit solution is ancient, that is defined on a time interval of the form (−∞, T ). In general it may be hard to analyze an arbitrary ancient solution. However, Ivey [I] and Hamilton [H 4] proved that in dimension three, at the points where scalar curvature is large, the negative part of the curvature tensor is small compared to the scalar curvature, and therefore the blow-up limits have necessarily nonnegative sectional curvature. On the other hand, Hamilton [H 3] discovered a remarkable property of solutions with nonnegative curvature operator in arbitrary dimension, called a differential Harnack inequality, which allows, in particular, to compare the curvatures of the solution at different points and different times. These results lead Hamilton to certain conjectures on the structure of the blow-up limits in dimension three, see [H 4,§26]; the present work confirms them. The most natural way of forming a singularity in finite time is by pinching an (almost) round cylindrical neck. In this case it is natural to make a surgery by cutting open the neck and gluing small caps to each of the boundaries, and then to continue running the Ricci flow. The exact procedure was described by Hamilton [H 5] in the case of four-manifolds, satisfying certain curvature assumptions. He also expressed the hope that a similar procedure would work in the three dimensional case, without any a priory assumptions, and that after finite number of surgeries, the Ricci flow would exist for all time t → ∞, and be nonsingular, in the sense that the normalized curvatures
R ̃m(x, t) = tRm(x, t) would stay bounded. The topology of such nonsingular solutions was described by Hamilton [H 6] to the extent sufficient to make sure that no counterexample to the Thurston geometrization conjecture can
2


 occur among them. Thus, the implementation of Hamilton program would imply the geometrization conjecture for closed three-manifolds. In this paper we carry out some details of Hamilton program. The more technically complicated arguments, related to the surgery, will be discussed elsewhere. We have not been able to confirm Hamilton’s hope that the solution that exists for all time t → ∞ necessarily has bounded normalized curvature; still we are able to show that the region where this does not hold is locally collapsed with curvature bounded below; by our earlier (partly unpublished) work this is enough for topological conclusions. Our present work has also some applications to the Hamilton-Tian conjecture concerning K ̈ahler-Ricci flow on K ̈ahler manifolds with positive first Chern class; these will be discussed in a separate paper.
2. The Ricci flow has also been discussed in quantum field theory, as an approximation to the renormalization group (RG) flow for the two-dimensional nonlinear σ-model, see [Gaw,§3] and references therein. While my background in quantum physics is insufficient to discuss this on a technical level, I would like to speculate on the Wilsonian picture of the RG flow. In this picture, t corresponds to the scale parameter; the larger is t, the larger is the distance scale and the smaller is the energy scale; to compute something on a lower energy scale one has to average the contributions of the degrees of freedom, corresponding to the higher energy scale. In other words, decreasing of t should correspond to looking at our Space through a microscope with higher resolution, where Space is now described not by some (riemannian or any other) metric, but by an hierarchy of riemannian metrics, connected by the Ricci flow equation. Note that we have a paradox here: the regions that appear to be far from each other at larger distance scale may become close at smaller distance scale; moreover, if we allow Ricci flow through singularities, the regions that are in different connected components at larger distance scale may become neighboring when viewed through microscope. Anyway, this connection between the Ricci flow and the RG flow suggests that Ricci flow must be gradient-like; the present work confirms this expectation.
3. The paper is organized as follows. In §1 we explain why Ricci flow can be regarded as a gradient flow. In §2, 3 we prove that Ricci flow, considered as a dynamical system on the space of riemannian metrics modulo diffeomorphisms and scaling, has no nontrivial periodic orbits. The easy (and known)
3


 case of metrics with negative minimum of scalar curvature is treated in §2; the other case is dealt with in §3, using our main monotonicity formula (3.4) and the Gaussian logarithmic Sobolev inequality, due to L.Gross. In §4 we apply our monotonicity formula to prove that for a smooth solution on a finite time interval, the injectivity radius at each point is controlled by the curvatures at nearby points. This result removes the major stumbling block in Hamilton’s approach to geometrization. In §5 we give an interpretation of our monotonicity formula in terms of the entropy for certain canonical ensemble. In §6 we try to interpret the formal expressions , arising in the study of the Ricci flow, as the natural geometric quantities for a certain Riemannian manifold of potentially infinite dimension. The Bishop-Gromov relative volume comparison theorem for this particular manifold can in turn be interpreted as another monotonicity formula for the Ricci flow. This formula is rigorously proved in §7; it may be more useful than the first one in local considerations. In §8 it is applied to obtain the injectivity radius control under somewhat different assumptions than in §4. In §9 we consider one more way to localize the original monotonicity formula, this time using the differential Harnack inequality for the solutions of the conjugate heat equation, in the spirit of Li-Yau and Hamilton. The technique of §9 and the logarithmic Sobolev inequality are then used in §10 to show that Ricci flow can not quickly turn an almost euclidean region into a very curved one, no matter what happens far away. The results of sections 1 through 10 require no dimensional or curvature restrictions, and are not immediately related to Hamilton program for geometrization of three manifolds. The work on details of this program starts in §11, where we describe the ancient solutions with nonnegative curvature that may occur as blow-up limits of finite time singularities ( they must satisfy a certain noncollapsing assumption, which, in the interpretation of §5, corresponds to having bounded entropy). Then in §12 we describe the regions of high curvature under the assumption of almost nonnegative curvature, which is guaranteed to hold by the Hamilton and Ivey result, mentioned above. We also prove, under the same assumption, some results on the control of the curvatures forward and backward in time in terms of the curvature and volume at a given time in a given ball. Finally, in §13 we give a brief sketch of the proof of geometrization conjecture. The subsections marked by * contain historical remarks and references. See also [Cao-C] for a relatively recent survey on the Ricci flow.
4


 1 Ricci flow as a gradient flow
1.1. Consider the functional F = ∫
M (R + |∇f |2)e−f dV for a riemannian
metric gij and a function f on a closed manifold M. Its first variation can be expressed as follows:
δF (vij, h) =
∫
M
e−f [−△v + ∇i∇jvij − Rijvij
−vij∇if ∇jf + 2 < ∇f, ∇h > +(R + |∇f |2)(v/2 − h)]
=
∫
M
e−f [−vij (Rij + ∇i∇jf ) + (v/2 − h)(2△f − |∇f |2 + R)],
where δgij = vij, δf = h, v = gijvij. Notice that v/2 − h vanishes identically iff the measure dm = e−f dV is kept fixed. Therefore, the symmetric tensor −(Rij +∇i∇jf ) is the L2 gradient of the functional F m = ∫
M (R + |∇f |2)dm,
where now f denotes log(dV /dm). Thus given a measure m , we may consider the gradient flow (gij)t = −2(Rij + ∇i∇jf ) for F m. For general m this flow may not exist even for short time; however, when it exists, it is just the Ricci flow, modified by a diffeomorphism. The remarkable fact here is that different choices of m lead to the same flow, up to a diffeomorphism; that is, the choice of m is analogous to the choice of gauge.
1.2. Proposition. Suppose that the gradient flow for F m exists for t ∈ [0, T ]. Then at t = 0 we have F m ≤ n
2T
∫
M dm.
Proof. We may assume ∫
M dm = 1. The evolution equations for the
gradient flow of F m are
(gij)t = −2(Rij + ∇i∇jf ), ft = −R − △f, (1.1)
and F m satisfies
Ftm = 2
∫
|Rij + ∇i∇jf |2dm (1.2)
Modifying by an appropriate diffeomorphism, we get evolution equations
(gij)t = −2Rij, ft = −△f + |∇f |2 − R, (1.3)
5


 and retain (1.2) in the form
Ft = 2
∫
|Rij + ∇i∇jf |2e−f dV (1.4)
Now we compute
Ft ≥ 2
n
∫
(R + △f )2e−f dV ≥ 2
n(
∫
(R + △f )e−f dV )2 = 2
n F 2,
and the proposition follows. 1.3 Remark. The functional F m has a natural interpretation in terms of Bochner-Lichnerovicz formulas. The classical formulas of Bochner (for one-forms) and Lichnerovicz (for spinors) are ∇∗∇ui = (d∗d + dd∗)ui − Rijuj and ∇∗∇ψ = δ2ψ − 1/4Rψ. Here the operators ∇∗ , d∗ are defined using the riemannian volume form; this volume form is also implicitly used in the definition of the Dirac operator δ via the requirement δ∗ = δ. A routine computation shows that if we substitute dm = e−f dV for dV , we get modified Bochner-Lichnerovicz formulas ∇∗m∇ui = (d∗md + dd∗m)ui − Rimj uj
and ∇∗m∇ψ = (δm)2ψ − 1/4Rmψ, where δmψ = δψ − 1/2(∇f ) · ψ , Rimj =
Rij +∇i∇jf , Rm = 2△f −|∇f |2+R. Note that gijRimj = R+△f 6= Rm. How
ever, we do have the Bianchi identity ∇i∗mRimj = ∇iRimj −Rij ∇if = 1/2∇jRm.
Now F m = ∫
M Rmdm = ∫
M gijRimj dm.
1.4* The Ricci flow modified by a diffeomorphism was considered by DeTurck, who observed that by an appropriate choice of diffeomorphism one can turn the equation from weakly parabolic into strongly parabolic, thus considerably simplifying the proof of short time existence and uniqueness; a nice version of DeTurck trick can be found in [H 4,§6]. The functional F and its first variation formula can be found in the literature on the string theory, where it describes the low energy effective action; the function f is called dilaton field; see [D,§6] for instance. The Ricci tensor Rimj for a riemannian manifold with a smooth measure has been used by Bakry and Emery [B-Em]. See also a very recent paper [Lott].
2 No breathers theorem I
2.1. A metric gij(t) evolving by the Ricci flow is called a breather, if for some t1 < t2 and α > 0 the metrics αgij(t1) and gij(t2) differ only by a diffeomorphism; the cases α = 1, α < 1, α > 1 correspond to steady, shrinking and
6


 expanding breathers, respectively. Trivial breathers, for which the metrics gij(t1) and gij(t2) differ only by diffeomorphism and scaling for each pair of t1 and t2, are called Ricci solitons. (Thus, if one considers Ricci flow as a dynamical system on the space of riemannian metrics modulo diffeomorphism and scaling, then breathers and solitons correspond to periodic orbits and fixed points respectively). At each time the Ricci soliton metric satisfies an equation of the form Rij + cgij + ∇ibj + ∇jbi = 0, where c is a number and
bi is a one-form; in particular, when bi = 1
2 ∇ia for some function a on M, we
get a gradient Ricci soliton. An important example of a gradient shrinking soliton is the Gaussian soliton, for which the metric gij is just the euclidean metric on Rn, c = 1 and a = −|x|2/2. In this and the next section we use the gradient interpretation of the Ricci flow to rule out nontrivial breathers (on closed M). The argument in the steady case is pretty straightforward; the expanding case is a little bit more subtle, because our functional F is not scale invariant. The more difficult shrinking case is discussed in section 3.
2.2. Define λ(gij) = inf F (gij, f ), where infimum is taken over all smooth f, satisfying ∫
M e−f dV = 1. Clearly, λ(gij) is just the lowest eigenvalue of the
operator −4△+R. Then formula (1.4) implies that λ(gij(t)) is nondecreasing in t, and moreover, if λ(t1) = λ(t2), then for t ∈ [t1, t2] we have Rij +∇i∇jf = 0 for f which minimizes F . Thus a steady breather is necessarily a steady soliton.
2.3. To deal with the expanding case consider a scale invariant version
 ̄λ(gij) = λ(gij)V 2/n(gij). The nontrivial expanding breathers will be ruled out once we prove the following
Claim  ̄λ is nondecreasing along the Ricci flow whenever it is nonpositive; moreover, the monotonicity is strict unless we are on a gradient soliton.
(Indeed, on an expanding breather we would necessarily have dV /dt > 0 for some t∈[t1, t2]. On the other hand, for every t, − d
dt logV = 1
V
∫ RdV ≥
λ(t), so  ̄λ can not be nonnegative everywhere on [t1, t2], and the claim applies.)
Proof of the claim.
dλ ̄(t)/dt ≥ 2V 2/n ∫ |Rij + ∇i∇j f |2e−f dV + 2
n V (2−n)/nλ ∫ −RdV ≥
2V 2/n[∫ |Rij + ∇i∇jf − 1
n (R + △f )gij|2e−f dV +
1
n (∫ (R + △f )2e−f dV − (∫ (R + △f )e−f dV )2)] ≥ 0,
7


 where f is the minimizer for F .
2.4. The arguments above also show that there are no nontrivial (that is with non-constant Ricci curvature) steady or expanding Ricci solitons (on closed M). Indeed, the equality case in the chain of inequalities above requires that R+△f be constant on M; on the other hand, the Euler-Lagrange equation for the minimizer f is 2△f − |∇f |2 + R = const. Thus, △f − |∇f |2 = const = 0, because ∫ (△f − |∇f |2)e−f dV = 0. Therefore, f is constant by the maximum principle.
2.5*. A similar, but simpler proof of the results in this section, follows im
mediately from [H 6,§2], where Hamilton checks that the minimum of RV 2
n
is nondecreasing whenever it is nonpositive, and monotonicity is strict unless the metric has constant Ricci curvature.
3 No breathers theorem II
3.1. In order to handle the shrinking case when λ > 0, we need to replace our functional F by its generalization, which contains explicit insertions of the scale parameter, to be denoted by τ. Thus consider the functional
W(gij, f, τ ) =
∫
M
[τ (|∇f |2 + R) + f − n](4πτ )− n
2 e−f dV , (3.1)
restricted to f satisfying
∫
M
(4πτ )− n
2 e−f dV = 1, (3.2)
τ > 0. Clearly W is invariant under simultaneous scaling of τ and gij. The evolution equations, generalizing (1.3) are
(gij)t = −2Rij, ft = −△f + |∇f |2 − R + n
2τ , τt = −1 (3.3)
The evolution equation for f can also be written as follows: ✷∗u = 0, where
u = (4πτ )− n
2 e−f , and ✷∗ = −∂/∂t − △ + R is the conjugate heat operator. Now a routine computation gives
dW/dt =
∫
M
2τ |Rij + ∇i∇jf − 1
2τ gij|2(4πτ )− n
2 e−f dV . (3.4)
8


 Therefore, if we let μ(gij, τ ) = inf W(gij, f, τ ) over smooth f satisfying (3.2), and ν(gij) = inf μ(gij, τ ) over all positive τ, then ν(gij(t)) is nondecreasing along the Ricci flow. It is not hard to show that in the definition of μ there always exists a smooth minimizer f (on a closed M). It is also clear that limτ→∞ μ(gij, τ ) = +∞ whenever the first eigenvalue of −4△ + R is positive. Thus, our statement that there is no shrinking breathers other than gradient solitons, is implied by the following
Claim For an arbitrary metric gij on a closed manifold M, the function μ(gij, τ ) is negative for small τ > 0 and tends to zero as τ tends to zero.
Proof of the Claim. (sketch) Assume that τ ̄ > 0 is so small that Ricci
flow starting from gij exists on [0, τ ̄]. Let u = (4πτ )− n
2 e−f be the solution of the conjugate heat equation, starting from a δ-function at t = τ ̄, τ (t) = τ ̄ − t. Then W(gij(t), f (t), τ (t)) tends to zero as t tends to τ ̄, and therefore μ(gij, τ ̄) ≤ W(gij(0), f (0), τ (0)) < 0 by (3.4). Now let τ → 0 and assume that f τ are the minimizers, such that
W(1
2 τ −1gij, f τ , 1
2 ) = W(gij, f τ , τ ) = μ(gij, τ ) ≤ c < 0.
The metrics 1
2 τ −1gij ”converge” to the euclidean metric, and if we could
extract a converging subsequence from f τ , we would get a function f on Rn, such that ∫
Rn (2π)− n
2 e−f dx = 1 and
∫
Rn
[1
2|∇f |2 + f − n](2π)− n
2 e−f dx < 0
The latter inequality contradicts the Gaussian logarithmic Sobolev inequality, due to L.Gross. (To pass to its standard form, take f = |x|2/2 − 2 log φ and integrate by parts) This argument is not hard to make rigorous; the details are left to the reader.
3.2 Remark. Our monotonicity formula (3.4) can in fact be used to prove a version of the logarithmic Sobolev inequality (with description of the equality cases) on shrinking Ricci solitons. Indeed, assume that a metric gij satisfies Rij − gij − ∇ibj − ∇jbi = 0. Then under Ricci flow, gij(t) is
isometric to (1 − 2t)gij(0), μ(gij(t), 1
2 − t) = μ(gij(0), 1
2), and therefore the
monotonicity formula (3.4) implies that the minimizer f for μ(gij, 1
2 ) satisfies
Rij + ∇i∇jf − gij = 0. Of course, this argument requires the existence of minimizer, and justification of the integration by parts; this is easy if M
9


 is closed, but can also be done with more efforts on some complete M, for instance when M is the Gaussian soliton. 3.3* The no breathers theorem in dimension three was proved by Ivey [I]; in fact, he also ruled out nontrivial Ricci solitons; his proof uses the almost nonnegative curvature estimate, mentioned in the introduction. Logarithmic Sobolev inequalities is a vast area of research; see [G] for a survey and bibliography up to the year 1992; the influence of the curvature was discussed by Bakry-Emery [B-Em]. In the context of geometric evolution equations, the logarithmic Sobolev inequality occurs in Ecker [E 1].
4 No local collapsing theorem I
In this section we present an application of the monotonicity formula (3.4) to the analysis of singularities of the Ricci flow.
4.1. Let gij(t) be a smooth solution to the Ricci flow (gij)t = −2Rij on [0, T ). We say that gij(t) is locally collapsing at T, if there is a sequence of times tk → T and a sequence of metric balls Bk = B(pk, rk) at times tk, such that
rk2/tk is bounded, |Rm|(gij(tk)) ≤ r−2
k in Bk and r−n
k V ol(Bk) → 0.
Theorem. If M is closed and T < ∞, then gij(t) is not locally collapsing at T.
Proof. Assume that there is a sequence of collapsing balls Bk = B(pk, rk) at times tk → T. Then we claim that μ(gij(tk), rk2) → −∞. Indeed one
can take fk(x) = − log φ(disttk (x, pk)r−1
k ) + ck, where φ is a function of one variable, equal 1 on [0, 1/2], decreasing on [1/2, 1], and very close to 0 on [1, ∞), and ck is a constant; clearly ck → −∞ as r−n
k V ol(Bk) → 0. Therefore,
applying the monotonicity formula (3.4), we get μ(gij(0), tk + rk2) → −∞.
However this is impossible, since tk + rk2 is bounded.
4.2. Definition We say that a metric gij is κ-noncollapsed on the scale ρ, if every metric ball B of radius r < ρ, which satisfies |Rm|(x) ≤ r−2 for every x ∈ B, has volume at least κrn.
It is clear that a limit of κ-noncollapsed metrics on the scale ρ is also κ-noncollapsed on the scale ρ; it is also clear that α2gij is κ-noncollapsed on the scale αρ whenever gij is κ-noncollapsed on the scale ρ. The theorem above essentially says that given a metric gij on a closed manifold M and T < ∞, one can find κ = κ(gij, T ) > 0, such that the solution gij(t) to the Ricci flow starting at gij is κ-noncollapsed on the scale T 1/2 for all t ∈ [0, T ),
10


 provided it exists on this interval. Therefore, using the convergence theorem of Hamilton, we obtain the following
Corollary. Let gij(t), t ∈ [0, T ) be a solution to the Ricci flow on a closed manifold M, T < ∞. Assume that for some sequences tk → T, pk ∈ M and some constant C we have Qk = |Rm|(pk, tk) → ∞ and |Rm|(x, t) ≤ CQk, whenever t < tk. Then (a subsequence of ) the scalings of gij(tk) at pk with factors Qk converges to a complete ancient solution to the Ricci flow, which is κ-noncollapsed on all scales for some κ > 0.
5 A statistical analogy
In this section we show that the functional W, introduced in section 3, is in a sense analogous to minus entropy. 5.1 Recall that the partition function for the canonical ensemble at temperature β−1 is given by Z = ∫ exp(−βE)dω(E), where ω(E) is a ”density of states” measure, which does not depend on β. Then one computes the average energy < E >= − ∂
∂β log Z, the entropy S = β < E > + log Z, and
the fluctuation σ =< (E− < E >)2 >= ∂2
(∂β)2 log Z.
Now fix a closed manifold M with a probability measure m, and suppose that our system is described by a metric gij(τ ), which depends on the temperature τ according to equation (gij)τ = 2(Rij + ∇i∇jf ), where dm = udV, u =
(4πτ )− n
2 e−f , and the partition function is given by log Z = ∫ (−f + n
2 )dm.
(We do not discuss here what assumptions on gij guarantee that the corresponding ”density of states” measure can be found) Then we compute
< E >= −τ 2
∫
M
(R + |∇f |2 − n
2τ )dm,
S=−
∫
M
(τ (R + |∇f |2) + f − n)dm,
σ = 2τ 4
∫
M
|Rij + ∇i∇jf − 1
2τ gij|2dm
Alternatively, we could prescribe the evolution equations by replacing the t-derivatives by minus τ -derivatives in (3.3 ), and get the same formulas for Z, < E >, S, σ, with dm replaced by udV.
Clearly, σ is nonnegative; it vanishes only on a gradient shrinking soliton. < E > is nonnegative as well, whenever the flow exists for all sufficiently
11


 small τ > 0 (by proposition 1.2). Furthermore, if (a) u tends to a δ-function as τ → 0, or (b) u is a limit of a sequence of functions ui, such that each ui tends to a δ-function as τ → τi > 0, and τi → 0, then S is also nonnegative. In case (a) all the quantities < E >, S, σ tend to zero as τ → 0, while in case (b), which may be interesting if gij(τ ) goes singular at τ = 0, the entropy S may tend to a positive limit. If the flow is defined for all sufficiently large τ (that is, we have an ancient solution to the Ricci flow, in Hamilton’s terminology), we may be interested in the behavior of the entropy S as τ → ∞. A natural question is whether we have a gradient shrinking soliton whenever S stays bounded. 5.2 Remark. Heuristically, this statistical analogy is related to the description of the renormalization group flow, mentioned in the introduction: in the latter one obtains various quantities by averaging over higher energy states, whereas in the former those states are suppressed by the exponential factor. 5.3* An entropy formula for the Ricci flow in dimension two was found by Chow [C]; there seems to be no relation between his formula and ours. The interplay of statistical physics and (pseudo)-riemannian geometry occurs in the subject of Black Hole Thermodynamics, developed by Hawking et al. Unfortunately, this subject is beyond my understanding at the moment.
6 Riemannian formalism in potentially infi
nite dimensions
When one is talking of the canonical ensemble, one is usually considering an embedding of the system of interest into a much larger standard system of fixed temperature (thermostat). In this section we attempt to describe such an embedding using the formalism of Rimannian geometry.
6.1 Consider the manifold M ̃ = M × SN × R+ with the following metric:
g ̃ij = gij, g ̃αβ = τ gαβ, g ̃00 = N
2τ + R, g ̃iα = g ̃i0 = g ̃α0 = 0,
where i, j denote coordinate indices on the M factor, α, β denote those on the SN factor, and the coordinate τ on R+ has index 0; gij evolves with τ by the backward Ricci flow (gij)τ = 2Rij, gαβ is the metric on SN of
constant curvature 1
2N . It turns out that the components of the curvature
tensor of this metric coincide (modulo N −1) with the components of the
12


 matrix Harnack expression (and its traces), discovered by Hamilton [H 3]. One can also compute that all the components of the Ricci tensor are equal to zero (mod N −1). The heat equation and the conjugate heat equation on
M can be interpreted via Laplace equation on M ̃ for functions and volume forms respectively: u satisfies the heat equation on M iff u ̃ (the extension of
u to M ̃ constant along the SN fibres) satisfies  ̃△u ̃ = 0 mod N −1; similarly, u satisfies the conjugate heat equation on M iff u ̃∗ = τ − N−1
2 u ̃ satisfies △ ̃ u ̃∗ =
0 mod N −1 on M ̃ .
6.2 Starting from g ̃, we can also construct a metric gm on M ̃ , isometric to g ̃ (mod N −1), which corresponds to the backward m-preserving Ricci flow ( given by equations (1.1) with t-derivatives replaced by minus τ -derivatives,
dm = (4πτ )− n
2 e−f dV ). To achieve this, first apply to g ̃ a (small) diffeomorphism, mapping each point (xi, yα, τ ) into (xi, yα, τ (1 − 2f
N )); we would get a
metric g ̃m, with components (mod N −1)
g ̃imj = g ̃ij, g ̃αmβ = (1 − 2f
N )g ̃αβ, g ̃0m0 = g ̃00 − 2fτ − f
τ , g ̃im0 = −∇if, g ̃imα = g ̃αm0 = 0;
then apply a horizontal (that is, along the M factor) diffeomorphism to get gm satisfying (gimj )τ = 2(Rij + ∇i∇jf ); the other components of gm become
(mod N −1)
gαmβ = (1 − 2f
N )g ̃αβ, g0m0 = g ̃0m0 − |∇f |2 = 1
τ (N
2 − [τ (2△f − |∇f |2 + R) + f − n]),
gim0 = gαm0 = gimα = 0
Note that the hypersurface τ =const in the metric gm has the volume form τ N/2e−f times the canonical form on M and SN , and the scalar curvature of this hypersurface is 1
τ (N
2 + τ (2△f − |∇f |2 + R) + f ) mod N −1. Thus the
entropy S multiplied by the inverse temperature β is essentially minus the total scalar curvature of this hypersurface. 6.3 Now we return to the metric g ̃ and try to use its Ricci-flatness by interpreting the Bishop-Gromov relative volume comparison theorem. Con
sider a metric ball in (M ̃ , g ̃) centered at some point p where τ = 0. Then clearly the shortest geodesic between p and an arbitrary point q is always orthogonal to the SN fibre. The length of such curve γ(τ ) can be computed
as
∫ τ (q)
0
√N
2τ + R + |γ ̇ M (τ )|2dτ
13


 = √2Nτ (q) + 1
√2N
∫ τ (q)
0
√τ (R + |γ ̇ M (τ )|2)dτ + O(N − 3
2)
Thus a shortest geodesic should minimize L(γ) = ∫ τ(q)
0
√τ (R + |γ ̇ M (τ )|2)dτ , an expression defined entirely in terms of M. Let L(qM ) denote the corre
sponding infimum. It follows that a metric sphere in M ̃ of radius √2Nτ (q) centered at p is O(N −1)-close to the hypersurface τ = τ (q), and its volume can be computed as V (SN ) ∫
M (√τ (q) − 1
2N L(x) + O(N −2))N dx, so the ratio
of this volume to √2N τ (q)N+n is just constant times N − n
2 times
∫
M
τ (q)− n
2 exp(− 1
√2τ (q)L(x))dx + O(N −1)
The computation suggests that this integral, which we will call the reduced
volume and denote by V ̃ (τ (q)), should be increasing as τ decreases. A rigorous proof of this monotonicity is given in the next section. 6.4* The first geometric interpretation of Hamilton’s Harnack expressions was found by Chow and Chu [C-Chu 1,2]; they construct a potentially degenerate riemannian metric on M × R, which potentially satisfies the Ricci soliton equation; our construction is, in a certain sense, dual to theirs. Our formula for the reduced volume resembles the expression in Huisken monotonicity formula for the mean curvature flow [Hu]; however, in our case the monotonicity is in the opposite direction.
7 A comparison geometry approach to the
Ricci flow
7.1 In this section we consider an evolving metric (gij)τ = 2Rij on a manifold M; we assume that either M is closed, or gij(τ ) are complete and have uniformly bounded curvatures. To each curve γ(τ ), 0 < τ1 ≤ τ ≤ τ2, we associate its L-length
L(γ) =
∫ τ2
τ1
√τ (R(γ(τ )) + |γ ̇ (τ )|2)dτ
(of course, R(γ(τ )) and |γ ̇ (τ )|2 are computed using gij(τ )) Let X(τ ) = γ ̇ (τ ), and let Y (τ ) be any vector field along γ(τ ). Then the first variation formula can be derived as follows:
δY (L) =
14


 ∫ τ2
τ1
√τ (< Y, ∇R > +2 < ∇Y X, X >)dτ =
∫ τ2
τ1
√τ (< Y, ∇R > +2 < ∇XY, X >)dτ
=
∫ τ2
τ1
√τ (< Y, ∇R > +2 d
dτ < Y, X > −2 < Y, ∇XX > −4Ric(Y, X))dτ
= 2√τ < X, Y >∣
∣
τ2
τ1 +
∫ τ2
τ1
√τ < Y, ∇R − 2∇XX − 4Ric(X, ·) − 1
τ X > dτ
(7.1)
Thus L-geodesics must satisfy
∇X X − 1
2 ∇R + 1
2τ X + 2Ric(X, ·) = 0 (7.2)
Given two points p, q and τ2 > τ1 > 0, we can always find an L-shortest curve γ(τ ), τ ∈ [τ1, τ2] between them, and every such L-shortest curve is L
geodesic. It is easy to extend this to the case τ1 = 0; in this case √τ X(τ ) has a limit as τ → 0. From now on we fix p and τ1 = 0 and denote by L(q, τ ̄) the L-length of the L-shortest curve γ(τ ), 0 ≤ τ ≤ τ ̄, connecting p and q. In the computations below we pretend that shortest L-geodesics between p and q are unique for all pairs (q, τ ̄); if this is not the case, the inequalities that we obtain are still valid when understood in the barrier sense, or in the sense of distributions.
The first variation formula (7.1) implies that ∇L(q, τ ̄) = 2√τ ̄X(τ ̄), so that |∇L|2 = 4τ ̄|X|2 = −4τ ̄R + 4τ ̄(R + |X|2). We can also compute
Lτ ̄(q, τ ̄) = √τ ̄(R + |X|2)− < X, ∇L >= 2√τ ̄R − √τ ̄(R + |X|2)
To evaluate R + |X|2 we compute (using (7.2))
d
dτ (R(γ(τ )) + |X(τ )|2) = Rτ + < ∇R, X > +2 < ∇XX, X > +2Ric(X, X)
= Rτ + 1
τ R + 2 < ∇R, X > −2Ric(X, X) − 1
τ (R + |X|2)
= −H(X) − 1
τ (R + |X|2), (7.3)
15


 where H(X) is the Hamilton’s expression for the trace Harnack inequality (with t = −τ ). Hence,
τ ̄ 3
2 (R + |X|2)(τ ̄) = −K + 1
2 L(q, τ ̄), (7.4)
where K = K(γ, τ ̄) denotes the integral ∫ τ ̄
0 τ3
2 H(X)dτ, which we’ll encounter a few times below. Thus we get
Lτ ̄ = 2√τ ̄R − 1
2τ ̄L + 1
τ ̄K (7.5)
|∇L|2 = −4τ ̄R + √2τ ̄ L − √4τ ̄K (7.6)
Finally we need to estimate the second variation of L. We compute
δY2 (L) =
∫ τ ̄
0
√τ (Y · Y · R + 2 < ∇Y ∇Y X, X > +2|∇Y X|2)dτ
=
∫ τ ̄
0
√τ (Y · Y · R + 2 < ∇X∇Y Y, X > +2 < R(Y, X), Y, X > +2|∇XY |2)dτ
Now
d
dτ < ∇Y Y, X >=< ∇X ∇Y Y, X > + < ∇Y Y, ∇XX > +2Y ·Ric(Y, X)−X·Ric(Y, Y ),
so, if Y (0) = 0 then
δY2 (L) = 2 < ∇Y Y, X > √τ ̄+
∫ τ ̄
0
√τ (∇Y ∇Y R + 2 < R(Y, X), Y, X > +2|∇XY |2
+ 2∇X Ric(Y, Y ) − 4∇Y Ric(Y, X))dτ, (7.7)
where we discarded the scalar product of −2∇Y Y with the left hand side of (7.2). Now fix the value of Y at τ = τ ̄, assuming |Y (τ ̄)| = 1, and construct Y on [0, τ ̄] by solving the ODE
∇XY = −Ric(Y, ·) + 1
2τ Y (7.8)
16


 We compute
d
dτ < Y, Y >= 2Ric(Y, Y ) + 2 < ∇XY, Y >= 1
τ < Y, Y >,
so |Y (τ )|2 = τ
τ ̄, and in particular, Y (0) = 0. Making a substitution into (7.7),
we get HessL(Y, Y ) ≤
∫ τ ̄
0
√τ (∇Y ∇Y R + 2 < R(Y, X), Y, X > +2∇XRic(Y, Y ) − 4∇Y Ric(Y, X)
+2|Ric(Y, ·)|2 − 2
τ Ric(Y, Y ) + 1
2τ τ ̄ )dτ To put this in a more convenient form, observe that
d
dτ Ric(Y (τ ), Y (τ )) = Ricτ (Y, Y ) + ∇XRic(Y, Y ) + 2Ric(∇X Y, Y )
= Ricτ (Y, Y ) + ∇X Ric(Y, Y ) + 1
τ Ric(Y, Y ) − 2|Ric(Y, ·)|2,
so
HessL(Y, Y ) ≤ √1τ ̄ − 2√τ ̄Ric(Y, Y ) −
∫ τ ̄
0
√τ H(X, Y )dτ , (7.9)
where
H(X, Y ) = −∇Y ∇Y R−2 < R(Y, X)Y, X > −4(∇X Ric(Y, Y )−∇Y Ric(Y, X))
−2Ricτ (Y, Y ) + 2|Ric(Y, ·)|2 − 1
τ Ric(Y, Y )
is the Hamilton’s expression for the matrix Harnack inequality (with t = −τ ). Thus
△L ≤ −2√τ R + √nτ − 1
τ K (7.10)
A field Y (τ ) along L-geodesic γ(τ ) is called L-Jacobi, if it is the derivative of a variation of γ among L-geodesics. For an L-Jacobi field Y with |Y (τ ̄)| = 1 we have
d
dτ |Y |2 = 2Ric(Y, Y ) + 2 < ∇XY, Y >= 2Ric(Y, Y ) + 2 < ∇Y X, Y >
17


 = 2Ric(Y, Y ) + √1τ ̄ HessL(Y, Y ) ≤ 1
τ ̄ − √1τ ̄
∫ τ ̄
0
τ
1
2 H(X, Y ̃ )dτ , (7.11)
where Y ̃ is obtained by solving ODE (7.8) with initial data Y ̃ (τ ̄) = Y (τ ̄).
Moreover, the equality in (7.11) holds only if Y ̃ is L-Jacobi and hence
d
dτ |Y |2 = 2Ric(Y, Y ) + √1τ ̄ HessL(Y, Y ) = 1
τ ̄ .
Now we can deduce an estimate for the jacobian J of the L-exponential map, given by LexpX(τ ̄) = γ(τ ̄), where γ(τ ) is the L-geodesic, starting at p
and having X as the limit of √τ γ ̇ (τ ) as τ → 0. We obtain
d
dτ logJ(τ ) ≤ n
2τ ̄ − 1
2 τ ̄− 3
2 K, (7.12)
with equality only if 2Ric + √1τ ̄ HessL = 1
τ ̄ g. Let l(q, τ ) = 1
2√τ L(q, τ ) be the reduced distance. Then along an L-geodesic γ(τ ) we have (by (7.4))
d
dτ l(τ ) = − 1
2τ ̄ l + 1
2 (R + |X|2) = −1
2 τ ̄− 3
2 K,
so (7.12) implies that τ − n
2 exp(−l(τ ))J(τ ) is nonincreasing in τ along γ, and monotonicity is strict unless we are on a gradient shrinking soliton. Integrating over M, we get monotonicity of the reduced volume function
V ̃ (τ ) = ∫
M τ−n
2 exp(−l(q, τ ))dq. ( Alternatively, one could obtain the same monotonicity by integrating the differential inequality
lτ ̄ − △l + |∇l|2 − R + n
2τ ̄ ≥ 0, (7.13)
which follows immediately from (7.5), (7.6) and (7.10). Note also a useful inequality
2△l − |∇l|2 + R + l − n
τ ̄ ≤ 0, (7.14)
which follows from (7.6), (7.10).)
On the other hand, if we denote L ̄(q, τ ) = 2√τ L(q, τ ), then from (7.5), (7.10) we obtain
L ̄τ ̄ + △L ̄ ≤ 2n (7.15)
Therefore, the minimum of L ̄(·, τ ̄) − 2nτ ̄ is nonincreasing, so in particular, the minimum of l(·, τ ̄) does not exceed n
2 for each τ ̄ > 0. (The lower bound for
18


 l is much easier to obtain since the evolution equation Rτ = −△R − 2|Ric|2
implies R(·, τ ) ≥ − n
2(τ0−τ) , whenever the flow exists for τ ∈ [0, τ0].) 7.2 If the metrics gij(τ ) have nonnegative curvature operator, then Hamilton’s differential Harnack inequalities hold, and one can say more about the behavior of l. Indeed, in this case, if the solution is defined for τ ∈ [0, τ0], then H(X, Y ) ≥ −Ric(Y, Y )( 1
τ+ 1
τ0−τ ) ≥ −R( 1
τ+ 1
τ0−τ )|Y |2 and
H(X) ≥ −R( 1
τ+ 1
τ0−τ ). Therefore, whenever τ is bounded away from τ0
(say, τ ≤ (1 − c)τ0, c > 0), we get (using (7.6), (7.11))
|∇l|2 + R ≤ Cl
τ , (7.16)
and for L-Jacobi fields Y
d
dτ log|Y |2 ≤ 1
τ (Cl + 1) (7.17)
7.3 As the first application of the comparison inequalities above, let us give an alternative proof of a weakened version of the no local collapsing theorem 4.1. Namely, rather than assuming |Rm|(x, tk) ≤ r−2
k for x ∈ Bk,
we require |Rm|(x, t) ≤ r−2
k whenever x ∈ Bk, tk − rk2 ≤ t ≤ tk. Then the
proof can go as follows: let τk(t) = tk −t, p = pk, ǫk = r−1
k V ol(Bk) 1
n . We claim
that V ̃k(ǫkrk2) < 3ǫ
n 2
k when k is large. Indeed, using the L-exponential map we can integrate over TpM rather than M; the vectors in TpM of length at most
1
2 ǫ− 1
2
k give rise to L-geodesics, which can not escape from Bk in time ǫkrk2, so
their contribution to the reduced volume does not exceed 2ǫ
n 2
k ; on the other
hand, the contribution of the longer vectors does not exceed exp(−1
2 ǫ− 1
2
k ) by
the jacobian comparison theorem. However, V ̃k(tk) (that is, at t = 0) stays
bounded away from zero. Indeed, since min lk(·, tk − 1
2T) ≤ n
2 , we can pick a
point qk, where it is attained, and obtain a universal upper bound on lk(·, tk)
by considering only curves γ with γ(tk − 1
2T ) = qk, and using the fact that all
geometric quantities in gij(t) are uniformly bounded when t ∈ [0, 1
2 T ]. Since
the monotonicity of the reduced volume requires V ̃k(tk) ≤ V ̃k(ǫkrk2), this is a contradiction. A similar argument shows that the statement of the corollary in 4.2 can be strengthened by adding another property of the ancient solution, obtained as a blow-up limit. Namely, we may claim that if, say, this solution is defined for t ∈ (−∞, 0), then for any point p and any t0 > 0, the reduced volume
function V ̃ (τ ), constructed using p and τ (t) = t0 − t, is bounded below by κ.
19


 7.4* The computations in this section are just natural modifications of those in the classical variational theory of geodesics that can be found in any textbook on Riemannian geometry; an even closer reference is [L-Y], where they use ”length”, associated to a linear parabolic equation, which is pretty much the same as in our case.
8 No local collapsing theorem II
8.1 Let us first formalize the notion of local collapsing, that was used in 7.3. Definition. A solution to the Ricci flow (gij)t = −2Rij is said to be κ-collapsed at (x0, t0) on the scale r > 0 if |Rm|(x, t) ≤ r−2 for all (x, t) satisfying distt0(x, x0) < r and t0 − r2 ≤ t ≤ t0, and the volume of the metric ball B(x0, r2) at time t0 is less than κrn. 8.2 Theorem. For any A > 0 there exists κ = κ(A) > 0 with the following property. If gij(t) is a smooth solution to the Ricci flow (gij)t =
−2Rij, 0 ≤ t ≤ r02, which has |Rm|(x, t) ≤ r0−2 for all (x, t), satisfying dist0(x, x0) < r0, and the volume of the metric ball B(x0, r0) at time zero is at least A−1r0n, then gij(t) can not be κ-collapsed on the scales less than r0
at a point (x, r02) with distr2
0 (x, x0) ≤ Ar0.
Proof. By scaling we may assume r0 = 1; we may also assume dist1(x, x0) = A. Let us apply the constructions of 7.1 choosing p = x, τ (t) = 1 − t. Arguing as in 7.3, we see that if our solution is collapsed at x on the scale r ≤ 1, then
the reduced volume V ̃ (r2) must be very small; on the other hand, V ̃ (1) can not be small unless min l(x, 1
2 ) over x satisfying dist 1
2 (x, x0) ≤ 1
10 is large.
Thus all we need is to estimate l, or equivalently L ̄, in that ball. Recall that
L ̄ satisfies the differential inequality (7.15). In order to use it efficiently in a maximum principle argument, we need first to check the following simple assertion.
8.3 Lemma. Suppose we have a solution to the Ricci flow (gij)t = −2Rij. (a) Suppose Ric(x, t0) ≤ (n − 1)K when distt0(x, x0) < r0. Then the distance function d(x, t) = distt(x, x0) satisfies at t = t0 outside B(x0, r0) the differential inequality
dt − △d ≥ −(n − 1)( 2
3 Kr0 + r0−1)
(the inequality must be understood in the barrier sense, when necessary)
20


 (b) (cf. [H 4,§17]) Suppose Ric(x, t0) ≤ (n − 1)K when distt0(x, x0) < r0, or distt0 (x, x1) < r0. Then
d
dt distt(x0, x1) ≥ −2(n − 1)( 2
3 Kr0 + r0−1) at t = t0
Proof of Lemma. (a) Clearly, dt(x) = ∫
γ −Ric(X, X), where γ is the shortest
geodesic between x and x0 and X is its unit tangent vector, On the other
hand, △d ≤ ∑n−1
k=1 s′Y′k(γ), where Yk are vector fields along γ, vanishing at
x0 and forming an orthonormal basis at x when complemented by X, and s′Y′k(γ) denotes the second variation along Yk of the length of γ. Take Yk to be parallel between x and x1, and linear between x1 and x0, where d(x1, t0) = r0. Then
△d ≤
n−1
∑
k=1
s′Y′k (γ) =
∫ d(x,t0)
r0
−Ric(X, X)ds+
∫ r0
0
( s2
r02
(−Ric(X, X)) + n − 1
r02
)ds
=
∫
γ
−Ric(X, X)+
∫ r0
0
(Ric(X, X)(1 − s2
r02
)+ n−1
r02
)ds ≤ dt+(n−1)( 2
3 Kr0+r0−1)
The proof of (b) is similar. Continuing the proof of theorem, apply the maximum principle to the
function h(y, t) = φ(d(y, t) − A(2t − 1))(L ̄(y, 1 − t) + 2n + 1), where d(y, t) = distt(x, x0), and φ is a function of one variable, equal 1 on (−∞, 1
20 ), and
rapidly increasing to infinity on ( 1
20 , 1
10 ), in such a way that
2(φ′)2/φ − φ′′ ≥ (2A + 100n)φ′ − C(A)φ, (8.1)
for some constant C(A) < ∞. Note that L ̄ + 2n + 1 ≥ 1 for t ≥ 1
2 by the
remark in the very end of 7.1. Clearly, min h(y, 1) ≤ h(x, 1) = 2n + 1. On the other hand, min h(y, 1
2) is achieved for some y satisfying d(y, 1
2) ≤ 1
10 .
Now we compute
✷h = (L ̄ + 2n + 1)(−φ′′ + (dt − △d − 2A)φ′) − 2 < ∇φ∇L ̄ > +(L ̄t − △L ̄)φ (8.2)
∇h = (L ̄ + 2n + 1)∇φ + φ∇L ̄ (8.3)
At a minimum point of h we have ∇h = 0, so (8.2) becomes
✷h = (L ̄ + 2n + 1)(−φ′′ + (dt − △d − 2A)φ′ + 2(φ′)2/φ) + (L ̄t − △L ̄)φ (8.4)
21


 Now since d(y, t) ≥ 1
20 whenever φ′ 6= 0, and since Ric ≤ n − 1 in B(x0, 1
20 ),
we can apply our lemma (a) to get dt − △d ≥ −100(n − 1) on the set where φ′ 6= 0. Thus, using (8.1) and (7.15), we get
✷h ≥ −(L ̄ + 2n + 1)C(A)φ − 2nφ ≥ −(2n + C(A))h
This implies that min h can not decrease too fast, and we get the required estimate.
9 Differential Harnack inequality for solutions
of the conjugate heat equation
9.1. Proposition. Let gij(t) be a solution to the Ricci flow (gij)t = −2Rij, 0 ≤
t ≤ T, and let u = (4π(T − t))− n
2 e−f satisfy the conjugate heat equation ✷∗u = −ut − △u + Ru = 0. Then v = [(T − t)(2△f − |∇f |2 + R) + f − n]u satisfies
✷∗v = −2(T − t)|Rij + ∇i∇jf − 1
2(T − t) gij|2 (9.1)
Proof. Routine computation. Clearly, this proposition immediately implies the monotonicity formula (3.4); its advantage over (3.4) shows up when one has to work locally.
9.2. Corollary. Under the same assumptions, on a closed manifold M,or whenever the application of the maximum principle can be justified, min v/u is nondecreasing in t.
9.3. Corollary. Under the same assumptions, if u tends to a δ-function as t → T, then v ≤ 0 for all t < T.
Proof. If h satisfies the ordinary heat equation ht = △h with respect to
the evolving metric gij(t), then we have d
dt
∫ hu = 0 and d
dt
∫ hv ≥ 0. Thus we only need to check that for everywhere positive h the limit of ∫ hv as t → T is nonpositive. But it is easy to see, that this limit is in fact zero.
9.4. Corollary. Under assumptions of the previous corollary, for any smooth curve γ(t) in M holds
−d
dtf (γ(t), t) ≤ 1
2(R(γ(t), t) + |γ ̇ (t)|2) − 1
2(T − t) f (γ(t), t) (9.2)
22


 Proof. From the evolution equation ft = −△f + |∇f |2 − R + n
2(T −t) and
v ≤ 0 we get ft + 1
2R− 1
2 |∇f |2 − f
2(T −t) ≥ 0. On the other hand,− d
dt f (γ(t), t) = −ft− < ∇f, γ ̇ (t) >≤ −ft + 1
2 |∇f |2 + 1
2|γ ̇ |2. Summing these two inequalities,
we get (9.2).
9.5. Corollary. If under assumptions of the previous corollary, p is the point where the limit δ-function is concentrated, then f (q, t) ≤ l(q, T − t), where l is the reduced distance, defined in 7.1, using p and τ (t) = T − t.
Proof. Use (7.13) in the form ✷∗exp(−l) ≤ 0. 9.6 Remark. Ricci flow can be characterized among all other evolution equations by the infinitesimal behavior of the fundamental solutions of the conjugate heat equation. Namely, suppose we have a riemannian metric gij(t) evolving with time according to an equation (gij)t = Aij(t). Then we have
the heat operator ✷ = ∂
∂t − △ and its conjugate ✷∗ = − ∂
∂t − △ − 1
2 A, so that
d dt
∫ uv = ∫ ((✷u)v − u(✷∗v)). (Here A = gijAij) Consider the fundamental
solution u = (−4πt)− n
2 e−f for ✷∗, starting as δ-function at some point (p, 0).
Then for general Aij the function (✷f ̄+ f ̄
t )(q, t), where f ̄ = f −∫ f u, is of the
order O(1) for (q, t) near (p, 0). The Ricci flow Aij = −2Rij is characterized
by the condition (✷f ̄+ f ̄
t )(q, t) = o(1); in fact, it is O(|pq|2 + |t|) in this case.
9.7* Inequalities of the type of (9.2) are known as differential Harnack inequalities; such inequality was proved by Li and Yau [L-Y] for the solutions of linear parabolic equations on riemannian manifolds. Hamilton [H 7,8] used differential Harnack inequalities for the solutions of backward heat equation on a manifold to prove monotonicity formulas for certain parabolic flows. A local monotonicity formula for mean curvature flow making use of solutions of backward heat equation was obtained by Ecker [E 2].
10 Pseudolocality theorem
10.1. Theorem. For every α > 0 there exist δ > 0, ǫ > 0 with the following property. Suppose we have a smooth solution to the Ricci flow (gij)t =
−2Rij, 0 ≤ t ≤ (ǫr0)2, and assume that at t = 0 we have R(x) ≥ −r0−2 and
V ol(∂Ω)n ≥ (1 − δ)cnV ol(Ω)n−1 for any x, Ω ⊂ B(x0, r0), where cn is the euclidean isoperimetric constant. Then we have an estimate |Rm|(x, t) ≤ αt−1 + (ǫr0)−2 whenever 0 < t ≤ (ǫr0)2, d(x, t) = distt(x, x0) < ǫr0.
23


 Thus, under the Ricci flow, the almost singular regions (where curvature is large) can not instantly significantly influence the almost euclidean regions. Or , using the interpretation via renormalization group flow, if a region looks trivial (almost euclidean) on higher energy scale, then it can not suddenly become highly nontrivial on a slightly lower energy scale. Proof. It is an argument by contradiction. The idea is to pick a point (x ̄, t ̄) not far from (x0, 0) and consider the solution u to the conjugate heat
equation, starting as δ-function at (x ̄, t ̄), and the corresponding nonpositive function v as in 9.3. If the curvatures at (x ̄, t ̄) are not small compared to t ̄−1 and are larger than at nearby points, then one can show that ∫ v at time t is bounded away from zero for (small) time intervals t ̄ − t of the order of |Rm|−1(x ̄, t ̄). By monotonicity we conclude that ∫ v is bounded away from zero at t = 0. In fact, using (9.1) and an appropriate cut-off function, we can show that at t = 0 already the integral of v over B(x0, r) is bounded away from zero, whereas the integral of u over this ball is close to 1, where r can be made as small as we like compared to r0. Now using the control over the scalar curvature and isoperimetric constant in B(x0r0), we can obtain a contradiction to the logarithmic Sobolev inequality. Now let us go into details. By scaling assume that r0 = 1. We may also
assume that α is small, say α < 1
100n . From now on we fix α and denote by
Mα the set of pairs (x, t), such that |Rm|(x, t) ≥ αt−1.
Claim 1.For any A > 0, if gij(t) solves the Ricci flow equation on 0 ≤
t ≤ ǫ2, Aǫ < 1
100n , and |Rm|(x, t) > αt−1 + ǫ−2 for some (x, t), satisfying 0 ≤
t ≤ ǫ2, d(x, t) < ǫ, then one can find (x ̄, t ̄) ∈ Mα, with 0 < t ̄ ≤ ǫ2, d(x ̄, t ̄) < (2A + 1)ǫ, such that
|Rm|(x, t) ≤ 4|Rm|(x ̄, t ̄), (10.1)
whenever
(x, t) ∈ Mα, 0 < t ≤ t ̄, d(x, t) ≤ d(x ̄, t ̄) + A|Rm|− 1
2 (x ̄, t ̄) (10.2)
Proof of Claim 1. We construct (x ̄, t ̄) as a limit of a (finite) sequence (xk, tk), defined in the following way. Let (x1, t1) be an arbitrary point, satisfying 0 < t1 ≤ ǫ2, d(x1, t1) < ǫ, |Rm|(x1, t1) ≥ αt−1 + ǫ−2. Now if (xk, tk)
is already constructed, and if it can not be taken for (x ̄, t ̄), because there is some (x, t) satisfying (10.2), but not (10.1), then take any such (x, t) for (xk+1, tk+1). Clearly, the sequence, constructed in such a way, satisfies |Rm|(xk, tk) ≥ 4k−1|Rm|(x1, t1) ≥ 4k−1ǫ−2, and therefore, d(xk, tk) ≤ (2A +
24


 1)ǫ. Since the solution is smooth, the sequence is finite, and its last element fits.
Claim 2. For (x ̄, t ̄), constructed above, (10.1) holds whenever
t ̄− 1
2 αQ−1 ≤ t ≤ t ̄, distt ̄(x, x ̄) ≤ 1
10 AQ− 1
2 , (10.3)
where Q = |Rm|(x ̄, t ̄).
Proof of Claim 2. We only need to show that if (x, t) satisfies (10.3), then it must satisfy (10.1) or (10.2). Since (x ̄, t ̄) ∈ Mα, we have Q ≥ αt ̄−1, so
t ̄− 1
2 αQ−1 ≥ 1
2t ̄. Hence, if (x, t) does not satisfy (10.1), it definitely belongs to
Mα. Now by the triangle inequality, d(x, t ̄) ≤ d(x ̄, t ̄) + 1
10 AQ− 1
2 . On the other hand, using lemma 8.3(b) we see that, as t decreases from t ̄ to t ̄ − 1
2 αQ−1,
the point x can not escape from the ball of radius d(x ̄, t ̄) + AQ− 1
2 centered at x0. Continuing the proof of the theorem, and arguing by contradiction, take sequences ǫ → 0, δ → 0 and solutions gij(t), violating the statement; by reducing ǫ, we’ll assume that
|Rm|(x, t) ≤ αt−1 + 2ǫ−2 whenever 0 ≤ t ≤ ǫ2 and d(x, t) ≤ ǫ (10.4)
Take A = 1
100nǫ → ∞, construct (x ̄, t ̄), and consider solutions u = (4π(t ̄ −
t))− n
2 e−f of the conjugate heat equation, starting from δ-functions at (x ̄, t ̄), and corresponding nonpositive functions v.
Claim 3.As ǫ, δ → 0, one can find times t ̃ ∈ [t ̄− 1
2 αQ−1, t ̄], such that the
integral ∫
B v stays bounded away from zero, where B is the ball at time t ̃ of
radius √t ̄− t ̃ centered at x ̄.
Proof of Claim 3(sketch). The statement is invariant under scaling, so we can try to take a limit of scalings of gij(t) at points (x ̄, t ̄) with factors
Q. If the injectivity radii of the scaled metrics at (x ̄, t ̄) are bounded away from zero, then a smooth limit exists, it is complete and has |Rm|(x ̄, t ̄) = 1 and |Rm|(x, t) ≤ 4 when t ̄ − 1
2α ≤ t ≤ t ̄. It is not hard to show that the
fundamental solutions u of the conjugate heat equation converge to such a solution on the limit manifold. But on the limit manifold, ∫
B v can not be
zero for t ̃ = t ̄ − 1
2 α, since the evolution equation (9.1) would imply in this
case that the limit is a gradient shrinking soliton, and this is incompatible with |Rm|(x ̄, t ̄) = 1. If the injectivity radii of the scaled metrics tend to zero, then we can change the scaling factor, to make the scaled metrics converge to a flat man
25


 ifold with finite injectivity radius; in this case it is not hard to choose t ̃ in such a way that ∫
B v → −∞.
The positive lower bound for − ∫
B v will be denoted by β.
Our next goal is to construct an appropriate cut-off function. We choose
it in the form h(y, t) = φ( d ̃(y,t)
10Aǫ ), where d ̃(y, t) = d(y, t) + 200n√t, and φ is
a smooth function of one variable, equal one on (−∞, 1] and decreasing to zero on [1, 2]. Clearly, h vanishes at t = 0 outside B(x0, 20Aǫ); on the other
hand, it is equal to one near (x ̄, t ̄). Now ✷h = 1
10Aǫ (dt − △d + 10√0tn )φ′ − 1
(10Aǫ)2 φ′′. Note that dt − △t + 10√0tn ≥ 0 on the set where φ′ 6= 0 − this follows from the lemma 8.3(a) and our assumption (10.4). We may also choose φ so that φ′′ ≥ −10φ, (φ′)2 ≤ 10φ. Now we can compute (∫
M hu)t = ∫
M (✷h)u ≤ 1
(Aǫ)2 , so ∫
M hu |t=0≥ ∫
M hu |t=t ̄
− t ̄
(Aǫ)2 ≥ 1 − A−2. Also, by (9.1), (∫
M −hv)t ≤ ∫
M −(✷h)v ≤ 1
(Aǫ)2
∫
M −hv,
so by Claim 3, − ∫
M hv |t=0≥ βexp(− t ̄
(Aǫ)2 ) ≥ β(1 − A−2).
From now on we”ll work at t = 0 only. Let u ̃ = hu and correspondingly
f ̃ = f − logh. Then
β(1 − A−2) ≤ −
∫
M
hv =
∫
M
[(−2△f + |∇f |2 − R)t ̄− f + n]hu
=
∫
M
[−t ̄|∇f ̃|2 − f ̃ + n]u ̃ +
∫
M
[t ̄(|∇h|2/h − Rh) − hlogh]u
≤
∫
M
[−t ̄|∇f ̃|2 − f ̃ − n]u ̃ + A−2 + 100ǫ2
( Note that ∫
M −uh log h does not exceed the integral of u over
B(x0, 20Aǫ)\B(x0, 10Aǫ), and ∫
B(x0,10Aǫ) u ≥ ∫
M  ̄hu ≥ 1 − A−2,
where  ̄h = φ( d ̃
5Aǫ ))
Now scaling the metric by the factor 1
2 t ̄−1 and sending ǫ, δ to zero, we
get a sequence of metric balls with radii going to infinity, and a sequence
of compactly supported nonnegative functions u = (2π)− n
2 e−f with ∫ u → 1 and ∫ [− 1
2 |∇f |2 − f + n]u bounded away from zero by a positive constant.
We also have isoperimetric inequalities with the constants tending to the euclidean one. This set up is in conflict with the Gaussian logarithmic Sobolev inequality, as can be seen by using spherical symmetrization.
10.2 Corollary(from the proof) Under the same assumptions, we also
have at time t, 0 < t ≤ (ǫr0)2, an estimate V olB(x, √t) ≥ c√tn for x ∈ B(x0, ǫr0), where c = c(n) is a universal constant.
26


 10.3 Theorem. There exist ǫ, δ > 0 with the following property. Suppose gij(t) is a smooth solution to the Ricci flow on [0, (ǫr0)2], and assume that at
t = 0 we have |Rm|(x) ≤ r0−2 in B(x0, r0), and V olB(x0, r0) ≥ (1 − δ)ωnr0n,
where ωn is the volume of the unit ball in Rn. Then the estimate |Rm|(x, t) ≤ (ǫr0)−2 holds whenever 0 ≤ t ≤ (ǫr0)2, distt(x, x0) < ǫr0.
The proof is a slight modification of the proof of theorem 10.1, and is left to the reader. A natural question is whether the assumption on the volume of the ball is superfluous. 10.4 Corollary(from 8.2, 10.1, 10.2) There exist ǫ, δ > 0 and for any A > 0 there exists κ(A) > 0 with the following property. If gij(t) is a smooth solution to the Ricci flow on [0, (ǫr0)2], such that at t = 0 we have
R(x) ≥ −r0−2, V ol(∂Ω)n ≥ (1 − δ)cnV ol(Ω)n−1 for any x, Ω ⊂ B(x0, r0), and
(x, t) satisfies A−1(ǫr0)2 ≤ t ≤ (ǫr0)2, distt(x, x0) ≤ Ar0, then gij(t) can not
be κ-collapsed at (x, t) on the scales less than √t.
10.5 Remark. It is straightforward to get from 10.1 a version of the Cheeger diffeo finiteness theorem for manifolds, satisfying our assumptions on scalar curvature and isoperimetric constant on each ball of some fixed radius r0 > 0. In particular, these assumptions are satisfied (for some controllably smaller r0), if we assume a lower bound for Ric and an almost euclidean lower bound for the volume of the balls of radius r0. (this follows from the LevyGromov isoperimetric inequality); thus we get one of the results of Cheeger and Colding [Ch-Co] under somewhat weaker assumptions. 10.6* Our pseudolocality theorem is similar in some respect to the results of Ecker-Huisken [E-Hu] on the mean curvature flow.
11 Ancient solutions with nonnegative cur
vature operator and bounded entropy
11.1. In this section we consider smooth solutions to the Ricci flow (gij)t = −2Rij, −∞ < t ≤ 0, such that for each t the metric gij(t) is a complete non-flat metric of bounded curvature and nonnegative curvature operator. Hamilton discovered a remarkable differential Harnack inequality for such solutions; we need only its trace version
Rt + 2 < X, ∇R > +2Ric(X, X) ≥ 0 (11.1)
and its corollary, Rt ≥ 0. In particular, the scalar curvature at some time t0 ≤ 0 controls the curvatures for all t ≤ t0.
27


 We impose one more requirement on the solutions; namely, we fix some κ > 0 and require that gij(t) be κ-noncollapsed on all scales (the definitions 4.2 and 8.1 are essentially equivalent in this case). It is not hard to show that this requirement is equivalent to a uniform bound on the entropy S, defined as in 5.1 using an arbitrary fundamental solution to the conjugate heat equation.
11.2. Pick an arbitrary point (p, t0) and define V ̃ (τ ), l(q, τ ) as in 7.1, for τ (t) = t0 − t. Recall that for each τ > 0 we can find q = q(τ ), such that
l(q, τ ) ≤ n
2.
Proposition.The scalings of gij(t0 − τ ) at q(τ ) with factors τ −1 converge along a subsequence of τ → ∞ to a non-flat gradient shrinking soliton.
Proof (sketch). It is not hard to deduce from (7.16) that for any ǫ > 0 one can find δ > 0 such that both l(q, τ ) and τ R(q, t0 − τ ) do not exceed
δ−1 whenever 1
2 τ ̄ ≤ τ ≤ τ ̄ and dist2
t0−τ ̄(q, q(τ ̄)) ≤ ǫ−1τ ̄ for some τ ̄ > 0. Therefore, taking into account the κ-noncollapsing assumption, we can take a blow-down limit, say g ̄ij(τ ), defined for τ ∈ ( 1
2 , 1), (g ̄ij)τ = 2R ̄ij. We may
assume also that functions l tend to a locally Lipschitz function l ̄, satisfying
(7.13),(7.14) in the sense of distributions. Now, since V ̃ (τ ) is nonincreasing and bounded away from zero (because the scaled metrics are not collapsed
near q(τ )) the limit function V ̄ (τ ) must be a positive constant; this constant
is strictly less than limτ→0V ̃ (τ ) = (4π) n
2 , since gij(t) is not flat. Therefore,
on the one hand, (7.14) must become an equality, hence l ̄ is smooth, and on the other hand, by the description of the equality case in (7.12), g ̄ij(τ ) must
be a gradient shrinking soliton with R ̄ij +  ̄∇i  ̄∇jl ̄− 1
2τ g ̄ij = 0. If this soliton
is flat, then l ̄ is uniquely determined by the equality in (7.14), and it turns
out that the value of V ̄ is exactly (4π) n
2 , which was ruled out.
11.3. Corollary. There is only one oriented two-dimensional solution, satisfying the assumptions stated in 11.1, - the round sphere.
Proof. Hamilton [H 10] proved that round sphere is the only non-flat oriented nonnegatively curved gradient shrinking soliton in dimension two. Thus, the scalings of our ancient solution must converge to a round sphere. However, Hamilton [H 10] has also shown that an almost round sphere is getting more round under Ricci flow, therefore our ancient solution must be round.
11.4. Recall that for any non-compact complete riemannian manifold M of nonnegative Ricci curvature and a point p ∈ M, the function V olB(p, r)r−n
28


 is nonincreasing in r > 0; therefore, one can define an asymptotic volume ratio V as the limit of this function as r → ∞.
Proposition.Under assumptions of 11.1, V = 0 for each t.
Proof. Induction on dimension. In dimension two the statement is vacuous, as we have just shown. Now let n ≥ 3, suppose that V > 0 for some t = t0, and consider the asymptotic scalar curvature ratio R = lim supR(x, t0)d2(x) as d(x) → ∞. (d(x) denotes the distance, at time t0, from x to some fixed point x0) If R = ∞, then we can find a sequence of points xk and radii rk > 0, such that rk/d(xk) → 0, R(xk)rk2 → ∞, and R(x) ≤ 2R(xk) whenever x ∈ B(xk, rk). Taking blow-up limit of gij(t) at (xk, t0) with factors R(xk), we get a smooth non-flat ancient solution, satisfying the assumptions of 11.1, which splits off a line (this follows from a standard argument based on the Aleksandrov-Toponogov concavity). Thus, we can do dimension reduction in this case (cf. [H 4,§22]). If 0 < R < ∞, then a similar argument gives a blow-up limit in a ball of finite radius; this limit has the structure of a non-flat metric cone. This is ruled out by Hamilton’s strong maximum principle for nonnegative curvature operator. Finally, if R = 0, then (in dimensions three and up) it is easy to see that the metric is flat.
11.5. Corollary. For every ǫ > 0 there exists A < ∞ with the following property. Suppose we have a sequence of ( not necessarily complete) solutions (gk)ij(t) with nonnegative curvature operator, defined on Mk × [tk, 0], such that for each k the ball B(xk, rk) at time t = 0 is compactly contained in Mk,
1
2 R(x, t) ≤ R(xk, 0) = Qk for all (x, t), tkQk → −∞, rk2Qk → ∞ as k → ∞.
Then V olB(xk, A/√Qk) ≤ ǫ(A/√Qk)n at t = 0 if k is large enough.
Proof. Assuming the contrary, we may take a blow-up limit (at (xk, 0) with factors Qk) and get a non-flat ancient solution with positive asymptotic volume ratio at t = 0, satisfying the assumptions in 11.1, except, may be, the κ-noncollapsing assumption. But if that assumption is violated for each κ > 0, then V(t) is not bounded away from zero as t → −∞. However, this is impossible, because it is easy to see that V(t) is nonincreasing in t. (Indeed, Ricci flow decreases the volume and does not decrease the distances
faster than C√R per time unit, by lemma 8.3(b)) Thus, κ-noncollapsing holds for some κ > 0, and we can apply the previous proposition to obtain a contradiction.
29


 11.6. Corollary. For every w > 0 there exist B = B(w) < ∞, C = C(w) < ∞, τ0 = τ0(w) > 0, with the following properties. (a) Suppose we have a (not necessarily complete) solution gij(t) to the Ricci flow, defined on M × [t0, 0], so that at time t = 0 the metric ball B(x0, r0) is compactly contained in M. Suppose that at each time t, t0 ≤ t ≤ 0, the metric gij(t) has nonnegative curvature operator, and V olB(x0, r0) ≥
wr0n. Then we have an estimate R(x, t) ≤ Cr0−2 + B(t − t0)−1 whenever
distt(x, x0) ≤ 1
4 r0.
(b) If, rather than assuming a lower bound on volume for all t, we assume it only for t = 0, then the same conclusion holds with −τ0r02 in place of t0,
provided that −t0 ≥ τ0r02.
Proof. By scaling assume r0 = 1. (a) Arguing by contradiction, consider a sequence of B, C → ∞, of solutions gij(t) and points (x, t), such that
distt(x, x0) ≤ 1
4 and R(x, t) > C + B(t − t0)−1. Then, arguing as in the
proof of claims 1,2 in 10.1, we can find a point (x ̄, t ̄), satisfying distt ̄(x ̄, x0) <
1
3 , Q = R(x ̄, t ̄) > C + B(t ̄ − t0)−1, and such that R(x′, t′) ≤ 2Q whenever
t ̄ − AQ−1 ≤ t′ ≤ t ̄, distt ̄(x′, x ̄) < AQ− 1
2 , where A tends to infinity with B, C. Applying the previous corollary at (x ̄, t ̄) and using the relative volume comparison, we get a contradiction with the assumption involving w. (b) Let B(w), C(w) be good for (a). We claim that B = B(5−nw), C = C(5−nw) are good for (b) , for an appropriate τ0(w) > 0. Indeed, let gij(t) be a solution with nonnegative curvature operator, such that V olB(x0, 1) ≥ w at t = 0, and let [−τ, 0] be the maximal time interval, where the assumption of (a) still holds, with 5−nw in place of w and with −τ in place of t0. Then at time t = −τ we must have V olB(x0, 1) ≤ 5−nw. On the other hand, from lemma 8.3 (b) we see that the ball B(x0, 1
4 ) at time t = −τ contains the ball
B(x0, 1
4 − 10(n − 1)(τ √C + 2√Bτ )) at time t = 0, and the volume of the
former is at least as large as the volume of the latter. Thus, it is enough to choose τ0 = τ0(w) in such a way that the radius of the latter ball is > 1
5.
Clearly, the proof also works if instead of assuming that curvature operator is nonnegative, we assumed that it is bounded below by −r0−2 in the (time-dependent) metric ball of radius r0, centered at x0.
11.7. From now on we restrict our attention to oriented manifolds of dimension three. Under the assumptions in 11.1, the solutions on closed manifolds must be quotients of the round S3 or S2 × R - this is proved in the same way as in two dimensions, since the gradient shrinking solitons are known
30


 from the work of Hamilton [H 1,10]. The noncompact solutions are described below.
Theorem.The set of non-compact ancient solutions , satisfying the assumptions of 11.1, is compact modulo scaling. That is , from any sequence of such solutions and points (xk, 0) with R(xk, 0) = 1, we can extract a smoothly converging subsequence, and the limit satisfies the same conditions.
Proof. To ensure a converging subsequence it is enough to show that whenever R(yk, 0) → ∞, the distances at t = 0 between xk and yk go to infinity as well. Assume the contrary. Define a sequence zk by the requirement
that zk be the closest point to xk (at t = 0), satisfying R(zk, 0)dist2
0(xk, zk) = 1.
We claim that R(z, 0)/R(zk, 0) is uniformly bounded for z ∈ B(zk, 2R(zk, 0)− 1
2 ). Indeed, otherwise we could show, using 11.5 and relative volume comparison
in nonnegative curvature, that the balls B(zk, R(zk, 0)− 1
2 ) are collapsing on the scale of their radii. Therefore, using the local derivative estimate, due to W.-X.Shi (see [H 4,§13]), we get a bound on Rt(zk, t) of the order of R2(zk, 0). Then we can compare 1 = R(xk, 0) ≥ cR(zk, −cR−1(zk, 0)) ≥ cR(zk, 0) for some small c > 0, where the first inequality comes from the Harnack inequality, obtained by integrating (11.1). Thus, R(zk, 0) are bounded. But now the existence of the sequence yk at bounded distance from xk implies, via 11.5 and relative volume comparison, that balls B(xk, c) are collapsing - a contradiction. It remains to show that the limit has bounded curvature at t = 0. If this was not the case, then we could find a sequence yi going to infinity, such
that R(yi, 0) → ∞ and R(y, 0) ≤ 2R(yi, 0) for y ∈ B(yi, AiR(yi, 0)− 1
2 ), Ai → ∞. Then the limit of scalings at (yi, 0) with factors R(yi, 0) satisfies the assumptions in 11.1 and splits off a line. Thus by 11.3 it must be a round infinite cylinder. It follows that for large i each yi is contained in a round
cylindrical ”neck” of radius (1
2 R(yi, 0))− 1
2 → 0, - something that can not happen in an open manifold of nonnegative curvature.
11.8. Fix ǫ > 0. Let gij(t) be an ancient solution on a noncompact oriented three-manifold M, satisfying the assumptions in 11.1. We say that a point x0 ∈ M is the center of an ǫ-neck, if the solution gij(t) in the set {(x, t) :
−(ǫQ)−1 < t ≤ 0, dist2
0(x, x0) < (ǫQ)−1}, where Q = R(x0, 0), is, after scaling with factor Q, ǫ-close (in some fixed smooth topology) to the corresponding subset of the evolving round cylinder, having scalar curvature one at t = 0. Corollary (from theorem 11.7 and its proof) For any ǫ > 0 there exists C = C(ǫ, κ) > 0, such that if gij(t) satisfies the assumptions in 11.1, and
31


 Mǫ denotes the set of points in M, which are not centers of ǫ-necks, then
Mǫ is compact and moreover, diamMǫ ≤ CQ− 1
2 , and C−1Q ≤ R(x, 0) ≤ CQ whenever x ∈ Mǫ, where Q = R(x0, 0) for some x0 ∈ ∂Mǫ.
11.9 Remark. It can be shown that there exists κ0 > 0, such that if an ancient solution on a noncompact three-manifold satisfies the assumptions in 11.1 with some κ > 0, then it would satisfy these assumptions with κ = κ0. This follows from the arguments in 7.3, 11.2, and the statement (which is not hard to prove) that there are no noncompact three-dimensional gradient shrinking solitons, satisfying 11.1, other than the round cylinder and its Z2quotients. Furthermore, I believe that there is only one (up to scaling) noncompact three-dimensional κ-noncollapsed ancient solution with bounded positive curvature - the rotationally symmetric gradient steady soliton, studied by R.Bryant. In this direction, I have a plausible, but not quite rigorous argument, showing that any such ancient solution can be made eternal, that is, can be extended for t ∈ (−∞, +∞); also I can prove uniqueness in the class of gradient steady solitons. 11.10* The earlier work on ancient solutions and all that can be found in [H 4, §16 − 22, 25, 26].
12 Almost nonnegative curvature in dimen
sion three
12.1 Let φ be a decreasing function of one variable, tending to zero at infinity. A solution to the Ricci flow is said to have φ-almost nonnegative curvature if it satisfies Rm(x, t) ≥ −φ(R(x, t))R(x, t) for each (x, t).
Theorem. Given ǫ > 0, κ > 0 and a function φ as above, one can find r0 > 0 with the following property. If gij(t), 0 ≤ t ≤ T is a solution to the Ricci flow on a closed three-manifold M, which has φ-almost nonnegative curvature and is κ-noncollapsed on scales < r0, then for any point (x0, t0)
with t0 ≥ 1 and Q = R(x0, t0) ≥ r0−2, the solution in {(x, t) : dist2
t0(x, x0) <
(ǫQ)−1, t0 − (ǫQ)−1 ≤ t ≤ t0} is , after scaling by the factor Q, ǫ-close to the corresponding subset of some ancient solution, satisfying the assumptions in 11.1.
Proof. An argument by contradiction. Take a sequence of r0 converging to zero, and consider the solutions gij(t), such that the conclusion does not
32


 hold for some (x0, t0); moreover, by tampering with the condition t0 ≥ 1 a little bit, choose among all such (x0, t0), in the solution under consideration, the one with nearly the smallest curvature Q. (More precisely, we can choose (x0, t0) in such a way that the conclusion of the theorem holds for all (x, t), satisfying R(x, t) > 2Q, t0 − HQ−1 ≤ t ≤ t0, where H → ∞ as r0 → 0) Our goal is to show that the sequence of blow-ups of such solutions at such points with factors Q would converge, along some subsequence of r0 → 0, to an ancient solution, satisfying 11.1.
Claim 1. For each (x ̄, t ̄) with t0 − HQ−1 ≤ t ̄ ≤ t0 we have R(x, t) ≤ 4Q ̄
whenever t ̄ − cQ ̄−1 ≤ t ≤ t ̄ and distt ̄(x, x ̄) ≤ cQ ̄− 1
2 , where Q ̄ = Q + R(x ̄, t ̄) and c = c(κ) > 0 is a small constant.
Proof of Claim 1. Use the fact ( following from the choice of (x0, t0) and the description of the ancient solutions) that for each (x, t) with R(x, t) > 2Q and t0 − HQ−1 ≤ t ≤ t0 we have the estimates |Rt(x, t)| ≤ CR2(x, t), |∇R|(x, t) ≤ CR 3
2 (x, t).
Claim 2. There exists c = c(κ) > 0 and for any A > 0 there exist D = D(A) < ∞, ρ0 = ρ0(A) > 0, with the following property. Suppose that
r0 < ρ0, and let γ be a shortest geodesic with endpoints x ̄, x in gij(t ̄), for some
t ̄ ∈ [t0 − HQ−1, t0], such that R(y, t ̄) > 2Q for each y ∈ γ. Let z ∈ γ satisfy
cR(z, t ̄) > R(x ̄, t ̄) = Q ̄. Then distt ̄(x ̄, z) ≥ AQ ̄− 1
2 whenever R(x, t ̄) ≥ DQ ̄.
Proof of Claim 2. Note that from the choice of (x0, t0) and the description of the ancient solutions it follows that an appropriate parabolic (backward in time) neighborhood of a point y ∈ γ at t = t ̄ is ǫ-close to the evolving round
cylinder, provided c−1Q ̄ ≤ R(y, t ̄) ≤ cR(x, t ̄) for an appropriate c = c(κ). Now assume that the conclusion of the claim does not hold, take r0 to zero,
R(x, t ̄) - to infinity, and consider the scalings around (x ̄, t ̄) with factors Q ̄. We can imagine two possibilities for the behavior of the curvature along γ in the scaled metric: either it stays bounded at bounded distances from x ̄, or not. In the first case we can take a limit (for a subsequence) of the scaled metrics along γ and get a nonnegatively curved almost cylindrical metric, with γ going to infinity. Clearly, in this case the curvature at any point of the limit does not exceed c−1; therefore, the point z must have escaped to infinity, and the conclusion of the claim stands. In the second case, we can also take a limit along γ; it is a smooth nonnegatively curved manifold near x ̄ and has cylindrical shape where curvature is large; the radius of the cylinder goes to zero as we approach the (first) singular point, which is located at finite distance from x ̄; the region beyond
33


 the first singular point will be ignored. Thus, at t = t ̄ we have a metric, which is a smooth metric of nonnegative curvature away from a single singular point o. Since the metric is cylindrical at points close to o, and the radius of the cylinder is at most ǫ times the distance from o, the curvature at o is nonnegative in Aleksandrov sense. Thus, the metric near o must be cone-like. In other words, the scalings of our metric at points xi → o with
factors R(xi, t ̄) converge to a piece of nonnegatively curved non-flat metric cone. Moreover, using claim 1, we see that we actually have the convergence of the solutions to the Ricci flow on some time interval, and not just metrics at t = t ̄. Therefore, we get a contradiction with the strong maximum principle of Hamilton [H 2]. Now continue the proof of theorem, and recall that we are considering scalings at (x0, t0) with factor Q. It follows from claim 2 that at t = t0 the curvature of the scaled metric is bounded at bounded distances from x0. This allows us to extract a smooth limit at t = t0 (of course, we use the κ-noncollapsing assumption here). The limit has bounded nonnegative curvature (if the curvatures were unbounded, we would have a sequence of cylindrical necks with radii going to zero in a complete manifold of nonnegative curvature). Therefore, by claim 1, we have a limit not only at t = t0, but also in some interval of times smaller than t0. We want to show that the limit actually exists for all t < t0. Assume that this is not the case, and let t′ be the smallest value of time, such that the blowup limit can be taken on (t′, t0]. From the differential Harnack inequality of Hamilton [H 3] we have an estimate Rt(x, t) ≥ −R(x, t)(t−t′)−1, therefore, if
Q ̃ denotes the maximum of scalar curvature at t = t0, then R(x, t) ≤ Q ̃ t0−t′
t−t′ .
Hence by lemma 8.3(b) distt(x, y) ≤ distt0(x, y) + C for all t, where C =
10n(t0 − t′)
√
Q ̃.
The next step is needed only if our limit is noncompact. In this case there exists D > 0, such that for any y satisfying d = distt0(x0, y) > D, one
can find x satisfying distt0(x, y) = d, distt0(x, x0) > 3
2d. We claim that the
scalar curvature R(y, t) is uniformly bounded for all such y and all t ∈ (t′, t0]. Indeed, if R(y, t) is large, then the neighborhood of (y, t) is like in an ancient solution; therefore, (long) shortest geodesics γ and γ0, connecting at time t the point y to x and x0 respectively, make the angle close to 0 or π at y; the former case is ruled out by the assumptions on distances, if D > 10C; in the latter case, x and x0 are separated at time t by a small neighborhood of y,
with diameter of order R(y, t)− 1
2 , hence the same must be true at time t0,
34


 which is impossible if R(y, t) is too large. Thus we have a uniform bound on curvature outside a certain compact set, which has uniformly bounded diameter for all t ∈ (t′, t0]. Then claim 2 gives a uniform bound on curvature everywhere. Hence, by claim 1, we can extend our blow-up limit past t′ - a contradiction.
12.2 Theorem. Given a function φ as above, for any A > 0 there exists K = K(A) < ∞ with the following property. Suppose in dimension three we have a solution to the Ricci flow with φ-almost nonnegative curvature, which satisfies the assumptions of theorem 8.2 with r0 = 1. Then R(x, 1) ≤ K whenever dist1(x, x0) < A.
Proof. In the first step of the proof we check the following
Claim. There exists K = K(A) < ∞, such that a point (x, 1) satisfies the conclusion of the previous theorem 12.1 (for some fixed small ǫ > 0), whenever R(x, 1) > K and dist1(x, x0) < A.
The proof of this statement essentially repeats the proof of the previous theorem (the κ-noncollapsing assumption is ensured by theorem 8.2). The only difference is in the beginning. So let us argue by contradiction, and suppose we have a sequence of solutions and points x with dist1(x, x0) < A and R(x, 1) → ∞, which do not satisfy the conclusion of 12.1. Then an argument, similar to the one proving claims 1,2 in 10.1, delivers points (x ̄, t ̄) with 1
2 ≤ t ̄ ≤ 1, distt ̄(x ̄, x0) < 2A, with Q = R(x ̄, t ̄) → ∞, and such that
(x, t) satisfies the conclusion of 12.1 whenever R(x, t) > 2Q, t ̄− DQ−1 ≤ t ≤ t ̄, distt ̄(x ̄, x) < DQ− 1
2 , where D → ∞. (There is a little subtlety here in the application of lemma 8.3(b); nevertheless, it works, since we need to apply it only when the endpoint other than x0 either satisfies the conclusion of 12.1,
or has scalar curvature at most 2Q) After such (x ̄, t ̄) are found, the proof of 12.1 applies. Now, having checked the claim, we can prove the theorem by applying the claim 2 of the previous theorem to the appropriate segment of the shortest geodesic, connecting x and x0.
12.3 Theorem. For any w > 0 there exist τ = τ (w) > 0, K = K(w) < ∞, ρ = ρ(w) > 0 with the following property. Suppose we have a solution gij(t) to the Ricci flow, defined on M × [0, T ), where M is a closed threemanifold, and a point (x0, t0), such that the ball B(x0, r0) at t = t0 has
volume ≥ wr0n, and sectional curvatures ≥ −r0−2 at each point. Suppose that gij(t) is φ-almost nonnegatively curved for some function φ as above.
Then we have an estimate R(x, t) < Kr0−2 whenever t0 ≥ 4τ r02, t ∈ [t0 −
35


 τ r02, t0], distt(x, x0) ≤ 1
4 r0, provided that φ(r0−2) < ρ.
Proof. If we knew that sectional curvatures are ≥ −r0−2 for all t, then we could just apply corollary 11.6(b) (with the remark after its proof) and take τ (w) = τ0(w)/2, K(w) = C(w) + 2B(w)/τ0(w). Now fix these values of τ, K, consider a φ-almost nonnegatively curved solution gij(t), a point (x0, t0) and a radius r0 > 0, such that the assumptions of the theorem do hold whereas the conclusion does not. We may assume that any other point (x′, t′) and radius r′ > 0 with that property has either t′ > t0 or t′ < t0 − 2τ r02, or
2r′ > r0. Our goal is to show that φ(r0−2) is bounded away from zero.
Let τ ′ > 0 be the largest time interval such that Rm(x, t) ≥ −r0−2 when
ever t ∈ [t0 − τ ′r02, t0], distt(x, x0) ≤ r0. If τ ′ ≥ 2τ, we are done by corollary 11.6(b). Otherwise, by elementary Aleksandrov space theory, we can find at time t′ = t0 − τ ′r02 a ball B(x′, r′) ⊂ B(x0, r0) with V olB(x′, r′) ≥ 1
2 ωn(r′)n,
and with radius r′ ≥ cr0 for some small constant c = c(w) > 0. By the choice of (x0, t0) and r0, the conclusion of our theorem holds for (x′, t′), r′. Thus we have an estimate R(x, t) ≤ K(r′)−2 whenever t ∈ [t′ − τ (r′)2, t′], distt(x, x′) ≤
1
4r′. Now we can apply the previous theorem (or rather its scaled version) and
get an estimate on R(x, t) whenever t ∈ [t′ − 1
2 τ (r′)2, t′], distt(x′, x) ≤ 10r0.
Therefore, if r0 > 0 is small enough, we have Rm(x, t) ≥ −r0−2 for those (x, t), which is a contradiction to the choice of τ ′.
12.4 Corollary (from 12.2 and 12.3) Given a function φ as above, for any w > 0 one can find ρ > 0 such that if gij(t) is a φ-almost nonnegatively curved solution to the Ricci flow, defined on M × [0, T ), where M is a closed three-manifold, and if B(x0, r0) is a metric ball at time t0 ≥ 1, with r0 <
ρ, and such that min Rm(x, t0) over x ∈ B(x0, r0) is equal to −r0−2, then
V olB(x0, r0) ≤ wr0n.
13 The global picture of the Ricci flow in di
mension three
13.1 Let gij(t) be a smooth solution to the Ricci flow on M × [1, ∞), where M is a closed oriented three-manifold. Then, according to [H 6, theorem 4.1],
the normalized curvatures R ̃m(x, t) = tRm(x, t) satisfy an estimate of the
form R ̃m(x, t) ≥ −φ(R ̃(x, t))R ̃(x, t), where φ behaves at infinity as lo1g . This
estimate allows us to apply the results 12.3,12.4, and obtain the following
Theorem. For any w > 0 there exist K = K(w) < ∞, ρ = ρ(w) > 0,
36


 such that for sufficiently large times t the manifold M admits a thick-thin decomposition M = Mthick
⋃ Mthin with the following properties. (a) For
every x ∈ Mthick we have an estimate |R ̃m| ≤ K in the ball B(x, ρ(w)√t).
and the volume of this ball is at least 1
10 w(ρ(w)√t)n. (b) For every y ∈ Mthin
there exists r = r(y), 0 < r < ρ(w)√t, such that for all points in the ball B(y, r) we have Rm ≥ −r−2, and the volume of this ball is < wrn.
Now the arguments in [H 6] show that either Mthick is empty for large t, or , for an appropriate sequence of t → 0 and w → 0, it converges to a (possibly, disconnected) complete hyperbolic manifold of finite volume, whose cusps (if there are any) are incompressible in M. On the other hand, collapsing with lower curvature bound in dimension three is understood well enough to claim that, for sufficiently small w > 0, Mthin is homeomorphic to a graph manifold. The natural questions that remain open are whether the normalized curvatures must stay bounded as t → ∞, and whether reducible manifolds and manifolds with finite fundamental group can have metrics which evolve smoothly by the Ricci flow on the infinite time interval. 13.2 Now suppose that gij(t) is defined on M × [1, T ), T < ∞, and goes singular as t → T. Then using 12.1 we see that, as t → T, either the curvature goes to infinity everywhere, and then M is a quotient of either S3 or S2 × R, or the region of high curvature in gij(t) is the union of several necks and capped necks, which in the limit turn into horns (the horns most likely have finite diameter, but at the moment I don’t have a proof of that). Then at the time T we can replace the tips of the horns by smooth caps and continue running the Ricci flow until the solution goes singular for the next time, e.t.c. It turns out that those tips can be chosen in such a way that the need for the surgery will arise only finite number of times on every finite time interval. The proof of this is in the same spirit, as our proof of 12.1; it is technically quite complicated, but requires no essentially new ideas. It is likely that by passing to the limit in this construction one would get a canonically defined Ricci flow through singularities, but at the moment I don’t have a proof of that. (The positive answer to the conjecture in 11.9 on the uniqueness of ancient solutions would help here) Moreover, it can be shown, using an argument based on 12.2, that every maximal horn at any time T, when the solution goes singular, has volume at least cT n; this easily implies that the solution is smooth (if nonempty) from some finite time on. Thus the topology of the original manifold can
37


 be reconstructed as a connected sum of manifolds, admitting a thick-thin decomposition as in 13.1, and quotients of S3 and S2 × R. 13.3* Another differential-geometric approach to the geometrization conjecture is being developed by Anderson [A]; he studies the elliptic equations, arising as Euler-Lagrange equations for certain functionals of the riemannian metric, perturbing the total scalar curvature functional, and one can observe certain parallelism between his work and that of Hamilton, especially taking into account that, as we have shown in 1.1, Ricci flow is the gradient flow for a functional, that closely resembles the total scalar curvature.
References
[A] M.T.Anderson Scalar curvature and geometrization conjecture for three-manifolds. Comparison Geometry (Berkeley, 1993-94), MSRI Publ. 30 (1997), 49-82. [B-Em] D.Bakry, M.Emery Diffusions hypercontractives. Seminaire de Probabilites XIX, 1983-84, Lecture Notes in Math. 1123 (1985), 177-206. [Cao-C] H.-D. Cao, B.Chow Recent developments on the Ricci flow. Bull. AMS 36 (1999), 59-74. [Ch-Co] J.Cheeger, T.H.Colding On the structure of spaces with Ricci curvature bounded below I. Jour. Diff. Geom. 46 (1997), 406-480. [C] B.Chow Entropy estimate for Ricci flow on compact two-orbifolds. Jour. Diff. Geom. 33 (1991), 597-600. [C-Chu 1] B.Chow, S.-C. Chu A geometric interpretation of Hamilton’s Harnack inequality for the Ricci flow. Math. Res. Let. 2 (1995), 701-718. [C-Chu 2] B.Chow, S.-C. Chu A geometric approach to the linear trace Harnack inequality for the Ricci flow. Math. Res. Let. 3 (1996), 549-568. [D] E.D’Hoker String theory. Quantum fields and strings: a course for mathematicians (Princeton, 1996-97), 807-1011. [E 1] K.Ecker Logarithmic Sobolev inequalities on submanifolds of euclidean space. Jour. Reine Angew. Mat. 522 (2000), 105-118. [E 2] K.Ecker A local monotonicity formula for mean curvature flow. Ann. Math. 154 (2001), 503-525. [E-Hu] K.Ecker, G.Huisken In terior estimates for hypersurfaces moving by mean curvature. Invent. Math. 105 (1991), 547-569. [Gaw] K.Gawedzki Lectures on conformal field theory. Quantum fields and strings: a course for mathematicians (Princeton, 1996-97), 727-805.
38


 [G] L.Gross Logarithmic Sobolev inequalities and contractivity properties of semigroups. Dirichlet forms (Varenna, 1992) Lecture Notes in Math. 1563 (1993), 54-88. [H 1] R.S.Hamilton Three manifolds with positive Ricci curvature. Jour. Diff. Geom. 17 (1982), 255-306. [H 2] R.S.Hamilton Four manifolds with positive curvature operator. Jour. Diff. Geom. 24 (1986), 153-179. [H 3] R.S.Hamilton The Harnack estimate for the Ricci flow. Jour. Diff. Geom. 37 (1993), 225-243. [H 4] R.S.Hamilton Formation of singularities in the Ricci flow. Surveys in Diff. Geom. 2 (1995), 7-136. [H 5] R.S.Hamilton Four-manifolds with positive isotropic curvature. Commun. Anal. Geom. 5 (1997), 1-92. [H 6] R.S.Hamilton Non-singular solutions of the Ricci flow on threemanifolds. Commun. Anal. Geom. 7 (1999), 695-729. [H 7] R.S.Hamilton A matrix Harnack estimate for the heat equation. Commun. Anal. Geom. 1 (1993), 113-126. [H 8] R.S.Hamilton Monotonicity formulas for parabolic flows on manifolds. Commun. Anal. Geom. 1 (1993), 127-137. [H 9] R.S.Hamilton A compactness property for solutions of the Ricci flow. Amer. Jour. Math. 117 (1995), 545-572. [H 10] R.S.Hamilton The Ricci flow on surfaces. Contemp. Math. 71 (1988), 237-261. [Hu] G.Huisken Asymptotic behavior for singularities of the mean curvature flow. Jour. Diff. Geom. 31 (1990), 285-299. [I] T.Ivey Ricci solitons on compact three-manifolds. Diff. Geo. Appl. 3 (1993), 301-307. [L-Y] P.Li, S.-T. Yau On the parabolic kernel of the Schrodinger operator. Acta Math. 156 (1986), 153-201. [Lott] J.Lott Some geometric properties of the Bakry-Emery-Ricci tensor. arXiv:math.DG/0211065.
39