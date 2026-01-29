---
title: "Finite extinction time for the solutions to the Ricci flow on certain three-manifolds"
authors:
  - "Grisha Perelman"
date: "2003-07-17 2003-07-17"
publication: null
doi: "10.48550/arXiv.math/0307245"
url: "http://arxiv.org/abs/math/0307245"
zotero:
  attachment_key: "WRPAHBGV"
  parent_key: "F2SR47XH"
  item_id: 2254
  attachment_item_id: 2263
---

arXiv:math/0307245v1 [math.DG] 17 Jul 2003
Finite extinction time for the solutions to the
Ricci flow on certain three-manifolds
Grisha Perelman∗
November 26, 2024
In our previous paper we constructed complete solutions to the Ricci flow with surgery for arbitrary initial riemannian metric on a (closed, oriented) three-manifold [P,6.1], and used the behavior of such solutions to classify threemanifolds into three types [P,8.2]. In particular, the first type consisted of those manifolds, whose prime factors are diffeomorphic copies of spherical space forms and S2 × S1; they were characterized by the property that they admit metrics, that give rise to solutions to the Ricci flow with surgery, which become extinct in finite time. While this classification was sufficient to answer topological questions, an analytical question of significant independent interest remained open, namely, whether the solution becomes extinct in finite time for every initial metric on a manifold of this type. In this note we prove that this is indeed the case. Our argument (in conjunction with [P,§1-5]) also gives a direct proof of the so called ”elliptization conjecture”. It turns out that it does not require any substantially new ideas: we use only a version of the least area disk argument from [H,§11] and a regularization of the curve shortening flow from [A-G].
1 Finite time extinction
1.1 Theorem. Let M be a closed oriented three-manifold, whose prime decomposition contains no aspherical factors. Then for any initial metric on M the solution to the Ricci flow with surgery becomes extinct in finite time.
Proof for irreducible M . Let ΛM denote the space of all contractible loops in C1(S1 → M ). Given a riemannian metric g on M and c ∈ ΛM, define A(c, g) to be the infimum of the areas of all lipschitz maps from D2 to M, whose restriction to ∂D2 = S1 is c. For a family Γ ⊂ ΛM let A(Γ, g) be the supremum of A(c, g) over all c ∈ Γ. Finally, for a nontrivial homotopy class α ∈ π∗(ΛM, M ) let A(α, g) be the infimum of A(Γ, g) over all Γ ∈ α. Since M is not aspherical, it follows from a classical (and elementary) result of Serre that such a nontrivial homotopy class exists.
∗St.Petersburg branch of Steklov Mathematical Institute, Fontanka 27, St.Petersburg 191023, Russia. Email: perelman@pdmi.ras.ru or perelman@math.sunysb.edu
1


 1.2 Lemma. (cf. [H,§11]) If gt is a smooth solution to the Ricci flow, then for any α the rate of change of the function At = A(α, gt) satisfies the estimate
d
dt At ≤ −2π − 1
2 Rt
minAt
(in the sense of the lim sup of the forward difference quotients), where Rt
min
denotes the minimum of the scalar curvature of the metric gt.
A rigorous proof of this lemma will be given in §3, but the idea is simple and can be explained here. Let us assume that at time t the value At is attained by the family Γ, such that the loops c ∈ Γ where A(c, gt) is close to At are embedded and sufficiently smooth. For each such c consider the minimal disk Dc with boundary c and with area A(c, gt). Now let the metric evolve by the Ricci flow and let the curves c evolve by the curve shortening flow (which moves every point of the curve in the direction of its curvature vector at this point) with the same time parameter. Then the rate of change of the area of Dc can be computed as ∫
D
c
(−Tr(RicT)) +
∫
c
(−kg )
where RicT is the Ricci tensor of M restricted to the tangent plane of Dc, and kg is the geodesic curvature of c with respect to Dc (cf. [A-G, Lemma 3.2]). In three dimensions the first integrand equals − 1
2 R − (K − det II), where K is the intrinsic curvature of Dc and det II, the determinant of the second fundamental form, is nonpositive, because Dc is minimal. Thus, the rate of change of the area of Dc can be estimated from above by ∫
D
c
(− 1
2R − K) +
∫
c
(−kg) =
∫
D
c
(− 1
2 R) − 2π
by the Gauss-Bonnet theorem, and the statement of the lemma follows. The problem with this argument is that if Γ contains curves, which are not immersed (for instance, a curve could pass an arc once in one direction and then make an about turn and pass the same arc in the opposite direction), then it is not clear how to define curve shortening flow so that it would be continuous both in the time parameter and in the family parameter. In §3 we’ll explain how to circumvent this difficulty, essentially by adding one dimension to the ambient manifold. This regularization of the curve shortening flow has been worked out by Altschuler and Grayson [A-G] (who were interested in approximating the singular curve shortening flow on the plane and obtained for that case more precise results than what we need). 1.3 Now consider the solution to the Ricci flow with surgery. Since M is assumed irreducible, the surgeries are topologically trivial, that is one of the components of the post-surgery manifold is diffeomorphic to the pre-surgery manifold, and all the others are spheres. Moreover, by the construction of the surgery [P,4.4], the diffeomorphism from the pre-surgery manifold to the post-surgery one can be chosen to be distance non-increasing ( more precisely, (1 + ξ)-lipschitz, where ξ > 0 can be made as small as we like). It follows that
2


 the conclusion of the lemma above holds for the solutions to the Ricci flow with surgery as well. Now recall that the evolution equation for the scalar curvature
d
dt R = △R + 2|Ric|2 = △R + 2
3 R2 + 2|Ric◦|2
implies the estimate Rt
min ≥ − 3
2
1
t+const . It follows that Aˆt = At
t+const satisfies
d
dt Aˆt ≤ − 2π
t+const , which implies finite extinction time since the right hand side
is non-integrable at infinity whereas Aˆt can not become negative. 1.4 Remark. The finite time extinction result for irreducible non-aspherical manifolds already implies (in conjuction with the work in [P,§1-5] and the Kneser finiteness theorem) the so called ”elliptization conjecture”, claiming that a closed manifold with finite fundamental group is diffeomorphic to a spherical space form. The analysis of the long time behavior in [P,§6-8] is not needed in this case; moreover the argument in [P,§5] can be slightly simplified, replacing
the sequences rj , κj, δ ̄j by single values r, κ, δ ̄, since we already have an upper bound on the extinction time in terms of the initial metric. In fact, we can even avoid the use of the Kneser theorem. Indeed, if we start from an initial metric on a homotopy sphere (not assumed irreducible), then at each surgery time we have (almost) distance non-increasing homotopy equivalences from the pre-surgery manifold to each of the post-surgery components, and this is enough to keep track of the nontrivial relative homotopy class of the loop space. 1.5 Proof of theorem 1.1 for general M . The Kneser theorem implies that our solution undergoes only finitely many topologically nontrivial surgeries, so from some time T on all the surgeries are trivial. Moreover, by the Milnor uniqueness theorem, each component at time T satisfies the assumption of the theorem. Since we already know from 1.4 that there can not be any simply connected prime factors, it follows that every such component is either irreducible, or has nontrivial π2; in either case the proof in 1.1-1.3 works.
2 Preliminaries on the curve shortening flow
In this section we rather closely follow [A-G]. 2.1 Let M be a closed n-dimensional manifold, n ≥ 3, and let gt be a smooth family of riemannian metrics on M evolving by the Ricci flow on a finite time interval [t0, t1]. It is known [B] that gt for t > t0 are real analytic. Let ct be a solution to the curve shortening flow in (M, gt), that is ct satisfies the equation
d
dt ct(x) = Ht(x), where x is the parameter on S1, and Ht is the curvature
vector field of ct with respect to gt. It is known [G-H] that for any smoothly immersed initial curve c the solution ct exists on some time interval [t0, t′1), each ct for t > t0 is an analytic immersed curve, and either t′1 = t1, or the curvature kt = gt(Ht, Ht) 1
2 is unbounded when t → t′1.
3


 Denote by Xt the tangent vector field to ct, and let St = gt(Xt, Xt)− 1
2 Xt
be the unit tangent vector field; then H = ∇SS (from now on we drop the superscript t except where this omission can cause confusion). We compute
d
dt g(X, X) = −2Ric(X, X) − 2g(X, X)k2, (1)
which implies
[H, S] = (k2 + Ric(S, S))S (2)
Now we can compute
d
dt k2 = (k2)′′ − 2g((∇SH)⊥, (∇SH)⊥) + 2k4 + ..., (3)
where primes denote differentiation with respect to the arclength parameter s, and where dots stand for the terms containing the curvature tensor of g, which can be estimated in absolute value by const · (k2 + k). Thus the curvature k satisfies
d
dt k ≤ k′′ + k3 + const · (k + 1) (4)
Now it follows from (1) and (4) that the length L and the total curvature
Θ = ∫ kds satisfy
d
dt L ≤
∫
(const − k2)ds, (5)
d
dt Θ ≤
∫
const · (k + 1)ds (6)
In particular, both quantities can grow at most exponentially in t (they would be non-increasing in a flat manifold). 2.2 In general the curvature of ct may concentrate near certain points, creating singularities. However, if we know that this does not happen at some time t∗, then we can estimate the curvature and higher derivatives at times shortly thereafter. More precisely, there exist constants ǫ, C1, C2, ... (which may depend on the curvatures of the ambient space and their derivatives, but are independent of ct), such that if at time t∗ for some r > 0 the length of ct is at least r and the total curvature of each arc of length r does not exceed ǫ, then for every t ∈ (t∗, t∗ + ǫr2) the curvature k and higher derivatives satisfy the estimates k2 = g(H, H) ≤ C0(t − t∗)−1, g(∇S H, ∇SH) ≤ C1(t − t∗)−2, ... This can be proved by adapting the arguments of Ecker and Huisken [E-Hu]; see also [A-G,§4].
2.3 Now suppose that our manifold (M, gt) is a metric product (M ̄ , g ̄t) × S1
λ,
where the second factor is the circle of constant length λ; let U denote the unit
4


 tangent vector field to this factor. Then u = g(S, U ) satisfies the evolution equation
d
dt u = u′′ + (k2 + Ric(S, S))u (7)
Assume that u was strictly positive everywhere at time t0 (in this case the curve is called a ramp). Then it will remain positive and bounded away from zero as long as the solution exists. Now combining (4) and (7) we can estimate the right hand side of the evolution equation for the ratio k
u and conclude that
this ratio, and hence the curvature k, stays bounded (see [A-G,§2]). It follows that ct is defined on the whole interval [t0, t1]. 2.4 Assume now that we have two ramp solutions ct1, ct2, each winding once around the S1
λ factor. Let μt be the infimum of the areas of the annuli with
boundary ct1 ∪ ct2. Then
d
dt μt ≤ (2n − 1)|Rmt|μt, (8)
where |Rmt| denotes a bound on the absolute value of sectional curvatures of gt. Indeed, the curves ct1 and ct2, being ramps, are embedded and without substantial loss of generality we may assume them to be disjoint. In this case the results of Morrey [M] and Hildebrandt [Hi] yield an analytic minimal annulus A, immersed, except at most finitely many branch points, with prescribed boundary and with area μ. The rate of change of the area of A can be computed as ∫
A
(−Tr(RicT )) +
∫
∂A
(−kg) ≤
∫
A
(−Tr(RicT ) + K)
≤
∫
A
(−Tr(RicT ) + RmT ) ≤ (2n − 1)|Rm|μ,
where the first inequality comes from the Gauss-Bonnet theorem, with possible contribution of the branch points, and the second one is due to the fact that a minimal surface has nonpositive extrinsic curvature with respect to any normal vector. 2.5 The estimate (8) implies that μt can grow at most exponentially; in particular, if ct1 and ct2 were very close at time t0, then they would be close for all t ∈ [t0, t1] in the sense of minimal annulus area. In general this does not imply that the lengths of the curves are also close. However, an elementary argument shows that if ǫ > 0 is small then, given any r > 0, one can find μ ̄, depending only on r and on upper bound for sectional curvatures of the ambient space, such that if the length of ct1 is at least r, each arc of ct1 with length r has total curvature at most ǫ, and μt ≤ μ ̄, then L(ct2) ≥ (1 − 100ǫ)L(ct1).
3 Proof of lemma 1.2
3.1 In this section we prove the following statement
5


 Let M be a closed three-manifold, and let (M, gt) be a smooth solution to the Ricci flow on a finite time interval [t0, t1]. Suppose that Γ ⊂ ΛM is a compact family. Then for any ξ > 0 one can construct a continuous deformation Γt, t ∈ [t0, t1], Γt0 = Γ, such that for each curve c ∈ Γ either the value A(ct1 , gt1) is bounded from above by ξ plus the value at t = t1 of the solution to the ODE
d
dt w(t) = −2π − 1
2 Rt
minw(t) with the initial data w(t0) = A(ct0 , gt0), or
L(ct1) ≤ ξ; moreover, if c was a constant map, then all ct are constant maps. It is clear that our statement implies lemma 1.2, because a family consisting of very short loops can not represent a nontrivial relative homotopy class. 3.2 As a first step of the proof of the statement we can replace Γ by a family, which consists of piecewise geodesic loops with some large fixed number of vertices and with each segment reparametrized in some standard way to make the parametrizations of the whole curves twice continuously differentiable. Now consider the manifold Mλ = M × S1
λ, 0 < λ < 1, and for each c ∈ Γ consider the smooth embedded closed curve cλ such that p1cλ(x) = c(x) and p2cλ(x) = λx mod λ, where p1 and p2 are projections of Mλ to the first and second factor respectively, and x is the parameter of the curve c on the standard circle of length one. Using 2.3 we can construct a solution ctλ, t ∈ [t0, t1] to the curve shortening flow with initial data cλ. The required deformation will be obtained as Γt = p1Γtλ (where Γtλ denotes the family consisting of ctλ) for certain sufficiently small λ > 0. We’ll verify that an appropriate λ can be found for each individual curve c, or for any finite number of them, and then show that if our λ works for all elements of a μ-net in Γ, for sufficiently small μ > 0, then it works for all elements of Γ. 3.3 In the following estimates we shall denote by C large constants that may depend on metrics gt, family Γ and ξ, but are independent of λ, μ and a particular curve c. The first step in 3.2 implies that the lengths and total curvatures of cλ are uniformly bounded, so by 2.1 the same is true for all ct
λ. It follows that the area
swept by ct
λ, t ∈ [t′, t′′] ⊂ [t0, t1] is bounded above by C(t′′ − t′), and therefore we have the estimates A(p1ct
λ, gt) ≤ C, A(p1ct′′
λ , gt′′ ) − A(p1ct′
λ , gt′ ) ≤ C(t′′ − t′).
3.4 It follows from (5) that ∫ t1
t0
∫ k2dsdt ≤ C for any ct
λ. Fix some large constant B, to be chosen later. Then there is a subset IB(cλ) ⊂ [t0, t1] of
measure at least t1 − t0 − CB−1 where ∫ k2ds ≤ B, hence ∫ kds ≤ ǫ on any arc of length ≤ ǫ2B−1. Assuming that ctλ are at least that long, we can apply 2.2
and construct another subset JB(cλ) ⊂ [t0, t1] of measure at least t1−t0 −CB−1, consisting of finitely many intervals of measure at least C−1B−2 each, such that for any t ∈ JB(cλ) we have pointwise estimates on ctλ for curvature and higher derivatives, of the form k ≤ CB, ... Now fix c, B, and consider any sequence of λ → 0. Assume again that the lengths of ct
λ are bounded below by ǫ2B−1, at least for t ∈ [t0, t2], where t2 =
t1 − B−1. Then an elementary argument shows that we can find a subsequence Λc and a subset JB(c) ⊂ [t0, t2] of measure at least t1 − t0 − CB−1, consisting of finitely many intervals, such that JB(c) ⊂ JB(cλ) for all λ ∈ Λc. It follows that on every interval of JB(c) the curve shortening flows ct
λ smoothly converge
6


 (as λ → 0 in some subsequence of Λc ) to a curve shortening flow in M. Let wc(t) be the solution of the ODE d
dt wc(t) = −2π − 1
2 Rt
minwc(t) with
initial data wc(t0) = A(c, gt0 ). Then for sufficiently small λ ∈ Λc we have A(p1ctλ, gt) ≤ wc(t) + 1
2 ξ provided that B > Cξ−1. Indeed, on the intervals of JB(c) we can estimate the change of A for the limit flow using the minimal disk argument as in 1.2, and this implies the corresponding estimate for p1ct
λ if λ ∈ Λc is small enough, whereas for the intervals of the complement of JB(c) we can use the estimate in 3.3. On the other hand, if our assumption on the lower bound for lengths does not hold, then it follows from (5) that L(ct2
λ ) ≤ CB−1 ≤ 1
2 ξ.
3.5 Now apply the previous argument to all elements of some finite μ-net
ˆΓ ⊂ Γ for small μ > 0 to be determined later. We get a λ > 0 such that for each
cˆ ∈ ˆΓ either A(p1cˆt1
λ , gt1 ) ≤ wcˆ(t1) + 1
2 ξ or L(cˆt2
λ)≤ 1
2 ξ. Now for any curve c ∈ Γ
pick a curve cˆ ∈ Γˆ, μ-close to c, and apply the result of 2.4. It follows that if A(p1cˆt1
λ , gt1 ) ≤ wcˆ(t1) + 1
2 ξ and μ ≤ C−1ξ, then A(p1ct1
λ , gt1 ) ≤ wc(t1) + ξ. On
the other hand, if L(cˆt2
λ)≤ 1
2 ξ, then we can conclude that L(ct1
λ ) ≤ ξ provided
that μ > 0 is small enough in comparison with ξ and B−1. Indeed, if L(ct1
λ ) > ξ,
then L(ct
λ) > 3
4 ξ for all t ∈ [t2, t1]; on the other hand, using (5) we can find a
t ∈ [t2, t1], such that ∫ k2ds ≤ CB for ct
λ; hence, applying 2.5, we get L(cˆt
λ) > 2
3ξ
for this t, which is incompatible with L(cˆt2
λ)≤ 1
2 ξ. The proof of the statement 3.1 is complete.
References
[A-G] S.Altschuler, M.Grayson Shortening space curves and flow through singularities. Jour. Diff. Geom. 35 (1992), 283-298. [B] S.Bando Real analyticity of solutions of Hamilton’s equation. Math. Zeit. 195 (1987), 93-97. [E-Hu] K.Ecker, G.Huisken Interior estimates for hypersurfaces moving by mean curvature. Invent. Math. 105 (1991), 547-569. [G-H] M.Gage, R.S.Hamilton The heat equation shrinking convex plane curves. Jour. Diff. Geom. 23 (1986), 69-96. [H] R.S.Hamilton Non-singular solutions of the Ricci flow on three-manifolds. Commun. Anal. Geom. 7 (1999), 695-729. [Hi] S.Hildebrandt Boundary behavior of minimal surfaces. Arch. Rat. Mech. Anal. 35 (1969), 47-82. [M] C.B.Morrey The problem of Plateau on a riemannian manifold. Ann. Math. 49 (1948), 807-851. [P] G.Perelman Ricci flow with surgery on three-manifolds. arXiv:math.DG/0303109 v1
7