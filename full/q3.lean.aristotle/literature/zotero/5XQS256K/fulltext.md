---
title: "Ricci flow with surgery on three-manifolds"
authors:
  - "Grisha Perelman"
date: "2003-03-10 2003-03-10"
publication: null
doi: "10.48550/arXiv.math/0303109"
url: "http://arxiv.org/abs/math/0303109"
zotero:
  attachment_key: "A87TGFAF"
  parent_key: "5XQS256K"
  item_id: 2255
  attachment_item_id: 2265
---

arXiv:math/0303109v1 [math.DG] 10 Mar 2003
Ricci flow with surgery on three-manifolds
Grisha Perelman∗
February 1, 2008
This is a technical paper, which is a continuation of [I]. Here we verify most of the assertions, made in [I, §13]; the exceptions are (1) the statement that a 3-manifold which collapses with local lower bound for sectional curvature is a graph manifold - this is deferred to a separate paper, as the proof has nothing to do with the Ricci flow, and (2) the claim about the lower bound for the volumes of the maximal horns and the smoothness of the solution from some time on, which turned out to be unjustified, and, on the other hand, irrelevant for the other conclusions. The Ricci flow with surgery was considered by Hamilton [H 5,§4,5]; unfortunately, his argument, as written, contains an unjustified statement (RMAX = Γ, on page 62, lines 7-10 from the bottom), which I was unable to fix. Our approach is somewhat different, and is aimed at eventually constructing a canonical Ricci flow, defined on a largest possible subset of space-time, - a goal, that has not been achieved yet in the present work. For this reason, we consider two scale bounds: the cutoff radius h, which is the radius of the necks, where the surgeries are performed, and the much larger radius r, such that the solution on the scales less than r has standard geometry. The point is to make h arbitrarily small while keeping r bounded away from zero.
Notation and terminology
B(x, t, r) denotes the open metric ball of radius r, with respect to the metric at time t, centered at x. P (x, t, r, △t) denotes a parabolic neighborhood, that is the set of all points (x′, t′) with x′ ∈ B(x, t, r) and t′ ∈ [t, t + △t] or t′ ∈ [t + △t, t], depending on the sign of △t. A ball B(x, t, ǫ−1r) is called an ǫ-neck, if, after scaling the metric with factor r−2, it is ǫ-close to the standard neck S2 × I, with the product metric, where S2 has constant scalar curvature one, and I has length 2ǫ−1; here ǫ-close refers to CN topology, with N > ǫ−1. A parabolic neighborhood P (x, t, ǫ−1r, r2) is called a strong ǫ-neck, if, after scaling with factor r−2, it is ǫ-close to the evolving standard neck, which at each
∗St.Petersburg branch of Steklov Mathematical Institute, Fontanka 27, St.Petersburg 191011, Russia. Email: perelman@pdmi.ras.ru or perelman@math.sunysb.edu
1


 time t′ ∈ [−1, 0] has length 2ǫ−1 and scalar curvature (1 − t′)−1. A metric on S2 × I, such that each point is contained in some ǫ-neck, is called an ǫ-tube, or an ǫ-horn, or a double ǫ-horn, if the scalar curvature stays bounded on both ends, stays bounded on one end and tends to infinity on the other, and tends to infinity on both ends, respectively.
A metric on B3 or RP3 \ B ̄3, such that each point outside some compact subset is contained in an ǫ-neck, is called an ǫ-cap or a capped ǫ-horn, if the scalar curvature stays bounded or tends to infinity on the end, respectively. We denote by ǫ a fixed small positive constant. In contrast, δ denotes a positive quantity, which is supposed to be as small as needed in each particular argument.
1 Ancient solutions with bounded entropy
1.1 In this section we review some of the results, proved or quoted in [I,§11], correcting a few inaccuracies. We consider smooth solutions gij(t) to the Ricci flow on oriented 3-manifold M , defined for −∞ < t ≤ 0, such that for each t the metric gij (t) is a complete non-flat metric of bounded nonnegative sectional curvature, κ-noncollapsed on all scales for some fixed κ > 0; such solutions will be called ancient κ-solutions for short. By Theorem I.11.7, the set of all such solutions with fixed κ is compact modulo scaling, that is from any sequence of such solutions (M α, giαj(t)) and points (xα, 0) with R(xα, 0) = 1, we can extract a smoothly (pointed) convergent subsequence, and the limit (M, gij(t)) belongs to the same class of solutions. (The assumption in I.11.7. that M α be noncompact was clearly redundant, as it was not used in the proof. Note also that M need not have the same topology as M α.) Moreover, according to Proposition I.11.2, the scalings of any ancient κ-solution gij(t) with factors (−t)−1 about appropriate points converge along a subsequence of t → −∞ to a non-flat gradient shrinking soliton, which will be called an asymptotic soliton of the ancient solution. If the sectional curvature of this asymptotic soliton is not strictly positive, then by Hamilton’s strong maximum principle it admits local metric splitting, and it is easy to see that in this case the soliton is either the round infinite cylinder, or its Z2 quotient, containing one-sided projective plane. If the curvature is strictly positive and the soliton is compact, then it has to be a metric quotient of the round 3-sphere, by [H 1]. The noncompact case is ruled out below.
1.2 Lemma. There is no (complete oriented 3-dimensional) noncompact κ-noncollapsed gradient shrinking soliton with bounded positive sectional curvature.
Proof. A gradient shrinking soliton gij(t), −∞ < t < 0, satisfies the equation
∇i∇j f + Rij + 1
2t gij = 0 (1.1)
Differentiating and switching the order of differentiation, we get
∇iR = 2Rij∇jf (1.2)
2


 Fix some t < 0, say t = −1, and consider a long shortest geodesic γ(s), 0 ≤ s ≤ s ̄; let x = γ(0), x ̄ = γ(s ̄), X(s) = γ ̇ (s). Since the curvature is bounded and
positive, it is clear from the second variation formula that ∫ s ̄
0 Ric(X, X)ds ≤
const. Therefore, ∫ s ̄
0 |Ric(X, ·)|2ds ≤ const, and ∫ s ̄
0 |Ric(X, Y )|ds ≤ const(√s ̄ +
1) for any unit vector field Y along γ, orthogonal to X. Thus by integrating (1.1) we get X · f (γ(s ̄)) ≥ s ̄
2 + const, |Y · f (γ(s ̄))| ≤ const(√s ̄ + 1). We conclude
that at large distances from x0 the function f has no critical points, and its gradient makes small angle with the gradient of the distance function from x0. Now from (1.2) we see that R is increasing along the gradient curves of f,
in particular, R ̄ = lim sup R > 0. If we take a limit of our soliton about points
(xα, −1) where R(xα) → R ̄, then we get an ancient κ-solution, which splits off a line, and it follows from I.11.3, that this solution is the shrinking round
infinite cylinder with scalar curvature R ̄ at time t = −1. Now comparing the evolution equations for the scalar curvature on a round cylinder and for the
asymptotic scalar curvature on a shrinking soliton we conclude that R ̄ = 1. Hence, R(x) < 1 when the distance from x to x0 is large enough, and R(x) → 1 when this distance tends to infinity. Now let us check that the level surfaces of f, sufficiently distant from x0, are convex. Indeed, if Y is a unit tangent vector to such a surface, then ∇Y ∇Y f =
1
2 − Ric(Y, Y ) ≥ 1
2−R
2 > 0. Therefore, the area of the level surfaces grows as f
increases, and is converging to the area of the round sphere of scalar curvature one. On the other hand, the intrinsic scalar curvature of a level surface turns out to be less than one. Indeed, denoting by X the unit normal vector, this intrinsic curvature can be computed as
R − 2Ric(X, X) + 2 det(Hessf )
|∇f |2 ≤ R − 2Ric(X, X) + (1 − R + Ric(X, X))2
2|∇f |2 < 1
when R is close to one and |∇f | is large. Thus we get a contradiction to the Gauss-Bonnet formula. 1.3 Now, having listed all the asymptotic solitons, we can classify the ancient κ-solutions. If such a solution has a compact asymptotic soliton, then it is itself a metric quotient of the round 3-sphere, because the positive curvature pinching can only improve in time [H 1]. If the asymptotic soliton contains the one-sided projective plane, then the solution has a Z2 cover, whose asymptotic soliton is the round infinite cylinder. Finally, if the asymptotic soliton is the cylinder,then the solution can be either noncompact (the round cylinder itself, or the Bryant soliton, for instance), or compact. The latter possibility, which was overlooked in the first paragraph of [I.11.7], is illustrated by the example below, which also gives the negative answer to the question in the very end of [I.5.1]. 1.4 Example. Consider a solution to the Ricci flow, starting from a metric on S3 that looks like a long round cylinder S2 × I (say, with radius one and length L >> 1), with two spherical caps, smoothly attached to its boundary components. By [H 1] we know that the flow shrinks such a metric to a point in time, comparable to one (because both the lower bound for scalar curvature and the upper bound for sectional curvature are comparable to one) , and after
3


 normalization, the flow converges to the round 3-sphere. Scale the initial metric and choose the time parameter in such a way that the flow starts at time t0 = t0(L) < 0, goes singular at t = 0, and at t = −1 has the ratio of the maximal sectional curvature to the minimal one equal to 1 + ǫ. The argument in [I.7.3] shows that our solutions are κ-noncollapsed for some κ > 0 independent of L. We also claim that t0(L) → −∞ as L → ∞. Indeed, the Harnack inequality of Hamilton [H 3] implies that Rt ≥ R
t0−t , hence R ≤ 2(−1−t0)
t−t0 for t ≤ −1,
and then the distance change estimate d
dt distt(x, y) ≥ −const√Rmax(t)
from [H 2,§17] implies that the diameter of gij(t0) does not exceed −const · t0,
which is less than L√−t0 unless t0 is large enough. Thus, a subsequence of
our solutions with L → ∞ converges to an ancient κ-solution on S3, whose asymptotic soliton can not be anything but the cylinder. 1.5 The important conclusion from the classification above and the proof of Proposition I.11.2 is that there exists κ0 > 0, such that every ancient κ-solution is either κ0-solution, or a metric quotient of the round sphere. Therefore, the compactness theorem I.11.7 implies the existence of a universal constant η, such that at each point of every ancient κ-solution we have estimates
|∇R| < ηR 3
2 , |Rt| < ηR2 (1.3)
Moreover, for every sufficiently small ǫ > 0 one can find C1,2 = C1,2(ǫ), such that for each point (x, t) in every ancient κ-solution there is a radius r, 0 < r < C1R(x, t)− 1
2 , and a neighborhood B, B(x, t, r) ⊂ B ⊂ B(x, t, 2r), which falls into one of the four categories: (a) B is a strong ǫ-neck (more precisely, the slice of a strong ǫ-neck at its maximal time), or (b) B is an ǫ-cap, or
(c) B is a closed manifold, diffeomorphic to S3 or RP3, or (d) B is a closed manifold of constant positive sectional curvature;
furthermore, the scalar curvature in B at time t is between C2−1R(x, t) and
C2R(x, t), its volume in cases (a),(b),(c) is greater than C2−1R(x, t)− 3
2 , and in
case (c) the sectional curvature in B at time t is greater than C2−1R(x, t).
2 The standard solution
Consider a rotationally symmetric metric on R3 with nonnegative sectional curvature, which splits at infinity as the metric product of a ray and the round 2-sphere of scalar curvature one. At this point we make some choice for the metric on the cap, and will refer to it as the standard cap; unfortunately, the most obvious choice, the round hemisphere, does not fit, because the metric on R3 would not be smooth enough, however we can make our choice as close to it as we like. Take such a metric on R3 as the initial data for a solution gij(t) to the Ricci flow on some time interval [0, T ), which has bounded curvature for each t ∈ [0, T ).
Claim 1. The solution is rotationally symmetric for all t.
4


 Indeed, if ui is a vector field evolving by uit = △ui + Rijuj, then vij = ∇iuj evolves by (vij )t = △vij + 2Rikjlvkl − Rikvkj − Rkj vik. Therefore, if ui was a Killing field at time zero, it would stay Killing by the maximum principle. It is also clear that the center of the cap, that is the unique maximum point for the Busemann function, and the unique point, where all the Killing fields vanish, retains these properties, and the gradient of the distance function from this point stays orthogonal to all the Killing fields. Thus, the rotational symmetry is preserved.
Claim 2. The solution converges at infinity to the standard solution on the round infinite cylinder of scalar curvature one. In particular, T ≤ 1. Claim 3. The solution is unique.
Indeed, using Claim 1, we can reduce the linearized Ricci flow equation to the system of two equations on (−∞, +∞) of the following type
ft = f ′′ + a1f ′ + b1g′ + c1f + d1g, gt = a2f ′ + b2g′ + c2f + d2g,
where the coefficients and their derivatives are bounded, and the unknowns f, g and their derivatives tend to zero at infinity by Claim 2. So we get uniqueness by looking at the integrals ∫ A
−A (f 2 + g2) as A → ∞.
Claim 4. The solution can be extended to the time interval [0, 1).
Indeed, we can obtain our solution as a limit of the solutions on S3, starting from the round cylinder S2 × I of length L and scalar curvature one, with two caps attached; the limit is taken about the center p of one of the caps, L → ∞. Assume that our solution goes singular at some time T < 1. Take T1 < T very close to T, T − T1 << 1 − T. By Claim 2, given δ > 0, we can find
L ̄, D ̄ < ∞, depending on δ and T1, such that for any point x at distance D ̄
from p at time zero, in the solution with L ≥ L ̄, the ball B(x, T1, 1) is δ-close
to the corresponding ball in the round cylinder of scalar curvature (1 − T1)−1. We can also find r = r(δ, T ), independent of T1, such that the ball B(x, T1, r) is δ-close to the corresponding euclidean ball. Now we can apply Theorem I.10.1 and get a uniform estimate on the curvature at x as t → T , provided that T − T1 < ǫ2r(δ, T )2. Therefore, the t → T limit of our limit solution on the capped infinite cylinder will be smooth near x. Thus, this limit will be a positively curved space with a conical point. However, this leads to a contradiction via a blow-up argument; see the end of the proof of the Claim 2 in I.12.1. The solution constructed above will be called the standard solution.
Claim 5. The standard solution satisfies the conclusions of 1.5 , for an appropriate choice of ǫ, η, C1(ǫ), C2(ǫ), except that the ǫ-neck neighborhood need not be strong; more precisely, we claim that if (x, t) has neither an ǫ-cap neighborhood as in 1.5(b), nor a strong ǫ-neck neighborhood as in 1.5(a), then x is not in B(p, 0, ǫ−1), t < 3/4, and there is an ǫ-neck B(x, t, ǫ−1r), such that the solution in P (x, t, ǫ−1r, −t) is, after scaling with factor r−2, ǫ-close to the appropriate piece of the evolving round infinite cylinder. Moreover, we have an estimate Rmin(t) ≥ const · (1 − t)−1.
5


 Indeed, the statements follow from compactness and Claim 2 on compact subintervals of [0, 1), and from the same arguments as for ancient solutions, when t is close to one.
3 The structure of solutions at the first singular time
Consider a smooth solution gij(t) to the Ricci flow on M × [0, T ), where M is a closed oriented 3-manifold, T < ∞. Assume that curvature of gij (t) does not stay bounded as t → T. Recall that we have a pinching estimate Rm ≥ −φ(R)R for some function φ decreasing to zero at infinity [H 4,§4], and that the solution is κ-noncollapsed on the scales ≤ r for some κ > 0, r > 0 [I, §4].Then by Theorem I.12.1 and the conclusions of 1.5 we can find r = r(ǫ) > 0, such that each point (x, t) with R(x, t) ≥ r−2 satisfies the estimates (1.3) and has a neighborhood, which is either an ǫ-neck, or an ǫ-cap, or a closed positively curved manifold. In the latter case the solution becomes extinct at time T, so we don’t need to consider it any more. If this case does not occur, then let Ω denote the set of all points in M, where curvature stays bounded as t → T. The estimates (1.3) imply that Ω is open and that R(x, t) → ∞ as t → T for each x ∈ M \Ω. If Ω is empty, then the solution becomes extinct at time T and it is entirely covered by ǫ-necks and caps shortly before that time, so it is easy to see that M is diffeomorphic to
either S3, or RP3, or S2 × S1, or RP3 ♯ RP3. Otherwise, if Ω is not empty, we may (using the local derivative estimates due to W.-X.Shi, see [H 2,§13]) consider a smooth metric g ̄ij on Ω, which is the limit of gij(t) as t → T. Let Ωρ for some ρ < r denotes the set of points x ∈ Ω,
where the scalar curvature R ̄(x) ≤ ρ−2. We claim that Ωρ is compact. Indeed, if
R ̄(x) ≤ ρ−2, then we can estimate the scalar curvature R(x, t) on [T − η−1ρ2, T ) using (1.3), and for earlier times by compactness, so x is contained in Ω with a ball of definite size, depending on ρ. Now take any ǫ-neck in (Ω, g ̄ij) and consider a point x on one of its boundary components. If x ∈ Ω\Ωρ, then there is either an ǫ-cap or an ǫ-neck, adjacent to the initial ǫ-neck. In the latter case we can take a point on the boundary of the second ǫ-neck and continue. This procedure can either terminate when we reach a point in Ωρ or an ǫ-cap, or go on indefinitely, producing an ǫ-horn. The same procedure can be repeated for the other boundary component of the initial ǫ-neck. Therefore, taking into account that Ω has no compact components, we conclude that each ǫ-neck of (Ω, g ̄ij ) is contained in a subset of Ω of one of the following types: (a) An ǫ-tube with boundary components in Ωρ, or (b) An ǫ-cap with boundary in Ωρ, or (c) An ǫ-horn with boundary in Ωρ, or (d) A capped ǫ-horn, or (e) A double ǫ-horn.
6


 Clearly, each ǫ-cap, disjoint from Ωρ, is also contained in one of the subsets above. It is also clear that there is a definite lower bound (depending on ρ) for the volume of subsets of types (a),(b),(c), so there can be only finite number of them. Thus we can conclude that there is only a finite number of components of Ω, containing points of Ωρ, and every such component has a finite number of ends, each being an ǫ-horn. On the other hand, every component of Ω, containing no points of Ωρ, is either a capped ǫ-horn, or a double ǫ-horn. Now, by looking at our solution for times t just before T, it is easy to see that the topology of M can be reconstructed as follows: take the components Ωj, 1 ≤ j ≤ i of Ω which contain points of Ωρ, truncate their ǫ-horns, and glue to the boundary components of truncated Ωj a collection of tubes S2 × I and caps
B3 or RP3\B3. Thus, M is diffeomorphic to a connected sum of  ̄Ωj, 1 ≤ j ≤ i, with a finite number of S2 × S1 (which correspond to gluing a tube to two
boundary components of the same Ωj), and a finite number of RP3; here  ̄Ωj denotes Ωj with each ǫ-horn one point compactified.
4 Ricci flow with cutoff
4.1 Suppose we are given a collection of smooth solutions gij(t) to the Ricci flow, defined on Mk × [t−
k , t+
k ), which go singular as t → t+
k . Let (Ωk, g ̄ikj) be the limits
of the corresponding solutions as t → t+
k , as in the previous section. Suppose also that for each k we have t−
k = t+
k−1, and (Ωk−1, g ̄k−1
ij ) and (Mk, gikj (t−
k )) contain compact (possibly disconnected) three-dimensional submanifolds with smooth boundary, which are isometric. Then we can identify these isometric submanifolds and talk about the solution to the Ricci flow with surgery on the union of all [t−
k , t+
k ).
Fix a small number ǫ > 0 which is admissible in sections 1,2. In this section we consider only solutions to the Ricci flow with surgery, which satisfy the following a priori assumptions: (pinching) There exists a function φ, decreasing to zero at infinity, such that Rm ≥ −φ(R)R,
(canonical neighborhood) There exists r > 0, such that every point where scalar curvature is at least r−2 has a neighborhood, satisfying the conclusions of 1.5. (In particular, this means that if in case (a) the neighborhood in question is B(x0, t0, ǫ−1r0), then the solution is required to be defined in the whole
P (x0, t0, ǫ−1r0, −r02); however, this does not rule out a surgery in the time in
terval (t0 − r02, t0), that occurs sufficiently far from x0.) Recall that from the pinching estimate of Ivey and Hamilton, and Theorem I.12.1, we know that the a priori assumptions above hold for a smooth solution on any finite time interval. For Ricci flow with surgery they will be justified in the next section.
4.2 Claim 1. Suppose we have a solution to the Ricci flow with surgery, satisfying the canonical neighborhood assumption, and let Q = R(x0, t0)+r−2. Then we have estimate R(x, t) ≤ 8Q for those (x, t) ∈ P (x0, t0, 1
2 η−1Q− 1
2,−1
8 η−1Q−1),
for which the solution is defined.
7


 Indeed, this follows from estimates (1.3).
Claim 2. For any A < ∞ one can find Q = Q(A) < ∞ and ξ = ξ(A) > 0 with the following property. Suppose we have a solution to the Ricci flow with surgery, satisfying the pinching and the canonical neighborhood assumptions. Let γ be a shortest geodesic in gij (t0) with endpoints x0 and x, such
that R(y, t0) > r−2 for each y ∈ γ, and Q0 = R(x0, t0) is so large that φ(Q0) < ξ. Finally, let z ∈ γ be any point satisfying R(z, t0) > 10C2R(x0, t0).
Then distt0 (x0, z) ≥ AQ− 1
2
0 whenever R(x, t0) > QQ0.
The proof is exactly the same as for Claim 2 in Theorem I.12.1; in the very end of it, when we get a piece of a non-flat metric cone as a blow-up limit, we get a contradiction to the canonical neighborhood assumption, because the canonical neighborhoods of types other than (a) are not close to a piece of metric cone, and type (a) is ruled out by the strong maximum principle, since the ǫ-neck in question is strong. 4.3 Suppose we have a solution to the Ricci flow with surgery, satisfying our a priori assumptions, defined on [0, T ), and going singular at time T. Choose a small δ > 0 and let ρ = δr. As in the previous section, consider the limit (Ω, g ̄ij ) of our solution as t → T, and the corresponding compact set Ωρ.
Lemma. There exists a radius h, 0 < h < δρ, depending only on δ, ρ and the
pinching function φ, such that for each point x with h(x) = R ̄− 1
2 (x) ≤ h in an ǫhorn of (Ω, g ̄ij) with boundary in Ωρ, the neighborhood P (x, T, δ−1h(x), −h2(x)) is a strong δ-neck.
Proof. An argument by contradiction. Assuming the contrary, take a sequence of solutions with limit metrics (Ωα, g ̄iαj) and points xα with h(xα) → 0.
Since xα lies deeply inside an ǫ-horn, its canonical neighborhood is a strong ǫ-neck. Now Claim 2 gives the curvature estimate that allows us to take a limit of appropriate scalings of the metrics giαj on [T − h2(xα), T ] about xα, for a subsequence of α → ∞. By shifting the time parameter we may assume that the limit is defined on [−1, 0]. Clearly, for each time in this interval, the limit is a complete manifold with nonnegative sectional curvature; moreover, since xα was contained in an ǫ-horn with boundary in Ωρα, and h(xα)/ρ → 0, this manifold
has two ends. Thus, by Toponogov, it admits a metric splitting S2 × R. This implies that the canonical neighborhood of the point (xα, T − h2(xα)) is also of type (a), that is a strong ǫ-neck, and we can repeat the procedure to get the limit, defined on [−2, 0], and so on. This argument works for the limit in any finite time interval [−A, 0], because h(xα)/ρ → 0. Therefore, we can construct a limit on [−∞, 0]; hence it is the round cylinder, and we get a contradiction. 4.4 Now we can specialize our surgery and define the Ricci flow with δ-cutoff. Fix δ > 0, compute ρ = δr and determine h from the lemma above. Given a smooth metric gij on a closed manifold, run the Ricci flow until it goes singular at some time t+; form the limit (Ω, g ̄ij). If Ωρ is empty, the procedure stops here, and we say that the solution became extinct. Otherwise we remove the components of Ω which contain no points of Ωρ, and in every ǫ-horn of each of the remaining components we find a δ-neck of radius h, cut it along the middle two-sphere, remove the horn-shaped end, and glue in an almost standard cap
8


 in such a way that the curvature pinching is preserved and a metric ball of radius (δ′)−1h centered near the center of the cap is, after scaling with factor h−2, δ′-close to the corresponding ball in the standard capped infinite cylinder, considered in section 2. (Here δ′ is a function of δ alone, which tends to zero with δ.) The possibility of capping a δ-neck preserving a certain pinching condition in dimension four was proved by Hamilton [H 5,§4]; his argument works in our case too (and the estimates are much easier to verify). The point is that we can change our δ-neck metric near the middle of the neck by a conformal factor e−f , where f = f (z) is positive on the part of the neck we want to remove, and zero on the part we want to preserve, and z is the coordinate along I in our parametrization S2 × I of the neck. Then, in the region near the middle of the neck, where f is small, the dominating terms in the formulas for the change of curvature are just positive constant multiples of f ′′, so the pinching improves, and all the curvatures become positive on the set where f > δ′. Now we can continue our solution until it becomes singular for the next time. Note that after the surgery the manifold may become disconnected; in this case, each component should be dealt with separately. Furthermore, let us agree to declare extinct every component which is ǫ-close to a metric quotient of the round sphere; that allows to exclude such components from the list of canonical neighborhoods. Now since every surgery reduces the volume by at least h3, the sequence of surgery times is discrete, and, taking for granted the a priori assumptions, we can continue our solution indefinitely, not ruling out the possibility that it may become extinct at some finite time. 4.5 In order to justify the canonical neighborhood assumption in the next section, we need to check several assertions.
Lemma. For any A < ∞, 0 < θ < 1, one can find δ ̄ = δ ̄(A, θ) with the following property. Suppose we have a solution to the Ricci flow with δ-cutoff,
satisfying the a priori assumptions on [0, T ], with δ < δ ̄. Suppose we have a surgery at time T0 ∈ (0, T ), let p correspond to the center of the standard cap,
and let T1 = min(T, T0 + θh2). Then either (a) The solution is defined on P (p, T0, Ah, T1 − T0), and is, after scaling with
factor h−2 and shifting time T0 to zero, A−1-close to the corresponding subset on the standard solution from section 2, or (b) The assertion (a) holds with T1 replaced by some time t+ ∈ [T0, T1), where
t+ is a surgery time; moreover, for each point in B(p, T0, Ah), the solution is
defined for t ∈ [T0, t+) and is not defined past t+.
Proof. Let Q be the maximum of the scalar curvature on the standard solution in the time interval [0, θ], let △t = N −1(T1 − T0) < ǫη−1Q−1h2, and let tk = T0 + k△t, k = 0, ..., N.
Assume first that for each point in B(p, T0, A0h), where A0 = ǫ(δ′)−1, the solution is defined on [t0, t1]. Then by (1.3) and the choice of △t we have a
uniform curvature bound on this set for h−2-scaled metric. Therefore we can define A1, depending only on A0 and tending to infinity with A0, such that
the solution in P (p, T0, A1h, t1 − t0) is, after scaling and time shifting, A1−1close to the corresponding subset in the standard solution. In particular, the
9


 scalar curvature on this subset does not exceed 2Qh−2. Now if for each point in B(p, T0, A1h) the solution is defined on [t1, t2], then we can repeat the procedure, defining A2 etc. Continuing this way, we eventually define AN , and it would remain to choose δ so small, and correspondingly A0 so large, that AN > A. Now assume that for some k, 0 ≤ k < N, and for some x ∈ B(p, T0, Akh) the solution is defined on [t0, tk] but not on [tk, tk+1]. Then we can find a surgery
time t+ ∈ [tk, tk+1], such that the solution on B(p, T0, Akh) is defined on [t0, t+),
but for some points of this ball it is not defined past t+. Clearly, the A−1
k+1 
closeness assertion holds on P (p, T0, Ak+1h, t+ − T0). On the other hand, the
solution on B(p, T0, Akh) is at least ǫ-close to the standard one for all t ∈ [tk, t+), hence no point of this set can be the center of a δ-neck neighborhood at time t+. However, the surgery is always done along the middle two-sphere of such a neck. It follows that for each point of B(p, T0, Akh) the solution terminates at
t+.
4.6 Corollary. For any l < ∞ one can find A = A(l) < ∞ and θ = θ(l), 0 < θ < 1, with the following property. Suppose we are in the situation
of the lemma above, with δ < δ ̄(A, θ). Consider smooth curves γ in the set B(p, T0, Ah), parametrized by t ∈ [T0, Tγ], such that γ(T0) ∈ B(p, T0, Ah/2) and either Tγ = T1 < T , or Tγ < T1 and γ(Tγ) ∈ ∂B(p, T0, Ah). Then
∫ Tγ
T0 (R(γ(t), t) + |γ ̇ (t)|2)dt > l.
Proof. Indeed, if Tγ = T1, then on the standard solution we would have
∫ Tγ
T0 R(γ(t), t)dt ≥ const ∫ θ
0 (1 − t)−1dt = −const · (log(1 − θ))−1, so by choosing
θ sufficiently close to one we can handle this case. Then we can choose A so large that on the standard solution distt(p, ∂B(p, 0, A)) ≥ 3A/4 for each t ∈ [0, θ]. Now if γ(Tγ) ∈ ∂B(p, T0, Ah) then ∫ Tγ
T0 |γ ̇ (t)|2dt ≥ A2/100, so by taking A large
enough, we can handle this case as well.
4.7 Corollary. For any Q < ∞ there exists θ = θ(Q), 0 < θ < 1 with the following property. Suppose we are in the situation of the lemma above,
with δ < δ ̄(A, θ), A > ǫ−1. Suppose that for some point x ∈ B(p, T0, Ah) the
solution is defined at x (at least) on [T0, Tx], Tx ≤ T, and satisfies Q−1R(x, t) ≤
R(x, Tx) ≤ Q(Tx − T0)−1 for all t ∈ [T0, Tx]. Then Tx ≤ T0 + θh2.
Proof. Indeed, if Tx > T0 + θh2, then by lemma R(x, T0 + θh2) ≥
const · (1 − θ)−1h−2, whence R(x, Tx) ≥ const · Q−1(1 − θ)−1h−2, and Tx − T0 ≤
const · Q2(1 − θ)h2 < θh2 if θ is close enough to one.
5 Justification of the a priori assumption
5.1 Let us call a riemannian manifold (M, gij) normalized if M is a closed oriented 3-manifold, the sectional curvatures of gij do not exceed one in absolute value, and the volume of every metric ball of radius one is at least half the volume of the euclidean unit ball. For smooth Ricci flow with normalized initial data we have, by [H 4, 4.1], at any time t > 0 the pinching estimate
Rm ≥ −φ(R(t + 1))R, (5.1)
10


 where φ is a decreasing function, which behaves at infinity like 1
log . As explained
in 4.4, this pinching estimate can be preserved for Ricci flow with δ-cutoff. Justification of the canonical neighborhood assumption requires additional arguments. In fact, we are able to construct solutions satisfying this assumption only allowing r and δ be functions of time rather than constants; clearly, the arguments of the previous section are valid in this case, if we assume that r(t), δ(t) are non-increasing, and bounded away from zero on every finite time interval. Proposition. There exist decreasing sequences 0 < rj < ǫ2, κj > 0, 0 <
δ ̄j < ǫ2, j = 1, 2, ..., such that for any normalized initial data and any function
δ(t), satisfying 0 < δ(t) < δ ̄j for t ∈ [2j−1ǫ, 2jǫ], the Ricci flow with δ(t)-cutoff is defined for t ∈ [0, +∞] and satisfies the κj-noncollapsing assumption and the canonical neighborhood assumption with parameter rj on the time interval [2j−1ǫ, 2jǫ].( Recall that we have excluded from the list of canonical neighborhoods the closed manifolds, ǫ-close to metric quotients of the round sphere. Complete extinction of the solution in finite time is not ruled out.)
The proof of the proposition is by induction: having constructed our se
quences for 1 ≤ j ≤ i, we make one more step, defining ri+1, κi+1, δ ̄i+1, and
redefining δ ̄i = δ ̄i+1; each step is analogous to the proof of Theorem I.12.1. First we need to check a κ-noncollapsing condition.
5.2 Lemma. Suppose we have constructed the sequences, satisfying the proposition for 1 ≤ j ≤ i. Then there exists κ > 0, such that for any r, 0 < r <
ǫ2, one can find δ ̄ = δ ̄(r) > 0, which may also depend on the already constructed sequences, with the following property. Suppose we have a solution to the Ricci flow with δ(t)-cutoff on a time interval [0, T ], with normalized initial data, satisfying the proposition on [0, 2iǫ], and the canonical neighborhood assumption with
parameter r on [2iǫ, T ], where 2iǫ ≤ T ≤ 2i+1ǫ, 0 < δ(t) < δ ̄ f or t ∈ [2i−1ǫ, T ]. Then it is κ-noncollapsed on all scales less than ǫ.
Proof. Consider a neighborhood P (x0, t0, r0, −r02), 2iǫ < t0 ≤ T, 0 < r0 <
ǫ, where the solution is defined and satisfies |Rm| ≤ r0−2. We may assume r0 ≥ r, since otherwise the lower bound for the volume of the ball B(x0, t0, r0) follows from the canonical neighborhood assumption. If the solution was smooth everywhere, we could estimate from below the volume of the ball B(x0, t0, r0) using the argument from [I.7.3]: define τ (t) = t0 − t and consider the reduced volume function using the L-exponential map from x0; take a point (x, ǫ) where the reduced distance l attains its minimum for τ = t0 − ǫ, l(x, τ ) ≤ 3/2; use it to obtain an upper bound for the reduced distance to the points of B(x, 0, 1), thus getting a lower bound for the reduced volume at τ = t0, and apply the monotonicity formula. Now if the solution undergoes surgeries, then we still can measure the L-length, but only for admissible curves, which stay in the region, unaffected by surgery. An inspection of the constructions in [I,§7] shows that the argument would go through if we knew that every barely admissible curve, that is a curve on the boundary of the set of admissible curves, has reduced length at least 3/2 + κ′ for some fixed κ′ > 0. Unfortunately, at the moment I don’t see how to ensure that without imposing new restrictions on δ(t) for all t ∈ [0, T ], so we need some additional arguments. Recall that for a curve γ, parametrized by t, with γ(t0) = x0, we have
11


 L(γ, τ ) = ∫ t0
t0−τ
√t0 − t(R(γ(t), t) + |γ ̇ (t)|2)dt. We can also define L+(γ, τ ) by
replacing in the previous formula R with R+ = max(R, 0). Then L+ ≤ L+4T √T because R ≥ −6 by the maximum principle and normalization. Now suppose we could show that every barely admissible curve with endpoints (x0, t0) and (x, t),
where t ∈ [2i−1ǫ, T ), has L+ > 2ǫ−2T √T ; then we could argue that either there
exists a point (x, t), t ∈ [2i−1ǫ, 2iǫ], such that R(x, t) ≤ r−2
i and L+ ≤ ǫ−2T √T , in which case we can take this point in place of (x, ǫ) in the argument of the previous paragraph, and obtain (using Claim 1 in 4.2) an estimate for κ in terms of ri, κi, T, or for any γ, defined on [2i−1ǫ, t0], γ(t0) = x0, we have L+ ≥
min(ǫ−2T √T , 2
3 (2i−1ǫ) 3
2 r−2
i ) > ǫ−2T √T , which is in contradiction with the
assumed bound for barely admissible curves and the bound min l(x, t0−2i−1ǫ) ≤ 3/2, valid in the smooth case. Thus, to conclude the proof it is sufficient to check the following assertion.
5.3 Lemma. For any L < ∞ one can find δ ̄ = δ ̄(L, r0) > 0 with the following property. Suppose that in the situation of the previous lemma we have a curve γ, parametrized by t ∈ [T0, t0], 2i−1ǫ ≤ T0 < t0, such that γ(t0) = x0,
T0 is a surgery time, and γ(T0) ∈ B(p, T0, ǫ−1h), where p corresponds to the center of the cap, and h is the radius of the δ-neck. Then we have an estimate
∫ t0 T0
√t0 − t(R+(γ(t), t) + |γ ̇ (t)|2)dt ≥ L.
Proof. It is clear that if we take △t = ǫr04L−2, then either γ satisfies our estimate, or γ stays in P (x0, t0, r0, −△t) for t ∈ [t0 − △t, t0]. In the latter case our estimate follows from Corollary 4.6, for l = L(△t)− 1
2 , since clearly Tγ < t0 − △t when δ is small enough.
5.4 Proof of proposition. Assume the contrary, and let the sequences rα, δ ̄αβ
be such that rα → 0 as α → ∞, δ ̄αβ → 0 as β → ∞ with fixed α, and let
(M αβ , gαβ
ij ) be normalized initial data for solutions to the Ricci flow with δ(t)
cutoff, δ(t) < δ ̄αβ on [2i−1ǫ, 2i+1ǫ], which satisfy the statement on [0, 2iǫ], but violate the canonical neighborhood assumption with parameter rα on [2iǫ, 2i+1ǫ]. Slightly abusing notation, we’ll drop the indices α, β when we consider an individual solution. Let t ̄ be the first time when the assumption is violated at some point x ̄; clearly such time exists, because it is an open condition. Then by lemma 5.2 we have uniform κ-noncollapsing on [0, t ̄]. Claims 1,2 in 4.2 are also valid on [0, t ̄]; moreover, since h << r, it follows from Claim 1 that the solution is defined on the whole parabolic neighborhood indicated there in case R(x0, t0) ≤ r−2.
Scale our solution about (x ̄, t ̄) with factor R(x ̄, t ̄) ≥ r−2 and take a limit for subsequences of α, β → ∞. At time t ̄, which we’ll shift to zero in the limit, the curvature bounds at finite distances from x ̄ for the scaled metric are ensured by Claim 2 in 4.2. Thus, we get a smooth complete limit of nonnegative sectional curvature, at time zero. Moreover, the curvature of the limit is uniformly bounded, since otherwise it would contain ǫ-necks of arbitrarily small radius. Let Q0 denote the curvature bound. Then, if there was no surgery, we could,
using Claim 1 in 4.2, take a limit on the time interval [−ǫη−1Q0−1, 0]. To prevent
this, there must exist surgery times T0 ∈ [t ̄ − ǫη−1Q0−1R−1(x ̄, t ̄), t ̄] and points
x with dist2
T0 (x, x ̄)R−1(x ̄, t ̄) uniformly bounded as α, β → ∞, such that the
12


 solution at x is defined on [T0, t ̄], but not before T0. Using Claim 2 from 4.2 at
time T0, we see that R(x ̄, t ̄)h2(T0) must be bounded away from zero. Therefore, in this case we can apply Corollary 4.7, Lemma 4.5 and Claim 5 in section 2 to show that the point (x ̄, t ̄) in fact has a canonical neighborhood, contradicting its choice. (It is not excluded that the strong ǫ-neck neighborhood extends to times before T0, where it is a part of the strong δ-neck that existed before surgery.) Thus we have a limit on a certain time interval. Let Q1 be the curvature bound for this limit. Then we either can construct a limit on the time interval [−ǫη−1(Q0−1 + Q1−1), 0], or there is a surgery, and we get a contradiction as before. We can continue this procedure indefinitely, and the final part of the proof of Theorem I.12.1 shows that the bounds Qk can not go to infinity while the limit is defined on a bounded time interval. Thus we get a limit on (−∞, 0], which is κ-noncollapsed by Lemma 5.2, and this means that (x ̄, t ̄) has a canonical neighborhood by the results of section 1 - a contradiction.
6 Long time behavior I
6.1 Let us summarize what we have achieved so far. We have shown the exis
tence of decreasing (piecewise constant) positive functions r(t) and δ ̄(t) (which we may assume converging to zero at infinity), such that if (M, gij) is a normal
ized manifold, and 0 < δ(t) < δ ̄(t), then there exists a solution to the Ricci flow with δ(t)-cutoff on the time interval [0, +∞], starting from (M, gij) and satisfying on each subinterval [0, t] the canonical neighborhood assumption with parameter r(t), as well as the pinching estimate (5.1). In particular, if the initial data has positive scalar curvature, say R ≥ a > 0, then the solution becomes extinct in time at most 3
2a , and it follows that M in
this case is diffeomorphic to a connected sum of several copies of S2 × S1 and metric quotients of round S3. ( The topological description of 3-manifolds with positive scalar curvature modulo quotients of homotopy spheres was obtained by Schoen-Yau and Gromov-Lawson more than 20 years ago, see [G-L] for instance; in particular, it is well known and easy to check that every manifold that can be decomposed in a connected sum above admits a metric of positive scalar curvature.) Moreover, if the scalar curvature is only nonnegative, then by the strong maximum principle it instantly becomes positive unless the metric is (Ricci-)flat; thus in this case, we need to add to our list the flat manifolds. However, if the scalar curvature is negative somewhere, then we need to work more in order to understand the long tome behavior of the solution. To achieve this we need first to prove versions of Theorems I.12.2 and I.12.3 for solutions with cutoff.
6.2 Correction to Theorem I.12.2. Unfortunately, the statement of Theorem I.12.2 was incorrect. The assertion I had in mind is as follows:
Given a function φ as above, for any A < ∞ there exist K = K(A) < ∞ and ρ = ρ(A) > 0 with the following property. Suppose in dimension three we have a solution to the Ricci flow with φ-almost nonnegative curvature, which
satisfies the assumptions of theorem 8.2 for some x0, r0 with φ(r0−2) < ρ. Then
13


 R(x, r02) ≤ Kr0−2 whenever distr2
0 (x, x0) < Ar0.
It is this assertion that was used in the proof of Theorem I.12.3 and Corollary I.12.4.
6.3 Proposition. For any A < ∞ one can find κ = κ(A) > 0, K1 = K1(A) < ∞, K2 = K2(A) < ∞, r ̄ = r ̄(A) > 0, such that for any t0 < ∞ there
exists δ ̄ = δ ̄A(t0) > 0, decreasing in t0, with the following property. Suppose we have a solution to the Ricci flow with δ(t)-cutoff on time interval [0, T ], δ(t) <
δ ̄(t) on [0, T ], δ(t) < δ ̄ on [t0/2, t0], with normalized initial data; assume that the
solution is defined in the whole parabolic neighborhood P (x0, t0, r0, −r02), 2r02 <
t0, and satisfies |Rm| ≤ r0−2 there, and that the volume of the ball B(x0, t0, r0)
is at least A−1r03. Then (a) The solution is κ-noncollapsed on the scales less than r0 in the ball B(x0, t0, Ar0).
(b) Every point x ∈ B(x0, t0, Ar0) with R(x, t0) ≥ K1r0−2 has a canonical neighborhood as in 4.1.
(c) If r0 ≤ r ̄√t0 then R ≤ K2r0−2 in B(x0, t0, Ar0).
Proof. (a) This is an analog of Theorem I.8.2. Clearly we have κ-noncollapsing on the scales less than r(t0), so we may assume r(t0) ≤ r0 ≤ √t0/2 , and study the scales ρ, r(t0) ≤ ρ ≤ r0. In particular, for fixed t0 we are interested in the scales, uniformly equivalent to one. So assume that x ∈ B(x0, t0, Ar0) and the solution is defined in the whole
P (x, t0, ρ, −ρ2) and satisfies |Rm| ≤ ρ−2 there. An inspection of the proof of I.8.2 shows that in order to make the argument work it suffices to check that for any barely admissible curve γ, parametrized by t ∈ [tγ, t0], t0 − r02 ≤ tγ ≤ t0, such that γ(t0) = x, we have an estimate
2
√t0 − tγ
∫ t0
tγ
√t0 − t(R(γ(t), t) + |γ ̇ (t)|2)dt ≥ C(A)r02 (6.1)
for a certain function C(A) that can be made explicit. Now we would like to conclude the proof by using Lemma 5.3. However, unlike the situation in Lemma 5.2, here Lemma 5.3 provides the estimate we need only if t0 − tγ is bounded
away from zero, and otherwise we only get an estimate ρ2 in place of C(A)r02. Therefore we have to return to the proof of I.8.2. Recall that in that proof we scaled the solution to make r0 = 1 and worked on the time interval [1/2, 1]. The maximum principle for the evolution equation of the scalar curvature implies that on this time interval we have R ≥ −3. We
considered a function of the form h(y, t) = φ(dˆ(y, t))Lˆ(y, τ ), where φ is a certain cutoff function, τ = 1 − t, dˆ(y, t) = distt(x0, y) − A(2t − 1), Lˆ(y, τ ) = L ̄(y, τ ) + 7,
and L ̄ was defined in [I,(7.15)]. Now we redefine Lˆ, taking Lˆ(y, τ ) = L ̄(y, τ ) +
2√τ . Clearly, Lˆ > 0 because R ≥ −3 and 2√τ > 4τ 2 for 0 < τ ≤ 1/2. Then the computations and estimates of I.8.2 yield
2h ≥ −C(A)h − (6 + √1τ )φ
14


 Now denoting by h0(τ ) the minimum of h(y, 1 − t), we can estimate
d
dτ (log( h0(τ )
√τ )) ≤ C(A) + 6√τ + 1
2τ − 4τ 2√τ − 1
2τ ≤ C(A) + √50τ , (6.2)
whence
h0(τ ) ≤ √τ exp(C(A)τ + 100√τ ), (6.3)
because the left hand side of (6.2) tends to zero as τ → 0 + . Now we can return to our proof, replace the right hand side of (6.1) by the
right hand side of (6.3) times r02, with τ = r0−2(t0 − tγ), and apply Lemma 5.3.
(b) Assume the contrary, take a sequence K1α → ∞ and consider the solu
tions violating the statement. Clearly, K1α(r0α)−2 < (r(t0α))−2, whence t0α → ∞; When K1 is large enough, we can, arguing as in the proof of Claim 1 in
[I.10.1], find a point (x ̄, t ̄), x ∈ B(x0, t ̄, 2Ar0), t ̄ ∈ [t0 − r02/2, t0], such that Q ̄ =
R(x ̄, t ̄) > K1r0−2, (x ̄, t ̄) does not satisfy the canonical neighborhood assumption,
but each point (x, t) ∈ P ̄ with R(x, t) ≥ 4Q ̄ does, where P ̄ is the set of all (x, t)
satisfying t ̄ − 1
4 K1Q ̄−1 ≤ t ≤ t ̄, distt(x0, x) ≤ distt ̄(x0, x ̄) + K
1 2
1 Q ̄− 1
2 . (Note
that P ̄ is not a parabolic neighborhood.) Clearly we can use (a) with slightly
different parameters to ensure κ-noncollapsing in P ̄. Now we apply the argument from 5.4. First, by Claim 2 in 4.2, for any
A ̄ < ∞ we have an estimate R ≤ Q(A ̄)Q ̄ in B(x ̄, t ̄, A ̄Q ̄− 1
2 ) when K1 is large
enough; therefore we can take a limit as α → ∞ of scalings with factor Q ̄ about (x ̄, t ̄), shifting the time t ̄ to zero; the limit at time zero would be a smooth complete nonnegatively curved manifold. Next we observe that this limit has
curvature uniformly bounded, say, by Q0, and therefore, for each fixed A ̄ and for
sufficiently large K1, the parabolic neighborhood P (x ̄, t ̄, A ̄Q ̄− 1
2 , −ǫη−1Q0−1Q ̄−1)
is contained in P ̄. (Here we use the estimate of distance change, given by Lemma
I.8.3(a).) Thus we can take a limit on the interval [−ǫη−1Q0−1, 0]. (The possibility of surgeries is ruled out as in 5.4) Then we repeat the procedure indefinitely, getting an ancient κ-solution in the limit, which means a contradiction. (c) If x ∈ B(x0, t0, Ar0) has very large curvature, then on the shortest geodesic γ at time t0, that connects x0 and x, we can find a point y, such
that R(y, t0) = K1(A)r0−2 and the curvature is larger at all points of the segment of γ between x and y. Then our statement follows from Claim 2 in 4.2, applied to this segment.
From now on we redefine the function δ ̄(t) to be min(δ ̄(t), δ ̄2t(2t)), so that the proposition above always holds for A = t0.
6.4 Proposition. There exist τ > 0, r ̄ > 0, K < ∞ with the following property. Suppose we have a solution to the Ricci flow with δ(t)-cutoff on the time interval [0, t0], with normalized initial data. Let r0, t0 satisfy 2C1h ≤ r0 ≤
r ̄√t0, where h is the maximal cutoff radius for surgeries in [t0/2, t0], and assume
that the ball B(x0, t0, r0) has sectional curvatures at least −r0−2 at each point, and the volume of any subball B(x, t0, r) ⊂ B(x0, t0, r0) with any radius r > 0 is at least (1 − ǫ) times the volume of the euclidean ball of the same radius. Then
the solution is defined in P (x0, t0, r0/4, −τ r02) and satisfies R < Kr0−2 there.
15


 Proof. Let us first consider the case r0 ≤ r(t0). Then clearly R(x0, t0) ≤
C12r0−2, since an ǫ-neck of radius r can not contain an almost euclidean ball of
radius ≥ r. Thus we can take K = 2C12, τ = ǫη−1C1−2 in this case, and since
r0 ≥ 2C1h, the surgeries do not interfere in P (x0, t0, r0/4, −τ r02).
In order to handle the other case r(t0) < r0 ≤ r ̄√t0 we need a couple of lemmas.
6.5 Lemma. There exist τ0 > 0 and K0 < ∞, such that if we have a smooth solution to the Ricci flow in P (x0, 0, 1, −τ ), τ ≤ τ0, having sectional curvatures at least −1, and the volume of the ball B(x0, 0, 1) is at least (1 − ǫ) times the volume of the euclidean unit ball, then
(a) R ≤ K0τ −1 in P (x0, 0, 1/4, −τ /2), and
(b) the ball B(x0, 1/4, −τ ) has volume at least 1
10 times the volume of the
euclidean ball of the same radius.
The proof can be extracted from the proof of Lemma I.11.6.
6.6 Lemma. For any w > 0 there exists θ0 = θ0(w) > 0, such that if B(x, 1) is a metric ball of volume at least w, compactly contained in a manifold without boundary with sectional curvatures at least −1, then there exists a ball B(y, θ0) ⊂ B(x, 1), such that every subball B(z, r) ⊂ B(y, θ0) of any radius r has volume at least (1 − ǫ) times the volume of the euclidean ball of the same radius.
This is an elementary fact from the theory of Aleksandrov spaces. 6.7 Now we continue the proof of the proposition. We claim that one can
take τ = min(τ0/2, ǫη−1C1−2), K = max(2K0τ −1, 2C12). Indeed, assume the con
trary, and take a sequence of r ̄α → 0 and solutions, violating our assertion for the chosen τ, K. Let t0α be the first time when it is violated, and let B(x0α, t0α, r0α)
be the counterexample with the smallest radius. Clearly r0α > r(t0α) and
(r0α)2(t0α)−1 → 0 as α → ∞. Consider any ball B(x1, t0, r) ⊂ B(x0, t0, r0), r < r0. Clearly we can apply
our proposition to this ball and get the solution in P (x1, t0, r/4, −τ r2) with the
curvature bound R < Kr−2. Now if r02t0−1 is small enough, then we can apply
proposition 6.3(c) to get an estimate R(x, t) ≤ K′(A)r−2 for (x, t) satisfying t ∈ [t0 − τ r2/2, t0], distt(x, x1) < Ar, for some function K′(A) that can be
made explicit. Let us choose A = 100r0r−1; then we get the solution with
a curvature estimate in P (x0, t0, r0, −△t), where △t = K′(A)−1r2. Now the
pinching estimate implies Rm ≥ −r0−2 on this set, if r02t0−1 is small enough
while rr0−1 is bounded away from zero. Thus we can use lemma 6.5(b) to
estimate the volume of the ball B(x0, t0 − △t, r0/4) by at least 1
10 of the volume
of the euclidean ball of the same radius, and then by lemma 6.6 we can find a subball B(x2, t0 −△t, θ0( 1
10 )r0/4), satisfying the assumptions of our proposition.
Therefore, if we put r = θ0( 1
10 )r0/4, then we can repeat our procedure as many
times as we like, until we reach the time t0 − τ0r02, when the lemma 6.5(b) stops working. But once we reach this time, we can apply lemma 6.5(a) and get the required curvature estimate, which is a contradiction.
6.8 Corollary. For any w > 0 one can find τ = τ (w) > 0, K = K(w) < ∞, r ̄ = r ̄(w) > 0, θ = θ(w) > 0 with the following property. Suppose we have a solution to the Ricci flow with δ(t)-cutoff on the time interval [0, t0], with
16


 normalized initial data. Let t0, r0 satisfy θ−1(w)h ≤ r0 ≤ r ̄√t0, and assume
that the ball B(x0, t0, r0) has sectional curvatures at least −r02 at each point,
and volume at least wr03. Then the solution is defined in P (x0, t0, r0/4, −τ r02)
and satisfies R < Kr0−2 there.
Indeed, we can apply proposition 6.4 to a smaller ball, provided by lemma 6.6, and then use proposition 6.3(c).
7 Long time behavior II
In this section we adapt the arguments of Hamilton [H 4] to a more general setting. Hamilton considered smooth Ricci flow with bounded normalized curvature; we drop both these assumptions. In the end of [I,13.2] I claimed that the volumes of the maximal horns can be effectively bounded below, which would imply that the solution must be smooth from some time on; however, the argument I had in mind seems to be faulty. On the other hand, as we’ll see below, the presence of surgeries does not lead to any substantial problems. From now on we assume that our initial manifold does not admit a metric with nonnegative scalar curvature, and that once we get a component with nonnegative scalar curvature, it is immediately removed. 7.1 (cf. [H 4,§2,7]) Recall that for a solution to the smooth Ricci flow the scalar curvature satisfies the evolution equation
d
dt R = △R + 2|Ric|2 = △R + 2|Ric◦|2 + 2
3 R2, (7.1)
where Ric◦ is the trace-free part of Ric. Then Rmin(t) satisfies d
dt Rmin ≥ 2
3 R2min,
whence
Rmin(t) ≥ − 3
2
1
t + 1/4 (7.2)
for a solution with normalized initial data. The evolution equation for the volume is d
dt V = − ∫ RdV, in particular
d
dt V ≤ −RminV, (7.3)
whence by (7.2) the function V (t)(t+1/4)− 3
2 is non-increasing in t. Let V ̄ denote its limit as t → ∞.
Now the scale invariant quantity Rˆ = RminV 2
3 satisfies
d
dt Rˆ(t) ≥ 2
3 RˆV −1
∫
(Rmin − R)dV, (7.4)
which is nonnegative whenever Rmin ≤ 0, which we have assumed from the
beginning of the section. Let R ̄ denote the limit of Rˆ(t) as t → ∞.
Assume for a moment that V ̄ > 0. Then it follows from (7.2) and (7.3) that Rmin(t) is asymptotic to − 3
2t ; in other words, R ̄V ̄ − 2
3 = −3
2 . Now the inequality
(7.4) implies that whenever we have a sequence of parabolic neighborhoods
17


 P (xα, tα, r√tα, −r2tα), for tα → ∞ and some fixed small r > 0, such that the scalings of our solution with factor tα smoothly converge to some limit solution, defined in an abstract parabolic neighborhood P (x ̄, 1, r, −r2), then the scalar curvature of this limit solution is independent of the space variables and equals −3
2t at time t ∈ [1 − r2, 1]; moreover, the strong maximum principle for (7.1)
implies that the sectional curvature of the limit at time t is constant and equals −1
4t . This conclusion is also valid without the a priori assumption that V ̄ > 0,
since otherwise it is vacuous. Clearly the inequalities and conclusions above hold for the solutions to the Ricci flow with δ(t)-cutoff, defined in the previous sections. From now on we assume that we are given such a solution, so the estimates below may depend on it.
7.2 Lemma. (a) Given w > 0, r > 0, ξ > 0 one can find T = T (w, r, ξ) <
∞, such that if the ball B(x0, t0, r√t0) at some time t0 ≥ T has volume at
least wr3 and sectional curvature at least −r−2t0−1, then curvature at x0 at time t = t0 satisfies
|2tRij + gij| < ξ. (7.5)
(b) Given in addition A < ∞ and allowing T to depend on A, we can ensure
(7.5) for all points in B(x0, t0, Ar√t0).
(c) The same is true for P (x0, t0, Ar√t0, Ar2t0).
Proof. (a) If T is large enough then we can apply corollary 6.8 to the ball
B(x0, t0, r0) for r0 = min(r, r ̄(w))√t0; then use the conclusion of 7.1.
(b) The curvature control in P (x0, t0, r0/4, −τ r02), provided by corollary 6.8, allows us to apply proposition 6.3 (a),(b) to a controllably smaller neighborhood
P (x0, t0, r′0, −(r′0)2). Thus by 6.3(b) we know that each point in B(x0, t0, Ar√t0)
with scalar curvature at least Q = K′1(A)r0−2 has a canonical neighborhood. This implies that for T large enough such points do not exist, since if there was a point with R larger than Q, there would be a point having a canonical neighborhood with R = Q in the same ball, and that contradicts the already proved assertion (a). Therefore we have curvature control in the ball in question, and applying 6.3(a) we also get volume control there, so our assertion has been reduced to (a).
(c) If ξ is small enough, then the solution in the ball B(x0, t0, Ar√t0) would
stay almost homothetic to itself on the time interval [t0, t0 + Ar2t0] until (7.5) is violated at some (first) time t′ in this interval. However, if T is large enough, then this violation could not happen, because we can apply the already proved assertion (b) at time t′ for somewhat larger A. 7.3 Let ρ(x, t) denote the radius ρ of the ball B(x, t, ρ) where inf Rm = −ρ−2. It follows from corollary 6.8, proposition 6.3(c), and the pinching estimate
(5.1) that for any w > 0 we can find ρ ̄ = ρ ̄(w) > 0, such that if ρ(x, t) < ρ ̄√t, then
V ol B(x, t, ρ(x, t)) < wρ3(x, t), (7.6)
provided that t is large enough (depending on w). Let M −(w, t) denote the thin part of M, that is the set of x ∈ M where (7.6) holds at time t, and let M +(w, t) be its complement. Then for t large enough
18


 (depending on w) every point of M + satisfies the assumptions of lemma 7.2. Assume first that for some w > 0 the set M +(w, t) is not empty for a sequence of t → ∞. Then the arguments of Hamilton [H 4,§8-12] work in our situation. In particular, if we take a sequence of points xα ∈ M +(w, tα), tα → ∞, then the scalings of giαj about xα with factors (tα)−1 converge, along a subsequence of α → ∞, to a complete hyperbolic manifold of finite volume. The limits may be different for different choices of (xα, tα). If none of the limits is closed, and H1 is such a limit with the least number of cusps, then, by an argument in [H 4,§8-10], based on hyperbolic rigidity, for all sufficiently small w′, 0 < w′ < w ̄(H1), there exists a standard truncation H1(w′) of H1, such that,
for t large enough, M +(w′/2, t) contains an almost isometric copy of H1(w′),
which in turn contains a component of M +(w′, t); moreover, this embedded copy of H1(w′) moves by isotopy as t increases to infinity. If for some w > 0 the
complement M +(w, t) \ H1(w) is not empty for a sequence of t → ∞, then we can repeat the argument and get another complete hyperbolic manifold H2, etc., until we find a finite collection of Hj, 1 ≤ j ≤ i, such that for each sufficiently small w > 0 the embeddings of Hj(w) cover M +(w, t) for all sufficiently large t. Furthermore, the boundary tori of Hj(w) are incompressible in M. This is proved [H 4,§11,12] by a minimal surface argument, using a result of Meeks and Yau. This argument does not use the uniform bound on the normalized curvature, and goes through even in the presence of surgeries, because the area of the least area disk in question can only decrease when we make a surgery. 7.4 Let us redefine the thin part in case the thick one isn’t empty, M −(w, t) = M \(H1(w)∪...∪Hi(w)). Then, for sufficiently small w > 0 and sufficiently large t, M −(w, t) is diffeomorphic to a graph manifold, as implied by the following general result on collapsing with local lower curvature bound, applied to the metrics t−1gij(t).
Theorem. Suppose (M α, giαj) is a sequence of compact oriented riemannian
3-manifolds, closed or with convex boundary, and wα → 0. Assume that (1) for each point x ∈ M α there exists a radius ρ = ρα(x), 0 < ρ < 1, not exceeding the diameter of the manifold, such that the ball B(x, ρ) in the metric giαj has volume at most wαρ3 and sectional curvatures at least −ρ−2;
(2) each component of the boundary of M α has diameter at most wα, and has a (topologically trivial) collar of length one, where the sectional curvatures are between −1/4 − ǫ and −1/4 + ǫ; (3) For every w′ > 0 there exist r ̄ = r ̄(w′) > 0 and Km = Km(w′) < ∞, m = 0, 1, 2..., such that if α is large enough, 0 < r ≤ r ̄, and the ball B(x, r) in giαj has volume at least w′r3 and sectional curvatures at least −r2, then the curvature and its m-th order covariant derivatives at x, m = 1, 2..., are bounded by K0r−2 and Kmr−m−2 respectively. Then M α for sufficiently large α are diffeomorphic to graph manifolds.
Indeed, there is only one exceptional case, not covered by the theorem above, namely, when M = M −(w, t), and ρ(x, t), for some x ∈ M, is much larger than the diameter d(t) of the manifold, whereas the ratio V (t)/d3(t) is bounded away from zero. In this case, since by the observation after formula (7.3) the
19


 volume V (t) can not grow faster than const · t 3
2 , the diameter does not grow
faster than const · √t, hence if we scale our metrics gij(t) to keep the diameter equal to one, the scaled metrics would satisfy the assumption (3) of the theorem above and have the minimum of sectional curvatures tending to zero. Thus we can take a limit and get a smooth solution to the Ricci flow with nonnegative sectional curvature, but not strictly positive scalar curvature. Therefore, in this exceptional case M is diffeomorphic to a flat manifold. The proof of the theorem above will be given in a separate paper; it has nothing to do with the Ricci flow; its main tool is the critical point theory for distance functions and maps, see [P,§2] and references therein. The assumption (3) is in fact redundant; however, it allows to simplify the proof quite a bit, by avoiding 3-dimensional Aleksandrov spaces, and in particular, the nonelementary Stability Theorem. Summarizing, we have shown that for large t every component of the solution is either diffeomorphic to a graph manifold, or to a closed hyperbolic manifold, or can be split by a finite collection of disjoint incompressible tori into parts, each being diffeomorphic to either a graph manifold or to a complete noncompact hyperbolic manifold of finite volume. The topology of graph manifolds is well understood [W]; in particular, every graph manifold can be decomposed in a connected sum of irreducible graph manifolds, and each irreducible one can in turn be split by a finite collection of disjoint incompressible tori into Seifert fibered manifolds.
8 On the first eigenvalue of the operator −4△+R
8.1 Recall from [I,§1,2] that Ricci flow is the gradient flow for the first eigenvalue λ of the operator −4△ + R; moreover, d
dt λ(t) ≥ 2
3 λ2(t) and λ(t)V 2
3 (t) is nondecreasing whenever it is nonpositive. We would like to extend these inequalities to the case of Ricci flow with δ(t)-cutoff. Recall that we immediately remove components with nonnegative scalar curvature.
Lemma. Given any positive continuous function ξ(t) one can chose δ(t) in such a way that for any solution to the Ricci flow with δ(t)-cutoff, with normalized initial data, and any surgery time T0, after which there is at least one component, where the scalar curvature is not strictly positive, we have an estimate λ+(T0)−λ−(T0) ≥ ξ(T0)(V +(T0)−V −(T0)), where V −, V + and λ−, λ+ are the volumes and the first eigenvalues of −4△+R before and after the surgery respectively.
Proof. Consider the minimizer a for the functional
∫
(4|∇a|2 + Ra2) (8.1)
under normalization ∫ a2 = 1, for the metric after the surgery on a component where scalar curvature is not strictly positive. Clearly is satisfies the equation
4△a = Ra − λ−a (8.2)
20


 Observe that since the metric contains an ǫ-neck of radius about r(T0), we can
estimate λ−(T0) from above by about r(T0)−2. Let Mcap denote the cap, added by the surgery. It is attached to a long tube, consisting of ǫ-necks of various radii. Let us restrict our attention to a maximal subtube, on which the scalar curvature at each point is at least 2λ−(T0). Choose any ǫ-neck in this subtube, say, with radius r0, and consider
the distance function with range [0, 2ǫ−1r0], whose level sets Mz are almost
round two-spheres; let Mz+ ⊃ Mcap be the part of M, chopped off by Mz. Then
∫
Mz
−4aaz =
∫
M+
z
(4|∇a|2 + Ra2 − λ−a2) > r0−2/2
∫
M+
z
a2
On the other hand,
|
∫
Mz
2aaz − (
∫
Mz
a2)z| ≤ const ·
∫
Mz
ǫr0−1 a2
These two inequalities easily imply that
∫
M+
0
a2 ≥ exp(ǫ−1/10)
∫
M+
ǫ−1 r0
a2
Now the chosen subtube contains at least about −ǫ−1log(λ−(T0)h2(T0)) disjoint ǫ-necks, where h denotes the cutoff radius, as before. Since h tends to zero with δ, whereas r(T0), that occurs in the bound for λ−, is independent of δ, we can ensure that the number of necks is greater then log h, and therefore,
∫
Mcap a2 < h6, say. Then standard estimates for the equation (8.2) show that
|∇a|2 and Ra2 are bounded by const · h on Mcap, which makes it possible to extend a to the metric before surgery in such a way that the functional (8.1) is preserved up to const · h4. However, the loss of volume in the surgery is at least h3, so it suffices to take δ so small that h is much smaller than ξ. 8.2 The arguments above lead to the following result
(a) If (M, gij) has λ > 0, then, for an appropriate choice of the cutoff parameter, the solution becomes extinct in finite time. Thus, if M admits a metric with λ > 0 then it is diffeomorphic to a connected sum of a finite collection of S2 × S1 and metric quotients of the round S3. Conversely, every such connected sum admits a metric with R > 0, hence with λ > 0.
(b) Suppose M does not admit any metric with λ > 0, and let λ ̄ denote the supremum of λV 2
3 over all metrics on this manifold. Then λ ̄ = 0 implies that
M is a graph manifold. Conversely, a graph manifold can not have  ̄λ < 0.
(c) Suppose λ ̄ < 0 and let V ̄ = (− 2
3 λ ̄) 3
2 . Then V ̄ is the minimum of V, such that M can be decomposed in connected sum of a finite collection of S2 × S1, metric quotients of the round S3, and some other components, the union of which will be denoted by M ′, and there exists a (possibly disconnected) complete hyperbolic manifold, with sectional curvature −1/4 and volume V, which can be embedded in M ′ in such a way that the complement (if not empty) is a graph
21


 manifold. Moreover, if such a hyperbolic manifold has volume V ̄ , then its cusps (if any) are incompressible in M ′.
For the proof one needs in addition easily verifiable statements that one can put metrics on connected sums preserving the lower bound for scalar curvature [G-L], that one can put metrics on graph manifolds with scalar curvature bounded below and volume tending to zero [C-G], and that one can close a compressible cusp, preserving the lower bound for scalar curvature and reducing the volume, cf. [A,5.2]. Notice that using these results we can avoid the hyperbolic rigidity and minimal surface arguments, quoted in 7.3, which, however, have the advantage of not requiring any a priori topological information about the complement of the hyperbolic piece. The results above are exact analogs of the conjectures for the Sigma constant, formulated by Anderson [A], at least in the nonpositive case.
References
[I] G.Perelman The entropy formula for the Ricci flow and its geometric applications. arXiv:math.DG/0211159 v1 [A] M.T.Anderson Scalar curvature and geometrization conjecture for threemanifolds. Comparison Geometry (Berkeley, 1993-94), MSRI Publ. 30 (1997), 49-82. [C-G] J.Cheeger, M.Gromov Collapsing Riemannian manifolds while keeping their curvature bounded I. Jour. Diff. Geom. 23 (1986), 309-346. [G-L] M.Gromov, H.B.Lawson Positive scalar curvature and the Dirac operator on complete Riemannian manifolds. Publ. Math. IHES 58 (1983), 83-196. [H 1] R.S.Hamilton Three-manifolds with positive Ricci curvature. Jour. Diff. Geom. 17 (1982), 255-306. [H 2] R.S.Hamilton Formation of singularities in the Ricci flow. Surveys in Diff. Geom. 2 (1995), 7-136. [H 3] R.S.Hamilton The Harnack estimate for the Ricci flow. Jour. Diff. Geom. 37 (1993), 225-243. [H 4] R.S.Hamilton Non-singular solutions of the Ricci flow on three-manifolds. Commun. Anal. Geom. 7 (1999), 695-729. [H 5] R.S.Hamilton Four-manifolds with positive isotropic curvature. Commun. Anal. Geom. 5 (1997), 1-92. G.Perelman Spaces with curvature bounded below. Proceedings of ICM1994, 517-525. F.Waldhausen Eine Klasse von 3-dimensionalen Mannigfaltigkeiten I,II. Invent. Math. 3 (1967), 308-333 and 4 (1967), 87-117.
22