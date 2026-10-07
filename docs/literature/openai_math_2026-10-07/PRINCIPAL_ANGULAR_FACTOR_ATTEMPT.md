# Principal residue slice: isolate the angular L-factor

2026-10-07. Own bounded calculation while Q2 runs, independent causal_algebra_audit PASS for local identities, character type, normal convergence and the stated principal-slice consequence. Same pinned source hash as sources.json. This concerns only the principal u=1 slice w=1,z=1/6, not the full high-side error or full N_eta.

## Exact local algebra

Source paper.tex 4007–4050 and 8670–8690. Let P=q_p, q=P^-1,
D=eta(p)P^-x, R=baralpha(p)^6 eta(p)^6 P^(3-6x), Delta=1-qR-(1-q)D.
The full source series at this slice gives

Pstar=(1+q)(R-D)/(1-R),
Pfull=(1+q)Delta/[(1-q)(1-R)],
H=(1-q²)Delta/[(1-R)(1-D)],
B=G/H=-(1-q)(1-R/D)/Delta-q.

These are rational identities in D,R,q, not merely asymptotics at x=2. In particular

H=(1-R)^(-1) Htilde,
Htilde=(1-q²)[1+q(D-R)/(1-D)].

For Re x>=1/2+delta, delta>0, uniformly in imaginary x and unit target phases, Htilde-1 is bounded by a fixed multiple of
P^-2 + P^(-1-Re x) + P^(2-6Re x).
Each term is summable over prime ideals. A fixed cutoff makes the tail close to one. Every remaining finite factor is also nonzero since |qR+(1-q)D|<1 for Re x>1/2. Thus the complete Htilde product is nonzero without changing S; only its tail is asserted close to one.

## What the extracted factor costs

Because alpha(a)=a/|a| and all six units have sixth power one, kappa((a))=baralpha(a)^6 eta((a))^6 is well-defined on good ideals and multiplicative. It is an angular Hecke character of nonzero infinity type, not a finite-order character. In the region of absolute Euler convergence,

H_eta,1(x,1,1/6)=L^S(6x-3,kappa) product_(p notin S) Htilde_p(x).

Standard continuation of this angular Hecke L-function would continue this expression into Re x>1/2. Normal convergence proves continuation only of Htilde there; it does NOT establish nonvanishing of the extracted L-function. The finite deleted Euler factors have no zeros at Re(6x-3)>0. For Re x>2/3 the L Euler product is itself absolutely convergent and nonzero. Thus on each half-plane Re x>=2/3+delta this principal unselected correction is nonzero with the original excluded set S. This conclusion needs no critical-strip zero-free claim.

The source target family is finite-order (fixed-data description 590–600). Any use of its target zero-selection argument for the new angular L-function would require an additional extension of that theorem family and its low/high estimates; it cannot be inferred from the factorization.

## Selected correction and the second threshold

The exact identity is

B+1=(1-q)[R/D-qR-(1-q)D]/Delta.

Since R/D=baralpha(p)^6 eta(p)^5 P^(3-5x), the elementary uniform estimate yields B=-1+o(1) for Re x>3/5, with fixed-positive margin and cutoff. For original nonnegative slot weights on the slice z=1/6, this gives B_i=-S_i(1+o(1)) uniformly in imaginary x; all subsets are already included by the finite disjoint-slot product. For Re x>2/3 the unselected L-factor is nonzero as well, so the entire principal selected correction is nonzero for sufficiently large original slot scales, with each slot mass positive, by this direct source calculation. Mere positivity of a mass at an arbitrary small fixed scale is not the claimed condition.

For 1/2<Re x<=3/5, this small-error argument is unavailable: the R/D term no longer tends uniformly to zero. This is not proof that the actual slot sum vanishes. Angular prime cancellation or a different normalization would need its own estimate and detector check. For 3/5<Re x<=2/3 the slot factors remain near -S_i, but the extracted angular L-factor can no longer be certified nonzero by absolute convergence alone.

## Scope

This is a candidate extension for the exact principal residue slice. The later checked ANGULAR_FACTOR_NEIGHBORHOOD.md supplies a local three-variable continuation of the extracted correction, including a q_u^epsilon bound; this slice calculation alone gives no bound for u!=1 rows, no shifted-contour error and no improvement to the low exponent 3/16. It cannot by itself improve the claimed zero-free endpoint or establish RH. It records the previously hidden angular L-factor and the two different obligations at 2/3 and 3/5 rather than treating Euler convergence as a universal obstruction.
