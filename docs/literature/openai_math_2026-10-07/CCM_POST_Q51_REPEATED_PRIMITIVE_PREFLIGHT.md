# Post-Q51: repeated boundary primitives do not give a free smoothing gain

2026-10-27. Own bounded PAPER preflight, not independent admission.
Original P, same Q51 Gamma,z0=b+iH and full low divisor retained.
No new arithmetic exponent, no Q52. This is not an actual-source no-go.

## Exact full boundary formula

Write K(z)=m^z S_P(z), and for EACH actual low root w with multiplicity r_w,
choose the continuous path branch log((z-w)/(z0-w)), initially zero.
For j>=0 set
 phi_j,w(z)=(z-w)^j/j! [log((z-w)/(z0-w))-H_j],
where H_0=0 and H_j=sum_(a=1)^j 1/a. Then phi_0 prime=1/(z-w),
and phi_j prime=phi_(j-1) for j>=1. All roots in the full DG remain in
this construction, including roots outside the right contour.
At completion of the path,
 jump phi_j,w=2pi i (z0-w)^j/j! if w is inside Gamma, and0 otherwise.

Let L_j=sum_all_low r_w phi_j,w, and
 A_j=sum_inside_low r_w (z0-w)^j/j!.
For every FIXED integer k>=1, repeated integration by parts gives exactly

 Rlow=He sum_(j=0)^(k-1) (-1)^j K^(j)(z0) A_j
       +He [(-1)^k/(2pi i) integral_Gamma K^(k)(z) L_(k-1)(z) dz].

This retains all sides, branches, multiplicities and mixed matrix entries.
The initial L_j values need not be zero for j>=1; only their jumps enter
the boundary because K and its derivatives return to the same endpoint.
For k=1 this is precisely Q51's monodromy formula. No new identity is
counted as favorable arithmetic cancellation.

## Complete price of the new corner completion

For fixed j, near z0 the contact P1=0 gives
 ||S_P^(j)(z0)|| <= C_j V2/H^(4+j).
One way to check it is P v_±(z)=P[v_±(z)-1/z], whose entries before P
are minus/plus i omega_l/[z(z±i omega_l)]. Product differentiation and
|Im z0|=H>=2Omega give the displayed bound for both orientations.
Leibniz therefore yields, eventually LH>=1,
 ||K^(j)(z0)|| <= C_j sqrt(m) V2 L^j/H^4.
Since G<H and |Re w|<1/2, |z0-w|<=3H eventually; hence
 |A_j| <= N0(G)(3H)^j/j!.
The separately bounded j-th boundary term costs at most

 C_j sqrt(m) V2 G log(G+2) L^j H^(j-4)
 =O_epsilon,j(m^[-7/24+j(1/4+epsilon)] L^(j-2)).

For the k-fold formula the highest such power is at j=k-1:
 k=1: -7/24, logs L^-2 (already Q51);
 k=2: -1/24+epsilon, logs L^-1, still negative for epsilon<1/32;
 k=3: 5/24+2epsilon, logs L^0, no longer a vanishing exponent family;
 higher FIXED k: this upper allowance grows further.
This is an AVAILABLE UPPER PRICE, not a lower on the combined corners.
The alternating A_j K^(j) may cancel; no obstruction to such cancellation
is asserted. Growing k requires new uniform constants and is not covered.

## Remaining full budget and disposition

The integral remainder is NOT independently bounded here. A one-sided
upper on its appropriately signed Hermitian part with scale m^theta would
need to pay the complete boundary sum above and then Q51's
B+e+high-tail+bdiv=O_epsilon(m^(2epsilon)) for T, and one arch fee for K.
For k=2, corner remains o1, but the remainder now has K double-prime and
L_1; no supplied arithmetic inequality becomes smaller by that change.
At the fixed Q51 height, for k>=3 the separate corner completion
itself already has a fixed positive power. Do not continue this absolute-bound completion as if each
primitive automatically bought a factor1/log(m).

Exact rational arithmetic checked exponents at epsilon1/128,1/64,1/33
and the excluded endpoint1/32 as algebra only. Eighteen polynomial K=z^n
checks confirmed the finite Taylor boundary sum equals K(w) once k>n.
These checks do not certify actual zeta zeros or the integral remainder.
No source term was dropped, no numerical CCM spectrum computed.

Decision: keep Q51 single-primitive representation available; higher
primitives need a NEW joint boundary/remainder inequality, not additional
bookkeeping. This preflight alone does not trigger another Pro question.
AUTOPSY: dropped=NO_DERIVATION; note=Repeated primitives transfer derivatives to m^z and amplify corner moments; joint arithmetic remainder still unpaid.

## Height refinement: the k=3 price is not intrinsic

The preceding table fixes Q51 H~m^(1/4+epsilon). Do NOT use it as a
height-uniform obstruction. Keep the source-inversion contour and all its
fees unchanged, and change ONLY the auxiliary contour representing Rlow.
The same DG has all its roots at |Im w|<=G. With unchanged u,b, any new
height Htilde>G contains exactly the same selected roots, and K has no
poles inside. Consequently its residue sum is exactly the same Rlow.
There is no need to move the original zeta inversion contour, invoke a new
zero-avoidance selection, or silently discard newly crossed high zeta zeros:
the auxiliary integrand uses DGprime/DG, not Fprime/F.

For Htilde=m^h with fixed h>kappa=5/24+epsilon, the j-th separately paid
corner has power
 E_j=1/2+3epsilon+kappa+(j-4)h
    =17/24+4epsilon+(j-4)h,
and logarithmic factor L^(j-2). All branch integrals must use the new
contour and basepoint; no bound on their remainder is transferred for free.

Choose h=1. For k<=4, j<=3, hence the worst corner power is at most
 -7/24+4epsilon < -1/6.
In particular THREE and FOUR integrations can have a fully small corner
budget. This removes the fixed-height corner difficulty recorded above;
it does not estimate the new whole remainder. For k=5, the j=4 term's
available bound has power17/24+4epsilon independently of h. This too is
an upper-certificate limitation, not an actual lower bound or universal
obstruction to a better joint boundary estimate.

Decision after refinement: do not exclude k=3 or k=4 based on the fixed
height. Their genuinely unpaid line is the full signed remainder on the
raised auxiliary contour. No exponent for T or K has improved; no new
attempt count is earned merely by adjusting this bookkeeping parameter.

## Completed remainder comparison for k=4, auxiliary height m

Name the WHOLE Hermitian boundary sum B4 and define
 J4=-He[(1/(2pi i)) integral_(raised Gamma) K^(4)(z)L_3(z) dz].
The even k sign is essential. The exact result is Rlow=B4-J4.
From the preceding bound choose j4=O_epsilon(m^(-7/24+4epsilon)L),
so ||B4||<=j4=o(1), uniformly on the original P.
Therefore, for any nonnegative scalar s,

 J4<=sP implies Rlow>=-(s+j4)P;
 Rlow>=-sP implies J4<=(s+j4)P.

Let p=B+e+t_high be the inherited ORIGINAL inversion fees (not a new
raised-contour inversion). The complete sufficient budget is then

 T_>R <= [s+j4+p+bdiv]P-H_P,
 PKP >= H_P-[s+j4+p+50L+8]P.

The old original-source upper gives only
 Rlow>=-[s_keep+4+p]P,
 hence J4<=[s_keep+4+p+j4]P.
Reinsertion would give T allowance s_keep+4+2p+2j4+bdiv, and the analogous
K allowance with one arch fee. This round trip is valid but worse than
the independent direct fallback, so it is not adopted. Its leading
power remains1/2. The actual J4 may be smaller; no lower bound is claimed.

Thus raising the auxiliary contour repairs the corner bookkeeping but
creates no independent signed remainder estimate. This completes ONE
primitive-mechanism preflight, including its correction, not three attempts.
The exact missing supplier is now identified on the raised contour, and
is equivalent to the prior floor up to o(1); it must not be presented to
Proshka as an easier proved input.

## Bounded supplier screen after the full return

2026-10-27. Read-only researcher post_q51_phase_supplier inspected Q43,
Q44 and Q45 conclusions; root re-read their exact remaining interfaces.
This is source applicability screening, not independent proof admission.
Q43's alternative actual-zero pair margin and Q44's finite seam margin
remain explicitly unpaid. Q45 returns the full psi term with coefficient
one after paying the common smooth edge. None supplies Jbranch or J4.
In particular J_seam in Q44 is not Jbranch in Q51. A bound on one selected
pair does not imply a uniform form bound on ran P; we do not promote it.
The proposed revisit of that pair without a new supplier is therefore not
selected as another all-P attempt. No global literature absence is claimed.

Disposition: stop further primitive/height optimization; keep the direct
fallback and the original all-P goal. The next question must ask for an
independent source-sensitive joint inequality, or a specifically justified
earlier fork, and include this completed no-gain return. It must not ask
Proshka merely to bound an equivalent renamed residual. No Q52 sent here.
Exact rational replay of the four corner powers at epsilon=1/128,1/64,
1/33 (and excluded endpoint1/32 as algebraic control) agrees with the
height-refinement table. This is bookkeeping verification, no source gain.
