# Angular extraction in a complex neighborhood — own calculation

2026-10-07. Extension of PRINCIPAL_ANGULAR_FACTOR_ATTEMPT.md; independent causal_algebra_audit PASS: unramified phases, ramified cases, convergence exponents, q_u^epsilon bound and original-S finite-prime correction checked. Same pinned paper.tex and source local identity (4007–4050). No new question sent while Q2 runs.

For a prime not dividing u, set q=P^-1, V=P^-6z, W=chi_p(u)P^-w, D=eta(p)bar chi_p(u)P^-x and R=baralpha(p)^6 eta(p)^6 P^(4-6x-6z). Direct algebra from Pstar and Pfull gives

Htilde_p=(1-R)H_p
=1+[-VW-R*q*(1-W)-R*W²*(1-V)+D*(W+V-P*W*V+(P-1)*W²*V)]/(1-D).

For u=1 these are exactly the principal factors. The same formula at p not dividing u uses D*W=eta(p)P^(-x-w), retaining the actual unit phases. Normal convergence of the unramified Htilde product follows, locally uniformly, on the sufficient open region

x_r,w_r,z_r>0;
w_r+6z_r>1;
6x_r+6z_r>4;
6x_r+6z_r+2w_r>5;
x_r+w_r>1;
x_r+6z_r>1;
x_r+w_r+6z_r>2;
x_r+2w_r+6z_r>2.

Here subscripts r mean real parts. Each inequality pays one displayed monomial; stricter terms are dominated since w_r,z_r>0. On compact real-part boxes inside this region, choose fixed P0 so |D|,|R|<1 and Htilde_p is uniformly near one. This supplies a genuine three-complex-variable neighborhood of every point (x,1,1/6) with Re x>1/2, not merely an identity on a slice. In absolute convergence the extracted product is L^S(6x+6z-4,kappa), kappa=baralpha^6 eta^6. Its absolute convergence and nonvanishing require 6x_r+6z_r>5.

## What this does and does not provide for slots

For u=1 the exact finite selected expression remains holomorphic wherever the local rational denominators are nonzero. This alone does not prove its nonvanishing away from the slice. A slot has factors P^(z-1): for Im z not zero its weights are complex, so the positive-slot-mass argument used at z=1/6 cannot simply be applied. At each fixed Z a nonzero slice value has some open nonzero neighborhood by continuity; no Z-uniform size is inferred. Full high-side contour error bounds require more than this local continuation.

## Ramified factors — checked

For p|u, j=v_p(u) in {1,...,5}, source W=D=0 in H definition, but rho=chi_p(u/p^j) in J_j remains. One must not replace the coefficient eta(p)P^(-x-w) in Pstar by D*W, since D=W=0 here. Instead the exact formula is

Htilde_p=1-qR-eta(p)(P-1)P^(-x-w)*V^(1_(j<=1))+(1-V)J_j,

with the source's six-entry J table and its rho phases. At j=1, on w=1,z=1/6, the two eta terms cancel and Htilde_p=1-qR. For j>=2 on this slice, the errors are bounded by the sum of

P^(2-6x_r), P^(-x_r), P^(3/2-3x_r), P^(1-3x_r), P^(2-4x_r), P^(3/2-4x_r), P^(3-6x_r),

each decaying for x_r>1/2. Their finite product has a divisor-type O_epsilon(q_u^epsilon) bound on fixed-positive-margin boxes, with constants allowed to depend on epsilon and that margin. This extends the correction-factor estimate for all u near this slice, not prove convergence or an improved bound for the full sum over u. The common extracted angular L-factor is independent of u.

For an explicit open neighborhood that also controls the ramified factors, intersect the unramified region with x_r>1/2, 3x_r+w_r>2 and 4x_r+w_r>5/2. These conditions hold near every (x,1,1/6) with Re x>1/2. On compact real-part boxes with positive margins, all ramified errors are O(P^-c) for c>0. Splitting at a fixed norm threshold gives product_(p|u)(1+C P^-c) <= C_epsilon q_u^epsilon. This is an upper bound for Htilde_eta,u, not for the removed angular L-factor.

Original S is preserved. At the principal slice, |Delta-1| <= q|R|+(1-q)|D|<1 for every retained prime since Re x>1/2. Hence all finite principal Htilde factors are nonzero too. The cutoff is only a proof split for the tail, not a change of the probe or deletion of troublesome factors. Finite-prime continuity plus the nonzero convergent tail supplies a local nonzero neighborhood at each principal-slice point; it does not assert one global zero-free domain for arbitrary Im w,Im z.

Accepted scope: only this correction-factor result. The low estimate, u-row summation, contour shifts, angular L nonvanishing below its absolute-convergence region, and RH remain unpaid.

## Return to the actual high consumer: no central exponent gain from extraction alone

Source paper.tex 6019–6155 uses z_0=17/50 and x_r=a+16e with a>=51/100 on the central contour. There the extracted angular argument has real part

6x_r+6z_0-4 >= 6*(51/100)+6*(17/50)-4+96e = 11/10+96e.

Both its Euler product and its reciprocal are bounded by fixed constants, uniformly in the retained heights and unit phases. Thus pulling this common factor out of the u-sum changes no Z or U power in the source central-bound hypothesis. In particular the exponent

E_sigma0(d;R,g)=a-sigma0+h*(z_0-1/6)-a*l_y-ell/2+g+d*(R+(2a-1)/2-z_0)

is unchanged if the same row-count and selected-correlation estimates (R,g) are used. Here R denotes the source row-count exponent, not the local geometric ratio used above. The published retained-integral lemma is itself stated for sigma0>=7/8; this observation does not extend it to new sigma0 by substitution.

The genuine progress is continuation and a clearer principal detector factor. It is not an improvement of the central row envelope, the selected correlation exponent g, or the low bound. A new aggregate estimate remains necessary; this returns the work to Q2 rather than selecting another Euler-factor optimization as though it solved that problem.
