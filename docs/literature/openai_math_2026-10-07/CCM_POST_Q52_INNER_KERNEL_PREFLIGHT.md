# Post-Q52: two-point finite-inner kernel, exact resolvent bridge

2026-10-27. Own bounded preflight; not a new arithmetic estimate or
independent admission. Original P and full low-root family retained.

## Pre-screen and selection

A scale-average of matrices was considered and NOT counted as an attempt:
CCM_COFINAL_MOMENT_BUDGET_2026-10-20.md already rejects the inference from
a small averaged matrix to one small spectral upper. Its opposite diagonal
controls have mean zero and large positive eigenvalue in every cell. Its
valid positive-spectral-moment alternative remains unpaid. Q17 averages
actual translated pairs within one cell and is a different, already tested
construction. No new averaging result is claimed.

Instead use the Q52 finite Blaschke B and its TWO-POINT positive kernel.
Write the actual selected roots as distinct w_a with multiplicities r_a.
For the telescope only, enumerate factors with repetitions, indexed k:
 b_k(z)=(z-w_k)/(z-w_k#), w_k#=2u-conj(w_k), a_k=Re(w_k)-u>0.
Then B=product b_k and, in Re z,Re v>u,

 k_B(z,v)=(1-B(z)conj(B(v)))/(z+conj(v)-2u)
         =sum_k f_k(z)conj(f_k(v)),
 f_k(z)=sqrt(2a_k)/(z-w_k#) product_(l<k) b_l(z).

This follows from 1-product t_k=sum_k(1-t_k)product_(l<k)t_l,
and the exact one-factor numerator identity. It proves positive Gram
matrices without assuming absence of actual right-half-plane roots.
It is an algebraic property of the finite inner function, not a new
constraint on zeta zeros.

## Exact map to the original resolvents

Use DISTINCT root indices for the matrix
 G_ab=k_B(w_a,w_b)=1/(w_a+conj(w_b)-2u).
It is positive definite: G is the Gram of the linearly independent
exponentials exp(-(w_a-u)t) in L2(0,infinity), up to conjugation convention.
For observations z_j^+=2u+i omega_j and z_j^-=2u-i omega_j, both in the
right half-plane, B(w_a)=0 gives exactly
 C^+_aj=k_B(w_a,z_j^+)=1/(w_a-i omega_j),
 C^-_aj=k_B(w_a,z_j^-)=1/(w_a+i omega_j).
Let H^+/-_jk=k_B(z_j^+/-,z_k^+/-). The full block Gram gives
 (C^+/-)* G^-1 C^+/- <= H^+/-,
and hence P(C^+/-)*G^-1 C^+/-P <= P H^+/- P.
No mode or mixed entry is removed; P is the original real symmetric
projector. For an empty actual root family the residue sum is zero and
this inverse is unnecessary.

## Where the sign and full price return

Put D=diag(r_a exp(L w_a)), Ghalf the positive Hermitian square root,
Y^+/-=Ghalf^-1 C^+/- P. The literal original low residue is

 Rlow=He[(Y^+)^T J Y^+ + (Y^-)^T J Y^-]/L,
 J=(Ghalf)^T D Ghalf.

This is transpose, not adjoint. The positive Gram inequality controls
(Y^+/-)*Y^+/-, but does not change the displayed bilinear form into a
positive quadratic form. D retains every actual oscillatory and growing
factor, and multiplicities have not been discarded by deduplicating G.
A sufficient norm completion is

 Rlow >= -beta_m P,
 beta_m=||J|| (||P H^+ P||+||P H^- P||)/L.

No independent vanishing-exponent bound for beta_m is supplied. A small
Re(w)-u alone is NOT proved to force a bad price: in a one-root case the
Gram blowup can cancel against the observation factor. Likewise no actual
CCM lower bound follows from a generic complex D or a synthetic root test.
The joint signed form may be cheaper than this sufficient norm completion.

If beta_m=Oepsilon(m^theta) were independently proved, Q52's full return
would yield T_>R<=(beta_m+p+bdiv)P-H_P and
PKP>=H_P-(beta_m+p+50L+8)P, with eta=max(theta,2epsilon).
Here p is the ORIGINAL contour fee. No Q52 stable-phase fee is added:
this exact bridge represents Rlow directly, not only its finite-time part.
No such new beta bound is established; retain the old direct half-power
fallback, with no auxiliary fees charged on top.

## Executed controls and scope

Standard-library exact Gaussian-rational arithmetic from q52_replay was
used for two FORMAL roots with multiplicities2,1 and five observation
points. Exact resolvent cross-map, positive G determinant and all five
scalar Schur gaps passed. These are algebra controls, not actual zeta data
or original-schedule spectral cells. An initial SymPy command failed at
import (package unavailable); no installation was attempted, and no result
from that failed command is counted.

The full joint-core estimate, not kernel positivity, is the unpaid line.
No Q53 dispatch or theorem-shape/source kill is justified by this note.
AUTOPSY: dropped=NO_DERIVATION; note=Positive two-point Gram maps exactly to resolvents, but the actual growing complex bilinear core remains unpaid.

## Observation-side budget from the finite Gram

Read-only researcher post_q52_inner_kernel independently derived the same
finite-factor and source map (not an admission audit). Its local ask.sh
query returned INCOMPLETE because q3_docs freshness validation failed;
Q22 Schur/phase-delay and Q36 sign screens do not supply the weighted core.

One additional part is payable without arithmetic input. On the observation
line Re z=2u, let H0_jk=1/(2u+i(omega_j-omega_k)), up to orientation.
H^+/-=H0-diag(B(z_j)) H0 diag(B(z_j))*; both terms are Gram kernels,
so 0<=H^+/-<=H0. Absolute row sums on the ORIGINAL frequency grid give
 ||H0||<=1/(2u)+(L/pi) harmonic_(2M)
        <=L/2+(L/pi) harmonic_(2M).
Consequently the sufficient beta above obeys
 beta_m<=||J||[1+(2/pi)harmonic_(2M)].
All observation/projection costs are thus logarithmic, not an uncounted
factor equal to the band dimension. This still leaves the actual complex
exponential-weighted J with no independent subpower bound. It does not
turn transpose into adjoint or authorize dropping its signed coupling.
The displayed beta is an available UPPER certificate price, not a lower
bound for the source. No new consumer exponent is obtained.

## Fixed actual off-line root survives the weighted-core norm (candidate)

Conditional statement only: assume a fixed actual root w*=delta+i gamma,
delta>0, of multiplicity r*. It lies in the selected family eventually for
each fixed epsilon, since u<=2/log m tends to zero and G tends to infinity.
No numerical off-line root is assigned and its existence is not asserted.

For the distinct-root Cauchy matrix, determinant division gives exactly
 (G^-1)_aa=2(Re w_a-u)
   product_(b!=a) |w_a+conj(w_b)-2u|²/|w_a-w_b|².
The determinant identity used here is
 det G=product_(a<b)|w_a-w_b|² /
       [product_a 2(Re w_a-u) product_(a<b)|w_a+conj(w_b)-2u|²].
It follows by putting the determinant over the common denominator: the
numerator vanishes when two row or column parameters coincide, giving
the two Vandermonde factors, and their leading coefficient is one.
Deleting row/column a and taking the determinant ratio gives the diagonal.
Multiplicity is still r_a in D; G has one row per DISTINCT root.

For a corresponding to w*, every factor is
 1+4(delta-u)(Re w_b-u)/|w*-w_b|²
 <=1+1/|w*-w_b|².
The actual zeta zeros have 0<Re w_b<1/2 on this selected side. Define
 C_w=2delta product_(all distinct actual Re w_b>0, w_b!=w*)
                       (1+1/|w*-w_b|²).
This is finite: in a bounded region the zeros are isolated and finite;
for |Im w_b|>2(|gamma|+1), the inverse square is <=4/|Im w_b|²,
and N0(T)=O(T log(T+2)) makes their sum converge by dyadic grouping.
No uniform separation of zeros or unproved zero-density input is used.
Therefore (G^-1)_aa<=C_w independently of m,epsilon and the selected
finite subset, once w* is included. C_w need not be effectively small.

Let x=Ghalf^-1 e_a. From D=Ghalf^-T J Ghalf^-1,
 r* m^delta=|D_aa|=|x^T J x|<=||J|| ||x||²
             =||J|| (G^-1)_aa.
Consequently
 ||J|| >= (r*/C_w) m^delta.                       (conditional)
All other selected roots remain in G and its inverse; no individual-root
triangle lower bound for the actual source has been used.

Thus an independently proved family ||J||<=Cepsilon m^theta(epsilon)
with theta(epsilon)->0 would itself exclude every fixed off-line root.
Conversely RH would make this selected-root space empty, with norm zero.
This is only a conditional strength comparison, NOT a proof of RH and NOT
an obstruction to proving the proposed family. It warns that kernel
positivity has not supplied an easier free core estimate.

Do not multiply this lower bound by the UPPER observation row cap to claim
a lower bound for beta or Rlow. The actual signed observation compression
can cancel or lose directions; no such lower transfer has been proved.
The all-P goal remains open, and no mechanism/route is killed here.

Bounded independent check: q44_bounded_audit qualified PAPER PASS of the
final conditional section on SHA256
2e3c750881d20a0e8a48d95c10502524579f2357f4c9180a32b049587042d4bd,
no material findings; earlier sections used only for definitions, classical
zero-location/count facts inherited. Root separately reproduced12 exact
Cauchy inverse-diagonal controls with formal rational roots, not zeta data.
Decision: do not treat the full weighted-core norm as a free consequence of
Pick positivity. Further work must exploit the actual signed observation
compression or an independent arithmetic property; the goal is unchanged.

Projection-only follow-up was screened and identified as DUPLICATE, not a
new attempt: CCM_Q14_PROJECTED_EXPONENTIAL_TEST.md already proves the full
three-contact Gram limit chi_w=1/(2delta)-1/|w+1/2|²>0; Q22 reuses its
2x2 version. Exact normalization is
 ||P V_w||²=|2sinh(wL/2)|² ||P v_+(w)||²/L,
 |2sinh(wL/2)|²/m^delta=|1-exp(-wL)|² ->1.
Reflection gives the minus orientation. Read-only researcher
post_q52_projection_resolvent confirmed the source crosswalk. Q04 already
has the conditional single-pair negative eigenvalue; it is not a lower
bound after adding all other actual pairs. No projection-only restart.
