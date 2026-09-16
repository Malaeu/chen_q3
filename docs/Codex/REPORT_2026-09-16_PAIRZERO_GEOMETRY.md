# Pair-zero-compatible geometry of the original V

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed analytic dictionary and controls.
DISCOVERY: INCOMPLETE_NO_CONSUMABLE_TARGET. Canonical theorem/consumer edge
is unbound; no canonical admission, Lean certification, or RH claim.
This is a direct-source compatibility audit, not a completed literature search.

## 1. Fixed object, preserved facts, and scope

Source base: eeab3bfa164e7f77646a0947284be0aac423efd1.
f=Phi/||Phi||_2 is the complete theta source, without truncation.
I=(-log(2)/2,0), S={z: |Im z|<pi/4}, and

    V(x,y)=integral_0^infinity (2X+x+y) f(X+x) f(X+y) dX.       (P1)

The target is V[c]>=0 for EVERY finite family in I and arbitrary complex
coefficients. A positive diagonal or an unrelated positive kernel does not
replace it. The accepted inputs under docs/Codex are:

- REPORT_2026-09-16_LOGVCURV_INTAKE.md, I1--I4, SHA256
  074a6ee11edf58ed502f8a41454515c06b5d286605b53ff0fe9e889981a3b929:
  V is holomorphic on S x S, has complex pair zeros, and

    D(z):=V(conj(z),z)=2 integral_|Re z|^infinity u|f(u+i Im z)|^2 du>0. (P2)

  C=partial_x partial_y log V is not PSD on any real open interval.
  This kills the infinitely divisible entrance, not ordinary Gram positivity.
- REPORT_2026-09-16_LOGVCURV_PREFLIGHT.md, section 1 and accepted scope,
  SHA256 79755565b206eb578a3681b5ef68a0580776869c61703a62a63625b6fcb182a9:
  d=V(0,0)>0, V_x(0,0)=0, and C(0,0)=(I1-f(0)^2)/d>0.
- REPORT_2026-09-14_SCHUR_REPEATABILITY.md, S5--S11, SHA256
  fe737941236b24c67bee7803a38014660698e852b2e61bc54f58672efb494190:
  logarithmic curvature PSD would be a stronger sufficient entrance.
- REPORT_2026-09-15_SPACE_SIBLING_HUNT.md, sections 2--5, SHA256
  cf4636f825869ef9bf4ea03486e3bfdd6433ace9155d7c8f96bc2ad3e87bb1e7:
  existing Fock, Krein and Schur constructions have unpaid theta interfaces.
- REPORT_2026-09-15_SOURCE_SUPPORT_HUNT.md, SUPPORT and W1--W2,
  SHA256 9b059659b10948bed90d9df482cfe97e9cc229116e1db46b029bba81a22c4966:
  the exact full-source weighted transfer is known; its unweighted bounded
  extension remains unpaid. This audit does not repair that estimate.
- REPORT_2026-09-15_SUPPORTSTABILITY_INTAKE.md, sections 4 and 6, SHA256
  14f8e48fd325f41df7b46f1da84140e1ff56b16df95ee3c6b9c0000f9ae9e895:
  W2 was already investigated by Proshka and reduced to one exact response
  p in L2(0,infinity). That criterion is retained; the user directed a
  return before another expansion of its critical tail.

Negative controls: the full-source-family control
f0(u)=exp(-u^2)-exp(-2u^2)/4 has a negative four-shift form despite the
positive complex diagonal mechanism. The additional polynomial kernel in
section 4 tests the stronger proposal that even a strictly positive metric
would provide the missing common Gram space.

Search rewrites, UNVERIFIED as theta suppliers:
(a) D as the squared norm of a holomorphic common feature, or log D as a
projectively induced Kahler potential; (b) positivity after multiplication
by an auxiliary kernel, followed by exact removal of that multiplier.
Three dictionaries: holomorphic Gram/polarization; Calabi diastasis and
projective immersion; Hermitian polynomial sums of squares and multipliers.

The mgrep local shelf query for Calabi/resolvability/Hermitian sums returned
HTTP 403, credits depleted. No no-hit claim follows. The registered ask.sh
query was not substituted for the higher-priority mandatory search tool.
No shared index was refreshed. The earlier named reports were read directly;
the known source below was fetched by its exact arXiv identifier, without a
replacement search. Thus search coverage is INCOMPLETE. Stop this bounded
audit after the exact mapping and its explicit negative control; do not send
another generic request to prove Gram positivity under a new name.

## 2. A positive source field is not yet a holomorphic feature

For z=a+ib and s>=0 put u=sqrt(s+a^2). The exact change of variables in P2 is

    D(z)=integral_0^infinity |H_z(s)|^2 ds,
    H_z(s)=f(sqrt(s+a^2)+ib).                                (P3)

This uses the full source and the physical boundary; it supplies a positive
L2 field for each z. It does NOT identify its cross inner products with V.
For s>0, direct differentiation gives the pointwise identities

    partial_bar_z H_z(s)=1/2 (a/u-1) f'(u+ib)
                       =(a-u) partial_s H_z(s),
    partial_z H_z(s)    =(a+u) partial_s H_z(s).               (P4)

Hence this particular moving-boundary field is not holomorphic. No claim
about a bounded generator at s=0 is made by these pointwise formulas.
The missing property is not finite energy: that is already paid by P2.
It is an independently constructed holomorphic common feature Psi with
||Psi(z)||^2=D(z). If such a feature exists on a neighborhood, uniqueness
of holomorphic polarization forces

    <Psi(z),Psi(w)>=V(conj(z),w).                             (P5)

The inner product is conjugate-linear in its first argument. P5 would keep
every mixed term. Declaring Psi to be the abstract square root of V would
assume the sign under investigation.

## 3. Exact Calabi dictionary: projective, not flat

On a sufficiently small disk about 0, V(z,0) is nonzero. Let d=V(0,0),

    R(z,w)=d V(z,w)/(V(z,0)V(0,w)),
    H(z,w)=log R(z,w),
    Q(z,w)=R(z,w)-1,
    S0(z,w)=V(z,w)-V(z,0)V(0,w)/d.                           (P6)

The branch is chosen with H(0,0)=0. R(z,0)=R(0,w)=1.
The diagonal H(conj(z),z) is the diastasis at 0 of the local potential
log D. Its metric coefficient is partial_z partial_bar_z log D;
at 0 it equals the paid C(0,0)>0, so it defines a Kahler metric on a
sufficiently small disk. Global positivity of this scalar metric is NOT
assumed or asserted.

Primary mathematical exposition fetched and checked:
Andrea Loi and Michela Zedda, arXiv:1712.04298v1,
https://arxiv.org/pdf/1712.04298v1,
PDF SHA256 5e25d237b432f342f0402cae5c75a3b7c80baf3d15fb0818c3ae144f6d460215.
Definition 2.2.2 and Theorem 2.2.4, printed pp.24--25 (PDF pp.30--31),
give the local b-resolvability criterion. Exact quote from the definition:
"if the matrix (sjk) is semipositive definite of rank N."
Here b=1, complex dimension one, N<=infinity, and the coefficient matrix
is that of exp(H(conj(z),z))-1=Q(conj(z),z). The theorem is a criterion;
it does not prove this coefficient matrix positive for theta.

Indeed,

    Q(z,w)=d S0(z,w)/(V(z,0)V(0,w)).                         (P7)

Thus Calabi's unpaid condition is exactly the normalized anchored Schur
condition. If Q(conj(z),w)=sum_j conjugate(h_j(z))h_j(w), the explicit
local feature is

    Psi(z)=V(0,z)/sqrt(d) * (1,h_1(z),h_2(z),...).            (P8)

Conversely a local Gram feature for V gives Q PSD by taking the orthogonal
complement of its value at 0. Taylor coefficient PSD means every finite
coefficient matrix, not finitely many low orders. This maps all complex
coefficients and all finite local families exactly.

The flat criterion would require the coefficient matrix of H itself to
be PSD. Its mixed derivatives give C PSD on a real neighborhood; the
accepted LOGVCURV result excludes this. The projective criterion asks for
exp(H)-1 and allows pair zeros. For instance V(z,w)=1+zw has the feature
(1,z) and has pair zeros, while its anchored Q=zw is positive.

Local ordinary Gram positivity would suffice globally here: the full V is
holomorphic on S x S, so local Hilbert Taylor coefficients obey a common
Cauchy bound on every compact path. In the existing feature domain,

    ||Psi^(n)(p)/n!||^2
      = partial_1^n partial_2^n V(conj(p),p)/(n!)^2
      <= M rho^(-2n).                                      (P9)

The left side is real nonnegative; the bound is on the absolute value of
the scalar coefficient. Compactness gives M,rho>0 independent of p along
the path. The Hilbert Taylor series continues the SAME feature through
successive disks. Identity of the kernel continues with it, and monodromy
on the simply connected strip gives P5 throughout S. Starting from PSD
on I gives the local feature by finite differences and Taylor coefficients;
starting from the local Calabi feature gives PSD on I. Thus no extra
global inequality is hidden in this dictionary, but the full local
coefficient positivity is still unpaid. This continuation is the n=1
ordinary-kernel version of LOGVCURV I2; no fractional root is taken.

## 4. Even strict metric positivity does not pay Calabi's condition

This is an explicit non-theta kernel, not a counterexample to V or RH:

    K(z,w)=1+zw-(zw)^2/4+(zw)^3+(zw)^4,
    P(r)=1+r-r^2/4+r^3+r^4,  r=|z|^2.                     (P10)

Since 1+r^4>=2r^2, P(r)>0 for all r>=0. For the potential log P,

    partial_z partial_bar_z log P(|z|^2)=N(r)/P(r)^2,
    N(r)=1-r+(35/4)r^2+20r^3+(35/4)r^4-r^5+r^6
        =(1-r+r^2)+(31/4)r^2+20r^3+(31/4)r^4
          +r^4(1-r+r^2)>0.                                (P11)

Thus the complex diagonal is positive and its logarithm defines a
strictly positive analytic Kahler metric on all of C. Nevertheless the
anchored coefficient of z^2 w^2 in K-1 is -1/4. Calabi's required
coefficient matrix is not PSD.

For an explicit finite row entirely within the original real interval,
take h=1/100, x=(-h,-2h,-3h), c=(1,-2,1)/h^2. Directly, the moments
sum_i c_i x_i^k for k=0,...,4 are (0,0,2,-12h,50h^2), hence

    sum_ij c_i K(x_i,x_j)c_j
      =-1+144h^2+2500h^4=-39423/40000<0.                  (P12)

This is exact rational algebra, not a numerical sign scan. It refutes
the generic transfer from positive diagonal plus positive scalar metric
to a common positive Gram space. The failing hypothesis is precisely
1-resolvability, already visible in the negative second-degree coefficient.

## 5. A positive multiplier cannot simply be removed

For t=zw the SAME control has

    (1+t)(1+t-t^2/4+t^3+t^4)
       =1+2t+(3/4)t^2+(3/4)t^3+2t^4+t^5.                  (P13)

Both 1+zw and the product on the right are Gram kernels, with explicit
monomial features and positive coefficients. K is not. A multiplier can
create positivity which is lost on division; positivity after a
Hermitian sum-of-squares stabilization is not a transfer back to V.
No theorem of Quillen/Catlin is invoked or claimed checked here.

An exact reversible safe class is a nonvanishing scalar congruence
V(z,w) -> a(z)V(z,w)a(w) with real values a on I (the Hermitian version
uses conjugate(a(z))a(w)). On each real finite family this is invertible
diagonal congruence and therefore cannot repair a negative direction.
For a general positive multiplier, an independent reverse implication
would have to be proved; P13 disproves it as a universal rule.

## 6. Decision and remaining concrete interface

The requested semantic brother exists: Calabi's projective criterion is
an exact local dictionary for ordinary V positivity and admits pair zeros.
It supplies no new theta-specific inequality. The next action is NOT to
rename the open Schur matrix as a metric or to prove only scalar curvature.
Likewise, P3 is a finite-energy field but not yet the holomorphic feature
required by polarization; P4 shows the precise defect of that direct map.

Keep the exact source-support bridge W2 from the earlier report as a diagnostic:
for one fixed v>1/2, the known support-preserving weighted transfer T_v
must satisfy ||T_v h||_2<=M||h||_2 for every compact smooth h in the
UNWEIGHTED norm. The subsequent SUPPORTSTABILITY response already reduced
it to one exact half-line response having finite unweighted energy; the
user then requested return before another tail expansion. It is therefore
not selected or re-dispatched here. The reconciliation note's preference
for W2 does not supply a new hypothesis or override that return point.
Before a new substantive Pro request, identify a full-theta structural
identity supplying a common positive feature or an independently proved
bound for the original coupled contribution. Merely requesting the
Calabi coefficient sign or the old response energy repeats the target.

Outcome: exact geometric dictionary and two analytic negative controls
against automatic diagonal/metric and multiplier-removal transfers.
No new lower bound for the original V, no negative V witness, and no RH
proof or refutation. Search-provider failure is operational, not a
mathematical no-hit and not a reason to declare the active goal blocked.

## Independent acceptance

Candidate SHA256: `ed0fb279a1949bbc0c39bff88fe0c48ebe95b5463f0798cff79dbcd91042ec6f`.
Review SHA256: `97ba1dbe235b43dd5c3d62226956af5c0873d9b14866534401592f30c08ebf3c`.
Verdict: `ACCEPT_PAIRZERO_GEOMETRY_DICTIONARY_AND_CONTROLS_ONLY`.
Parent checked the source passage, normalization, Cauchy continuation, CR defect,
exact rational control and multiplier identity. This is not a new theta sign
bound or canonical theorem admission. Search coverage remains INCOMPLETE.
