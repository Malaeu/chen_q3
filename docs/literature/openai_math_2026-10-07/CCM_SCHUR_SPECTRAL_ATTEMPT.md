# Own CCM Q2 followup: exact Schur spectral return

2026-10-07. Same full affine H_t and T of Q2(4), same two grids and
central pairing Q2(23). This attempts Q2 section8 alternative B. No Q3 sent.

The obstruction is the correlation of the actual negative spectral density
with the signed prime-pole transfer. A two-mode extension has a small Schur
matrix but still carries the whole old resolvent. We must retain that old term
and its poles before claiming any signed gain.

Fix one t, write H=[[A,B],[B^T,D]] real symmetric, D two by two, and let
R(w)=(H-wI)^(-1), Q(w)=(A-wI)^(-1), S(w)=D-wI-B^T Q(w)B.
For nonreal w both Q and S are invertible. For either actual channel b=b_(r,+/-)(z)
split into old/new coordinates (zero new coordinates for the padded old channel).
The exact bilinear Schur contraction is

    b^T R(w)b = b_o^T Q(w)b_o + v(w)^T S(w)^(-1)v(w),
    v(w)=b_n-B^T Q(w)b_o.                                      (1)

For fixed m choose R0>max_(0<=t<=1)||H_t||. Functional calculus gives

    H_(t,-)^(p-1) = lim_(y down to0) (1/pi)
      integral_(-R0)^0 (-lambda)^(p-1) Im R_t(lambda+iy) d lambda. (2)

Finite dimension, p>1, and a cutoff outside the spectrum justify this limit;
the zero eigenvalue has weight zero. A uniform dominating scalar Poisson
integral bound permits the subsequent t integration. The fixed-basis
diagonal companion in T is added separately, exactly as in Q2(13).

For complex b(z), the integrand in its bilinear contraction is

    b^T Im R(lambda+iy)b
      = [b^T R(lambda+iy)b-b^T R(lambda-iy)b]/(2i).               (3)

It is NOT in general Im[b^T R(lambda+iy)b]. Thus use (1) at BOTH spectral
parameters in (3). The contour parameter z is independent of w and fixed
during the spectral inversion. For H=[0], lambda=0,y=1,b=1+i,
b^T Im R(i)b=2i, whereas Im[b^T R(i)b]=0. This is an abstract diagnostic,
not a CCM counterexample. Replacing transpose by adjoint is equally invalid.

The correct return of the first term of(1) is b_o^T A_-^(p-1)b_o.
The second term returns the full correction to that isolated old spectral
functional, including all cross couplings and both new modes. It cannot
be dropped or assumed positive as a bilinear expression. At B=0 it still
contains the independent new block; at B nonzero it contains the eigenvalue
motion. The Schur denominator depends on all old eigenvalues and B.

Small Schur dimension alone supplies no bound: the real reflection-symmetric
control H=diag(-a I_d, I_2), a>0, has a 2x2 S and no coupling, yet
Tr H_-^p=d*a^p with zero negative mass on the new block. The actual CCM source
has additional arithmetic constraints; this control refutes only a dimension-
or new-mass-only inference, not the central CCM estimate.

## Outcome

This is an exact representation attempt, not a signed supplier. The old
negative spectral term and the signed jump of the Schur term must jointly
contract with the same a(z) and both actual grids. No gap, spectral averaging
law, conditional independence, or positive perturbation is present by this
algebra alone. The fixed-basis diagonal density also remains. Before another
Pro question, seek a source-specific bound for this joint object; a repeated
spectral inversion or two-by-two determinant is not a gain. SP/RH OPEN.

Independent read-only moment_compensation_map audit: PASS on(1)–(3), both
controls, and the finite spectral/path limit. No interchange with a later
infinite arithmetic contour is claimed; that would require a further uniform
dominating estimate. The paid Q2 finite contour is the appropriate receiver.

## Alias return: spectral averaging is an exact derivative identity here

Dictionaries: block Schur spectral measure; matrix-valued spectral averaging;
Birman-Solomyak resolvent pairing. All three shelf queries returned
ASK_STATUS: INCOMPLETE (semantic-index freshness), not absence. The bounded
literature lookup sought a worked signed spectral-measure mechanism.

Fetched source: Gesztesy–Makarov, Applications of the spectral shift operator,
arXiv:math/9903186v1, https://arxiv.org/abs/math/9903186 . Saved PDF:
sources/gesztesy_makarov_math9903186v1.pdf, SHA256
088cb83f557247c17461f8cdc16915f9958ffd16740be8af69e71c2a825dcca3.
Researcher ccm_schur_alias located it; root independently reread Hyp4.1,
Theorems4.3/4.5, Remark4.4(iv), and the worked proof(4.13)–(4.14), pp9–11.
Discovery/mapping VERIFIED; partial mechanism only.

Exact quote, Hyp4.1: “V (s) is continuously differentiable with respect to
s ∈ Ω in trace norm.” Theorem4.3(4.8) integrates the spectral measure with
insertion V'(s), yielding the difference of endpoint spectral shift functions.
It explicitly permits signed perturbations. In finite dimension our entire
affine path extends to an open real interval and meets these hypotheses with
V(t)=t deltaK. Integrating against (-lambda)_+^(p-1) returns

    integral_0^1 Tr(deltaK H_(t,-)^(p-1))dt
       = -(Tr K_(M,-)^p - Tr padK_(m,-)^p)/p.

This is a PROVED applicable identity, not a missing-path objection. But the
required insertion is deltaC. Substituting deltaC=deltaB-deltaK returns the
known background/moment balance and no independent inequality. The separate
fixed-basis diagonal account is not removed by this trace theorem.

Theorem4.5(4.9) instead averages K* E_(H0+sKK*) K along a positive KK* path.
Proof(4.13)–(4.14) uses the resolvent/log identity and weak Fubini; the result
is a positive operator-valued measure. Here its fixed positive insertion and
monotone path are OPEN/unprovided; the original full affine arithmetic path
cannot be replaced by that path without paying the difference. Q2(27) and
the complex-vector control above show why its adjoint compression cannot be
substituted for our analytic transpose square. No positivity of deltaK is
asserted false merely because it has not been proved.

Disposition: spectral averaging is excluded as an additional signed supplier
from the currently established inputs. Reopen only with a proved source-aligned
positive insertion AND a return controlling the actual central pairing,
including old spectral mass, both grids and diagonal companion. No general
no-go and no arithmetic CCM counterexample has been established.
