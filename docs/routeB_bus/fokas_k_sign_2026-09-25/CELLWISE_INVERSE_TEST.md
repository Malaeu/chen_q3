# Next test: full complement and inverse applied to the actual residual

2026-09-25. Source baseline 04df81d0. PAPER conditional derivation; no Lean
admission, no source positivity or decay asserted. This is independent of
Proshka request 9, which addresses the preceding scalar sign.

## Why this test

The constant positive floor is disproved for the selected family. A cellwise
floor may still exist. Before estimating a worst-direction floor and then
paying its inverse against the entire residual, test whether the residual
actually enters the small-eigenvalue directions. The distinction is between
`||r||/lambda_min(B)` and `||B^-1 r||`. It does not remove the need to prove
`B > 0` on the full complex complement.

Existing source block: PROSHKA_VERDICT_GOAL058_CELLWISE_COMPLEMENT_SIGN,
§4 (9)-(12). Existing inverse identity: G6N1SelectedFerrersFiniteAssetBank,
A2, at the true eigenvalue. The following argument specializes its shift to
the computable Rayleigh value using positivity and spectral monotonicity.
It is a conditional test, not a new claim that an inverse supplies positivity.

## Finite Hermitian statement and proof

Let K=K*, ||q||=1, a=q*Kq, Q=I-qq*, r=(K-aI)q and
B=Q(K-aI)Q restricted to q-perp. Assume B positive definite.
Let u be a unit lowest eigenvector, lambda its eigenvalue, t=a-lambda >= 0.
The min-max principle gives lambda<=a and lambda_2>=a+lambda_min(B)>a:
the lowest eigenspace is one dimensional. Its overlap c=q*u is nonzero,
because c=0 would give an eigenvector of B at -t<=0.
Writing u=cq+w, w in q-perp, the projected eigen-equation gives

    w = -c (B+tI)^-1 r.

Set h=||(B+tI)^-1 r||. Normalization gives |c|^2=1/(1+h^2), hence

    ||q-u(u*q)|| = h/sqrt(1+h^2).

Since B and B+tI have the SAME orthonormal eigenbasis and positive eigenvalues,

    h^2 = sum_l |r_l|^2/(b_l+t)^2
        <= sum_l |r_l|^2/b_l^2 = R^2,     R=||B^-1 r||.

Consequently the phase-independent projection error is bounded by

    ||q-u(u*q)|| <= R/sqrt(1+R^2) <= R <= ||r||/lambda_min(B).   (A)

The case r=0 is included (u is q up to phase and t=0). No smallness assumption
R<1 is required for nonzero overlap. This does not remove the distinct source
odd-sector/reality premises used to obtain real zeros of the ground transform.

## The exact two-block quantity to estimate

Use the source unit companion z in q-perp and X={q,z}-perp. Write

    B = [[tau, eta*], [eta, D]],    r = (r_z, r_X).

If D>0, put s=tau-eta*D^-1 eta. Then B>0 iff s>0. The inverse acting on
this particular residual is exactly

    v_z = (r_z-eta*D^-1 r_X)/s,
    v_X = D^-1(r_X-eta v_z),
    R^2 = |v_z|^2 + ||v_X||^2.                              (B)

These follow by eliminating the second row of Bv=r. They retain the joint
numerator; separately taking absolute values can lose its cancellation.
This is the dual Schur form of the already recorded source criterion, not a
replacement of the matrix or its full complex domain. Both D>0 and s>0 remain
unpaid source inputs. The dimensionless leakage eta*D^-1 eta/tau, when D>0
and tau>0, distinguishes a surviving scalar margin from one destroyed by
coupling to the rest of the complement.

## Exact consumer and an explicit compact sufficient rate

Let T(q,z) be sourceOrderedCCMRawTransform(L,N,q,z), L=log m>0. Assume
T(q,0)!=0, equivalently q_0!=0 (the selected source supplies rawZeroNonzero).
Let C=Xi(0)/T(q,0). Keep the existing projected ground transform
F_g(z)=C (u*q) T(u,z) and centered trial C T(q,z). Linearity, the existing
kernel-row Cauchy-Schwarz estimate, and (A) give

    |F_g(z)-C T(q,z)| <= |C| KernelL2(L,N,z) R/sqrt(1+R^2).  (C)

This matches the phase-independent projection used by the current pointwise
consumer. Selecting a different phase for u changes neither F_g nor (C).

The existing SIGNFREE_RITZ_INSIDE_CCM_UNIFORM_ERROR_ATOM verdict
(2026-09-04), S4, already supplies the dimension-free Bessel kernel bound
and warns that off-real growth is exponential in L. We reuse that bound;
this is not a newly discovered supplier. On [-L/2,L/2], the normalized
exponentials exp(2*pi*i*n*x/L)/sqrt(L) form an orthonormal family. Up to a
unit alternating sign and the production argument reflection, the kernel
row consists of Fourier coefficients of exp(i*z*x). Finite Bessel gives

    KernelL2(L,N,z)^2 <= integral_-L/2^L/2 exp(-2 Im(z) x) dx
                     <= L exp(|Im(z)| L).

The removable lattice values are included by the integral representation.
At zero, the exact kernel lattice identity gives T(q,0)=sqrt(L) q_0.
Thus on any compact subset of |Im(z)|<=H,

    |F_g(z)-C T(q,z)|
      <= |Xi(0)| m^(H/2)/|q_0| * R/sqrt(1+R^2).            (D)

For the selected source, the existing raw-transform/trial-row crosswalk
identifies this C with the current rawFplus normalization. Therefore a
sufficient PAPER rate is, for every fixed H>=0,

    m_j^(H/2) R_j/|q_(j,0)| -> 0.                         (E)

This is sufficient, not necessary: Bessel and the vector norm may lose
additional cancellations. It is not implied merely by R_j->0. It discharges
the tracking error only; trial-to-Xi convergence and the real-zero premises
remain separate. No uniform positive lower bound for B is assumed.

## Discriminating computation and stopping rule

Use the existing literal full K and rectangle-center Ferrers row at m=4,8;
these are finite diagnostic cells BELOW the accepted source threshold, and
the center row is not asserted to be the exact-energy source row. Compare
full complement minimum d, tau, full inverse residual R, raw ||r||/d, and
actual ground projection error at increased precision. If d<=0, do not use
(A). If R is also large, this route has not improved tracking at that cell.
If R is small while ||r||/d is large, the next source target is the joint
numerator in (B), together with full Schur positivity, rather than a blanket
residual norm estimate. A finite favorable result proves no cofinal rate.

## Independent review

Native read-only reviewer /root/sign_algebra_review checked (A)-(E) against
the exact kernel and tracked-transform definitions: no material mathematical
findings. The requested explicit nonzero anchor assumption is included above.
This checks only the conditional reduction, not its unpaid source premises.

## Executed diagnostic: positivity fails at the m8 center

Separate-process checks agree: root ambient compression at 70/90 digits and
Householder compression at 100/140 digits for m4/m8 respectively.
At m4, d=2.23465093071524e-7, ||r||/d=236.73617,
R=0.0309978352827 and actual projection error=0.0308907298849.
At m8, tau=8.28202808736703e-10 is positive but the full complement has
three negative eigenvalues, with minimum -1.14002276171903e-11. The saved
unit witness has |q*y|=6.02e-143 and the same negative ambient quadratic
value at 140 digits; it is almost entirely odd under mode reflection.
Four full-K eigenvalues lie below the central trial Rayleigh value.
Thus (A) is inapplicable at this cell. A small algebraic inverse-residual
norm without positivity must not be used as a ground-angle bound.
These are floating-point diagnostics, not interval certificates or a
counterexample on the selected cofinal source tail. They show why the full
complement, especially the odd sector, must be tested independently of tau.

Files: schur_probe.py, schur_probe_m4_dps100.json,
schur_probe_m8_dps140.json, inverse_independent_checks.json.
The independent reviewer checked compression, Schur separation, witness
lifting, parity and positivity guards without material findings. Runs use
separate processes to avoid reuse of precision-dependent cached values.

Subsequent check: INDEPENDENT_ENERGY_SHIFT.md certifies a finite repair by an
independent energy cut mu below a, with a separate ground upper certificate.
The Rayleigh-shift failure above remains true.
