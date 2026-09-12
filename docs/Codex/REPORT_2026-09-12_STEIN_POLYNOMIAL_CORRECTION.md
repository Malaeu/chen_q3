# Polynomial source covariance: the derivative correction has both signs

Status: ACCEPTED_PAPER_STEIN_DERIVATIVE_CORRECTION_DIAGNOSTIC_ONLY.
This is a bounded audit of the live ODDINFINITY mechanism, not a new
Proshka send, source numerical run, or all-order Hankel sign claim.

Use the exact full-source notation in the accepted
REPORT_2026-09-12_SOURCE_MOMENT_HANKEL_INTERFACE.md, SHA256
f549fb4fe3990bbc360cb39a657f713ee5576259f997f403938cfc6ed7280aa1:
p=Phi/Z, U=X^2, h(u)=log Phi(sqrt(u)), b=-2h', b'>=1/2.
Fix any integer k>=1 and let nu_k(du)=u^k law(U)(du)/mu_k.
Write E_k for this probability expectation. Its density is proportional
to u^(k-1/2)exp(h(u)), positive on(0,infinity). Full-source weighted
derivative decay and k>=1 justify the integrations by parts below;
the boundary density vanishes at both0 and infinity.

For any polynomial phi,

    E_k[b(U)phi(U)]=(2k-1)E_k[phi(U)/U]+2E_k[phi'(U)].   (1)

The inverse moment is integrable because k>=1. Complex polynomials are
handled by linearity. Given any nonzero complex polynomial q, define

    A=E_k[|q|^2],       B=E_k[U|q|^2],
    C=E_k[U^2|q|^2],    D=E_k[|q|^2/U],
    R=Re E_k[conjugate(q)q'],
    S=Re E_k[U conjugate(q)q'].

All quantities are finite; A>0. Apply(1) to |q|^2 and U|q|^2:

    E_k[b|q|^2]=(2k-1)D+4R,
    E_k[bU|q|^2]=(2k+1)A+4S.                              (2)

For the probability law |q|^2 nu_k/A, monotonicity b'>=1/2 gives
Cov(b(U),U)>=Var(U)/2 by the two-independent-copies identity. Thus

    (2k+1)A^2-(2k-1)BD+4(AS-BR)
        >=(AC-B^2)/2 >0.                                 (3)

The right side is strictly positive because a nonzero polynomial has
only finitely many zeros and the original law has positive density on
the entire positive halfline. Integrability follows from(2), b>0 and
finite polynomial moments; no second moment of b is needed.

The term AS-BR has no uniform sign, even for linear real test polynomials
and for this same actual source. Put m=E_k U, v=Var_k(U)>0.

- If q(U)=U-m, then A=v, R=0 and S=v, so AS-BR=v^2>0.
- If q(U)=U, then R=m, S=E_k U^2=A and B=E_k U^3, so
  AS-BR=(E_k U^2)^2-(E_k U)(E_k U^3)<0.
  Strict Cauchy-Schwarz for U^(1/2) and U^(3/2) gives this inequality:
  equality would force U to be constant almost surely, which it is not.

These are test polynomials under the unchanged actual source law. They
are not the old polynomial density control or perturbations of it.
Dropping the derivative correction from(3) is therefore not justified
by an assumed nonpositive sign for all q. These examples do not claim
that the desired Hankel sign is negative or that every possible source
covariance argument fails. They exclude that particular sign shortcut.

For constant q, R=S=0 and(3) is exactly the already accepted scalar
moment inequality(M). For general q all A,B,C,D,R,S are quadratic in
q's coefficients; (3) is homogeneous of degree4, whereas the required
H_n inequality is a quadratic form in the Hankel test coefficients.
A valid mapping or polarization that handles this distinction and the
derivative correction remains to be supplied. Neither the quartic
inequality nor these sign controls prove such a mapping impossible.

No source-sign counter reset or actual H_n positivity follows from this
audit. Keep the current live request unchanged and use this derivation
when checking its full final answer.

## Independent acceptance

The sole independent checker /root/sibling5_check read the complete
3350byte/71LF candidate, SHA256
158c7e469bfbbfe551399e6f00155eda5de6b259a674f76349fa879d5247fa60,
and returned ACCEPT at the diagnostic scope only. It verified the full
integration-by-parts factors, k>=1 boundary and inverse moment, complex
polynomial derivatives, the tilted covariance numerator, strict variance
margin and both actual-law correction signs. The parent derived all
these steps separately before review. No numerical run was required.
Only the status line and this receipt changed after review. This is not
an all-order source sign theorem and does not alter the count of failed
source-sign attempts or interrupt the current Proshka generation.
