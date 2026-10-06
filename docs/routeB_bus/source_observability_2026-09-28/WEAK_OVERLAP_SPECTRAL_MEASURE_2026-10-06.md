# Weak overlap: spectral measure alias and its missing input

Root PAPER calculation, 2026-10-06, while Proshka question10 computes.
This does not prove or refute the actual-source lower overlap. Its role is
to discriminate literature mechanisms before importing a Herglotz argument.

## Exact source target

Keep the same full K_m and unit g_m=c_m(G)/||c_m(G)||, with m=N and L=log m.
For the entire bottom projector P0, write rho=||P0 g||, eps=||K g||.
The independently checked conditional consumer in
`DIRECT_THETA_LOCALIZATION_AUDIT_2026-10-06.md` needs eps/rho->0 on negative
bottom cells. A fixed-polynomial lower rho is sufficient because eps is
superpolynomially small. Neither nonvanishing nor such a lower bound has
been proved. Define the positive source spectral measure

  mu_m=sum_distinct_lambda ||P_lambda g||^2 delta_lambda,
  M_m(z)=<g,(K_m-zI)^(-1)g>=integral (t-z)^(-1) dmu_m(t).

Its total mass is1. Its bottom atom has mass rho^2, if present. Hermitian K
makes M a Herglotz function in the upper half-plane, regardless of the sign
of the spectrum. Positivity of this measure is NOT Weil-form positivity.

## What the residual already proves

For every nonreal z, the resolvent identity gives exactly

  (K-zI)^(-1)g=-g/z+(K-zI)^(-1)K g/z,
  |M_m(z)+1/z|<=eps_m/(|z| |Im z|).

Therefore our source Weyl functions converge to -1/z locally uniformly off
the real line, using only the already checked residual; no RH is needed.
This convergence says nothing sufficient about tiny unseen negative atoms.
A limiting Herglotz theorem that merely reproduces this limit cannot supply
the missing lower weight. A real-axis evaluation outside the spectrum would
need a proved separation from that spectrum, not a presumed gap.

## Explicit negative control outside the CCM class

Take K_m=diag(-1,0), delta_m=exp(-m^2),
g_m=(delta_m,sqrt(1-delta_m^2)). Then g is unit with positive coordinates,
P0=diag(1,0), eps_m=rho_m=delta_m, and eps_m/rho_m=1. The bottom eigenvalue
stays -1 even though the residual decreases faster than every fixed power.
For every m, g and Kg are linearly independent, so g is a cyclic vector.
Its spectral function is exactly

  M_m(z)=-delta_m^2/(1+z)-(1-delta_m^2)/z,
  M_m(z)+1/z=delta_m^2/[z(1+z)].

Thus positive atom weights, cyclicity, source positivity in coordinates,
superpolynomial residuals, and arbitrarily rapid off-real convergence of M
still do not give the required quantitative lower bottom weight. The control
violates the desired polynomial lower-weight hypothesis and has no CCM/theta
structure; it is NOT a counterexample to the actual target. In the actual
problem, g is even and a wholly odd negative bottom could also make rho=0.

## Bounded search question

Can a theorem on norming constants, Christoffel weights or quantitative
eigenfunction observability impose a lower atom weight from hypotheses that
are actually verified for the full CCM matrix and exact theta source?
The decisive step must distinguish this control, retain degeneracies via
P0, and supply constants on the original eventual sequence. Merely naming
cyclicity, a positive spectral measure, or the limiting Weyl function does
not constitute such a step. The bounded alias-hunt is complete: the Jacobi identity lacks an actual
upper Christoffel-kernel bound, and open-region PDE observability has no
proved map to our scalar observation. See
`../../literature/weak_overlap_2026-10-06/README.md` for primary sources, hashes
and precise hypothesis mismatches. Neither supplies the lower overlap.
