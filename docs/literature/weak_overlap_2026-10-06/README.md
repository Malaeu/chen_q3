# Bounded source-weight alias check, 2026-10-06

Target and explicit negative control:
`../../routeB_bus/source_observability_2026-09-28/WEAK_OVERLAP_SPECTRAL_MEASURE_2026-10-06.md`.
Need rho_m=||P_bottom g_m||>=c m^(-A) on negative-bottom cells for the
literal full CCM matrix and normalized theta source. Small residual and
cyclicity alone fail on the explicit 2x2 control. Root's resolvent identity
shows that off-real source-Weyl convergence is already automatic and cannot
supply the missing lower atom weight. No actual-source inequality obtained.

Read-only researcher weak_overlap_alias used three object dictionaries:
Jacobi/Christoffel norming weights; Weyl/Krylov spectral measures; PDE
spectral observability/unique continuation. Shelf search via ask.sh returned
ASK_STATUS: INCOMPLETE, NOT an absence result. A bounded primary-source pass
found the two mechanisms below. Root reread the cited formulas/theorem.

## Jacobi/Christoffel weights — verified partial analogue

Source https://dlmf.nist.gov/3.5, section3.5(vi), equations3.5.30-32.
Local dlmf_3_5.html SHA-256:
e85fcbd132dc6a09d683427a6c2566e8c52d7f24992facaaaba90b50d7ffa611.
Quote immediately before(3.5.32): “Then the weights are given by”.
The formula is w_k=beta_0 v_(k,1)^2 for normalized Jacobi eigenvectors.
For our unit source, beta_0=1. Lanczos on its cyclic subspace maps g to the
first basis vector, preserving the observed spectral weights. A missing
bottom atom stays missing; this construction cannot create it. The associated
orthonormal polynomial kernel has w_j=1/sum_(k=0)^(d-1)|p_k(lambda_j)|^2
at observed atoms. Thus rho>=c m^(-A) needs an UPPER kernel bound
sum|p_k(lambda_min)|^2<=c^(-2)m^(2A), plus bottom visibility. Both are OPEN
for our actual recurrence. The 2x2 cyclic control also has this representation
and arbitrarily small bottom weight: the identity alone fails the control.
No lower-weight theorem for the CCM source follows from this reference.

## Open-region PDE observation — verified mismatch

Le Rousseau--Robbiano, Spectral inequality and resolvent estimate for the
bi-Laplace operator, https://arxiv.org/abs/1509.02098v5, 2017-11-30.
Local 1509.02098v5.pdf SHA-256:
f05d5003a1e11f210216cf627a89b402b370070790e7334bebaa162df3d462c8.
Quote, Abstract p1: “from an arbitrary open subset of the manifold”.
Theorem1.3 p4 bounds ||u||_L2(Omega) by C exp(C mu^(1/4))||u||_L2(O)
for the clamped bi-Laplacian spectral subspace below mu. Its input is a
specified elliptic PDE and observation on an open region. Our signed dense
matrix and single scalar integral against G satisfy neither observation nor
operator hypotheses through any proved map. The 2x2 control has neither,
so this theorem does not exclude it or give the desired CCM estimate.

Disposition: no supplier in these checked mechanisms. This is bounded search,
not a claim of global nonexistence. Do not turn a representation into a
quantitative estimate. Next decision awaits Proshka answer10 on actual-source
lower overlap; no new route, status promotion, or separate research loop.
