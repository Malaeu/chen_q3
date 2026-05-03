# Q3 PSD-pd Step 8 Certificate Design (2026-05-03)

Status: in progress

Placement:

- This belongs to the fallback corrected-cone route
  `A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 -> LF-pd -> G6`.
- It does not pivot the active control plane away from the primary
  `H-bridge / PO3-square.2d3` frontier.

## Target

Step 8 is the certificate problem for the boundary-null compact-support Gram
kernel from the Hermitian Weil-square route.

For a local compact bump basis, Step 7 gives:

```math
K = A + B - P.
```

After imposing the boundary-null constraints

```math
H(1/2)=H(-1/2)=0,
```

the boundary term disappears, so the reduced target is:

```math
\widetilde K
=
N^\ast(A-P)N
\succeq 0,
```

where the columns of `N` span the nullspace of the two boundary functionals.

This is the exact Step 8 blocker:

```math
\boxed{
\text{Arch Toeplitz kernel dominates sparse prime-shift kernel on }
\ker(H(1/2),H(-1/2)).
}
```

## Semantic search synthesis

Local search hits:

- `full/sections/Main_closure.tex` contains a sparse Gershgorin criterion for
  packet Toeplitz blocks, but also records why a uniform dense packet gap cannot
  hold.
- `docs/insights/full_kernel_psd_frontier_2026_03_07.md` says the prime block
  alone is not PSD on dense packet spaces; the honest target is direct PSD of
  the full kernel `K_Q`.
- `docs/insights/route_p_primary_2026_03_07.md` marks the old literal route
  `prime-block PSD factorization -> Arch domination` as superseded.
- `docs/insights/prime_term_shift_K_dependent_2026_01_19.md` is the warning
  that shifted caps are K-dependent, so no uniform shifted prime cap should be
  assumed.
- `docs/insights/target_cone_audit_2026_03_07.md` confirms that the broad
  pointwise-nonnegative cone is false; Step 8 must stay inside the
  positive-definite/autocorrelation cone.

External sanity:

- Bombieri's Weil-quadratic-functional paper frames the target exactly as a
  quadratic form: positive semidefinite iff RH, with finite truncations and
  eigenvalues as the natural approximation language.
- Bombieri--Lagarias relate Li positivity to Guinand--Weil and Weil's
  criterion; this supports using explicit-formula quadratic positivity as the
  public mathematical contract, not scalar mirror identities.

References:

- Enrico Bombieri, *Remarks on Weil's quadratic functional in the theory of
  prime numbers, I*: `https://eudml.org/doc/252338`
- Enrico Bombieri and J. C. Lagarias, *Complements to Li's Criterion for the
  Riemann Hypothesis*: `https://doi.org/10.1006/jnth.1999.2392`

## Matrix structure

For compact local bump basis

```math
\psi_j(u)=\ell^{-1/2}\eta((u-u_j)/\ell),
```

the matrices before boundary reduction have the following shape:

```math
A_{ij}=a_\ell(u_j-u_i),
```

so `A` is Toeplitz-like on a uniform grid.

```math
P_{ij}
=
\sum_{m\log p\le 2L}
\frac{\log p}{p^{m/2}}
\left[
r_\eta((u_j-u_i-m\log p)/\ell)
+
r_\eta((u_j-u_i+m\log p)/\ell)
\right],
```

so `P` is a sparse shifted-band matrix.

The boundary matrix `B` has rank at most two, but Step 7 removes it by reducing
to `ker Q`, where

```math
Qv=(H_v(1/2),H_v(-1/2)).
```

Thus the certificate is not `K=A+B-P` on the full coordinate space.  It is:

```math
\widetilde K=N^\ast(A-P)N.
```

## Certificate triage

### Route 8A: Herglotz/full-symbol certificate

For a fixed packet family, prove that the full Toeplitz sequence

```math
\kappa_m=\alpha_m-\beta_m
```

is positive-definite.  Equivalently, exhibit a positive measure or prove the
full symbol nonnegative in the regular symbol regime.

This is the cleanest certificate, but also the hardest.

### Route 8B: Toeplitz floor minus sparse-band norm

Prove a lower bound

```math
A\succeq c\,G
```

on the boundary-null subspace and an upper bound

```math
P\preceq \rho\,G
```

with `rho <= c`.

This matches the existing `PSD_FormAlgebra` consumer.  The risk is the known
K-dependent shifted prime cap.

### Route 8C: Sparse Gershgorin finite certificate

Use the old sparse Gershgorin proposition as a finite-block checker:

```math
\kappa_0\ge\sum_{m\ne0}|\kappa_m|+\varepsilon.
```

This is useful for finite evidence and small blocks, but it is explicitly not a
dense main theorem because collapsing packet differences can make any uniform
positive gap false.

### Route 8D: Schur-complement / boundary projection certificate

Treat boundary-null reduction as a constrained positivity problem:

```math
v^\ast(A-P)v\ge0
\quad\text{for all }Qv=0.
```

Equivalent finite check:

```math
N^\ast(A-P)N\succeq0.
```

This is likely the best Lean landing surface because it is pure finite
linear algebra once `A` and `P` are provided.

## Recommended next theorem order

Do **not** jump straight to a global infinite positivity statement.

The next Lean/document target should be:

1. `boundaryNull_reduction_form_eq`:
   `Qv=0` removes `B` and rewrites the form as `v*(A-P)v`.
2. `psd_on_kernel_of_reduced_psd`:
   if `range N = ker Q` and `N*(A-P)N` is PSD, then the original form is
   nonnegative on boundary-null vectors.
3. `finite_step8_certificate_contract`:
   a data structure recording `A`, `P`, `Q`, `N`, `G`, and the reduced
   generalized-eigenvalue check.
4. Only after that, instantiate with bump/Toeplitz/sparse-band matrices.

## Failure criteria

Step 8 fails with current Q3 constants if:

- sparse Gershgorin is the only certificate and it does not survive dense
  packet exhaustion;
- the shifted prime cap grows past the Arch floor on the compact/scale ladder;
- boundary-null projection destroys the Toeplitz floor estimate;
- the finite certificates cannot be made uniform in `L`, `ell`, and packet
  order.

If any of these occurs, record a route obstruction rather than promoting finite
evidence to an RH proof.

## Current recommendation

Use Step 8 first as a constrained finite linear-algebra package, not as a
global analytic claim.

The fastest robust landing surface is:

```math
\boxed{
Qv=0,\quad N^\ast(A-P)N\succeq0
\Longrightarrow
\mathcal W(h_v)\ge0
\text{ on the boundary-null finite span.}
}
```

This keeps the certificate basis-invariant and avoids repeating the killed
broad-cone or prime-block-PSD routes.

## Prime-Graph SOS amendment (2026-05-03)

Follow-up note:

```text
docs/insights/q3_psdpd_prime_graph_sos_step9_audit_2026_05_03.md
```

The sharper Step 8 certificate rewrites the prime term by the shift identity

```math
2\operatorname{Re}\langle h,S_a h\rangle
=
2\|h\|^2-\|h-S_a h\|^2.
```

Thus

```math
A-P
=
A+\sum_aw_a(I-S_a)^\ast(I-S_a)-2W_LG.
```

The finite target becomes:

```math
N^\ast
\left(
A+\sum_aw_aL_a-2W_LG
\right)
N
\succeq0.
```

This is equivalent to `N^*(A-P)N >= 0`, but it exposes the exact
Prime-Graph spectral-gap target.  The algebraic consumer is now Lean-checked in
`Q3/Proofs/PSD_FormAlgebra.lean`.
