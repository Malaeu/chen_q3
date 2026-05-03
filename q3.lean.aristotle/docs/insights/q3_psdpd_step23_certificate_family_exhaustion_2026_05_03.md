# Step 23 -- Certificate family and exhaustion contract

## Status

Step 22 closed the first fully interval-backed finite PSD-pd block:

```text
k_spline = 11
L        = 3.0
ell      = 0.30
delta    = 0.25
kappa    = 3.25
theta    = 1e-4
```

with all matrix sources under midpoint/radius contracts:

```text
A, P, P0, Q.
```

The certified finite penalty guard gives

```text
Dtheta safe_lower ~= 1.22e-4
Rkappa safe_lower ~= 1.36e-1.
```

This is a real finite certificate candidate.  It is not a global RH proof.
The missing layer is a directed certificate family plus an exhaustion theorem.

## Numbering alignment after Step 24

The intended theorem packet is:

- Theorem 23A: finite penalty certificate on `ker Q`.
- Theorem 23B: boundary-null exhaustion.
- Lemma 23D: boundary-null correction.
- Theorem 23C: RH closure from boundary-null positivity plus the existing Q3
  linkage.

In the repository timeline, Step 24 has already landed as the Lean receiver for
Theorem 23A:

```text
Q3/Proofs/PSD_PenaltyCertificate.lean
```

Therefore the next engineering step after this note is the certificate
family/manifest generator, not another finite sweep.  To avoid renumbering
committed work, that manifest step should be recorded as the next project step
after the Step 24 Lean receiver.

## Semantic Search Synthesis

Local search found no ready-made project theorem that already performs this
exhaustion.  The useful existing anchors are:

- `PSD-pd` is the public fallback certificate target: PSD of
  `K_Q(g_i,g_j)` on a dense translation-compatible packet subspace.
- `A3-pd` as a uniform floor on the whole dense packet dictionary was already
  rejected as too strong.  Step 23 must not resurrect a false uniform gap.
- The `Q_zeta` core explicitly accepts finite interval certificates as real
  certificate backend progress.
- The Step 12--22 B-spline lane now supplies the concrete finite block and the
  interval contract shape.

External sanity search points to standard Galerkin/Cea-style convergence and
B-spline quasi-interpolation as the right approximation template, but the Q3
boundary-null correction and Weil-form topology must be stated inside this
project.

## Objects

For a finite level

```text
alpha = (L, k_spline, ell, delta, kappa, theta, T)
```

define the local B-spline packet space

```text
V_alpha = span{ psi_j },
psi_j(u) = ell^(-1/2) eta_k((u-u_j)/ell),
u_j in [-L+ell, L-ell].
```

The boundary constraints are

```text
Q_alpha v = 0,
Q_alpha =
  [ exp(u_j/2)  ]
  [ exp(-u_j/2) ].
```

On this space the finite matrices are

```text
G_alpha, A_alpha, P_alpha, P0_alpha, Q_alpha.
```

The kappa split is

```text
C_alpha      = A_alpha - P_alpha,
R_alpha      = A_alpha - kappa P0_alpha,
D_alpha      = C_alpha - theta R_alpha,
             = (1-theta)A_alpha - P_alpha + theta kappa P0_alpha.
```

## Finite Certificate Predicate

Define `FiniteCert(alpha)` to mean:

1. midpoint/radius interval contracts enclose all entries of
   `A_alpha`, `P_alpha`, `P0_alpha`, and `Q_alpha`;
2. there exist penalties `tau_D, tau_R > 0` such that the Weyl guards prove

```text
D_alpha + tau_D Q_alpha^T Q_alpha > 0,
R_alpha + tau_R Q_alpha^T Q_alpha > 0
```

on the full coordinate space;

3. the interval algebra uses the exact identities

```text
C_alpha = A_alpha - P_alpha,
R_alpha = A_alpha - kappa P0_alpha,
D_alpha = C_alpha - theta R_alpha.
```

The Step 22 primary block proves `FiniteCert(alpha_0)` for

```text
alpha_0 = (3.0, 11, 0.30, 0.25, 3.25, 1e-4, 260).
```

## Theorem 23A -- Penalty Certificate on `ker Q`

### Statement

If `FiniteCert(alpha)` holds, then for every coefficient vector `v` with

```text
Q_alpha v = 0
```

we have

```text
v^T D_alpha v >= 0,
v^T R_alpha v > 0       for v != 0 modulo the finite Gram degeneracy.
```

Consequently

```text
v^T C_alpha v >= theta v^T R_alpha v >= 0.
```

### Proof Shape

For `Q_alpha v = 0`,

```text
v^T (D_alpha + tau_D Q_alpha^T Q_alpha) v = v^T D_alpha v.
```

The full-space SPD certificate gives the right side positive.  The same
argument applies to `R_alpha`.

This is the first Lean target because it is finite-dimensional and generic.
It should not mention zeta, primes, B-splines, or Arch integrals.

## Theorem 23B -- Certified Finite Weil Positivity

### Statement

Let

```text
h_v = sum_j v_j psi_j.
```

If `FiniteCert(alpha)` and `Q_alpha v = 0`, then

```text
W(h_v) = v^T C_alpha v >= 0.
```

More strongly,

```text
W(h_v) >= theta R_alpha(h_v).
```

### Required Bridges

This theorem needs the exact matrix identification:

```text
A_alpha(h_v) = v^T A_alpha v,
P_alpha(h_v) = v^T P_alpha v,
P0_alpha(h_v) = v^T P0_alpha v,
Q_alpha v = (H_v(1/2), H_v(-1/2)) up to nonzero common constants.
```

These are already implemented numerically in Steps 12--22.  The formal bridge
should be split into small lemmas:

- B-spline transform formula;
- B-spline autocorrelation formula;
- finite prime cutoff from compact support;
- Arch matrix identity;
- continuous-main `P0` identity;
- boundary row identity.

## Theorem 23C -- Boundary-Null B-spline Exhaustion

This is the object that should be promoted to the user-facing Theorem 23B in
the final theorem packet.

### Target Class

Let `T_L^0` be the smooth compactly supported test class in `[-L,L]` satisfying

```text
H(1/2) = H(-1/2) = 0.
```

Let `||.||_E` be a form topology strong enough that

```text
h_n -> h in ||.||_E
```

implies

```text
A(h_n) -> A(h),
P(h_n) -> P(h),
P0(h_n) -> P0(h),
W(h_n) -> W(h).
```

### Statement

For every `h in T_L^0`, there exists a sequence of finite levels
`alpha_n` and vectors `v_n in ker Q_alpha_n` such that

```text
h_{v_n} -> h in ||.||_E.
```

### Proof Shape

1. Use compact B-spline quasi-interpolation on a mesh `delta_n -> 0` and
   scale `ell_n -> 0` with enough overlap to approximate `h` in the chosen
   energy topology.
2. The raw approximants `s_n` need not satisfy boundary-null exactly, but their
   boundary residuals tend to zero:

```text
H_{s_n}(1/2) -> H_h(1/2) = 0,
H_{s_n}(-1/2) -> H_h(-1/2) = 0.
```

3. Choose two fixed local correction packets `b_+`, `b_-` in the same large
   enough finite dictionary such that the 2-by-2 boundary matrix

```text
[
  H_{b_+}(1/2)   H_{b_-}(1/2)
  H_{b_+}(-1/2)  H_{b_-}(-1/2)
]
```

is invertible.

4. Solve a 2-by-2 correction problem and set

```text
h_n = s_n - correction_n.
```

Because the residual tends to zero and the inverse correction matrix is fixed
at each large level, `correction_n -> 0` in the energy topology.  Hence
`h_n -> h` and `Q_alpha_n v_n = 0`.

### Lemma 23D -- Boundary-null correction

The correction substep above is its own lemma candidate:

```text
raw approximants converging to boundary-null h
  -> corrected approximants in ker(Q) with the same limit.
```

It is the main place where the two boundary functionals
`H(1/2), H(-1/2)` must be handled explicitly.

## Theorem 23D -- Family Exhaustion Implies `PSD-pd`

In the final user-facing theorem packet, this should be split into:

- Theorem 23B: boundary-null exhaustion;
- Theorem 23C: RH closure after invoking the existing Q3 Weil-linkage route.

### Statement

Assume:

1. for every compact window `L` and every target accuracy there exists a finite
   level `alpha` with `FiniteCert(alpha)`;
2. the certified spaces form a directed boundary-null exhaustion as in
   Theorem 23C;
3. the Weil form is continuous in the chosen energy topology.

Then

```text
W(h) >= 0
```

for every boundary-null test `h` in the corrected positive-definite packet
class.  This is the fallback `PSD-pd` theorem shape.

### Proof Shape

Given `h`, choose `h_n` from certified finite spaces with `h_n -> h`.
For every `n`,

```text
W(h_n) >= 0.
```

By continuity,

```text
W(h) = lim_n W(h_n) >= 0.
```

## What Step 23 Does Not Claim

Step 23 does not claim RH.

The Step 22 block is one finite certified level.  RH needs the whole chain:

```text
finite certificate family
-> PSD-pd on the corrected packet class
-> A2/LF closure
-> G6 Weil linkage
-> RH.
```

The first hard missing theorem after Step 22 is not another matrix check.  It
is the family/exhaustion theorem above.

## Immediate Lean Targets

### Lean Target 1 -- finite penalty theorem

Generic finite-dimensional theorem:

```text
if M + tau Q^T Q is SPD, then M is PSD on ker Q.
```

This should land first.  It is independent of the analytic kernel.

### Lean Target 2 -- interval Weyl guard

Generic theorem:

```text
lambda_min(M_mid) - ||Rad||_2 > 0
  -> every matrix in the midpoint/radius box is SPD.
```

This is optional if we keep the interval guard outside Lean, but it is the
clean way to make the finite certificate checker auditable.

### Lean Target 3 -- boundary-null correction lemma

Analytic approximation theorem:

```text
B-spline approximants can be corrected into ker Q without losing convergence.
```

This is the real exhaustion hinge.

### Lean Target 4 -- Arch tail envelope

Reusable analytic lemma:

```text
|Omega(t)| <= C log(2+t), t >= T0.
```

Step 22 used `C=10`, `T0=260`, which is intentionally conservative.

## Fastest Next Move

Do not run more sweeps.

Step 24 is now closed as:

```text
Q3/Proofs/PSD_PenaltyCertificate.lean
```

This converted the strongest finite numerical insight into a small reusable
Lean theorem block and gave the certificate pipeline a clean formal receiver.

The fastest next move is now the certificate-family manifest:

```text
family_id, L, k_spline, ell, delta, kappa, theta, tau,
midpoint_csv, radius_csv, Dtheta_safe_lower, Rkappa_safe_lower, status.
```

In parallel, keep boundary-null exhaustion and the Arch tail envelope as the
main analytic blockers for the full RH route.
