# Q3 PSD-pd Prime-Graph SOS and Step 9 Audit (2026-05-03)

Status: in progress

Placement:

- This extends the fallback `PSD-pd` corrected-cone route.
- It does **not** claim RH.
- It records the valid Step 8 SOS reduction and isolates the missing Step 9
  A3/Weil bridge.

## Valid Step 8 improvement

For prime shifts `S_a` with weights `w_a`, set

```math
W_L=\sum_{a\le 2L} w_a,
\qquad
D_a=I-S_a.
```

Using unitarity of shifts,

```math
\|h-S_a h\|^2
=2\|h\|^2-2\operatorname{Re}\langle h,S_a h\rangle.
```

Thus the prime form rewrites as

```math
\mathcal P(h)
=2W_L\|h\|^2-\sum_{a\le 2L}w_a\|h-S_a h\|^2.
```

On the boundary-null subspace, where `B(h)=0`,

```math
\mathcal W(h)
=\mathcal A(h)-\mathcal P(h)
=
\mathcal A(h)
+\sum_{a\le2L}w_a\|h-S_a h\|^2
-2W_L\|h\|^2.
```

So Step 8 becomes a precise spectral-gap target:

```math
\mathcal A(h)
+\sum_{a\le2L}w_a\|h-S_a h\|^2
\ge
2W_L\|h\|^2
\quad
\text{on } H(1/2)=H(-1/2)=0.
```

Finite matrix form:

```math
L_a=2G-C(a)-C(-a),
```

```math
C=A+\sum_{a\le2L}w_aL_a-2W_LG,
```

and after boundary projection:

```math
\widetilde C=N^\ast C N\succeq0.
```

This is equivalent to the previous reduced target

```math
N^\ast(A-P)N\succeq0,
```

but it exposes the positive prime graph-Laplacian energy and the exact mass
penalty.

## Lean landing surface added

`Q3/Proofs/PSD_FormAlgebra.lean` now contains the abstract finite-form algebra
for this SOS step.

New names:

- `Q3.Proofs.FormNonnegOn`
- `Q3.Proofs.primeGraphCert`
- `Q3.Proofs.formDiff_eq_primeGraphCert_of_prime_sos`
- `Q3.Proofs.primeGraphCert_nonneg_of_spectral_gap`
- `Q3.Proofs.formNonnegOn_diff_of_primeGraph_cert`
- `Q3.Proofs.formNonnegOn_diff_of_primeGraph_gap`
- `Q3.Proofs.formPSD_diff_of_primeGraph_cert`

Verification:

```text
cd q3.lean.aristotle && lake env lean Q3/Proofs/PSD_FormAlgebra.lean
```

This is intentionally abstract.  It proves only the safe algebra:

```math
q_P(v)=2Wq_G(v)-q_{\mathrm{Lap}}(v),
\qquad
2Wq_G(v)\le q_A(v)+q_{\mathrm{Lap}}(v)
\Longrightarrow
0\le q_A(v)-q_P(v).
```

## Step 9 audit: why the final A3 jump is not closed

The proposed finish was:

```math
f_a=h_a*h_a^\sharp\in W^{pd},
\qquad
\text{apply existing A3/Toeplitz--RKHS theorem},
\qquad
\mathcal W(h_a)\ge0.
```

This is the right desired shape, but it is **not currently a closed theorem** in
the repository.

The missing bridge is:

```math
\boxed{
\text{A3 positivity applies to every boundary-null compact-support
Hermitian-square localizer used in Step 3.}
}
```

Current blockers:

1. The old A3/Rayleigh theorem is for the Fejer--heat/Rayleigh packet family,
   frequently with centered atoms or a specific finite periodic polynomial
   model.  It is not yet a theorem for arbitrary boundary-null compact-support
   Hermitian squares.
2. The broad cone closure is already rejected.  Positivity cannot be transferred
   through `C^+_{even}`; the target cone must remain `W^{pd}`.
3. The naive Rayleigh family is background-only in `PROJECT_ORCHESTRATOR.md`.
   The public route requires exact autocorrelation-packet compatibility.
4. The prime normalization must keep the `(2M+1)` Rayleigh factor explicit.
5. The shifted/full-vector prime cap remains a live gap: the known shifted cap
   is K-dependent through `rho_oneK(K)` and cannot be silently substituted for
   the unshifted `rho(1)<1/25` budget.
6. The Step 3/compact-support localizers are Paley--Wiener/physical-space
   localizers, not automatically the same dictionary as the A3 Fejer--heat
   generator family.

Therefore the final RH conclusion is conditional on a new theorem, not already
available from the current A3 bridge.

## Correct Step 9 target

There are two honest Step 9 targets.

### Step 9A: Prime-Graph spectral gap

Prove directly:

```math
\lambda_{\min}
\left(
A+\mathcal L_P,\ G;\ \ker Q
\right)
\ge 2W_L.
```

Equivalently:

```math
\mathcal A(h)+\sum_aw_a\|h-S_a h\|^2
\ge
2W_L\|h\|^2
```

on boundary-null compact-support tests.

### Step 9B: A3 compatibility bridge

Prove that every Step 3/Step 7 boundary-null localizer can be approximated in
the exact A3-positive packet family with continuity of the corrected Weil form:

```math
h_n*h_n^\sharp \to h*h^\sharp,
\qquad
Q^\star(h_n*h_n^\sharp)\ge0,
\qquad
Q^\star(h*h^\sharp)\ge0.
```

This requires a corrected-cone, same-normalization, same-prime-scaling bridge.

## Current recommendation

Do not claim global RH at this point.

The robust next move is:

```math
\boxed{
\text{formalize Step 9A/9B as an explicit missing theorem,
then attack one concrete bridge.}
}
```

The new Lean algebra means Step 9A now has a clean consumer:
it only needs the spectral-gap inequality on `ker Q`.

