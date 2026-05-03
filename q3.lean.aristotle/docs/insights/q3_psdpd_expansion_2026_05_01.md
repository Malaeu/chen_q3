# Q3 PSD-pd Expansion Packet (2026-05-01)

Status: in progress

Route placement:

- This is not a new RH architecture.
- It is a sharpening of the existing fallback corrected-cone route
  `T0-pd -> A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 -> LF-pd -> G6`.
- It does not replace the active `H-bridge / PO3-square.2d3` phase unless the
  control plane explicitly pivots to fallback.

## Local recall

Semantic search hit the relevant existing packets:

- `target_cone_audit_2026_03_07.md`: the broad even/nonnegative cone is too
  wide; the public Weil target must be positive-definite / convolution-square.
- `pd_mainline_blocks_2026_03_07.md`: the corrected cone and packet
  autocorrelation objects are already frozen.
- `a3_pd_packet_package_2026_03_07.md`: `A1-pd` and exact packet-Rayleigh
  survive on autocorrelation packets.
- `psd_packet_kernel_frontier_2026_03_07.md`: the uniform floor theorem shape
  `A3-pd` is too strong; the honest hard theorem is `PSD-pd`.
- `Rayleigh_Q_identification_debug.lean`: the prime Rayleigh block carries a
  real normalization risk; only the prime part gets the `(2M+1)` correction
  coming from the `1/sqrt(2M+1)` prime-vector normalization.

External sanity:

- Bombieri's Weil-quadratic-functional framing confirms that the relevant
  public contract is a quadratic/positive-definite one, not positivity on every
  pointwise nonnegative bump.
- Baez-Duarte/Nyman-Beurling remains a useful deconvolution comparison, but the
  direct Q3 -> NB-Schur transfer is not available without a target column and a
  decaying Schur residual.

## Verdict

The broad cone

```math
C^+_{\mathrm{even},c}
```

is false as a positivity target for the Q3 functional

```math
Q^\star(\Phi)
= \int a^\star(\xi)\Phi(\xi)\,d\xi
- \sum_{n\ge2}\frac{2\Lambda(n)}{\sqrt n}\Phi(\xi_n).
```

An arbitrary narrow even nonnegative bump can be placed at a prime node or in a
bad Archimedean gap, depending on the obstruction being tested. Therefore the
project must not transfer positivity from the Rayleigh square engine to the
whole broad cone.

The correct cone is

```math
W_K^{pd}
= \overline{\operatorname{cone}\{\psi * \widetilde \psi:
   \operatorname{supp}\psi\subset[-K/2,K/2]\}},
\qquad
\widetilde\psi(x)=\overline{\psi(-x)}.
```

Equivalently, on the Fourier side these are the positive-definite /
autocorrelation tests.

## Important correction

Autocorrelation does not allow a free isolated prime spike.

If `\psi` is one narrow packet near `u_0`, then
`\psi*\widetilde\psi` peaks at `0`, not at `u_0`. To put mass at a prime
separation, one needs a two-pulse packet such as

```math
\psi \approx \delta_0+\delta_{\log 2},
```

and then

```math
\psi*\widetilde\psi
```

has mass at `0` and at `\pm\log 2`. This central-mass tax is exactly the
positive-definite structure that the broad cone misses.

So the live theorem is not "Arch beats every nonnegative bump". The live theorem
is the operator inequality:

```math
P_{\mathrm{prime}}\preceq A_{\mathrm{arch}}
```

on a dense autocorrelation class, with the prime sampling operator controlled
as a Carleson/RKHS embedding.

## Theorem packet: `Q3_PSDpd_Expansion`

### Lemma 1: broad-cone failure

Construct explicit compact even nonnegative tests showing that broad positivity
on `C^+_{\mathrm{even},c}` is not the Q3 theorem shape.

This should reference the older `target_cone_audit` and not reopen the broad
route.

### Lemma 2: corrected Weil cone

Freeze the working cone as autocorrelation/positive-definite:

```math
W_K^{pd}
= \overline{\operatorname{cone}\{\psi*\widetilde\psi\}}.
```

All closure statements must remain inside this cone.

### Lemma 3: exact finite square representation

For each finite packet dictionary `\{\psi_i\}`, prove the sesquilinear identity

```math
Q^\star\!\left(\Psi_c*\widetilde{\Psi_c}\right)
= c^*(A-P)c,
\qquad
\Psi_c=\sum_i c_i\psi_i.
```

This is the corrected `packet-Rayleigh-pd` object.

Scaling audit:

- if the prime block is built from normalized vectors, the prime contribution
  must carry the `(2M+1)` correction;
- do not use a theorem of the form `T_A - T_P^{Ray}` unless `T_P^{Ray}` has
  already been redefined as the unnormalized Weil prime block.

### Lemma 4: prime Carleson cap

For a chosen square/RKHS class `\mathcal C_j`, prove

```math
\sum_n \frac{2\Lambda(n)}{\sqrt n}\,
    |\mathcal E_{\xi_n}F|^2
\le
\rho_j\,\|F\|_{A_j}^2,
\qquad
\rho_j<1.
```

Equivalently,

```math
P_j\preceq \rho_j A_j.
```

Then

```math
A_j-P_j\succeq0.
```

This is the finite Gram/RKHS form of `PSD-pd`.

### Lemma 5: class expansion without losing the cap

Build an increasing ladder

```math
\mathcal C_0\subset\mathcal C_1\subset\mathcal C_2\subset\cdots
\subset W_K^{pd}.
```

Suggested ladder:

1. centered Fejer x heat autocorrelations;
2. shifted Fejer x heat autocorrelations;
3. finite sums with Gram-corrected generalized eigenvalue check;
4. mixed-scale packets;
5. closure to `W_K^{pd}`.

At each stage prove the same operator inequality

```math
P_j\preceq \rho_j A_j,\qquad \rho_j<1,
```

or record the exact obstruction if the prime cap fails.

## Success criterion

For every compact `K`, produce a dense square class inside `W_K^{pd}` on which

```math
Q^\star(\psi*\widetilde\psi)\ge0
```

holds and pass to the local closure by the existing corrected-cone continuity.
Then `LF-pd` and `G6` give the RH transfer.

## Failure criterion

If sharp/mixed-scale autocorrelations force

```math
\sup_j \rho_j\ge1
```

or if the Rayleigh scaling does not match the Weil prime block after the
`(2M+1)` audit, then current Q3 centered/RKHS constants do not close `PSD-pd`
and the fallback route remains finite-companion only.

## Current recommendation

Do not claim RH from this packet now.

The next honest micro-frontier is:

```math
\boxed{
\text{maximal autocorrelation/RKHS class on which prime sampling is
Carleson-small with the correct Rayleigh scaling.}
}
```

This is the right PSD-pd version of the "second Bochner" idea: not every
positive bump is a sound, but every allowed sound is a square, and the primes
must be small as a sampling operator on that square space.

## Lean landing surface (2026-05-01)

New lightweight module:

```text
Q3/Proofs/PSD_FormAlgebra.lean
```

It deliberately avoids importing the heavy Q3 analytic stack.  It freezes the
finite-form algebra:

```math
\text{arch floor} + \text{prime cap} + \text{cap}\le\text{floor}
\Longrightarrow
\text{difference form is PSD}.
```

Main exported names:

- `Q3.Proofs.FormPSD`
- `Q3.Proofs.formDiff`
- `Q3.Proofs.formDiff_nonneg_of_floor_cap`
- `Q3.Proofs.formPSD_diff_of_uniform_floor_cap`
- `Q3.Proofs.formPSD_diff_of_strict_uniform_floor_cap`
- `Q3.Proofs.formDiff_margin_of_uniform_floor_cap`

## Class 1 audit: shifted cap frontier (2026-05-01)

Detailed note:

```text
docs/insights/q3_psdpd_class1_shifted_cap_audit_2026_05_01.md
```

Current repository status:

- shifted scalar/basis0 facts exist:
  `prime_rayleigh_shift_le_rho_oneK`, `prime_term_phi_shift_le_rho_oneK`;
- shifted Q-identification exists:
  `T_P_comp_real_shift`, `prime_rayleigh_eq_shift`, `rayleigh_Q_eq_Q_shift`;
- unshifted full-vector op-norm route exists:
  `T_P_comp_real_opNorm_le_weight_sum`,
  `rkhs_cap_rayleigh_of_weight_sum`;
- shifted full-vector op-norm route is not yet present.

Therefore the first real Class 1 target is not mixed-scale density.  It is the
shifted operator cap:

```text
T_P_comp_real_shift_opNorm_le_weight_sum
shifted_rkhs_cap_rayleigh_of_weight_sum
```

Only after that cap exists should we instantiate `PSD_FormAlgebra` on shifted
packet blocks.  The scale bound also has to be checked honestly, because the
current shifted scalar cap lands at

```math
\rho_{\mathrm{oneK}}(K)
=
\exp(8\pi^2 t_{\mathrm{rkhs\_cap}}K^2)\rho_{\mathrm{one}},
```

which is K-dependent and not automatically below the Archimedean floor.

Verification:

```text
cd q3.lean.aristotle && lake env lean Q3/Proofs/PSD_FormAlgebra.lean
```

This is only the algebraic interface.  The next bridge must instantiate the
abstract forms with the concrete packet-Rayleigh / Carleson forms and keep the
`(2M+1)` prime normalization explicit.

## Step 8 certificate design (2026-05-03)

Detailed note:

```text
docs/insights/q3_psdpd_step8_certificate_design_2026_05_03.md
```

The next certificate-friendly formulation is not full-space positivity and not
raw Gershgorin promotion.  It is the boundary-null compact-support Gram target:

```math
Qv=(H_v(1/2),H_v(-1/2))=0,
\qquad
\widetilde K=N^\ast(A-P)N\succeq0.
```

Here `A` is the Arch Toeplitz-like matrix and `P` is the sparse shifted
prime-band matrix.  The boundary matrix has rank at most two, but it is not
automatically positive, so the clean route is to remove it by the two boundary
constraints and prove positivity on `ker Q`.

The immediate Lean-facing theorem order is:

- prove the boundary-null form rewrite;
- prove PSD transfer from the reduced matrix on `ker Q`;
- package the finite Step 8 certificate before instantiating bump/Toeplitz
  matrices.

## Prime-Graph SOS follow-up (2026-05-03)

Detailed note:

```text
docs/insights/q3_psdpd_prime_graph_sos_step9_audit_2026_05_03.md
```

The prime-shift term has a better certificate form:

```math
\mathcal P(h)
=2W_L\|h\|^2-\sum_aw_a\|h-S_a h\|^2.
```

So on the boundary-null subspace:

```math
\mathcal W(h)
=
\mathcal A(h)+\sum_aw_a\|h-S_a h\|^2-2W_L\|h\|^2.
```

This yields the concrete Step 9 target:

```math
\lambda_{\min}(A+\mathcal L_P,G;\ker Q)\ge2W_L.
```

`PSD_FormAlgebra.lean` now contains the verified abstract algebra for this
rewrite.  The old A3 bridge cannot yet be used as a finished RH proof because
it has not been proved for the boundary-null compact-support Hermitian-square
localizer class with corrected `W^{pd}` closure and explicit prime scaling.

## Prime fluctuation split (2026-05-03)

Detailed note:

```text
docs/insights/q3_psdpd_prime_fluctuation_split_2026_05_03.md
```

Instead of proving `A >= P`, split the prime measure as

```math
d\mu=d\mu_0+d\nu,
\qquad
d\mu_0(a)=e^{a/2}\,da.
```

The continuous main kernel gives

```math
P_0(h)=\iint h(u)\overline{h(v)}e^{|u-v|/2}\,du\,dv.
```

On boundary-null tests this satisfies

```math
P_0(h)=-\|\Phi'\|_2^2-\frac14\|\Phi\|_2^2\le0.
```

So the current sharp target is:

```math
N^\ast(A-P_\nu)N\succeq0,
\qquad
P_\nu=P-P_0.
```

The abstract Lean algebra for this split is now in
`Q3/Proofs/PSD_FormAlgebra.lean`.
