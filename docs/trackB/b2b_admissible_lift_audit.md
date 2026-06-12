# Track B B2b: Admissible-Lift Audit

Status: `B2-GAP(admissible lift)`.  This is strategy documentation and a
Proshka-ready blocker.  It is not a proof of E5', not a proof of RH, and not a
Lean proof file.

## Target

B2b tries to use the explicit formula in the only way that can avoid the B2a
cone trap:

```text
edge prime term
  <= lifted prime term
  <= lifted archimedean term        by Q(lift) >= 0 on the pd cone
  =  P0_edge + controlled error.
```

Thus the missing theorem is not another Selberg interval formula.  It is an
admissible lift of the signed edge operator into the corrected
positive-definite Weil cone.

## D2 Normalization

Raw Step13 variable:

```text
a = r * log p,
I_K = [2K, 4K],
weight_raw = log(p) / p^(r/2).
```

Q3 variable:

```text
xi_n = log n / (2*pi),
w_Q(n) = 2 * Lambda(n) / sqrt(n),
Q(Phi) = arch_term(Phi) - prime_term(Phi).
```

So raw `a in [2K,4K]` is Q3 `xi in [K/pi,2K/pi]`.  The factor `2` in `w_Q`
is the evenization factor and must not be inserted a second time.

Local source:

- `UNCONDITIONAL / local definition`: `q3.lean.aristotle/Q3/Basic/Defs.lean`
  defines `xi_n`, `w_Q`, `prime_term`, `arch_term`, and `Q`.

## Allowed Source Status

- `UNCONDITIONAL`: Selberg/Vaaler interval majorant-minorant and exact
  `1/delta` error; see `docs/trackB/clv_pair.md`.
- `UNCONDITIONAL`: CLV Gaussian subordination as an extremal-function
  construction; source: Carneiro--Littmann--Vaaler, TAMS 2013,
  <https://arxiv.org/abs/1008.4969>.
- `UNCONDITIONAL as identity / forbidden as theorem input`: the explicit formula
  architecture used in Carneiro--Milinovich--Soundararajan 2019 is a useful
  shape reference, but their prime-gap conclusions use RH.  Source:
  <https://arxiv.org/abs/1708.04122>.
- `UNCONDITIONAL / local contract`: current Q3 target is the corrected
  positive-definite / convolution-square cone, not the old broad nonnegative
  cone.  Local references:
  `q3.lean.aristotle/docs/reviewed_notes/2026_03_07_target_cone_reset_review.md`
  and
  `q3.lean.aristotle/docs/reviewed_notes/2026_03_07_pd_mainline_blocks_review.md`.

Forbidden inputs remain:

```text
RH / GRH / pair-correlation / zero-density assumptions
FQ-transfer
de Branges positivity as RH certificate
CMS prime-gap theorem as a theorem input
```

## Packet Edge Functional

For a Step13 packet vector `v in ker(Q_boundary)`, write the raw edge form as

```text
F_v(a) =
  sum_ij v_i v_j *
    ( r_k((u_i-u_j-a)/ell) + r_k((u_i-u_j+a)/ell) ).
```

The measured edge fluctuation is

```text
E_I(v)
  =
  sum_{p,r: r log p in I_K} log(p)/p^(r/2) * F_v(r log p)
  -
  integral_{I_K} e^(a/2) * F_v(a) da.
```

The `K=2` D2 sanity target from the current Step13 proxy is

```text
||Pnu_edge^circ||_G = 0.4416718760986585.
```

Any proposed B2b lift must majorize this same normalized object, or explicitly
state and justify a different normalization.

## Required Admissible-Lift Lemma

A useful one-sided B2b lemma would have the following structure.

For every admissible packet vector `v`, construct a test `Phi_v^+` in the
corrected positive-definite Weil cone and an explicit residual `R_v^+` such
that:

```text
(1) Prime operator dominance:
    P_edge(v) <= prime_term(Phi_v^+) + R_v^+.

(2) PSD eligibility:
    Phi_v^+ is a convolution-square / positive-definite Weil test,
    so the available Q3 PSD statement applies:
      Q(Phi_v^+) >= 0.

(3) Arch budget:
    arch_term(Phi_v^+) - P0_edge(v) + R_v^+
      <= epsilon_K^CLV * <v,Gv>.
```

Then

```text
P_edge(v)
  <= prime_term(Phi_v^+) + R_v^+
  <= arch_term(Phi_v^+) + R_v^+
  <= P0_edge(v) + epsilon_K^CLV * <v,Gv>,
```

which gives the upper edge-defect bound.  The lower bound needs the analogous
minor lift for `-P_edge`, or a symmetric two-sided construction.

This is the exact place where B2b can replace the RH step in
Carneiro--Milinovich--Soundararajan: Q3 must supply `Q(Phi)>=0` because
`Phi` is in the positive-definite cone.  It cannot use CMS's RH-conditional
zero-side estimate.

## Why Current CLV Objects Do Not Yet Prove It

The scalar Selberg theorem gives

```text
chi_I(a) <= M^+_{I,delta}(a)
```

pointwise.  This is not enough for `(1)`, because `F_v(a)` is a signed
cross-correlation operator.  Multiplying a pointwise majorant by a signed
operator kernel does not preserve Loewner order on the projected packet space.

This is not just philosophical.  The current finite probes show:

```text
ordinary Selberg majorant error:
  Fourier-positive only in the ultra-low band |u| < 1/(12K);

naive Gaussian PSD majorant:
  W_K >= chi_edge and hat(W_K) >= 0,
  but N^T(P_W-P_edge)N has negative generalized eigenvalues.
```

So the missing object must be stronger than both:

```text
pointwise edge majorant
positive Fourier transform of the majorant
```

It must produce a projected operator majorant, or an explicit formula lift that
is visibly a convolution square before the prime-shift oscillation is
introduced.

## Concrete Next Experiment

Finite `K=2` operator-majorant feasibility test:

1. Choose a small candidate family of lift kernels `L_m(a)` that are
   `UNCONDITIONAL` and positive-definite/convolution-square eligible after the
   Q3 D2 rescaling.  Start with Fejer-square or Gaussian-square packets, not
   arbitrary Selberg signs.
2. Build the projected matrices

   ```text
   N^T(P_{L_m} - P_edge)N
   ```

   in the same normalization as `scripts/trackb_edge_operator_probe.py`.
3. Search for nonnegative coefficients `c_m >= 0` and the smallest `eta` such
   that

   ```text
   N^T( sum_m c_m P_{L_m} - P_edge )N + eta * N^T G N  >= 0.
   ```

4. If `eta <= 0` and the associated arch budget is small, extract the kernel
   profile as a possible formula-level lift.
5. If every natural positive-definite family needs large positive `eta`, B2b
   should move to a direct `FINITE-OP` certificate or a new square-function
   route.

This experiment is not a proof, but it is the right minimal example for
Proshka because it tests exactly the missing lemma, not a pointwise surrogate.

Follow-up probe:

- `docs/trackB/b2b_liftsearch_probe.md` implements this experiment for `K=2`
  with two-point Gaussian autocorrelation lifts.  The dense dictionary can drive
  the prime-side slack down to `eta≈0.0077`, but the continuum proxy cost rises
  to about `5.27` in projected `G`-opnorm.  Thus the current wall is a
  cost-controlled admissible lift, not mere finite operator dominance.
- The same probe now includes joint cost optimization.  Forcing the one-sided
  continuum cost down to `gamma≈0.4417` raises prime-side slack to `eta≈1.71`.
  This is a family-level failure for simple scalar two-point Gaussian
  autocorrelation lifts, not a route-level failure for B2b.
- `docs/trackB/b2b_finiteop_tail_probe.md` implements the fallback
  `FINITE-OP + CLV-tail` diagnostic.  The fixed K projected eigenvalue
  certificate exists, but at K=2 and K=3 the worst vectors are distributed over
  the ordinary-prime comb: `r=1` carries about `97%` at K=2 and `99%` at K=3,
  while top-shift excision rapidly stops explaining the mass.  Thus the next
  theorem shape must control a structured ordinary-prime mean, not only a short
  list of exceptional shifts.
- `docs/trackB/b2b_packet_scale_sweep.md` tests whether the finite-op wall is
  only the fixed `ell=0.35` packet scale.  Packet scale matters: moderate
  `ell=0.5..1.0` lowers the K=2/K=3 epsilon to about `0.10..0.11`.  But very
  small epsilons occur only with low `kerQ_dim` or nearly singular projected
  Gram metrics under grid refinement, so they are not yet a stable B3 route.
- `docs/trackB/b2b_stability_schedule.md` adds stability filters and checks the
  B3-facing schedule directly.  For `K=2,2.5,3,3.5`, the best eligible
  Step13 B-spline packet choices give a negative fitted decay exponent
  (`c≈-0.744` in `epsilon_K≈C*K^{-c}`), with stable bad points at K=2.5 and
  K=3.5.  This kills simple packet-width tuning inside the current family.

## Current Verdict

`B2-GAP(cost-controlled admissible lift, normalized packet theorem, or uniform finite-op prime-mean estimate)`.

What is known:

- B1 formulas are correct and unconditional.
- The explicit formula identity itself is allowed, but RH-conditional zero-side
  estimates are not allowed.
- Q3 can only replace RH if the constructed lift stays in the corrected
  positive-definite/convolution-square cone.
- Existing Selberg and Gaussian probes do not satisfy the required operator
  dominance.

What remains:

```text
Find Phi_v^+ / Phi_v^- in the pd cone with operator dominance and arch budget,
but not from the simple scalar two-point Gaussian autocorrelation dictionary;
or upgrade the direct finite projected operator inequality into a uniform
structured ordinary-prime mean estimate with CLV used only for tail/continuum
transfer; the packet-scale sweep suggests this must be done with a stable
normalization/family, not by relying on low-dimensional wide-packet collapse.
```

## Proshka Request

Claim:
B2b reduces to a cost-controlled admissible-lift lemma: construct a
positive-definite Weil test `Phi_v^+` whose prime term operator-majorizes the
signed edge prime form, and whose arch term is within `epsilon_K` of the edge
continuum model.

Point of blockage:
Scalar CLV/Selberg majorization does not imply the projected operator
dominance because the packet edge kernel `F_v(a)` is signed/oscillatory.
Naive Gaussian positivity also fails in the finite packet test.  A richer
two-point Gaussian autocorrelation dictionary nearly solves finite dominance
at `K=2`, but only with large continuum proxy cost; joint optimization confirms
the cost/eta tradeoff is too expensive for this family.

What was tried:
- Extracted unconditional Selberg/Vaaler formulas and constants.
- Verified K=2 raw-log sanity against the measured edge proxy.
- Killed ordinary Selberg as unrestricted PSD multiplier.
- Killed the naive Gaussian positive-definite majorant via projected negative
  generalized eigenvalues.
- Checked local Q3 definitions: B2b may use `Q=arch-prime` only for tests in
  the corrected positive-definite cone.
- Ran the finite `liftsearch` probe: dense two-point Gaussian dictionary gets
  `eta≈0.0077`, but `opnorm_G(P0_lift-P0_edge)≈5.27`.
- Added joint cost constraints: forcing `gamma≈0.4417` gives `eta≈1.71`.

Minimal example:
`K=2`, raw edge `[4,8]`, Step13 packet parameters `ell=0.35`,
grid `delta=0.5`, `k_spline=5`.  The finite target is the Loewner inequality

```text
N^T(P_lift - P_edge)N + eta * N^T G N >= 0
```

with `eta` as small as possible, plus an arch-budget check against
`P0_edge`.  Current edge proxy norm is `0.4416718760986585`; the best dense
probe so far has small `eta` but continuum cost an order of magnitude larger,
while the cost-controlled probe has order-`1` prime slack.
