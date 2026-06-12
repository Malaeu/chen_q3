# Track B B2b: Route-Equivalence Audit for Smoothed Receiver

Status: RP1 audit.  This is not a proof of E5', not a proof of RH, and not a
Lean proof file.

After `docs/trackB/b2b_affine_receiver_no_free_lunch.md`, one surviving option
was:

```text
RP1: prove that the E5' ledger can use the smoothed receiver residual D_R
     instead of the hard edge residual D_I.
```

This note checks whether that is already justified by local Q3/Track B
documents.  It is not.

## D2 Normalization

Raw variable:

```text
a = r * log p,
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

All statements below are in raw `a` coordinates unless explicitly marked as
Q3 `xi` statements.  No evenization factor is inserted into Step13 raw probes.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV receiver formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: explicit-formula linearity as an identity for the chosen
  test function.  This does not import RH positivity.
- `UNCONDITIONAL / local definitions`: Q3 uses
  `Q(Phi)=arch_term(Phi)-prime_term(Phi)` with
  `prime_term(Phi)=sum_n w_Q(n)*Phi(xi_n)`.
  Local source: `q3.lean.aristotle/Q3/Basic/Defs.lean`.
- `UNCONDITIONAL / finite-dimensional linear algebra`: projected operator
  identities on the current packet `kerQ`.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

Shape reference only:

- Carneiro--Milinovich--Soundararajan use Fourier optimization plus the
  explicit formula for prime gaps, but their prime-gap conclusion assumes RH.
  Source: https://arxiv.org/abs/1708.04122

## Local Search Synthesis

Local `rg` and `q3_docs` searches for:

```text
E5 edge defect mu ledger hard edge receiver ledger D_R D_I
prime edge defect E5 epsilon_K C K^{-c} ledger
smoothed receiver hard edge replacement ledger exact route equivalence
```

returned the same pattern:

- `docs/trackB/k2_sanity_gap.md` says the missing object is an inequality
  for the measured Q3 cross-correlation edge defect.
- `docs/trackB/b2b_explicit_formula_route_gap.md` defines the target
  fluctuation over the hard interval `I`:

  ```text
  E_I(v)
    = sum_{p,r: r log p in I} log(p)/p^(r/2) * F_v(r log p)
      - integral_I e^(a/2) * F_v(a) da.
  ```

- `docs/trackB/b2_cone_transport_probe.md` states the hard-edge matrix target:

  ```text
  N^T (P_edge - P0_edge) N <= epsilon_K^CLV * N^T G N.
  ```

- `docs/trackB/b2b_admissible_lift_audit.md` uses `P_edge` and `P0_edge` in
  the admissible-lift theorem shape.
- No local theorem states that the downstream E5' ledger accepts
  `P(M^+) - P0(M^+)` in place of `P_edge - P0_edge`.

The q3_docs hits also point to the corrected positive-definite cone and to
older warnings that standalone prime-block PSD is false on packet space.  They
do not supply route-equivalence for the smoothed receiver.

## What RP1 Would Need

Write:

```text
D_I := P(1_I) - P0(1_I),
D_R := P(R)   - P0(R),
```

where `R` is a CLV/Selberg receiver such as `M^+_{I,delta}`.

RP1 would need a theorem of one of the following forms.

### RP1a: Ledger Equivalence

```text
If ||D_R||_G <= epsilon_K, then the original E5' hard-edge ledger is closed.
```

This is false without extra hypotheses, because `D_R` and `D_I` are different
linear functionals.

### RP1b: Downstream Smoothed Ledger

```text
The downstream theorem never needed D_I; it only needed D_R for an allowed
receiver R.
```

This would be a real route rewrite.  It must update the statement of E5' and
prove that every downstream use accepts the smoothed receiver normalization.
No local document provides this.

### RP1c: Exact Correction Cancellation

```text
D_I = D_R - B_R, and B_R cancels against another named ledger term.
```

This is not currently available.  The measured `B_R` tracks the hard-edge
defect, and the affine receiver scan shows that paying it separately returns
the direct hard-edge cost.

## Why Plain RP1 Fails

The explicit formula is linear in the chosen test function.  Applying it to
`R` gives a statement about the `R`-weighted prime/arch functional, not about
the hard indicator `1_I`.

The exact finite identity is:

```text
D_I = D_R - B_R,
B_R = (P(R)-P(1_I)) - (P0(R)-P0(1_I)).
```

Therefore a proof of

```text
||D_R||_G <= epsilon_K
```

does not imply

```text
||D_I||_G <= epsilon_K
```

unless it also controls or cancels `B_R`, or proves that the original downstream
ledger only required `D_R`.

Numerically, for the ordinary Selberg receiver at `K=3.5`, `ell=1.375`,
`delta=1`:

```text
||D_R||_G ~= 0.001014
||D_I||_G ~= 0.238486
||B_R||_G ~= 0.238634
```

So the smoothed receiver residual is attractive, but it is not the original
edge defect.

## Verdict

`FATAL(plain RP1 replacement of E5' by D_R)`.

This is not fatal for Track B.  It kills only the route:

```text
prove the smoothed receiver residual and call that E5'.
```

The remaining viable options are:

1. **RP1b route rewrite**: explicitly change the downstream ledger to a
   smoothed receiver theorem and prove every downstream use accepts it.  This
   is a new theorem package, not currently available.
2. **RP4 nonlinear/cone-adapted receiver**: construct a receiver whose
   correction cancels structurally, not by a separate norm bound.
3. **Direct finite-op / ordinary-prime mean control**: control `D_I` itself on
   the structured cross-correlation cone.

The next mathematical move should be RP4 or direct ordinary-prime mean control,
unless Proshka supplies a concrete RP1b route rewrite with exact downstream
interfaces.

Follow-up:

- `docs/trackB/b2b_correction_anatomy.md` starts the RP4 diagnostic.  The
  correction `B_R` is not an arbitrary bulk error: its prime side is strongly
  endpoint-halo and ordinary-prime dominated, while its continuum side often
  carries the larger interior-bulk budget.  This points to a matched
  endpoint-continuum correction theorem, not a plain endpoint-only norm bound.

## Proshka Audit Block

Claim:
The small smoothed receiver residual `D_R = P(M^+) - P0(M^+)` does not close
the original E5' hard-edge ledger, whose local target is
`D_I = P(1_I) - P0(1_I)`.

Point of blockage:
Local Track B documents define E5'/B3 targets using the hard edge:
`E_I(v)`, `P_edge`, `P0_edge`, and
`N^T(P_edge-P0_edge)N <= epsilon_K*N^T G N`.  No local theorem says the
downstream ledger accepts `D_R` instead.

What was tried:
- Searched local docs and `q3_docs` for E5 ledger / receiver replacement /
  route-equivalence statements.
- Checked the exact identity `D_I = D_R - B_R`.
- Used the previous correction and affine scans showing `B_R` tracks the hard
  edge.
- Refreshed primary-source status: CLV/Selberg is unconditional, but
  Fourier-optimization prime-gap conclusions are RH-conditional and cannot be
  used as theorem inputs.

Minimal example:
At K=3.5, `ell=1.375`, `delta=1`:

```text
||D_R||_G ~= 0.001014
||D_I||_G ~= 0.238486
||B_R||_G ~= 0.238634
```

Question for Proshka:
Is there a legitimate downstream rewrite in which E5' only needs the smoothed
receiver ledger `D_R`?  If yes, what exact theorem statements and interfaces
replace `P_edge-P0_edge`?  If not, Track B should stop pursuing RP1 and move
to a nonlinear cone-adapted receiver or direct ordinary-prime mean control.
