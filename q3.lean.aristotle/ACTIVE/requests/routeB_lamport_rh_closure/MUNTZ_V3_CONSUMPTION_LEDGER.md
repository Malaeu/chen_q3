# Müntz v3 consumption ledger — Goal 039

Date: 2026-07-30
Project: `987ff124-3032-42e5-aa9f-24ceef69f62a`
Task: `472e126c-759f-4c69-8816-fa013ff740b2`
Lane: `CHALLENGER / NOT_RH`

## Exact consumed hypothesis

```lean
AnalyticOnNhd ℂ
  (fun s ↦ ∫ u in Set.Ioi (0 : ℝ), h u * (u : ℂ) ^ (s - 1))
  {s : ℂ | 0 < s.re}
```

from:

```lean
Measurable h
∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0
LipschitzOnWith K h (Set.Ico 0 b)
```

Goal 039 closes this hypothesis locally in
`muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean`.

## Patch v1.1 — R6 template port

The local proof is the direct T4a port of
`docs/routeB_bus/muntz_r6/RequestProject/ConcreteAnalyticity.lean`:

| Repair | Checked implementation |
|---|---|
| R-i (`hbot`) | `LipschitzOnWith` bounds `‖h u‖` on `Ico 0 b` by `‖h 0‖ + K * |b|`; this is `K * b` on the intended `0 < b` branch and gives exponent `0` via `IsBigO.of_bound`/`isBigO_iff` |
| R-ii (`hlocal`) | `Measurable h` plus the same a.e. constant bound gives `LocallyIntegrableOn h (Ioi 0)` by `locallyIntegrableOn_const.mono`; the endpoint `u = b` is discarded as a null singleton |
| R-iii (`htop`) | unchanged compact-support eventual-zero proof at `atTop` |
| W | Mathlib `mellin` crosswalk uses only `smul_eq_mul` and `mul_comm`; `DifferentiableOn.analyticOnNhd` uses openness of `{s | 0 < s.re}` |

The bridge is 71 lines including import/open/namespace lines, builds without
holes, and needs no Aristotle iteration.

## K7 theorem classification

`H_mellin` below means exactly
`AnalyticOnNhd ℂ (Mellin h) H`, with `H = {w : ℂ | 0 < w.re}`.

| v3 declaration | Classification before Goal 039 | Exact live hypotheses |
|---|---|---|
| `one_mem_H` | `THEOREM_UNCONDITIONAL` | none |
| `mellin_one_eq_zero` | `THEOREM_CONDITIONAL(on hmass)` | `∫ v in Ioi 0, h v = 0` |
| `mellinDivOne_value_one` | `THEOREM_UNCONDITIONAL` | none |
| `mellinDivOne_of_ne` | `THEOREM_CONDITIONAL(on w ≠ 1)` | `w ≠ 1` |
| `mellinDivOne_of_ne_of_zero` | `THEOREM_CONDITIONAL(on hmass,w ≠ 1)` | `Mellin h 1 = 0`, `w ≠ 1` |
| `mellinDivOne_analyticOn` | `THEOREM_CONDITIONAL(on H_mellin)` | `H_mellin` |
| `zetaResidueFactor_value_one` | `THEOREM_UNCONDITIONAL` | none |
| `zetaResidueFactor_of_ne` | `THEOREM_CONDITIONAL(on w ≠ 1)` | `w ≠ 1` |
| `zetaResidueFactor_continuousAt_one` | `THEOREM_UNCONDITIONAL` | none |
| `zetaResidueFactor_analyticAt_one` | `THEOREM_UNCONDITIONAL` | none |
| `zetaResidueFactor_analyticOn` | `THEOREM_UNCONDITIONAL` | none |
| `zetaMellinPoleSub_analyticOn` | `THEOREM_CONDITIONAL(on H_mellin)` | `H_mellin` |
| `zetaMellinPoleSub_off_pole` | `THEOREM_CONDITIONAL(on hmass,w∈H,w≠1)` | `Mellin h 1 = 0`, `w ∈ H`, `w ≠ 1` |
| `zetaMellinPoleSub_value_one` | `THEOREM_UNCONDITIONAL` | none |
| `shiftedHalfPlane_isPreconnected` | `THEOREM_UNCONDITIONAL` | none |
| `continued_window_identity_of_analytic` | `THEOREM_CONDITIONAL(on H_mellin,hzero,hG,hRm,hRp,habs)` | exact six hypotheses in `Main.lean` |
| `continued_window_identity_raw_off_pole` | `THEOREM_CONDITIONAL(on hzero,hcont)` | `Mellin h 1 = 0`, continued identity |
| `continued_window_identity_pole_value` | `THEOREM_CONDITIONAL(on hcont)` | continued identity |

## Consumption result

| new declaration | Result |
|---|---|
| `mellin_compactSupport_analyticOnNhd` | discharges `H_mellin` from the exact measurable/support/Lipschitz hypotheses |
| `continued_window_identity_unconditional_mellin` | T5 with `H_mellin` discharged; retained window/tail analyticity and absolute-region identity remain explicit |
| `continued_window_identity_raw_off_pole_unconditional_mellin` | punctured raw-product corollary with `H_mellin` discharged |
| `continued_window_identity_pole_value_unconditional_mellin` | pole-value corollary with `H_mellin` discharged |

The unique open *hypothesis* recorded by the delivered v3 source was T4a,
and it is now closed locally.

## Plant inventory discrepancy

The delivered v3 archive contains no declarations named or semantically
implementing the requested explicit triangular-bump plants PL1–PL3. Its
`RequestProject/Main.lean` has 239 lines and ends at the two T5 corollaries.
Therefore PL1–PL3 cannot be “mechanically instantiated from the conditional
v3 layer”: there are no such declarations to instantiate.

This is a source-inventory mismatch, not a T4a failure. Goal 039 does not
assert `MUNTZ_V3_UNCONDITIONAL_LAYER_COMPLETE`. The existing v3 T5 and both
corollaries are consumed; the explicit plant package remains absent and must
be supplied by a separate theorem contract if the owner still requires it.

## Lane status

`T4A_CLOSED_LOCALLY`; Müntz v3 T5 consumption is Lean-checked; explicit
PL1–PL3 source declarations are absent; Route B remains
`CHALLENGER / NOT_RH`; Bus 010 remains void.

## 2026-08-02 addendum — exact-class supplier front assembled

The later exact-class execution has now discharged the four retained analytic
suppliers for the same measurable/Icc-zero/Ico-Lipschitz function class:

| Supplier | Checked declaration |
|---|---|
| `hG` | `gwin_analyticOnNhd_shiftedHalfPlane_v3Class` |
| `hRm` | `rminus_analyticOnNhd_shiftedHalfPlane_v3Class` |
| `hRp` | `rplus_analyticOnNhd_shiftedHalfPlane_v3Class` |
| `habs` | `habs_of_IccZero_IcoLipschitz` |

`MuntzV3ExactClassClosure.lean` consumes all four and exports:

- `continued_window_identity_v3Class`;
- `continued_window_identity_raw_off_pole_v3Class`;
- `continued_window_identity_pole_value_v3Class`.

The native v3 `habs` proof makes the semantic transport explicit: E-star core,
Mathlib/project Mellin conventions, `Icc`/`Ioo` null endpoints, and both tail
indicators.  The full standalone project builds 8050 jobs, the new production
files have no holes, and the four public declarations depend only on
`[propext, Classical.choice, Quot.sound]`.

Verdict: `HABS_SUPPLIER_DISCHARGED_FOR_V3_CLASS /
MUNTZ_V3_EXACT_CLASS_CONTINUATION_ASSEMBLED`.  This is not tail smallness,
cofinal convergence, detector closure, or RH.  Route B remains
`CHALLENGER / NOT_RH`; physical Bus 010 remains void.

## 2026-08-02 addendum — symmetric source-trial bridge

`MuntzV3SymmetricTrialCrosswalk.lean` closes the next representation-only
boundary.  For a measurable trial supported in `Icc (-b) b`, Lipschitz on its
positive half, and with zero positive-half mass, it proves
`continued_window_identity_symmetricTrial_v3Class` for the original symmetric
function.

The proof uses `(Ici 0).indicator h` internally and separately proves
invariance of `Estar`, `Mellin`, `Gwin`, `Rminus`, `Rplus`, and
`ZetaMellinPoleSub` on their positive domains.  It then consumes the already
closed exact-class receiver; no T2 argument is repeated.

Direct Lean, the 8038-job target build, and the full 8051-job v3 build pass.
The production hole scan is empty and the theorem depends only on
`[propext, Classical.choice, Quot.sound]`.

Verdict: `MUNTZ_V3_SYMMETRIC_TRIAL_CROSSWALK_PROVED`.  Concrete prolate-trial
regularity, finite projection/ground equality, cofinal tail control, S1/S2,
and RH remain open; Route B stays `CHALLENGER / NOT_RH` and Bus 010 stays void.

## 2026-08-02 addendum — provenance-locked prolate receiver

The Q3/Mathlib-4.26 declarations `Q3.RouteB.D0Pstar.ProlatePair`,
`prolateCombination`, and `prolateCombination_muntzRegularity_of_modes` are
exported into the standalone Mathlib-4.28 project under
`RequestProject/ProlateExport/`.  The export pins source commit `6e78e4e5`,
both Git blob IDs and SHA-256 digests, preserves the original namespace, and
changes only the regularity file's import path.

`MuntzV3ProlateCombinationReceiver.lean` consumes that exact exported object
and the symmetric-trial bridge.  It exports
`continued_window_identity_prolateCombination_v3Class`, conditional on the
two supplied modes being measurable and Lipschitz on `Ico 0 P.pw.lambda`.

Mechanical provenance diffs are empty modulo the recorded header/import
rewrite.  Direct Lean passes for all three files, the target build passes
8041/8041, the full project passes 8054/8054, the production taint scan is
empty, and the receiver depends only on
`[propext, Classical.choice, Quot.sound]`.

Verdict: `PROLATE_EXPORT_PROVENANCE_LOCKED`.  This does not construct the
source prolate modes or supply their regularity, denominator nonvanishing,
midpoint representative, `MemLp`, `TrialNonzero`, finite ground/trial tracking,
cofinal control, S1/S2, or RH.  Route B remains `CHALLENGER / NOT_RH`; physical
Bus 010 remains void.

## 2026-08-02 addendum — prolate mode measurability removed from the v3 contract

The Q3 theorem `measurable_of_even_support_positiveHalfLipschitz` is exported
from source commit `298701cb` into
`RequestProject/ProlateExport/ProlateModeRegularity.lean`.  Its proof body is
byte-faithful; the only change is the recorded import rename to the existing
provenance-locked `ProlateLayer`.

`MuntzV3ProlateCombinationReceiver.lean` preserves its original theorem and
adds `continued_window_identity_prolateCombination_v3Class_of_modeLipschitz`.
The new corollary obtains measurability of both stored modes from their
`ProlatePair` evenness/support fields and the two supplied positive-half
Lipschitz bounds, then invokes the original receiver.  Thus measurability is no
longer an independent source-side input.

The reverse-import SHA-256 equals the pinned source digest.  Direct Lean passes,
the target build passes 8042/8042, the full standalone build passes 8055/8055,
the production taint scan is empty, and the new declarations depend only on
`[propext, Classical.choice, Quot.sound]`.

Verdict: `PROLATE_MODE_MEASURABILITY_ELIMINATION_PROPAGATED_TO_V3`.  No further
transport wrapper is authorized without actual source-mode definitions.  The
next genuine wall is
`SOURCE_LOCKED_PROLATE_MODE_CONSTRUCTION_AND_POSITIVE_HALF_LIPSCHITZ`: the
repository has no Lean PSWF constructor or mode-existence theorem, so this is
not yet a self-contained Aristotle request.  Route B remains
`CHALLENGER / NOT_RH`; physical Bus 010 remains void.

## 2026-08-03 addendum — finite-Fourier eigenrelation regularity leaf

`Q3/Proofs/RouteB/ProlateSourceRegularity.lean` materializes the source-locked
finite-Fourier kernel with the repository's plus-sign convention
`exp(+2*pi*i*x*y)` and its action on `Icc (-lambda) lambda`.

The file proves three supplier reductions:

- the zero-frequency eigenrelation plus symmetric support implies the existing
  full-integral/center identity;
- interval integrability makes the finite-Fourier action globally Lipschitz;
- an exact restricted eigenrelation with `chi != 0` transfers that bound to
  `LipschitzOnWith` for the mode on `Ico 0 lambda`.

Consequently positive-half Lipschitz is no longer an independent analytic
obligation after actual source modes and their nonzero eigenrelations have been
constructed.  The exact remaining wall is source-level existence and canonical
selection of `h0 <-> chi0` and `h4 <-> chi2`, together with integrability,
nonzero eigenvalues, and the restricted finite-Fourier eigenrelations for those
constructed modes.

Direct Lean, target/full Q3 builds, `q3_check`, the production taint scan, and
the standard-axiom audit pass.  This result is not a PSWF constructor, does not
discharge the independent D0.7e.5a WPrime source pause, and makes no concrete
trial, RH, or Bus 010 claim.  Route B remains `CHALLENGER / NOT_RH`; physical
Bus 010 remains void.  No Aristotle request is opened because the remaining
existence/selection target is not self-contained in the current Lean library.

### B0 a.e. eigenrepresentative closure

An initial Proshka review named the a.e. eigenrepresentative as the first
self-contained B0 gate.  That gate is now closed locally in
`Q3/Proofs/RouteB/ProlateFiniteFourierRegularity.lean`.

`finiteFourierEigenRepresentative` defines the canonical representative
`chi^-1 * finiteFourierAction`.  Under `0 <= lambda`, `chi != 0`, interval
integrability, and an a.e. finite-Fourier eigenrelation on the source interval,
`finiteFourier_aeEigenfunction_lipschitzRepresentative` proves both:

- `LipschitzOnWith` for that representative on `Icc (-lambda) lambda`;
- a.e. equality of the representative with the supplied eigenfunction on the
  restricted volume measure.

The target build passes 7745 jobs, the full Q3 build passes 7817 jobs,
`q3_check` is `ok`, the taint scan is empty, and both declarations use only
`[propext, Classical.choice, Quot.sound]`.  Aristotle was not needed.

Verdict: `FINITE_FOURIER_EIGENFUNCTION_LIPSCHITZ_REPRESENTATIVE_PROVED`.
After inspection of the published kernel theorem, Proshka selected the
source-defined Sturm--Liouville degrees as the canonical construction backend;
finite Fourier remains a derived characterization/regularity layer.  The next
self-contained gate is exact finite-Fourier/prolate-expression commutation;
the deeper construction wall is
`SOURCE_LOCKED_STURM_LIOUVILLE_MODES_0_4_EXISTENCE_AND_SELECTION_MISSING`.
Neither the self-adjoint Sturm--Liouville existence/selection backend nor an
equivalent source theorem is present in Lean; no interface-only replacement
counts as closure.  The independent D0.7e.5a pause remains open, Route B remains
`CHALLENGER / NOT_RH`, and physical Bus 010 remains void.

### Prolate differential-expression / finite-Fourier intertwining closure

`Q3/Proofs/RouteB/ProlateSourceCommutation.lean` now proves the exact
source-layer commutation theorem
`finiteFourierAction_intertwines_prolateWaveExpression` for `0 < lambda` and
globally `C^2` complex test functions.  The proof is not a renamed hypothesis:
it establishes the symmetric differential identity for the plus-sign kernel,
differentiates under the compact Bochner integral, and uses two zero-flux
integration-by-parts identities whose endpoint factors are
`lambda^2-y^2 = 0`.

Direct Lean passes, the target build passes 7745/7745, the full Q3 build passes
7817/7817, `q3_check` is `ok`, the production hole scan is empty, and the two
public theorems depend only on `[propext, Classical.choice, Quot.sound]`.  The
proof DB records all declarations in the file as proven.

Verdict: `PROLATE_STURM_LIOUVILLE_FINITE_FOURIER_INTERTWINING_PROVED`.  This
removes commutation as a source-construction obligation but does not construct
a Sturm--Liouville realization, prove simple spectrum, supply a nonzero
finite-Fourier scalar, or select the exact source degrees `h0 <-> chi0` and
`h4 <-> chi2`.  The remaining wall is
`SOURCE_LOCKED_STURM_LIOUVILLE_MODES_0_4_EXISTENCE_AND_SELECTION_MISSING`.
The independent D0.7e.5a pause remains open, Route B remains
`CHALLENGER / NOT_RH`, and physical Bus 010 remains void.

### Prolate eigenrelation transport closure

Proshka ratified the published intertwining commit
`13f71c622814a52ed9af9d1f069764fdca45f84e` and selected the exact next
self-contained backend-A corollary.  The new file
`Q3/Proofs/RouteB/ProlateSourceEigenTransport.lean` proves
`finiteFourierAction_preserves_prolateWaveEigenrelation`.

For a globally `C^2` complex function satisfying the pointwise prolate-wave
eigenrelation on `Icc (-lambda) lambda`, the theorem combines the closed
intertwining identity with set-integral congruence and complex scalar
linearity.  It follows that the finite Fourier action satisfies the same
eigenrelation everywhere.  No new analytic construction is hidden in the
proof.

Direct Lean, the dedicated module build, the full Q3 build, and `q3_check`
pass.  The production hole scan is empty, the declaration depends only on
`[propext, Classical.choice, Quot.sound]`, and the proof DB records it as
`proven`.

Verdict: `PROLATE_FINITE_FOURIER_PRESERVES_STURM_LIOUVILLE_EIGENRELATION_PROVED`.
This preserves a supplied formal eigenspace; it does not construct the
self-adjoint realization, prove simplicity, show a Fourier scalar is nonzero,
or select the source modes `h0 <-> chi0` and `h4 <-> chi2`.  The deeper wall
remains
`SOURCE_LOCKED_STURM_LIOUVILLE_MODES_0_4_EXISTENCE_AND_SELECTION_MISSING`.
The independent D0.7e.5a pause remains open, Route B remains
`CHALLENGER / NOT_RH`, and physical Bus 010 remains void.

### Finite-Fourier action nonvanishing closure

Proshka ratified the published eigenrelation-transport commit
`df243cd2a7c60513b6ef4d500fd9e2f532162abb` and selected the exact next
self-contained local leaf.  The new file
`Q3/Proofs/RouteB/ProlateFiniteFourierNonvanishing.lean` proves
`finiteFourierAction_ne_zero_of_integrableOn_continuousAt`.

For an interval-integrable complex function with a continuous nonzero value at
an interior point, the theorem proves that its finite-Fourier action is nonzero
at some frequency.  The proof source-locks the plus-phase project convention by
identifying it with Mathlib's negative-frequency Fourier transform of the zero
extension, then applies pointwise Fourier inversion.  It does not assume or
construct a prolate mode.

Direct Lean, the dedicated module build, the full Q3 build, and `q3_check`
pass.  The production hole scan is empty, the public theorem depends only on
`[propext, Classical.choice, Quot.sound]`, and both declarations are recorded as
`proven` in the proof DB.  Aristotle remained a running background alternative
and was not used.

Verdict: `PROLATE_FINITE_FOURIER_NONVANISHING_FROM_INTERIOR_MODE_PROVED`.  This
closes only nonvanishing of the action from supplied local source data; it does
not construct the self-adjoint realization, prove simplicity, identify the
Fourier scalar, or select the source modes `h0 <-> chi0` and `h4 <-> chi2`.
The deeper wall remains
`SOURCE_LOCKED_STURM_LIOUVILLE_MODES_0_4_EXISTENCE_AND_SELECTION_MISSING`.
The independent D0.7e.5a pause remains open, Route B remains
`CHALLENGER / NOT_RH`, and physical Bus 010 remains void.

### Backend-A ratification and terminal stop

Proshka ratified published commit
`12a5095cde4b52faa65fe35c7e47c19f6cdfb3e5` with verdict
`PROLATE_FINITE_FOURIER_NONVANISHING_FROM_INTERIOR_MODE_PROVED` and selected
`B_TERMINAL_STOP`.  Backend A has no further honest self-contained transport
leaf in the current Lean object model.

Stop code:
`SOURCE_LOCKED_STURM_LIOUVILLE_MODES_0_4_EXISTENCE_AND_SELECTION_MISSING`.
Release requires an exact zero-flux self-adjoint Sturm--Liouville realization,
actual source degree-0 and degree-4 modes, and proved index/selection.  A new
record that merely assumes existence, simplicity, or the scalar eigenrelation
does not satisfy this release condition.

Aristotle project `07a1765f-0457-4577-8247-5c13c64dc9bb` remains a running
background alternative and is not authorized for integration unless its final
output is hole-scanned, locally compiled, axiom-audited, source-object
identical, and strictly stronger than the published local theorem.

The independent D0.7e.5a pause remains open, Route B remains
`CHALLENGER / NOT_RH`, and physical Bus 010 remains void.  No RH claim is made.

### Aristotle commutation output adjudication

Aristotle project `07a1765f-0457-4577-8247-5c13c64dc9bb` reached `IDLE` and
its UUID-scoped archive was downloaded and inspected.  Archive SHA-256 is
`979ffd092f56f100cf9a782945abbdce5b21b9f16b2f8b7942881c8f786690ce`.  The
Lean-source scan is empty for `sorry`, `admit`, `exact?`, `axiom`, and
`native_decide`.  Its standalone Mathlib 4.28 build passes 8028/8028, and the
requested theorem uses exactly `[propext, Classical.choice, Quot.sound]`.

The 1166-line candidate also compiles under the production Mathlib 4.26
environment against the real repository `ProlateSourceRegularity`.  It proves
the same public intertwining theorem as published commit
`13f71c622814a52ed9af9d1f069764fdca45f84e`, but does not expose the
production theorem `prolateWaveExpression_finiteFourierKernel_swap`; its
standalone project also substitutes a 25-line definitions-only shim for the
full production regularity module.

Verdict:
`ARISTOTLE_PROLATE_COMMUTATION_VALID_BUT_NOT_STRICTLY_STRONGER_NOT_INTEGRATED`.
No Aristotle-generated Lean source is integrated.  The backend-A terminal stop
and release condition are unchanged.

The independent D0.7e.5a pause remains open, Route B remains
`CHALLENGER / NOT_RH`, and physical Bus 010 remains void.  No RH claim is made.
