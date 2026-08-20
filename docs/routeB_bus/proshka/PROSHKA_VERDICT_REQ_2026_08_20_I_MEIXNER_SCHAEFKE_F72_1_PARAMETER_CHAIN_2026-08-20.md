# STATUS: CONDITIONAL — SATZ 9 PARAMETER/RATE CHAIN LOCKED; F72.1 BECOMES A BOUNDED PORT AFTER F72.0B
```yaml
PRIMARY: F72_1_MEIXNER_SCHAEFKE_PARAMETER_RATE_BUNDLE_SCOPE_LOCKED
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-20-I

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: 708d781344e479322907ef8422a5add8412db1f4
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  MS_USAGE_CARD: docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md
  MS_BOOK_DOI: 10.1007/978-3-662-00941-3
  MS_LOCATION: chapter_3_section_3_251_Satz_9_printed_page_243
  CCM_PAPER: arXiv_2511_22755v1
  CCM_CONSUMED_EQUATIONS: [7.9, 7.10, 7.11, 7.12]
  DLMF_CROSSCHECKS: [30.9.1, 12.7.2]

SOURCE_VERIFICATION:
  owner_usage_card_present: true
  local_book_pdf_independently_rendered_by_judge: false
  ccm_exact_formula_independently_checked: true
  dlmf_q_and_Dn_crosscheck: true

PARAMETER_CHAIN:
  spheroidal_order_m: 0
  project_even_carrier_j: [0, 2]
  full_degree_n: [0, 4]
  q_law: q = 2*(n-m)+1
  q_values: [1, 9]
  q_role: EIGENVALUE_LINEAR_SLOPE_AND_HARMONIC_OSCILLATOR_ENERGY
  parabolic_cylinder_order_law: nu = n-m = (q-1)/2
  parabolic_cylinder_orders: [0, 4]
  false_order_D_q: KILLED_BY_PARITY_AND_CENTER_PLANT

UNIT_CHAIN:
  project_window_lambda: lambda
  dimensionless_coordinate: z = x/lambda
  ms_gamma: 2*pi*lambda^2
  project_mode4SlepianC: ms_gamma
  project_mode4JacobiG: ms_gamma^2
  fuchs_a_squared: ms_gamma
  argument_transport: sqrt(2*ms_gamma)*z = sqrt(4*pi)*x

REMAINDER_CHAIN:
  raw_Satz9_remainder: O(ms_gamma^(-3/4))
  normalized_remainder_after_mul_by_(4gamma/pi)^(-1/4): O(ms_gamma^(-1))
  physical_remainder: O(lambda^(-2))
  usage_card_raw_O_gamma_minus_1: SUPERSEDED_RATE_PLACEMENT

PREFATOR_LOCK:
  m_zero_raw_leading_coefficient: (4*gamma/pi)^(1/4) / sqrt((2*n+1)*n!)
  exact_prefactor_needed_as_public_downstream_object: false
  exact_prefactor_may_be_ignored: false
  implementation: ABSORB_EXACTLY_ONCE_IN_SOURCE_NORMALIZATION
  physical_mode_zero_scalar: (1/sqrt(2))*lambda^(-1/2)
  physical_mode_four_scalar: (3/sqrt(2))*lambda^(-1/2)
  fitted_scalar: forbidden

F72_1_SPLIT:
  F72_0B_SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE: OPEN_PREDECESSOR
  F72_1A_NORMALIZED_SATZ9_FIXED_MODE_RATE: PAPER_SCOPE_CLOSED_PROJECT_PORT_OPEN
  F72_1B_D0_D4_TO_PROJECT_HERMITE_EXACT: LEAN_READY
  F72_1C_SELECTED_PHYSICAL_WINDOW_UNIFORM_RATE: OPEN_ASSEMBLY_AFTER_F72_0B

COST_REPAIR:
  previous_F72_1: 8/10
  paper_scope_and_parameter_uncertainty: 1/10_CLOSED
  fixed_mode_D_to_H_Lean: 2/10
  uniform_bigO_to_eventual_bound_port: 3/10
  F72_1_after_F72_0B: 4/10
  combined_F72_0B_then_F72_1: 6/10
  full_reproof_of_Satz9_in_Lean: 9/10_NOT_SELECTED

CLOSES:
  - MS_GAMMA_EQUALS_PROJECT_GAMMA
  - Q_VALUES_FOR_SELECTED_MODES
  - PARABOLIC_ORDER_CATEGORY_LOCK
  - RAW_VS_NORMALIZED_REMAINDER_LOCK
  - EXACT_FIXED_MODE_PREFATOR_RECOVERY
  - F72_1_THEOREM_DECOMPOSITION
  - FALSE_D_Q_TO_H_N_BRIDGE
OPENS:
  - SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE
  - F72_1_PROJECT_LEAN_PORT

DISCRIMINATOR:
  name: STRICT_SELECTED_FERRERS_FIXED_MODE_RATE
  formula: lambda_k^2 * sup_{|x|<=lambda_k} |h_selected_{n,k}(x)-h_n(x)|
  pass: eventually_bounded_for_n_0_and_4_under_one_source_normalization
  zero_consistent: INCONCLUSIVE

CANDIDATE_REPRESENTATIONS:
  R1_NORMALIZED_SATZ9_TWO_FIXED_MODES:
    rank: PRIMARY
    kill_power: 10/10
    cost: 4/10_after_F72_0B
  R2_DIRECT_SCALED_ODE_VOLterra_FIXED_MODES:
    rank: RUNNER_UP_NOT_AUTHORIZED
    kill_power: 8/10
    cost: 8/10

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED: false
ARISTOTLE_AUTHORIZED: false
NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE
NEXT_F72_1_LOCAL_GAP: F72_1A_NORMALIZED_SATZ9_FIXED_MODE_RATE_INTERFACE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

REQ-I closes the parameter and rate **scope-lock**, but it does not yet close the
project theorem. The shortest honest chain is

```text
selected project modes j=0,2
  -> full spheroidal degrees n=0,4 and order m=0
  -> literal Meixner--Schäfke representatives            [F72.0B, OPEN]
  -> normalized Satz-9 fixed-mode estimate               [F72.1A]
  -> exact D_0/D_4 polynomial-Gaussian identities        [F72.1B]
  -> physical-window O(lambda^-2) estimate               [F72.1C]
  -> F72.4 integral rate and downstream L73.2 assembly
```

The main repair is categorical. The integer

\[
q=2(n-m)+1
\]

belongs to the eigenvalue expansion. The parabolic-cylinder order is

\[
\nu=n-m=\frac{q-1}{2}.
\]

For the selected modes this gives

```text
n=0: q=1,  D-order=0;
n=4: q=9,  D-order=4.
```

Thus `q = 1,9` is correct only as the eigenvalue/harmonic-oscillator parameter.
The attempted bridge through `D_q` is false. `[ABSTRACT][PAPER]` **[C04]**

## 1. EXACT PARAMETER CHAIN

The project dictionary already fixes the full degrees `n=0,4`, the spheroidal
order `m=0`, the physical window `[-lambda,lambda]`, and the dimensionless
coordinate

\[
z=\frac{x}{\lambda}.
\]

CCM equation (7.9), obtained by a direct change of variables in the prolate
operator, gives

\[
\boxed{\gamma_{MS}=2\pi\lambda^2.}
\]

This is the project quantity `mode4SlepianC`. The Jacobi recurrence parameter
`mode4JacobiG` is its square:

\[
\boxed{G_{project}=\gamma_{MS}^{\,2}.}
\]

Fuchs's independently audited parameter satisfies `a^2 = gamma_MS`; that is a
cross-check, not a necessary premise for F72.1. `[COFINAL_FAMILY][PAPER]`

The argument of the parabolic-cylinder function transports exactly:

\[
\sqrt{2\gamma_{MS}}\,z
 =\sqrt{2(2\pi\lambda^2)}\frac{x}{\lambda}
 =\sqrt{4\pi}\,x.
\]

Therefore uniformity for `z in [-1,1]` is exactly uniformity for
`x in [-lambda,lambda]`. `[COFINAL_FAMILY][PAPER]`

### C04 plant: `D_q` is impossible

If the order were incorrectly set to `q`, the ground mode would use `D_1` and
the degree-four mode would use `D_9`. Both are odd and vanish at the origin.
The two project modes are even and have nonzero centre values. Hence the wrong
mapping fails before any asymptotic estimate is considered.

```text
D_q mapping:
  KILLED.

D_{n-m} mapping:
  RATIFIED.
```

`[ABSTRACT][PAPER]`

## 2. RAW AND NORMALIZED SATZ-9 RATES

The exact formula reproduced in CCM Lemma 7.2 is

\[
\operatorname{ps}_{n}^{m}(z;\gamma^2)
 =(-1)^m\left(\frac{4\gamma}{\pi}\right)^{1/4}
   \frac{1}{(n-m)!}
   \left(\frac{(n+m)!}{2n+1}\right)^{1/2}
   (1-z^2)^{m/2}
   D_{n-m}(\sqrt{2\gamma}\,z)
   +O(\gamma^{-3/4}),
\]

uniformly on `[-1,1]` for fixed `m,n`. For `m=0` this becomes

\[
\operatorname{ps}_{n}^{0}(z;\gamma^2)
 =\left(\frac{4\gamma}{\pi}\right)^{1/4}
   \frac{D_n(\sqrt{2\gamma}\,z)}
        {\sqrt{(2n+1)n!}}
   +O(\gamma^{-3/4}).
\]

Multiplication by `(4 gamma/pi)^(-1/4)` gives the theorem actually consumed by
the project:

\[
\boxed{
\left(\frac{4\gamma}{\pi}\right)^{-1/4}
\operatorname{ps}_{n}^{0}(z;\gamma^2)
 =\frac{D_n(\sqrt{2\gamma}\,z)}{\sqrt{(2n+1)n!}}
  +O(\gamma^{-1}).
}
\]

Thus the usage-card phrase putting `O(gamma^-1)` directly beside the unscaled
`ps` formula is superseded. The raw error is `O(gamma^-3/4)`; the normalized
error is `O(gamma^-1)`. This placement is load-bearing because the missing
quarter-power is exactly the normalization that controls the final rate.
`[COFINAL_FAMILY][PAPER]` **[C04] [C09]**

Finally,

\[
\gamma^{-1}=(2\pi\lambda^2)^{-1}=\frac1{2\pi}\lambda^{-2},
\]

so the normalized Satz-9 estimate supplies the exact rate required by CCM
Lemma 7.2. `[COFINAL_FAMILY][PAPER]`

## 3. SHORTEST DEFENSIBLE PARABOLIC-CYLINDER TO HERMITE BRIDGE

A general parabolic-cylinder library is unnecessary. The standard identity is

\[
D_n(t)=e^{-t^2/4}\operatorname{He}_n(t)
      =2^{-n/2}e^{-t^2/4}H_n(t/\sqrt2),
\]

where `He_n` is the probabilists' Hermite polynomial and `H_n` is the
physicists' Hermite polynomial. The expression

```text
2^(-n/2) * exp(-t^2/4) * He_n(t)
```

is therefore wrong if `He_n` denotes the probabilists' convention. The two
Hermite conventions must remain typed separately. `[ABSTRACT][PAPER]` **[C04]**

For Q3 only two exact identities are needed:

\[
D_0(\sqrt{4\pi}\,x)=e^{-\pi x^2}=2^{-1/4}h_0(x),
\]

\[
D_4(\sqrt{4\pi}\,x)
=e^{-\pi x^2}(16\pi^2x^4-24\pi x^2+3)
=2^{5/4}\sqrt3\,h_4(x).
\]

These are polynomial-Gaussian identities. They can be proved by unfolding the
already explicit Q3 definitions and using ordinary ring and exponential
rewrites. No general `D_n`, spheroidal, or special-function API is required.

```text
F72.1B cost:
  2/10.
```

`[ABSTRACT][LEAN_READY]`

## 4. EXACT PHYSICAL NORMALIZATIONS

For `m=0`, the normalized Satz-9 formula and the two identities above force the
physical normalizations uniquely:

\[
\boxed{
h_{0,\lambda}(x)
=\frac1{\sqrt2}\lambda^{-1/2}
 \operatorname{ps}_{0}^{0}(x/\lambda;\gamma^2),
}
\]

\[
\boxed{
h_{4,\lambda}(x)
=\frac3{\sqrt2}\lambda^{-1/2}
 \operatorname{ps}_{4}^{0}(x/\lambda;\gamma^2),
}
\]

with `gamma=2*pi*lambda^2`. The constants agree with the F72.0 dictionary and
are recovered algebraically, not fitted.

Consequently there is one common constant `C` and an eventual cutoff such that
for `n=0,4`,

\[
\max_{|x|\le\lambda}
 |h_{n,\lambda}(x)-h_n(x)|
 \le C\lambda^{-2}.
\]

This is still conditional as a project theorem because the selected project
Ferrers modes have not yet been bound to the literal `ps_0^0` and `ps_4^0`
representatives. That predecessor is `F72.0B`. `[COFINAL_FAMILY][CONDITIONAL]`

## 5. IS THE UNREADABLE PREFATOR REQUIRED?

### Verdict

```text
It may be hidden downstream.
It may not be omitted from the proof.
```

The exact quarter-power is not an independent project object. It should be
absorbed once into the source normalization before the rate is exported. But
one must record it exactly to convert the raw `O(gamma^-3/4)` remainder into the
normalized `O(gamma^-1)` remainder.

The prefactor is no longer unverifiable. CCM equation (7.10) reproduces the
normalized formula explicitly, and the recovered physical constants
`1/sqrt(2)` and `3/sqrt(2)` independently check the transcription against the
explicit `D_0/D_4` identities. `[COFINAL_FAMILY][PAPER]`

The selected implementation is therefore a **rate-only normalized bundle**:

```text
Input:
  the literal Satz-9 representatives and the exact source normalization.

Output:
  the two physical O(lambda^-2) bounds.

Not exported:
  a general parabolic-cylinder API;
  a free C(gamma) symbol;
  any fitted scalar.
```

A direct normalized ODE/Volterra proof remains possible, but it is not the
shortest route. It would need a quantitative eigenvalue expansion, initial or
norm normalization, a uniform Green/Volterra bound on the expanding window,
and the same project/source representative bind. It therefore remains the
runner-up at cost `8/10`. `[COFINAL_FAMILY][CONDITIONAL]`

## 6. REPAIRED F72.1 DECOMPOSITION

### F72.0B — `SelectedFerrersToSatz9Representative`

This remains the predecessor and the current load-bearing gap. It proves that
the exact selected project modes are nonzero source-derived scalar multiples
of the literal Meixner--Schäfke representatives. `[COFINAL_FAMILY][CONDITIONAL]`

### F72.1A — `NormalizedSatz9FixedModeRate`

Paper-facing statement for `n in {0,4}`:

\[
\exists C_n,\gamma_{0,n}\ \forall\gamma\ge\gamma_{0,n}\ \forall z\in[-1,1],
\]

\[
\left|
\left(\frac{4\gamma}{\pi}\right)^{-1/4}
\operatorname{ps}_n^0(z;\gamma^2)
-rac{D_n(\sqrt{2\gamma}\,z)}{\sqrt{(2n+1)n!}}
\right|
\le C_n\gamma^{-1}.
\]

The theorem scope is closed at PAPER level. Its project interface remains to be
materialized. `[ABSTRACT][PAPER]`

### F72.1B — `D0D4PhysicalHermiteExact`

Prove only the two displayed polynomial-Gaussian identities. This is a small
exact Lean node. `[ABSTRACT][LEAN_READY]`

### F72.1C — `SelectedFerrersPhysicalUniformRate`

Compose F72.0B, F72.1A, F72.1B, `gamma=2*pi*lambda^2`, and `z=x/lambda` to
obtain the project-facing two-mode bound. `[COFINAL_FAMILY][CONDITIONAL]`

The eigenvalue expansion and the values `q=1,9` are a mode-label firewall. They
are not a fourth analytic supplier for the uniform mode rate.

## FINAL PROPOSAL

Select **R1: normalized Satz-9, two fixed modes only**.

Registered prediction fate:

```text
P_I1  gamma_MS = 2*pi*lambda^2:
      CONFIRMED, directly by CCM (7.9).

P_I2  q=1,9 identifies the selected modes but is not the D-order:
      CONFIRMED; D_q is killed by parity and centre value.

P_I3  the broken prefactor can be recovered without fitting:
      CONFIRMED through CCM (7.10)-(7.12) and the D_0/D_4 constants.

P_I4  source acquisition lowers the wall price:
      CONFIRMED WITH SCOPE.
      F72.1 falls from 8/10 to about 4/10 after F72.0B;
      the combined F72.0B -> F72.1 path remains about 6/10.
```

Do not formalize a general parabolic-cylinder library. Do not reprove Satz 9.
Do not introduce an abstract `alpha` unless its type says explicitly that it is
the eigenvalue slope `q`; it is not the cylinder order.

## STRONGEST ATTACK

The strongest reviewer objection is provenance:

> The judge did not independently render the owner's local book page. The exact
> quarter-power was recovered from CCM's transcription of Satz 9, not from a
> second clean image of the monograph.

This prevents a `PROVED_FROM_PRIMARY_BYTES` verdict. It does not reopen the
parameter mathematics: CCM prints the complete formula, DLMF independently
confirms `q=2(n-m)+1` and the integer `D_n`/Hermite identity, and the resulting
normalizations reproduce CCM's explicit `h_{0,lambda}` and `h_{4,lambda}`
constants. The remaining provenance discriminator is a clean visual read of
the single quarter-power on printed page 243.

The second objection is more load-bearing:

> Satz 9 concerns the literal `ps_n^0`; the project selected Ferrers mode is not
> yet proved to be that object up to a source-derived scalar.

Correct. This is why the status is `CONDITIONAL`, and why F72.0B remains the
next load-bearing gap. No rate theorem may bypass it by defining `ps_n` to be
the project mode or by adding the desired equality as a hypothesis. **[C10]**

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION FROM THIS VERDICT.

Do not write Lean yet.
Do not start a parabolic-cylinder library.
Do not modify Q3.Main.
Do not call Aristotle.

After owner/Linux harvest and an explicit execution authorization, the first
admissible local node is either:

  F72_0B_SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE

or, if F72.0B is supplied independently:

  F72_1B_D0_D4_PHYSICAL_HERMITE_EXACT.
```

## META CLOSEOUT

**What became smaller?**

`F72.1` changed from an opaque external asymptotic wall into one paper supplier
plus two bounded exact transports.

**What was killed?**

- `D_q` as the parabolic-cylinder order;
- the raw-remainder label `O(gamma^-1)` before quarter-power normalization;
- the ambiguous `He_n` convention;
- the claim that a general parabolic-cylinder library is necessary;
- the idea that the prefactor may simply be discarded.

**What must not be tried again?**

- identify `q` with the cylinder order;
- merge `gamma` with `gamma^2` or with the physical window `lambda`;
- cite Satz 8 for a sup-norm theorem;
- fit the source scalar numerically;
- bypass F72.0B with a tautological alias.

**Current smallest named gap:**

```text
SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE
```

**Next cheapest decisive test:**

A source-faithful fixed-mode uniqueness/crosswalk proof for the two selected
Ferrers functions, with the scalar fixed by the nonzero centre value.

**Memory entry:**

```yaml
iteration: REQ-2026-08-20-I
target: F72_1_MEIXNER_SCHAEFKE_FIXED_MODE_UNIFORM_RATE
status: PROGRESS
failed_strategy: GENERAL_PARABOLIC_CYLINDER_PORT_AND_UNREADABLE_PREFATOR_BLOCK
cognitive_operator_used: UNIT_AUDIT
new_gap_name: SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE
invariant_learned: q_is_eigenvalue_slope_while_D_order_is_n_minus_m
forbidden_future_move: never_use_D_q_or_drop_the_quarter_power
next_decisive_test: literal_fixed_mode_source_bind_at_nonzero_center
```

## SOURCE LEDGER

- Meixner--Schäfke, *Mathieusche Funktionen und Sphäroidfunktionen*, §3.251,
  Satz 9, printed p. 243. `[ABSTRACT][PAPER]`
- Connes--Consani--Moscovici, *Zeta Spectral Triples*, Lemma 7.2,
  equations (7.9)--(7.12). `[COFINAL_FAMILY][PAPER]`
- DLMF §30.9(i), equation 30.9.1 for `q=2(n-m)+1`.
  `[ABSTRACT][PAPER]`
- DLMF §12.7(i), equation 12.7.2 for the integer parabolic-cylinder/Hermite
  identity. `[ABSTRACT][PAPER]`
