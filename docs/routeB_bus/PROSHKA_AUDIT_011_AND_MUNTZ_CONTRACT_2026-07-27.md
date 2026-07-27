# Proshka audit — 011 + EStar Müntz continuation contract

Date: 2026-07-27

## Primary status

```text
AUDIT_011_ACCEPTED_WITH_RENAMING
MUNTZ_V1_CONTRACT_FATAL
```

## Verdict codes

```text
HTRIAL_FORMULA_ACCEPTED
HTRIAL_MELLIN_MASS_ZERO_CONFIRMED
MEASURE_CONVENTION_MATCH
NO_ENDPOINT_TERM_IN_MASS_IDENTITY
H2_LABEL_COLLISION
SHA_LOCK_AUDIT_PARTIAL
CONCRETE_SPECIALIZATION_MISMATCH
ZETA_RAW_POLE_VALUE_MISMATCH
T4_FALSE_AS_STATED
T5_FALSE_AT_s_EQ_1_OVER_2
```

## 1. Audit 011

### Formula

The project dictionary fixes

\[
h_\lambda=
\frac{I_{4,\lambda}h_{0,\lambda}-I_{0,\lambda}h_{4,\lambda}}
{\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2}}.
\]

This appears in `D0_5_GROUND_AND_TRIAL_TYPES.md:55-69` and
`PEN_3_3_G04_OBJECT_DICTIONARY.md:79-104`. The primary excerpt itself only
states uniqueness up to nonzero scale; the normalized formula is the locked
project definition. The Stage-2 Lean object remains a free parameter and does
not construct this packet.

Verdict: `HTRIAL_FORMULA_ACCEPTED` as the canonical project object.

### Mass

The modes are even and supported on `[-lambda,lambda]`. Hence

\[
\int_0^\infty h_{n,\lambda}(v)\,dv=\frac12I_{n,\lambda}
\quad(n=0,4),
\]

and substitution gives

\[
\int_0^\infty h_\lambda(v)\,dv=0.
\]

This is an exact algebraic identity. It is not a grid observation.

Verdict: `HTRIAL_MELLIN_MASS_ZERO_CONFIRMED`.

Do not call this `H2_ZERO_CONFIRMED`. In the object dictionary, `H2-ZERO`
means `h_lambda(0)=0`, and that condition is explicitly false; the selected
branch is `H2-POLE/CORRECTION`. The two meanings must not share one code.

### Measure and Jacobian

The source integral `integral_R h_lambda(x) dx` and

\[
A_m=\int_0^\infty hTrial_m(v)\,dv
\]

use the same additive coordinate. The letter change `x -> v` is not a change
of variables. Evenness contributes the factor `1/2`. No `du/u` measure and no
Jacobian occur at this stage. The multiplicative measure appears only after
applying `E_star`.

Verdict: `MEASURE_CONVENTION_MATCH`.

### Endpoint terms

Midpoint values at `+-lambda` are a finite set and do not alter the Lebesgue
mass identity. There is no endpoint term in the mass calculation.

They do matter for pointwise `E_star` values at comb teeth. A later exact
Poisson or boundary identity must retain the half-weight.

Verdict: `NO_ENDPOINT_TERM_IN_MASS_IDENTITY`.

### Mellin domain and support regularity

The concrete positive-half packet is supported in `[0,lambda]`, not in
`[a,b]` with `a>0`. It generally has `h_lambda(0) != 0`. Therefore its Mellin
transform is naturally analytic on `Re w > 0`, not entire.

The midpoint zero extension has a jump at `lambda`; it is not globally
Lipschitz or `ContDiff` on `R`. A concrete consumer needs an interior
Lipschitz/BV hypothesis plus one boundary-cell estimate.

Verdict: `CONCRETE_SPECIALIZATION_MISMATCH` for the v1 standalone setup.

### SHA audit

The archive reproduces and matches the listed hashes for:

```text
D0_5_GROUND_AND_TRIAL_TYPES.md
PEN_3_3_G04_OBJECT_DICTIONARY.md
D0KTrialStage2.lean
EStarWindowedMellinCrosswalk.lean  (against report 012)
```

The archive contains only excerpts, not the full `fulltext.md`, and does not
contain the listed Stage-3 file or the older Proshka crosswalk file. Their
full-file hashes cannot be independently rechecked from this pack.

Verdict: `SHA_LOCK_AUDIT_PARTIAL`. This does not affect the mass algebra,
which uses the verified dictionary and evenness excerpt.

## 2. Audit of T1--T5

| Target | Verdict | Reason |
|---|---|---|
| T1 | viable | finite support kills the right tail; compact-away-from-zero parameter integral is holomorphic |
| T2 | viable after boundary repair | zero mass plus Riemann-sum error gives a bounded sum; the concrete midpoint packet requires one terminal boundary cell, not global Lipschitz |
| T3 | viable | `Estar(u)=O(sqrt u)` gives local domination `u^(Re s-1/2)` and log-weight domination for derivatives |
| T4 | false as written | the raw Mathlib function `zeta(w)*M(w)` has the wrong assigned value at `w=1` in general |
| T5 | false at `s=1/2` | the identity theorem continues the removable extension, not the raw point value |
| PL | viable | a positive triangular bump gives sums bounded below by `c*k` along `u=1/k` |

The absolute-region theorem in `EStarWindowedMellinCrosswalk.lean` does not
actually use zero mass: its proof binds and immediately clears `hmass`.
Zero mass becomes load-bearing only for the left-tail bound and pole removal.

## 3. Fatal planted counterexample to T4

Let

\[
\phi(t)=\max(1-4|t|,0),
\qquad
h_0(v)=\phi(v-5/4)-\phi(v-9/4).
\]

Then `h0` is globally Lipschitz, compactly supported away from zero, and

\[
M_{h_0}(1)=\int_0^\infty h_0(v)\,dv=0.
\]

But

\[
M_{h_0}'(1)
=
\int_{-1/4}^{1/4}
\phi(t)
\bigl(\log(t+5/4)-\log(t+9/4)\bigr)\,dt
<0.
\]

Since

\[
(w-1)\zeta(w)\to1,
\]

we have

\[
\zeta(w)M_{h_0}(w)\to M_{h_0}'(1)\ne0
\quad(w\to1,\ w\ne1).
\]

At `w=1`, however, the raw pointwise product equals

\[
\operatorname{riemannZeta}(1)\,M_{h_0}(1)=0.
\]

Thus the raw product is not even continuous at `1`. T4 cannot compile because
its mathematical statement is false, not merely because an API is missing.

Consequently T5 is false at `s=1/2` for this class.

## 4. Weakest repair

Define the removable extension

```lean
noncomputable def ZetaMellinReg (w : C) : C :=
  if w = 1 then deriv (Mellin h) 1
  else riemannZeta w * Mellin h w
```

and prove:

1. `ZetaMellinReg` is analytic on `Re w > 0`;
2. it equals the raw product for `w != 1`;
3. the continued window identity uses `ZetaMellinReg (s+1/2)`;
4. a raw-product corollary is stated only under `s != 1/2`.

For the concrete packet, replace support-away-from-zero/global-Lipschitz by:

```text
support in [0,b]
Lipschitz on [0,b) or bounded variation
one explicit midpoint boundary-cell budget
Mellin analytic on Re w > 0
```

## 5. Operational directive

Do not send v1 to Aristotle unchanged.

Use the repaired task:

```text
/mnt/data/ARISTOTLE_TASK_EStarMuntzContinuation_v2_REPAIRED.md
```

The first intended proof target is the regularized zeta--Mellin product. The
identity theorem itself has a suitable Mathlib API; it is not the current
mathematical blocker.
