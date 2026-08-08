# PROSHKA REQUEST — Goal 057 B3.0E source archimedean pairing / CCM-WR sign-normalization crosswalk

## 0. Requested decision

Choose exactly one operative next atom after proved B3.0D:

`GOAL057_B3_0E_SOURCE_ARCHIMEDEAN_PAIRING_CCM_WR_SIGN_NORMALIZATION_CROSSWALK`

The source audit fixes the intended endpoint as

```lean
sourceArchimedeanModePairing i n r =
  -(ccmWREntry (L_m i) n r : ℂ)
```

but the repository has no theorem connecting the two representations.

Candidates:

1. `TRY_GOAL057_B3_0E_DIRECT_CCM_WR_CROSSWALK` — release the displayed
   equality as one production atom only if the existing Lean API already
   carries every analytic interchange and source representation needed.
2. `TRY_GOAL057_B3_0E_ARCH_MULTIPLIER_TO_ONE_SIDED_WR_PREFLIGHT` — preferred:
   release only the smallest source-exact analytic preflight that converts the
   digamma frequency multiplier to CCM's one-sided regularized `W_R` kernel,
   explicitly exposing all Fubini and integrability obligations.
3. `WALL_GOAL057_B3_0E_SOURCE_ARCH_CCM_WR_BRIDGE_MISSING` — if neither can be
   honestly materialized, name the first missing theorem and the smallest
   repaired atom.  Do not replace it by a premise-only wrapper.

Return one `TRY_`, `KILL_`, or `WALL_` primary code.  This is one
`DELEGATED_STRATEGIC_REVIEW` in the same living Goal-057 phase and chat.  It is
not an owner boundary.

## 1. Immutable control state

```yaml
repo: /Users/emalam/GitHub/rh_lean_01_2026
branch: rh_clean
head: 46977cd50d93daa9ed25060dc7c5eb9dfd2e7351
origin_rh_clean: 46977cd50d93daa9ed25060dc7c5eb9dfd2e7351
active_goal: 057
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
aristotle_submission: NONE
route_promotion: false
px_rh_claim: NOT_MADE
owner_gate: PX_RH_CLAIM_ONLY
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
parent_request_message_id: 9727f4db-959d-4931-adb4-25f9a3865967
parent_response_message_id: 25c55fce-899f-4a41-8e93-d61533dbd4f4
```

Do not create Bus 010, decrement the ten-checkpoint ledger, invoke H4a1b,
promote Route B, or claim RH.

## 2. Closed parent B3.0D

Production file:

`Q3/Proofs/RouteB/D0PstarSourceArchModePairingKernel.lean`

SHA-256:

`02a382679fd1f401141d1e5c1ba6b3967fe5a10271281a4bc7b86daf3d620974`

Exact public surface:

```lean
noncomputable def sourceArchimedeanModePairing
    (i : PairIndex) (n r : ℤ) : ℂ :=
  ∫ t : ℝ,
    conj (𝓕 (logWindowZeroExtendedMode i n) t) *
      (sourceArchimedeanMultiplier t : ℂ) *
      𝓕 (logWindowZeroExtendedMode i r) t

theorem sourceArchimedeanModePairing_conj_symm
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i r n =
      conj (sourceArchimedeanModePairing i n r)
```

B3.0D is compiled, fully validated, committed, and pushed.  It proves only
the fixed-mode kernel and Hermitianity.  B3.0 remains open and the coarse
ledger remains 0/10.

## 3. Primary-source sign and coordinate audit

Primary source:

Connes--Consani--Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1:

https://arxiv.org/html/2511.22755v1

The source fixes:

```text
U_n(x) = L^(-1/2) exp(2*pi*i*n*x/L)
W_R = -W_infinity
W_infinity(F) = integral Fhat(s) * 2*theta'(s)/(2*pi) ds
QW = W_0,2 - W_R - sum_p W_p
```

and its equation (4.4) is exactly the repository definition
`ccmWREntry L n r`.  The source form is antilinear in the first slot and
linear in the second.

The repository fixes Mathlib's cycles-frequency transform
`exp(-2*pi*i*x*t)` and

```lean
sourceArchimedeanMultiplier t =
  -Real.log Real.pi +
    Re (digamma (1/4 + I*(Real.pi*t)))
```

while the source has

```text
theta'(s) = (-log pi + Re digamma(1/4 + i*s/2))/2.
```

Hence

```text
sourceArchimedeanMultiplier(t) = 2*theta'(2*pi*t).
```

Under `s = 2*pi*t`, `ds = 2*pi*dt`; the source factor `1/(2*pi)` and the
Jacobian cancel.  Therefore the B3.0D integral is `W_infinity`, hence
`-W_R`, hence the predicted crosswalk is exactly

```lean
sourceArchimedeanModePairing i n r =
  -(ccmWREntry (L_m i) n r : ℂ).
```

There is no extra `2*pi`, transpose, or conjugation swap.  The minus sign is
load-bearing: the new kernel is the archimedean contribution occurring in
the full `QW`, whereas `ccmWREntry` names positive `W_R` before the full-form
subtraction.

This section is a source audit and requested target, not a Lean proof.

## 4. Exact repository inventory

Literal CCM file:

`Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean`

SHA-256:

`f2f9d248a6f2ad703428c624ccbaf5a75b340655e4b4ebbbe3f1d77355523815`

It defines:

```lean
noncomputable def ccmWREntry (L : ℝ) (n m : ℤ) : ℝ :=
  ccmQKernel L n m 0 / 2 *
      (Real.eulerMascheroniConstant +
        Real.log (4 * Real.pi * ((Real.exp L - 1) / (Real.exp L + 1)))) +
    ∫ x in Set.Ioc 0 L, ccmWRIntegrand L n m x

noncomputable def ccmWeilTauN1 ... :=
  ccmW02Entry ... - ccmWREntry ... - ccmPrimeEntryN1 ...
```

The exact source multiplier file is
`D0PstarExactArchSymbolLogDomination.lean`, SHA-256
`197daeed0b975bbed63cf59d2f0cfa939ed345661935d258f7e79387815344da`.
It already proves

```lean
sourceArchimedeanMultiplier t = -Q3.a_star t / (2 * Real.pi).
```

Four semantic-index queries plus exact `rg` inspection found no theorem in
Route B connecting `sourceArchimedeanMultiplier` or
`sourceArchimedeanModePairing` to `ccmWREntry`.

Mathlib provides Fourier integral definitions, sesquilinear exchange, and
`integral_conj`, but no ready theorem identifying the digamma multiplier
integral with CCM equation (4.4).  `Q3.DigammaRemainder` supplies a Stieltjes
representation for digamma, not the required hyperbolic one-sided kernel.

## 5. Why Candidate 2 is recommended

A direct crosswalk must justify all of the following, not merely algebraically
rewrite definitions:

1. the exact integral representation of
   `Re digamma(1/4+i*pi*t)-log pi` producing the CCM hyperbolic kernel;
2. absolute integrability needed to exchange frequency and source variables;
3. the Mathlib cycles-frequency versus source angular-frequency change of
   variables;
4. the correlation identity that converts the two zero-extended mode Fourier
   factors into `ccmQKernel`;
5. the endpoint constant and mandatory one-sided `1/2` term;
6. equality of the resulting `Ioc 0 L` integral with the totalized Lean
   definition `ccmWREntry`.

Candidate 2 should pin the smallest theorem whose conclusion is an actual
integral identity and whose hypotheses are provable for
`logWindowZeroExtendedMode`; it must not introduce a structure field saying
the desired equality as a premise.

Possible decomposition, for Proshka to correct or replace:

```text
B3.0E1  multiplier hyperbolic representation;
B3.0E2  weighted Fubini/integrability carrier;
B3.0E3  zero-extended mode correlation = ccmQKernel;
B3.0E4  one-sided WR assembly and final negative-entry wrapper.
```

If the first source theorem is absent from both Mathlib and the repository,
return the wall immediately with that exact fact.  Do not let later algebra
hide it.

## 6. Mandatory attacks

At minimum cover:

1. delete the final minus sign:
   `SOURCE_ARCH_CCM_WR_SIGN_MISMATCH`;
2. insert an extra `2*pi` or `(2*pi)^-1`:
   `SOURCE_ANGULAR_CYCLES_NORMALIZATION_MISMATCH`;
3. transpose `n,r` or move conjugation to the second slot:
   `SOURCE_FORM_INDEX_ORIENTATION_MISMATCH`;
4. omit the one-sided `1/2` endpoint term:
   `SOURCE_WR_SHARP_HALF_FACTOR_MISSING`;
5. use Fubini without an absolute-integrability carrier:
   `SOURCE_ARCH_FUBINI_CARRIER_MISSING`;
6. identify a distributional source formula with a Lebesgue integral by
   definition:
   `SOURCE_DISTRIBUTION_TO_DENSITY_BRIDGE_MISSING`;
7. replace the analytic theorem by a premise-only wrapper:
   `SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION`;
8. infer diagonal sign or full Weil positivity from the crosswalk:
   `SOURCE_ARCH_ENTRY_VALUE_OR_FULL_FORM_NOT_PROVED`;
9. promote fixed modes to uniform/cofinal control:
   `UNIFORM_COFINAL_MODE_BOUND_MISSING`;
10. import generated PSD/Step33 support:
    `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`.

All mutation artifacts remain outside production and are removed after test.

## 7. Required response schema

```yaml
STATUS: OPEN
PRIMARY: TRY_|KILL_|WALL_
SELECTED_CANDIDATE: 1|2|3
RELEASED_ATOM:
FIRST_MISSING_SOURCE_THEOREM:
OWNED_FILE:
EXACT_IMPORTS:
EXACT_PUBLIC_DEFINITIONS:
EXACT_PUBLIC_THEOREMS:
PRIVATE_SUPPORT_BUDGET:
SUCCESS_CODE:
STOP_CODE:
PLANTS:
PARENT_AFTER_SUCCESS:
NEXT_GAP_AFTER_SUCCESS:
COARSE_CHECKPOINTS_CLOSED_AFTER_SUCCESS: 0
COARSE_CHECKPOINTS_REMAINING_AFTER_SUCCESS: 10
PHASE_KEY_CHANGE: false
NEW_CHAT: false
OWNER_AUTHORITY_REQUIRED: false
```

Then give:

1. independent sign/normalization/index audit;
2. strongest attack against the predicted equality;
3. minimal Lean proof DAG with the first executable atom singled out;
4. exact semantic boundary after success;
5. smallest next atom, without silently authorizing later children.

## 8. Boundary

This request authorizes no production Lean edit.  Codex may implement only an
operative released `TRY_` atom.  It may not invent a source theorem, create a
premise-only surrogate, or treat the audited target as proved.  The sole owner
gate remains `PX_RH_CLAIM`; promotion and every RH statement remain forbidden.
