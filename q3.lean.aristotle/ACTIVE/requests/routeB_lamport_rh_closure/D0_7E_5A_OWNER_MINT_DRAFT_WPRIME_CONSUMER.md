# D0.7e.5a — OWNER MINT DRAFT: nontautological WPrime consumer definition

Status: `R3_MINT_MENU_FALSIFIED / NO_VARIANT_RATIFIABLE / 5A_BLOCKED_NON_CRITICAL_PENDING_SOFT_0 / NOT_RH`
Revision: R1 (2026-07-12, V2 SELF-CORRECTION). Codex battery run caught a type
defect in R0: canonical `sTrial` is a POSITIVE SCALAR (D0.5/D0.7b norm
normalizer), not a vector; the trial VECTOR is `kTrial` (persisted as `k1`).
All operator applications below now use `kTrial`. Scored as V2 miss per K6;
Codex's strict-text FAIL verdict on R0 stands and is preserved in its report.
Revision: R2 (2026-07-12, V2 SELF-CORRECTION). Codex caught an algebraic
defect in R0/R1 §5 P2: the alpha-slot value had the gap in the denominator.
From WPrime^2*DeltaE=|b|^2*lambda*alpha with WPrime^2=lambda*||rVec||^2 the
correct probe is alpha_probe = ||rVec||^2*(mu3-mu1)/|b|^2 (gap in the
NUMERATOR). The orientation ratio |bCal|^4 is unaffected. Second V2 miss
scored publicly per K6.
Revision: R3 (2026-07-12, OWNER-DIRECTED MENU CLOSEOUT). The executed battery
falsifies both menu entries: Variant A's registered exact 5c equality misses
by closure ratios about 1e-102 (and 1e-112 on the third cell), while Variant B
fires `SLOT_VACUITY`. The menu is now `MINT_MENU_FALSIFIED`; no §7 utterance
can activate A or B. D0.7e.5a stays BLOCKED and receives only the scheduler
marker `NON_CRITICAL_PENDING_SOFT_0`.
Author channel: Claude-PRO (V2), acting as pen-drafter only.
Authority note: per `OWNER_STANDING_ORDER_RATIFICATION_2026-07-12.md` (Limits),
minting a NEW consumer definition is owner-only and non-delegable. This file is
a DRAFT MENU. It becomes a source only after the owner utterance in §7 is
physically recorded. Until then Codex MUST NOT close D0.7e.5a on its basis.

Companion verdict: `D0_7E_5A_PRO_VERDICT.md` (V2, fail-closed UPHELD on
external grounds; no independent consumer exists in literature or pinned
snapshot; owner mint is the unique unblocking move).

## 0. Structural trap analysis (why the previous owner formula was rejected,
##    and why the symmetric trap must also be avoided)

Rejected form (from `D0_7E_5_PRO_REVIEW_DECISION.md`):

```text
WPrime_(m,N) := |bDet_(m,N)| sqrt(lambda_m) sqrt(alpha_(m,N)/DeltaEfin_(m,N))
```

fires `D0_7E_TAUTOLOGY`: WPrime defined by the desired RHS makes the 5c
identity `WPrime^2 * DeltaE = |bW|^2 * lambda * alpha` empty.

Symmetric trap: ANY mint of WPrime that mentions `alpha` or `DeltaE`
re-tautologizes 5c from the other end, because `alpha` is itself still
unminted (`PO-1/A1` = `H0_A1_ALPHA_DEFINITION_MISSING`, OPEN_CRITICAL) and
`DeltaE`-true is downstream (H4c). A well-posed mint must therefore be built
ONLY from already-locked D0 objects:

```text
allowed alphabet: Mfin_(m,N) (D0.3g), mu_k spectral data of Mfin (D0.3g),
                  sTrial_(m,N) (D0.5/D0.7b), deltaVec_(m,N) (D0.7a),
                  xi ground vector (D0.5), lambda_m, L_m (D0.1),
                  Fhat, bCal=bDet, G (D0.7e.2/3), parity sectors (D0.4).
forbidden alphabet in the mint: alpha, DeltaE-true, filter F, kappa,
                  N(lambda) selector, any H3c/H4 theorem.
```

Consequence: after the mint, 5c changes epistemic class from
`DESIRED_IDENTITY` to `FALSIFIABLE_THEOREM_CANDIDATE` relating four
INDEPENDENTLY defined objects (WPrime: minted here; bW: oriented here;
alpha: to be minted in A1, NOT here; DeltaE: H4c). This is the only
architecture in which `D0_7E_TAUTOLOGY` and `D0_7E_SLOT_VACUITY` are both
structurally impossible.

## 1. Variant A (recommended): spectral residual amplitude

Q1 (independent approximant consumed): the ALREADY-PROVED normalized object

```text
FZeo_(m,N) := G_(m,N) = Fhat_(m,N) / bCal_(m,N),   G_(m,N)(0) = Xi(0)
```

on `CentralValueNonzero` (D0.7e.3, PROVED). No new approximant is invented;
the historical `FZeo` slot is filled by G under an explicit crosswalk line.

Q2 (WPrime definition BEFORE any desired inequality):

```text
rVec_(m,N)   := (Mfin_(m,N) - mu1_(m,N) Id) kTrial_(m,N)        (residual vector)
WPrime_(m,N) := sqrt(lambda_m) * || rVec_(m,N) ||_{H_lambda}
```

where `kTrial_(m,N)` is the canonical unit trial VECTOR (persisted coefficient
vector `k1`; e.g. `out/portable_k_coeffs_lambda_sq_*.json`), and the scalar
`sTrial` of D0.7b is NOT used in this definition.

Both factors are pure D0 objects. The sqrt(lambda_m) prefactor is traced to
the canonical target shape `docs/ROUTE_B_THEOREM_CONTRACT_v2.md:28-29` as the
unique lambda-homogeneity that makes the 5c candidate identity
dimensionally closed (derivation-fixed, not outcome-fixed; see §5 plants).

Q3 (b orientation): `bW := bCal_(m,N) = Fhat(0)/Xi(0)` (amplitude ratio, NOT
the normalizing multiplier bCal^(-1)). Rationale: WPrime measures the RAW
detector residual; the normalized side already carries bCal^(-1) inside
G = FZeo. Choosing bCal here keeps the pair (raw residual, normalized
approximant) in exact inverse balance and preserves
`D0_7E_BCAL_INVERSE_NORMALIZER_IDENTITY_LOCKED`. Registered as a prediction,
falsifiable pre-mint (§5, plant P2).

Q4 (nonzero domain): `SpectralResidualLocus := CentralValueNonzero`
(= BDetNonzero = FhatAtZeroNonzero = BCalNonzero; the audit already proved
TrialNonzero is insufficient). If mu1 is degenerate on some (m,N), that cell
is excluded by the existing simple-ground typing (D0.5); no new selector.

Q5 (classification): `OWNER_RATIFIED_NEW_DEFINITION`; locator = this file +
owner utterance sha (§7).

Downstream shape of 5c (NOT part of the mint; becomes the theorem to prove):

```text
WPrime_(m,N)^2 * DeltaE = |bCal_(m,N)|^2 * lambda_m * alpha    (5c-candidate)
```

By the spectral theorem, `||rVec||^2 = sum_{k>1} (mu_k - mu1)^2 |<sTrial, xi_k>|^2`,
so the 5c-candidate CONSTRAINS the future A1 mint of alpha: exact equality on
the two-level (rank-2 spectral) reduction, Temple-type inequality with an
explicit constant in general. That constraint is a pre-registration for A1,
not a definition of alpha (firewall respected).

## 2. Variant B (alternative): central determinant value

Q1: `FZeo_(m,N) := G_(m,N)` as in Variant A.
Q2:

```text
WPrime_(m,N) := | detreg_(m,N) |,  where detreg is the finite regularized
determinant central value with the CCM-shape identity
detreg(Dlog_(m,N) - z) = -i lambda^(-iz) xihat_(m,N)(z) evaluated at z=0,
so |detreg| = |xihat(0)| = sqrt(L_m) |c0(k1_(m,N))|.
```

Q3: `bW := bCal^(-1)` (normalizing multiplier), since here WPrime already IS a
central amplitude and the identity must divide it back out.
Q4: `CentralValueNonzero`. Q5: `OWNER_RATIFIED_NEW_DEFINITION`.

Cost of B relative to A: (i) WPrime collapses to a rescaling of |bCal| itself
(`|detreg| = |bCal| * |Xi(0)|`), so the 5c identity degenerates to a
constraint between alpha and DeltaE ONLY — high `D0_7E_SLOT_VACUITY` risk,
exactly the failure the Pro review pre-registered; (ii) it imports the CCM
determinant identity, which for the project carrier is a transfer assumption
(Mellin conventions) not yet source-locked. Variant B is retained only as a
falsification control for Variant A, not as a co-equal candidate.

## 3. Firewall audit (both variants)

- Not defined by desired RHS: PASS (A: residual norm; B: determinant value).
  No `alpha`, no `DeltaE` in either definition line.
- No bCal / bCal^(-1) aliasing: PASS — orientation is EXPLICIT per variant and
  opposite between variants; the pair (A,B) is itself an alias detector.
- Not sourced from Contract v2 / alpha-demand audit / FIT diagnostics: PASS —
  those documents supply only the lambda-homogeneity trace (shape), never the
  defining line.
- No H3c/H4 import into D0: PASS — Mfin spectral data are finite D0.3g
  objects; DeltaE-true and tracking statements stay in H4c/H3e.
- No new selector: PASS — both indices (m,N) free; loci are the already-locked
  dependent loci.
- Self-citation: this draft cites only repo-locked artifacts and the owner
  utterance; V2 verdict is referenced as context, not as mathematical source.

## 4. What closes and what does NOT close upon ratification

Closes: D0.7e.5a (consumer name + WPrime definition + b orientation + domain,
all four Q-slots answered with class OWNER_RATIFIED_NEW_DEFINITION).
Opens/unblocks: D0.7e.5c as `FALSIFIABLE_THEOREM_CANDIDATE` (prove the 5c
identity — or its Temple-inequality repaired form — from the mint + future A1).
Does NOT close: D0.7e.5c, D0.7e.5e, D0.7e, D0.7, PO-1/A1,
PO_XWALK_UNIFORM_EVAL, H3e. `NOT_RH` unchanged.

## 5. Pre-mint falsifier battery (K1/K2: judge before player; run BEFORE §7)

Numerical probes on the persisted cells (13,90), (13,120), (14,120) — and
(17,120) once its coefficient vector is persisted — float64, no dps escalation:

- P1 (two-level exactness): project onto span{xi_1, xi_3}; verify
  `||rVec||^2 = (mu3-mu1)^2 |<kTrial,xi_3>|^2` to machine precision.
  Registered prediction: PASS, residual < 1e-12 relative.
- P2 (orientation kill-switch): substitute bCal -> bCal^(-1) in the
  5c-candidate with the natural alpha-slot value alpha_probe :=
  ||rVec||^2 * (mu3-mu1) / |b|^2 computed for EACH orientation; the two
  probes must differ by the factor |bCal|^4. If |bCal| is within 10x of 1 on
  all probed cells, orientation is ZERO_CONSISTENT-undecidable numerically
  and Q3 must be decided by the derivation trace alone (this outcome is
  itself informative and must be logged, not hidden).
- P3 (variant-B vacuity plant): compute the B-version 5c-candidate; verify it
  reduces to a relation containing NO WPrime degree of freedom (planted
  SLOT_VACUITY must fire). If it does NOT fire, Variant B is stronger than
  assessed and the ranking A>B must be re-opened.
- P4 (lambda-homogeneity): rescale m across available cells; log-log slope of
  WPrime_A vs lambda_m must be consistent with the sqrt(lambda) prefactor
  within the two-cell lever arm (FIT_NOT_LAW discipline: slope is a
  consistency probe, never a proof).

Any FATAL here is reported as the sprint result and the mint menu is revised;
plants passing does not prove the mint, it only licenses ratification.

## 5A. R3 closeout (normative; supersedes the A/B menu)

The R2 battery is the judge for the R3 decision.

```text
MINT_MENU_FALSIFIED
Variant A: FALSIFIED_EXACT_EQUALITY
Variant B: FALSIFIED_SLOT_VACUITY
MINT_ACTIVATED: false
D0.7e.5a: BLOCKED / NON_CRITICAL_PENDING_SOFT_0
```

For Variant A, the natural registered two-level Rayleigh-alpha closure ratios
are

```text
(13,90)  6.9411616936599094e-102
(13,120) 4.907478950456342e-102
(14,120) 2.50509212816158e-112,
```

not one. The separate inverse/direct ratio `|bCal|^4` is algebraically true
for both orientations and therefore does not validate the proposed exact 5c
identity. For Variant B the planted reduction removes every independent
WPrime degree of freedom, so `SLOT_VACUITY` fires exactly as registered.

Sections 1--4 remain an immutable design-history record. Sections 6--7 are
inert historical pipeline text: neither variant is eligible for owner minting
after R3. A future mint requires a new physical definition and a new menu; it
cannot reuse this file's A/B templates.

## 6. Post-ratification pipeline (no-stop compatible)

1. Codex records utterance + sha in STATE.json (idempotent, like the standing
   order record), sets D0.7e.5a -> PROVED_BY_OWNER_MINT with this file as
   proof_evidence, activity moves to D0.7e.5c.
2. D0.7e.5c is retyped `FALSIFIABLE_THEOREM_CANDIDATE`; its proof obligations
   are (i) the finite spectral identity/inequality from §1, (ii) the alpha
   pre-registration constraint forwarded to PO-1/A1 as an ACCEPTANCE TEST for
   the future alpha mint (not as its definition).
3. H3e wording is untouched; PO_XWALK_UNIFORM_EVAL stays OPEN_CRITICAL.
4. Marker: nodes built on this mint carry `OWNER_MINT_2026-07-12` (full owner
   authority, no CONDITIONAL_ON_STANDING_ORDER marker needed; revert path =
   owner revocation utterance).

## 7. Owner ratification block (SUPERSEDED BY R3; templates inert)

The following block is preserved only as pre-R3 history. It is not executable
after `MINT_MENU_FALSIFIED`.

```text
OWNER UTTERANCE (template, choose exactly one):
  "Минчу вариант A из D0_7E_5A_OWNER_MINT_DRAFT_WPRIME_CONSUMER.md —
   запиши utterance и sha."
  "Минчу вариант B из D0_7E_5A_OWNER_MINT_DRAFT_WPRIME_CONSUMER.md —
   запиши utterance и sha."
  "Гони pre-mint falsifier battery (§5) до минта."
RECEIVED_AT: <timestamp>
DRAFT_FILE_SHA256: <sha of this file's pre-ratification bytes>
```

NOT_RH.
