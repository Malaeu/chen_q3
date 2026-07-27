# SOFT_0 — PRO VERDICT (Proshka V1) — 2026-07-12

Status: `EXTERNAL_VERDICT_TRANSCRIPT_VERBATIM / AUTHORITY_FOR_SOFT_0_GATE / NOT_RH`
Channel: V1 (Proshka, breaker, kill+repair mandate).
Provenance: owner-pasted transcript, materialized to repo by Mythos (V2) so the
SOFT_0 gate can consume it FROM DISK. No browser access needed or permitted
for this gate. This file is the single authority for SOFT_0 codes and the
SoftSubsequenceZeroEscape theorem statement/proof.

---

## TOP-LEVEL STATUS

```text
Route B-soft:            REFUTED_AS_STATED
Repaired abstract closure: CONDITIONAL_VALID
RH:                      NOT_RH
Route score:             4/5
Progress class:          FALSIFICATION_PROGRESS
```

Main conclusion: the soft subsequence roof is mathematically possible, but the
original statement (H2a_cofinal AND S1 AND S2 AND roof => RH) does not
type-check: it omits H1/H2b, uses a problematic sup-normalization, and can hide
RH entirely inside S2.

## 1. ATTACK ON S1 (sup-normalization) — KILL AS STATED

If "sup-normalized" means F_j^(K') := Ghat_j / ||Ghat_j||_{L^inf(K')}, then
sup_{K'} |F_j^(K')| <= 1 is true BY DEFINITION — a choice of scale, not an
analytic estimate. Different K' give different families; diagonal limits on
different compacts can differ by factors; no single holomorphic strip limit
follows. Also redundancy: if S2 already asserts a locally-uniformly convergent
subsequence, S1 is decoration; if S2 only identifies cluster points, S1 is
needed only as Montel compactness.

WEAKEST REPAIR: replace S1 by an independent statement
  for all K compactly contained in S: sup_j sup_{z in K} |F_j(z)| < infinity,
with F_j normalized ONCE and canonically, best via a fixed anchor point
z_* in S with F_j(z_*) = Xi(z_*) != 0. Then: local boundedness gives a normal
family; the fixed nonzero value forbids the identically-zero cluster point;
the normalization is compatible with all compacts.

```text
FAIL:     SOFT_S1_SUPNORM_TAUTOLOGY
REPAIRED: S1_CANONICAL_NORMAL_FAMILY
```

## 2. ATTACK ON ROOF 3.3' AND LEMMA T — REFUTED UNTIL EXACT BODIES SHOWN

The existing Corollary 3.3 consumes the full H1–H4; it cannot be "amputated"
by renaming hypotheses (its proof first gets locally-uniform convergence from
H3+H4, then applies Rouche against H2). The soft route needs TWO separate
theorems.

REQUIRED FINITE ROOF (exact form):
  H2a(j) => [ F_j in O(S)  AND  Z(F_j) intersect S subset R ].
Allowed dependencies (upstream only): D0, exact finite operator, exact ground
eigenvector, exact transform, exact normalization, H2a.
FORBIDDEN dependencies: H3, H4, S1, S2, convergence to Xi, absence of
off-critical zeros, RH. If the roof uses H4 the cycle
roof <- H4 <- soft closure <- roof is FATAL for the amputation.

REQUIRED LEMMA T (subsequence form), with proof: Let F_{j_k} be holomorphic in
a connected strip S, with no zeros in S \ R, and F_{j_k} -> F locally
uniformly, F not identically 0. Then F has no zeros in S \ R.
Proof: on any disc D compactly inside S \ R the F_{j_k} are nonvanishing; by
Hurwitz the limit is either nonvanishing on D or identically zero on D; the
latter would force F == 0 on the connected strip, excluded. This lemma needs
no H4, no full sequence, no quantitative rate.

Current kill: in the available ledger H2b is only CONDITIONAL_ON_H2a; no
closed roof body exists yet.

```text
FAIL:           SOFT_ROOF_BODY_MISSING
FATAL IF FOUND: SOFT_ROOF_H4_DEPENDENCY_CYCLE
PASS SIGNATURE: H2A_TO_REAL_ZERO_APPROXIMANT_POINTWISE
```

## 3. ATTACK ON S2 (identification) — MAIN WALL; DEFAULT REFUTED

Target form F = c * Xi * gamma, c != 0, gamma in O(S), gamma nowhere zero, is
logically sufficient (same zero divisor in the strip). BUT the most dangerous
RH-renaming lives here:

CRITICAL PLANT: one may NOT define gamma := F / (c*Xi) after obtaining F and
then demand gamma be zero-free. "F/(c*Xi) holomorphic and nowhere zero"
already says F and Xi share the zero divisor; since F has only real zeros this
IS the RH conclusion. Therefore gamma must be: defined BEFORE proving S2;
derived from the completion/transform dictionary; proved holomorphic and
zero-free independently of the location of Xi's zeros.

LEGAL identification, exactly two variants:
  Variant A (interval identity): if for an open interval I subset R∩S it is
  proved that F(x) = c*Xi(x)*gamma(x) for all x in I, the identity theorem
  extends the equality to the strip.
  Variant B (Vitali): if (1) the family F_j is locally bounded; (2) on a set
  E subset S WITH A LIMIT POINT exact pointwise convergence
  F_j(x) -> c*Xi(x)*gamma(x) is proved; (3) the right side is holomorphic —
  then Vitali gives locally-uniform convergence.
NOT admissible: finitely many points; values only at the first zeros;
numerical fit; agreement at m=13,14,53,101; discrete sets without a finite
accumulation point.

BFM FIREWALL: the modulus-square second moment over zero values is an
RH-conditional import and may not enter the concluding chain. Only the
unconditional explicit formula is allowed — prime/Gamma side, or the full
symmetric zero-sum without assuming all zeros have the form 1/2 + i*gamma.

Weakest legal S2: there exist j_k, F, c != 0, gamma in O(S)^x such that
F_{j_k} -> F locally uniformly and F(x) = c*Xi(x)*gamma(x) for all x in I,
where gamma is source-locked independently, the interval identity comes from
the unconditional explicit formula, and no BFM/modulus-square/critical-line-
only formulas are used.

```text
FAIL: SOFT_S2_RH_CONDITIONAL_IMPORT
FAIL: SOFT_GAMMA_POSTHOC_QUOTIENT
PASS: UNCONDITIONAL_CLUSTER_POINT_DIVISOR_IDENTIFICATION
```

## 4. ATTACK ON OffAxisGrowthProbe — NONDECISIVE

Data 0.0029 +/- 0.0003 at threshold 0.03, cells m=13,14,53,101. Problems:
four points give no asymptotic theorem (late regime change, log growth, rare
spikes, N-dependence, subsequence instability); y <= 0.4 does not control the
strip boundary |Im z| = 1/2 (growth may deteriorate on 0.4 < |Im z| < 0.5,
and no boundary-distance dependence of the constant is proved); low zeros do
not control the high-frequency tail (truncation, cancellation tail, completion
error); COMPLETION-FACTOR DEPENDENCE: multiplying by e^{az} or e^{az^2}
changes measured off-axis growth without creating zeros, so the slope is NOT
invariant under F ~ F*gamma with gamma in O(S)^x — until completion factor and
normalization are locked, 0.0029 has no canonical meaning.

Legal role: if slope robustly EXCEEDS 0.03 the route/calibration is
falsified; if below, "no obvious sampled blow-up detected" — no theorem
follows. A contentful falsifier needs: canonical completion; central
normalization; dozens of cofinal (m,N); windows y_max up to 1/2; several zero
cutoffs; precision escalation; interval/error ledger; leave-one-out stability.

```text
CURRENT CODE: OFF_AXIS_PROBE_NONDECISIVE
NOT:          S1_NUMERICALLY_PROVED
```

## 5. SUP-NORMALIZATION VS CENTRAL — REMOVE SUP

Three modes, all bad: per-K' normalization (no single global family);
normalization on growing K'_j (peak can escape to the boundary while
F -> 0 on every fixed inner compact: collapse along a subsequence); global sup
over the strip (may be infinite or not attained).

WEAKEST REPAIR: fixed central calibration F_j(z) := Ghat_j(z) /
(Ghat_j(z_*) / Xi(z_*)) with proved Xi(z_*) != 0 and Ghat_j(z_*) != 0, so that
F_j(z_*) = Xi(z_*) != 0 — kills zero-limit collapse automatically. If z_* = 0
is already the source-locked central calibration, use exactly it. If the
central value can vanish, use a fixed nonzero continuous functional
ell(F_j) = 1.

```text
FAIL: SOFT_SUP_NORMALIZATION_INCOHERENT
PASS: CENTRAL_ANCHOR_NORMALIZATION_LOCKED
```

## THE WEAKEST CORRECT SOFT THEOREM — SoftSubsequenceZeroEscape (PROVED HERE)

Let S = { z in C : |Im z| < 1/2 }. Let F_j in O(S). Assume:
  (1) Real-zero roof: Z(F_j) ∩ S subset R for all j of the chosen sequence.
  (2) Canonical nonzero normalization: there is z_* in S with
      F_j(z_*) = a_* != 0.
  (3) Local normality: for all K compactly in S,
      sup_j ||F_j||_{L^inf(K)} < infinity.
  (4) Unconditional cluster identification: there is a subsequence j_k with
      F_{j_k} -> F locally uniformly and F = c*Xi*gamma, c != 0,
      gamma in O(S)^x.
Then RH holds.

Proof: canonical normalization gives F(z_*) = a_* != 0, so F is not
identically 0. Each F_{j_k} has no zeros in S \ R; by Hurwitz the nonzero
locally-uniform limit F also has none there. Since c != 0 and gamma is nowhere
zero, Z(F) = Z(Xi) in the strip; hence all zeros of Xi in S are real; by the
classical interface this is RH. QED.

This is a PROVED CONDITIONAL ROOF. It does not prove its hypotheses.

## SUMMARY OF THE FIVE ATTACKS

```text
1. S1:    KILLED AS TAUTOLOGICAL under sup-normalization.
          Repair: canonical normalization + independent local bound.
2. Roof:  abstract subsequence Hurwitz roof VALID (proved above);
          existing project roof unusable if it consumes H4;
          physical theorem body still missing.
3. S2:    MAIN UNRESOLVED WALL. Valid only with unconditional,
          independently defined zero-free gamma. Post-hoc gamma = quotient
          is RH repackaging.
4. Probe: NONDECISIVE. Falsifier/calibration only.
5. Norm:  sup-normalization rejected; central anchored normalization required.
```

## FINAL PROPOSAL

Do not declare Route B-soft a new branch before one paper gate:

  SOFT_0_RoofAndS2Typecheck

It must return EXACTLY ONE code:

```text
SOFT_SUBSEQUENCE_CLOSURE_TYPED
SOFT_ROOF_H4_DEPENDENCY_CYCLE
SOFT_S2_RH_REPACKAGING
SOFT_NORMALIZATION_INCOHERENT
SOFT_EXPLICIT_FORMULA_CONDITIONAL
```

Cheap decisive test: (1) delete S1; (2) ask whether S2 already contains the
existence of a locally-uniform cluster point; (3) if yes, S1 is decoration;
(4) then check whether gamma is defined independently of F/Xi. If gamma is
post hoc, the route is killed immediately.

STRONGEST ATTACK (reviewer's sharpest objection): "You did not prove the
weaker limit identification. You defined the zero-free factor as the quotient
between the limit and Xi, and its zero-freeness IS the claim that Xi has no
extra non-real zeros." If this happens: SOFT_S2_IS_RH_REPACKAGING — fatal.

META: the soft route compressed to ONE real question — can the divisor of one
cluster point be identified UNCONDITIONALLY with the divisor of Xi? Killed:
sup-bound as content; four probe points as asymptotics; reuse of the old
H1–H4 roof; post-hoc zero-free completion factor. Preserved: one nondegenerate
subsequence + zero-divisor identification => RH, without quantitative H4.

NOT_RH.
