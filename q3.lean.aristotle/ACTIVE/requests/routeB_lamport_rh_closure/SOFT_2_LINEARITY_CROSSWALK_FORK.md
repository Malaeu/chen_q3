# SOFT_2 — LinearityCrosswalkFork (synthesis + fork contract)

Status: `FORK_POSED_BY_V2 / NOT_EXECUTED / NOT_RH`
Inputs: Codex `SOFT_1_..._2026-07-13.md` (type obstruction, phase falsifier,
code SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC) and Proshka round 3
(`SOFT_3_PRO_VERDICT_PROSHKA_TAILS_2026-07-13.md`).

## 0. The obstruction, stated once

The transform-side pairing P_I(Fhat_(m,N),phi) is LINEAR in kTrial
(kTrial -> e^{i theta} kTrial multiplies it by e^{i theta}); the entire
source-locked Weil corpus (Psi(h), h = f^* * g, QW, matrix entries) is
QUADRATIC/phase-invariant. Hence no theorem inside the current corpus can
identify the linear pairing with a prime/Gamma expression: identity (4.6) is
absent AT THE TYPE LEVEL, not merely unproved. Proshka's round-3 DAG
(3.1–3.4) presupposes a prime/Gamma decomposition of the LINEAR pairing and
is therefore CONTINGENT on resolving this fork first.

## 1. Three candidate crosswalks (exactly one must survive)

C1 FROZEN-SLOT POLARIZATION (linear route).
   Freeze the first Weil slot with a phi-built test f_phi (independent of
   kTrial); then h := f_phi^* * kTrial is linear in kTrial and
   Psi(h) = QW(f_phi, kTrial) is prime/Gamma-computable and linear.
   Obligation: exhibit f_phi and a proved identity relating QW(f_phi,kTrial)
   to P_I(Fhat,phi) — or to a modified target pairing that still feeds the
   distributional S2. KNOWN RISK (Proshka Attack B applies): the unconditional
   dual side of Psi is the FULL zero sum, so the natural identity lands on a
   zero-side distribution, not directly on the Xi-pairing; a separate
   target-identity step (3C class, route B1/B3) is then mandatory.
   Kill-shape: SOFT_TARGET_DISTRIBUTION_MISMATCH.

C2 QUADRATIC IDENTIFICATION + PHASE RIGIDITY (structure route).
   Replace the linear S2 by: (i) quadratic pairings
   <|H_(m,N)|^2, phi> -> |c|^2 <|Xi*gamma_0|^2, phi> on I (phase-invariant,
   possibly reachable inside the quadratic corpus), PLUS (ii) a structural
   phase theorem: the phase of H_(m,N) on I is fixed (e.g. H real-valued on
   R, or arg H = fixed linear function) by an exact symmetry of the packet
   (functional-equation / reflection symmetry of kTrial), so that |H| on I
   plus the anchor recovers H up to the fixed unit. Obligation: name the
   exact symmetry and prove the phase statement; then quadratic convergence
   + phase rigidity + continuity => linear identification.
   Kill-shape: no such symmetry (phase genuinely varies) — measurable NOW.

C3 THETA/MELLIN TARGET (representation route, Proshka B1).
   Bypass prime decomposition of the pairing entirely: identify BOTH sides
   as distributions via unconditional theta/Mellin representations —
   P_I(Fhat,phi) is already exact (4.2, transform side); express
   <Xi*gamma_0,phi> through the theta integral; prove convergence
   transform-side -> theta-side directly (kernel/heat-scale estimates, the
   Q3 log-Gaussian tail mechanism), with primes appearing only inside the
   unconditional theta/Mellin machinery.
   Kill-shape: the transform->theta comparison may secretly need the same
   uniform tail control (conservation of hardness) — but with fewer hiding
   places (no zero side at all).

## 2. Cheapest decisive test first (K2), registered

PHASE-STRUCTURE PROBE (feeds C2, one hour class, float64):
For cells (13,120),(14,120),(53,120),(101,120) compute
  theta_(m,N)(x) := arg H_(m,N)(x) on x in [gamma_1,gamma_11] (grid 2^12),
  with H = Xi(0) * B(z)/B(0) (SOFT_1 eq. 3.2).
Registered predictions and thresholds:
  P-PH1: if kTrial admits the reflection symmetry making B(-x)=conj(B(x)),
   then H is real on R up to the fixed unit => sd(theta mod pi) < 0.05 rad
   away from zeros -> C2_PHASE_RIGID (C2 promoted).
  P-PH2: if theta drifts (sd >= 0.3 rad or systematic slope) ->
   C2_PHASE_FREE (C2 killed as stated; C1/C3 remain).
  Between: EXTEND (finer grid, exclude zero neighborhoods).
Zero neighborhoods (|B| below 10x machine floor) are excluded from sd.

## 3. Execution order

SOFT_2.a Codex: implant Proshka plants A/B/C as validators (they must FIRE on
         the planted inputs; a validator that cannot fire is not a judge).
SOFT_2.b Codex: PhaseStructureProbe (above) + one-page symmetry audit of
         kTrial (exact packet symmetry from D0.1/D0.5 lines; no new objects).
SOFT_2.c Proshka round 4: kill two of C1/C2/C3, weakest repaired form of the
         survivor; explicit check of C1 against Attack B; if C2 survives the
         probe, name the minimal structural theorem it needs.
SOFT_2.d Only then: instantiate Proshka round-3 DAG (3.1–3.4) on the
         surviving branch. SOFT_3B remains the smallest gap AFTER the fork.

## 4. Firewalls inherited

All SOFT_1 G6 audit items; plants A/B/C; no critical-line-only zero sums; no
post-hoc gamma_0; LIMIT_UNIT fixed (a,b); quantifier order
forall phi forall eps exists R exists j0 forall j.

NOT_RH.
