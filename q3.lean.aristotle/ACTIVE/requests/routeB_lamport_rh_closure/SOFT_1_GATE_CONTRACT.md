# SOFT_1 — ZeroFreeGaugeAndDistributionalIdentification (gate contract)

Status: `CONTRACT_SYNTHESIS_BY_V2 / GATE_NOT_EXECUTED / NOT_RH`
Authority inputs: `SOFT_0_ROOF_AND_S2_TYPECHECK_2026-07-12.md` (Codex, code
SOFT_SUBSEQUENCE_CLOSURE_TYPED) and `SOFT_1_PRO_VERDICT_PROSHKA_GAUGE_2026-07-12.md`
(Proshka V1 round 2). Alias note: Proshka's "SOFT_0_ZeroFreeGauge..." == this
SOFT_1. No other new names (frozen glossary discipline).

## 0. Channel synthesis and the one collision, resolved

Both channels independently converge on the same wall: unconditional
identification of a cluster limit on an accumulating set / distributionally.
Collision: Codex's typed theorem fixes ONE gamma before the limit; Proshka
proves the FAMILY gamma_soft,j cannot serve as that fixed factor
(|lambda_j^(-iz)| = lambda_j^(Im z) blows up; no pointwise limit on R).
RESOLUTION — two distinct slots, both retained:

- CONSTRUCTION_GAUGE gamma_(m,N)(z) := gammaC(1/2+iz) * m^(-iz/2).
  Role: per-member completion unit inside the DEFINITION of each F_(m,N).
  Already Lean-locked zero-free (GammaSoftZeroFree.lean; DLMF 5.2, 4.2(iii)).
  It never appears as a limit factor.
- LIMIT_UNIT gamma_0(z), FIXED and j-independent, class e^(a+ibz) with
  a,b real constants (|gamma_0| = e^(a - b*Im z): zero-free, bounded on S;
  exactly the CCM "suitable constants" class). Identification target:
  cluster limit F = c * Xi * gamma_0. Codex's `Identified(F;Xi,gamma)` slot is
  instantiated ONLY with gamma_0, never with gamma_soft,j.

Operand-firewall corollary (from SOFT_0 §3): since
B --x m^(-iz/2)--> Fplus --x gammaC--> Fhat, gauge removal is literally
Fhat / gamma_(m,N) = B — the bare finite Fourier transform of kTrial. "Remove
the gauge" = "never dress the bare transform". Both presentations (bare B
with gauge-free hypotheses, or completed Fhat with gamma_0-identification)
are equivalent through the zero-free unit; the contract may use either but
must name which, once.

Anchor compatibility (new, small but load-bearing): gamma_(m,N)(0) =
gammaC(1/2) for EVERY (m,N) — the construction gauge is j-INDEPENDENT at the
center. Hence the central anchor survives gauge removal up to one fixed
constant; no j-dependent correction enters the anchor.

## 1. Gate obligations (executable checklist)

G1. GaugeSoftSubsequenceZeroEscape as a corollary: apply the SOFT_0 typed
    theorem to the gauge-removed family with LIMIT_UNIT gamma_0; record the
    exact statement; no new Hurwitz work. Pass: SOFT_GAUGE_ROOF_TYPED.
G2. Exact orientation lock: which of {Fhat/gamma, B} is the contract family
    F_j; one line, source-locked to D0.6 transform convention.
    Fail: SOFT_GAUGE_ORIENTATION_MISSING.
G3. Central anchor on BDetNonzero + fallback functional ell(f) := f(i/4).
    Obligations: (i) Lean or source-lock zeta(1/4) != 0 via eta-series
    positivity (0<s<1: eta(s)>0 and 1-2^(1-s)<0 => zeta(s)<0);
    (ii) statement F_j(i/4) != 0 from the real-zero roof (once H2 supplies
    it); (iii) explicit non-claim: uniform control of |F_j(i/4)| is OPEN
    (NONREAL_ANCHOR_UNIFORM_CONTROL). Fail: SOFT_ANCHOR_FUNCTIONAL_ZERO.
G4. Distributional S2 statement (THE WALL, to be posed, not proved here):
    for all phi in C_c^inf(I):  <F_j, phi> -> c * <Xi * gamma_0, phi>.
    Deliverable of this gate: the EXACT PAIRING FORMULA for <Fhat_(m,N), phi>
    in prime/Gamma-side terms. Parseval reduction: Fhat is the completed
    transform of kTrial supported on [0, L_m], so <Fhat, phi> collapses to a
    FINITE prime/prime-power sum against phi-hat plus the archimedean term —
    exactly the objects the D0 ledger computes. Write it, source-lock every
    term, and mark which side (prime/Gamma vs zero-sum) each term lives on.
    Fail codes: SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC (if only quadratic-form
    pairings exist, no linear pairing theorem), SOFT_S2_RH_CONDITIONAL_IMPORT.
G5. Joint-limit quantifier: state the (m,N) -> limit regime explicitly
    (which N per m, or N free with uniformity).  Round-13 overlay:
    H2a-cofinal and S1 must hold on one parent diagonal `j_k`, and S2 may
    consume only `j_(kappa(ell))` for a strictly increasing extraction
    `kappa`.  It may not select an independent cofinal sequence.  Guard:
    `SOFT_SAME_COFINAL_SUBSEQUENCE`.  Fail codes:
    `SOFT_JOINT_LIMIT_QUANTIFIER_MISSING`,
    `SOFT_COFINAL_SUBSEQUENCE_MISMATCH`.
G6. RH-conditional import audit over G1–G5 (BFM firewall; no |A(rho)|^2
    moments; no critical-line-only sums).
G7. Backup registered (not executed): MovingGridToIntervalBridge — grid
    X_j subset I with fill distance h_j -> 0 + S1 Cauchy derivative bound
    closes grid-to-interval; requires a mesh theorem the (m,N) ledger does
    not yet supply.

## 2. Stop codes (verbatim from V1 round 2)

SOFT_GAMMA_INTERIOR_POLE / SOFT_GAMMA_NOT_ZERO_FREE /
SOFT_GAUGE_ORIENTATION_MISSING / SOFT_GAUGE_NORMALITY_GAP /
SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC / SOFT_S2_RH_CONDITIONAL_IMPORT /
SOFT_ANCHOR_FUNCTIONAL_ZERO / SOFT_JOINT_LIMIT_QUANTIFIER_MISSING

## 3. What this gate does NOT do

Does not prove S1 (local normality) — that remains an independent open
hypothesis, now honest rather than definitional. Does not prove the
distributional S2 — it POSES it with an exact computable pairing formula.
Does not close H1/H2a/H2b/H2c (finite roof body ledger from SOFT_0 §2
unchanged). Does not touch 5a (NON_CRITICAL_PENDING_SOFT_0 -> _SOFT_1).
Does not create Bus 010. NOT_RH.

## 4. Needle ledger (K9 atlas entries from this round)

N1 GAUGE_REMOVAL: a zero-free j-dependent unit is clothing, not obstruction —
   divide it out before any limit; zeros are invariant. (Physics gauge fix.)
N2 REAL_ZERO_TRIPLE_DUTY: real zeros feed (i) the Hurwitz finish, (ii)
   growth control, (iii) the guaranteed-nonzero anchor at i/4.
N3 NATIVE_REPRESENTATION: prove statements in the representation the
   machinery natively outputs (pairings), not where they must be dragged
   (pointwise). Same needle as "Pair, don't multiply" (atlas), new clothes.
