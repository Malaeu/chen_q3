PACKET 4 FOR MYTHOS — kill-test closure material + Proshka routes verdict
Repo: Malaeu/chen_q3 · rh_clean · HEAD 4f9354b8a419353ddb1a486f7891b9b8f0b09711
Built: 2026-07-31 by conductor-CLI (Linux). UTF-8, LF.

COVER NOTE:
(1) 012GOAL — your last dashed link: who ordered 012 and under which PO node.
(2) 043ANSWER — fail-closed LEAN_BUILD_FAIL / DOMAIN_BRIDGE_NEEDED. Math is GOOD:
    Estar/Rminus byte-identical v3<->R6, half-planes propositionally equal,
    .analyticOnNhd passage confirmed. Blocker purely infrastructural: both Lake
    projects own module namespace RequestProject.*, joint import impossible.
    (This file ends with TWO newlines; the packet preserves them byte-exactly.)
(3) GOAL044 — already issued on the registered failure path (R6 certificate export
    under unique module namespace + thin consumer wrapper; honesty clause names
    WITNESS_CLASS_VS_R6_HYPOTHESES_GAP: R6 wants global Lipschitz + support away
    from zero, PL1/PL2 witnesses touch zero). Codex executing now. Your P-SUP-ALL
    got its first data point: hRp indeed sits in the same R6 file
    (Rplus_differentiable) — 044's export closure carries it for free.
(4) THM510SUPP — your card material: §8 verbatim, Theorem 3.6 (+Prop 3.5), δ_N
    Dirichlet normalization, SIMPLE_EVEN(QW_λ) card hook with K7 tags.
(5) PROSHKA-ROUTES — verdict you have NOT seen: ROUTES_DISAMBIGUATED. Key points
    for your next dispatch: (i) three objects, not two roads (legacy broad-cone
    Q3.Main wrapper ≠ corrected-cone H-bridge ≠ Route B); (ii) Route B roof exists
    as hole-free Lean theorem rh_of_canonical_strip_slots, slots G1..G7, open:
    G2/G3/G5/G6; (iii) smallest conceptual gap = MuntzV3_to_RouteBGate_Crosswalk —
    CONVERGES with your Müntz→012→ALPHA/D0→H4 chain: her demand is the theorem-form
    of your signed edge; (iv) her STRONGEST ATTACK binds all future dispatches:
    name the exact consumer theorem/gate, target cone, axiom profile (route
    crosswalk template included in the verdict); (v) conductor's "two certificates
    + one citation" claim was REJECTED (three cert-data axioms in the registry;
    conductor MY_MISS acknowledged).

DISPATCH QUESTION: with her crosswalk template and your signed chain — write the
MuntzV3_to_RouteBGate_Crosswalk card (which G-slot, through which theorem, or name
the one missing fact). This is the beam from our foundation to the roof.

VERIFICATION CONTRACT: each payload lies strictly BETWEEN its BEGIN/END marker
lines; the payload is the source file byte-exact (including any repeated trailing
newlines). SHA-256 over exactly those bytes = the file's on-disk SHA.

MANIFEST (label · bytes · sha256):
  012GOAL: docs/routeB_bus/012_estar_windowed_mellin_crosswalk.goal.md · 3822 · a322424d51aad88d4ee2d366220ad6ea2c4cea02c96bc07a6d97f247203b7a97
  043ANSWER: docs/routeB_bus/043_muntz_v3_supplier_hrm.answer.md · 7903 · da5ec23ff29d13862d466b662d68ff81efd6f97a264ce659564eab1e5796fd4d
  GOAL044: docs/routeB_bus/044_muntz_v3_r6_export_hrm_wrapper.goal.md · 4558 · 425b54615a7cf142105fa1bb060cb2ef5a2c815efcfe5776b8071aedbfcd79a1
  THM510SUPP: docs/routeB_bus/imports/THM510_SUPPLEMENT_S8_T36_DELTAN_2026-07-31.md · 3715 · 488fb7b3e623ac0d93cc583c22b737edf19a40830ae1d48cc348a0592120147b
  PROSHKA-ROUTES: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUTES_DISAMBIGUATED_2026-07-31.md · 14486 · 3aff7b1e8eed7693f36ea42b858d10f85d1bf541c5655a3de705374d32e12d30

═══ FILE BEGIN: 012GOAL: docs/routeB_bus/012_estar_windowed_mellin_crosswalk.goal.md ═══
# ГОЛ 012 — EStarWindowedMellinCrosswalk (ветка ZERO_MASS)

От: Mythos (по FINAL PROPOSAL Прошки, PROSHKA_MELLIN_CROSSWALK_2026-07-27.md;
развилка решена отчётом 011: H2_ZERO_CONFIRMED — работаем ТОЛЬКО в ветке zero-mass).
Статус проекта: CHALLENGER / NOT_RH. BUS_010_VOID соблюдать.

## Цель (Lean, локально; hTrial остаётся параметром)

Все утверждения формулируются для ПАРАМЕТРИЧЕСКОГО h : ℝ → ℂ с явными гипотезами
(hmeas, hdecay/hsupport по факту цепочки Stage 1-2, hmass : ∫₀^∞ h = 0), чтобы
инстанцировать пролатной комбинацией позже. Никакой конкретики h внутри доказательств.

T1 (первое машинное reference identity — «окно-тождество»):
   G_m(s) := M(gTrial_m)(s) = ∫₀^∞ h(v) · v^{s−1/2} · D_{λ,s+1/2}(v) dv,
   где D_{λ,p}(v) := Σ_{n : v/λ ≤ n ≤ vλ} n^{−p} (конечная сумма при каждом v).
   Маршрут: замена переменных u = v/n в каждом члене E_star + Фубини по
   конечному числу членов на окне; никаких пределов рядов в полосе.

T2 (декомпозиция zero-mass ветки):
   При hmass: G_m(s) = ζ(s+1/2)·M(h)(s+1/2) − R_m^−(s) − R_m^+(s)
   с ТОЧНЫМИ определениями R_m^−(s) = ∫₀^{λ^{-1}} E_star(h)(u)·u^{s−1} du,
   R_m^+(s) = ∫_λ^∞ (аналогично), в области, где всё абсолютно сходится,
   плюс лемма о продолжении на |Re s| < 1/2 через zero-mass (Мюнц-контртерм:
   E_star минус A·u^{-1/2} с A = 0). Если продолжение в Lean не проходит —
   зафиксировать T2 в области абс. сходимости + отдельной строкой назвать
   недостающую лемму продолжения (код в отчёте, не sorry).

T3 (ЗАПРЕТ малости): НИКАКИХ утверждений «R_m^± мало» — только определения
   и тождество. Относительные оценки — отдельный будущий гол.

PL (плант, обязательный): контрольный h₀ ≥ 0 с ∫h₀ ≠ 0 (например, индикатор
   или простая ступенька) — показать НА УРОВНЕ ТОЖДЕСТВА, что отношение
   |G(−σ)|/|G(0)| несёт полюсной член A·J_λ и растёт ≍ λ^σ.
   Если имплементация даёт bounded ratio для такого h₀ — она ПОТЕРЯЛА полюс,
   код ESTAR_POLE_COUNTERTERM_OBJECT_MISMATCH, стоп.

## Запреты
Без новых аксиом/sorry/native_decide; без перестановок Σ/∫ вне конечно-оконного
обоснования T1; без «малости» поправок; без RH; конвенции Меллина — как в
вердикте Прошки (M(k)(s)=∫₀^∞ k(u)u^{s-1}du), не менять.

## Валидация
lake build; #print axioms всех целей (тройка); грепы; отчёт 012_...answer.md
со статусом РОВНО ОДНИМ из:
ESTAR_MUNTZ_ZERO_MASS_GREEN ·
ESTAR_ZERO_MASS_SOURCE_MISSING ·
ESTAR_WINDOW_CORRECTION_DOMINATES ·
ESTAR_POLE_COUNTERTERM_OBJECT_MISMATCH ·
ESTAR_CONTINUATION_LEMMA_MISSING (+ имя недостающей леммы).
STATE — только после моего скоринга.
═══ FILE END: 012GOAL: docs/routeB_bus/012_estar_windowed_mellin_crosswalk.goal.md ═══

═══ FILE BEGIN: 043ANSWER: docs/routeB_bus/043_muntz_v3_supplier_hrm.answer.md ═══
LEAN_BUILD_FAIL

```yaml
PRIMARY: LEAN_BUILD_FAIL
PRIMARY_COUNT: 1
PHASE_0_OUTPUT: DOMAIN_BRIDGE_NEEDED
SCOPE: ABSTRACT_SUPPLIER_CONSUMPTION
VERIFIER: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
FROZEN_FILES_CHANGED: 0
R6_PROOF_COPIED_OR_REPROVED: false

GOAL_VERSION_CONSUMED:
  FILE: 043_muntz_v3_supplier_hrm.goal.md
  SHA256: 5531ef30cf15d1372bb3174a421695c8816d7719b0bf1eef06a0afe762c5e786

SUPPLIER:
  THEOREM: Rminus_differentiableOn_halfPlane
  FILE: muntz_r6/RequestProject/TailAnalyticity.lean
  FILE_SHA256: 88ba75b8b28df9a6b826f339a002c6e9af6c2263ccc4f79f022b0c2b99b87fc5
  DIRECT_LEAN: PASS
  LAKE_BUILD: PASS_8032_JOBS
  TAINT_MATCHES: 0
  AXIOMS: [propext, Classical.choice, Quot.sound]

TARGET:
  THEOREM: rminus_analyticOnNhd_shiftedHalfPlane
  MATERIALIZED: false
  FAILURE: REQUESTPROJECT_MAIN_MODULE_COLLISION
```

All mathematical/source inventory claims are `[ABSTRACT][LEAN]` or
`[ABSTRACT][SOURCE_AUDIT]`; hashes are `[CONTROL][SHA256]`, while
route, bus, submission, and frozen-file fields are `[CONTROL][LOCAL]`.

## PHASE 0 — mandatory inventory

1. **Same `Rminus` object: YES.** The R6 and v3 `Estar` plus
   `Rminus` definition blocks are byte-identical. The extracted four-line
   blocks have the same SHA-256
   `470385c431682160760b3f564676a3ce29294f9e036c3a209e7a077b8a540ba7`.
   `[ABSTRACT][SOURCE_AUDIT]`

2. **Same half-plane: propositionally YES, definitionally NO.**
   v3 defines `shiftedHalfPlane` with `-(1/2)`; R6 states `(-1)/2`.
   The required bridge is exactly:

   ```lean
   lemma shiftedHalfPlane_eq_r6HalfPlane :
       shiftedHalfPlane = {s : ℂ | -(1 : ℝ) / 2 < s.re} := by
     ext s
     simp only [shiftedHalfPlane, Set.mem_setOf_eq]
     norm_num
   ```

   This lemma was checked locally. `[ABSTRACT][LEAN]`

3. **`DifferentiableOn → AnalyticOnNhd`: RESOLVED.** The exact Mathlib
   API is `DifferentiableOn.analyticOnNhd`; openness is supplied by
   `isOpen_lt continuous_const Complex.continuous_re`.
   `[ABSTRACT][LEAN]`

4. **Hypothesis inventory: R6 INPUTS MUST BE RETAINED.** The wrapper would
   require exactly `0 < a`, `a ≤ b`, support in `Icc a b`, global
   `LipschitzWith K h`, zero mass on `Ioi 0`, and `1 ≤ Λ`.
   The v3 class used by `MuntzV3Unconditional.lean` only supplies
   `Measurable h`, support in `Icc 0 b`, and
   `LipschitzOnWith K h (Ico 0 b)`; it does not imply positive lower
   support or global Lipschitz continuity. No such implication is claimed.
   `[ABSTRACT][SOURCE_AUDIT]`

The mandatory PHASE 0 output is therefore
`DOMAIN_BRIDGE_NEEDED`, with the exact bridge lemma
`shiftedHalfPlane_eq_r6HalfPlane`. `[CONTROL][LOCAL]`

## PHASE 1 — fail-closed integration result

The domain bridge itself passes Lean, and the harvested R6 supplier separately
passes both direct Lean checking and its 8032-job Lake build.
`[ABSTRACT][LEAN]`

The requested consumption wrapper cannot be made a module of the frozen v3
project without an additional packaging/refactor contract. Both independent
archives export different files under the same Lean import name
`RequestProject.Main`: R6's `TailAnalyticity` transitively imports the R6
`RequestProject.Main`, while the v3 package's
`globs = ["RequestProject.+"]` resolves that name to the v3 file.
`[CONTROL][LEAN_MODULES]`

With the v3 resolver first, the diagnostic wrapper fails exactly with:

```text
object file '.../muntz_v3/.lake/build/lib/lean/RequestProject/TailAnalyticity.olean'
of module RequestProject.TailAnalyticity does not exist
```

With the R6 resolver first, `TailAnalyticity` loads but the v3 declaration
`shiftedHalfPlane` is absent. Thus the two source projects cannot be
co-imported merely from the byte equality of their initial definitions.
`[CONTROL][LEAN_MODULES]`

Per Goal 043's instruction to report rather than repair divergence, no proof
body was copied, no R6 source was reproved, no Lake/package topology was
changed, and no frozen file was touched. The target theorem is therefore not
materialized, and the one exact failure code is `LEAN_BUILD_FAIL`.
`[CONTROL][LOCAL]`

## Validation ledger

```text
[ABSTRACT][LEAN] R6 lake env lean RequestProject/TailAnalyticity.lean     PASS
[ABSTRACT][LEAN] R6 lake build RequestProject.TailAnalyticity             PASS (8032 jobs)
[ABSTRACT][LEAN] R6 supplier taint scan                                   0 matches
[ABSTRACT][LEAN] #print axioms Rminus_differentiableOn_halfPlane          [propext, Classical.choice, Quot.sound]
[ABSTRACT][LEAN] isolated shiftedHalfPlane_eq_r6HalfPlane                 PASS
[CONTROL][LEAN] joint v3/R6 wrapper import                                FAIL (module collision)
[CONTROL][LEAN] v3 baseline lake build                                    PASS (8031 jobs)
[CONTROL][GIT]  frozen source diff                                        0
[CONTROL][LOCAL] Aristotle submissions                                    0
```

## Prediction score

- `P043-M1`: **MISS AT INTEGRATION BOUNDARY**. The mathematical wrapper is
  below 80 lines and needs no new analysis, but it cannot be materialized in
  the v3 package without resolving the duplicate `RequestProject.Main`
  ownership. `[ABSTRACT][LEAN]`
- `P043-M2`: **PARTIAL**. Domain normalization and `Λ` bookkeeping are
  indeed trivial; the dominant friction is the unregistered module/package
  collision. `[CONTROL][LEAN_MODULES]`
- `P043-M3`: **PARTIAL**. The mismatch names itself in one line as
  `REQUESTPROJECT_MAIN_MODULE_COLLISION`, but it is not an `Estar` edge
  bound: the existing R6 bound and theorem compile cleanly.
  `[ABSTRACT][SOURCE_AUDIT]`

## ACTIONS LOG

```text
1. [CONTROL][GIT] Checked rh_clean and ran git pull --ff-only first.             PASS
2. [CONTROL][SHA256] Locked both Goal 043 copies at 5531ef30...c5e786.           PASS
3. [CONTROL][LOCAL] Read Route B execution state/control and ran status check.   PASS
4. [ABSTRACT][SOURCE_AUDIT] Byte-compared Estar/Rminus definitions.              IDENTICAL
5. [ABSTRACT][LEAN] Proved and checked the exact half-plane equality bridge.     PASS
6. [ABSTRACT][LEAN] Located DifferentiableOn.analyticOnNhd and openness API.     PASS
7. [ABSTRACT][SOURCE_AUDIT] Enumerated every R6 supplier hypothesis.              DONE
8. [CONTROL][LOCAL] Ran four q3_docs queries; all timed out.                      RECORDED
9. [ABSTRACT][LEAN] Built and checked the harvested R6 supplier locally.         PASS
10. [CONTROL][LEAN_MODULES] Tested both v3-first and R6-first import resolution.  COLLISION
11. [CONTROL][LOCAL] Removed diagnostic scratch files; retained no failed code.   DONE
12. [CONTROL][GIT] Verified v3 baseline build and frozen files.                   PASS
13. [CONTROL][LOCAL] Emitted no Aristotle submission and no numerical run.        PASS
14. [CONTROL][MIRROR] Wrote canonical and mirror answers together.                DONE
15. [CONTROL][STATE] Added one non-promoting failure-history row last.            DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: LEAN_BUILD_FAIL
PHASE_0: DOMAIN_BRIDGE_NEEDED
GOAL_SHA256: 5531ef30cf15d1372bb3174a421695c8816d7719b0bf1eef06a0afe762c5e786
OBJECT_DIFF: Estar and Rminus byte-identical
DOMAIN_DIFF: -(1/2) versus (-1)/2; tested bridge lemma available
ANALYTIC_API: DifferentiableOn.analyticOnNhd
R6_INPUTS: 0<a; a≤b; support Icc a b; global LipschitzWith; zero mass; 1≤Λ
V3_CLASS_BRIDGE: not supplied and not implied
R6_SUPPLIER: direct Lean/build PASS; taint zero; standard axiom triple
BLOCKER: REQUESTPROJECT_MAIN_MODULE_COLLISION
TARGET_THEOREM: not materialized
REPROOF_OR_COPY: none
ARISTOTLE: no submission
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
RECOMMENDED_NEXT_CONTRACT: collision-free R6 export under a unique module name,
or an explicit generic supplier certificate whose public type does not import
either RequestProject.Main; keep Main.lean frozen until that contract is approved
```

═══ FILE END: 043ANSWER: docs/routeB_bus/043_muntz_v3_supplier_hrm.answer.md ═══

═══ FILE BEGIN: GOAL044: docs/routeB_bus/044_muntz_v3_r6_export_hrm_wrapper.goal.md ═══
# Goal 044 — R6 certificate export under unique module name + hRm consumer wrapper

ISSUED: 2026-07-31 · Contour: Codex's named next move in 043.answer (fail-closed
  LEAN_BUILD_FAIL / DOMAIN_BRIDGE_NEEDED); transcribed by conductor-CLI on owner's
  order. Mythos ratification: post-hoc via packet 4 (this goal follows the exact
  failure-code escalation path registered in Goal 043; no new mathematics is chosen
  here, only the infrastructure repair the code names).
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen files untouched
PARENT: Goal 043 (immutable, closed fail-closed; its PHASE 0 findings are inputs here).

## Inherited PHASE 0 facts (from 043.answer, not re-derived)

- Estar and Rminus definitions are byte-identical between v3 and R6.
- Half-planes are propositionally equal; a small domain bridge is needed.
- DifferentiableOn → AnalyticOnNhd passes via `.analyticOnNhd` (open set).
- R6 hypotheses to be carried EXACTLY: global `LipschitzWith K h` and support in
  `Icc a b` with `0 < a` (support away from zero). The v3 witness class does NOT
  supply these — that mismatch is REPORTED, not repaired here (see Honesty clause).

## Task

PHASE A — EXPORT: copy the R6 certificate into muntz_v3/RequestProject/ under a
unique module namespace (e.g. `RequestProject.R6Export.TailAnalyticity`; naming free
but must not collide with any existing module in either project):
- dependency closure included (TailAnalyticity imports RequestProject.WindowAnalyticity;
  enumerate and export the full transitive closure needed);
- import lines renamed to the new namespace; proof bodies byte-preserved;
- each exported file carries a provenance header: source path + source SHA-256 +
  "exported verbatim, imports renamed only" + date;
- no statement changes, no proof changes, no reproving.

PHASE B — WRAPPER: in a NEW file, prove the consumer-shaped theorem

```lean
theorem rminus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane
```

via: exported R6 theorem → domain bridge (propositional equality of the half-planes)
→ `.analyticOnNhd`. Hypothesis list = exactly the R6 list, no weakening, no silent
strengthening of the consumer.

## Honesty clause (binding for the answer)

Discharging hRm UNDER R6 HYPOTHESES does not yet connect to the PL1/PL2 witness
class (their supports touch zero; Lipschitz is OnWith). The answer MUST state this
remaining obligation explicitly as a named open interface
(WITNESS_CLASS_VS_R6_HYPOTHESES_GAP) — deciding what to do with it belongs to the
Mythos/Proshka cycle, not to this goal.

## Forbidden

- modifying frozen files; modifying anything inside muntz_r6/;
- statement or proof changes in exported content (imports-line renames only);
- reproving R6 content from scratch;
- taint (sorry | admit | axiom | native_decide | exact?);
- any promotion; no Aristotle.

## Validation

```text
lake build            (v3 project, must include the export and the wrapper)
grep taint terms on all new files
#print axioms rminus_analyticOnNhd_shiftedHalfPlane
axioms exactly [propext, Classical.choice, Quot.sound]
diff each exported file against its R6 source modulo the import/namespace lines
  (report the exact diff in the answer — it must touch ONLY import/namespace lines)
```

## Success code

HRM_SUPPLIER_DISCHARGED_UNDER_R6_HYPOTHESES

## Failure codes (exactly one, fail-closed)

R6_DEP_CLOSURE_TOO_LARGE(enumerated)
MODULE_RENAME_BREAKS_PROOF(file, line)
DOMAIN_BRIDGE_FAIL
LEAN_BUILD_FAIL

## Registered predictions

P044-C1 (conductor): dependency closure ≤ 3 files; wrapper ≤ 40 lines; the whole
  goal closes in one Codex session with no new mathematics.
P044-C2 (conductor): the export diff is import-lines-only for every file (no proof
  body edits forced by the rename).

## Answer requirements

044_muntz_v3_r6_export_hrm_wrapper.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS
LOG; PHASE A file list with source/export SHA-256 pairs; the exact export diffs;
WITNESS_CLASS_VS_R6_HYPOTHESES_GAP stated; scoring P044-C1..C2; goal consumed by
SHA-256; one non-promoting state row; ROUTE_B_STATE last; canon+mirror one
transaction; report — do not repair — divergences.
═══ FILE END: GOAL044: docs/routeB_bus/044_muntz_v3_r6_export_hrm_wrapper.goal.md ═══

═══ FILE BEGIN: THM510SUPP: docs/routeB_bus/imports/THM510_SUPPLEMENT_S8_T36_DELTAN_2026-07-31.md ═══
# IMPORT SUPPLEMENT — §8, Theorem 3.6, δ_N normalization (for the simple+even card)

Acquired: 2026-07-31 by conductor-CLI (Mythos packet-4 item 3).
Source: arXiv 2511.22755, Connes–Consani–Moscovici, *Zeta Spectral Triples*
(PDF on the bus: `imports/2511.22755.pdf`; pdftotext extraction, PDF authoritative).
Companion to: `imports/THM510_ZETA_SPECTRAL_TRIPLES_2026-07-31.md`.

## §8 "The missing steps" (verbatim modulo OCR)

There are two essential steps still missing to justify our tentative proof of the
Riemann Hypothesis. The first is that, in order to apply Theorem 5.10 to the Weil
quadratic form QW_λ, one must prove that its smallest eigenvalue—whose existence is
ensured by Theorem 3.6—is simple and that its corresponding eigenvector ξ_λ is even.
The second step is to establish that k_λ provides a sufficiently accurate
approximation to (a scalar multiple of) ξ_λ, in order to justify the convergence of
the zeros of ξ̂_λ towards the non-trivial zeros of ζ(1/2 + is).

There are, however, three indications supporting the feasibility of these steps.
(1) The "simple-even" condition holds for all values of λ for the prolate-wave
operator PW_λ.
(2) The extremely small numbers ε_λ that occur as eigenvalues of the Weil quadratic
form QW_λ also appear—see Figure 4—when evaluating the discrepancy for h_λ to belong
simultaneously to P_λ and P̂_λ.
(3) The numerical evidence for the proximity between k_λ and ξ_λ extends to the
higher eigenfunctions of the Weil quadratic form.

## Theorem 3.6 + supporting Proposition 3.5 (verbatim modulo OCR)

Proposition 3.5 (from [12], Proposition 10.6). Suppose that A ≥ m_A is a lower
semibounded self-adjoint operator and m < m_A. Then the following are equivalent:
1. The embedding map I_t^A : (D[A], ‖·‖_t^A) → (H, ‖·‖) is compact.
2. The resolvent R_λ(A) is compact for one, hence for all, λ ∈ ρ(A).
3. (A − mI)^{−1/2} is compact.
4. A has a purely discrete spectrum.

Theorem 3.6. The selfadjoint operator A_λ has discrete lower bounded spectrum.

Proof (head, verbatim): By the proof of the lower boundedness in [4], the
contribution of the non-archimedean primes to the operator A_λ is bounded as well
as the contribution of the evaluation of the Fourier transform at the poles. Thus
it is enough to deal, for any λ > 1, with the contribution of the archimedean place
to A_λ in the Hilbert space L²(λ^{−1}, λ), d*u. It is given, after Fourier
transform, by the multiplication by
  ∂_t θ(t) = (1/2)(log|t| − log 2 − log π) − 1/2 + O(t^{−4})   (3.24)
[continues in PDF]

## δ_N — Dirichlet kernel and the normalization δ_N(ξ) = 1

§5.3 "The Dirichlet Kernel δ_N as an approximation of the Dirac Delta":

  D_N(x) = Σ_{n=−N}^{N} exp(2πinx/L), x ∈ [0, L]                (5.8)
         = sin(π(2N+1)x/L) / sin(πx/L)

Context line (paper p. ~5): "We let δ_N ∈ E_N be the vector representing the
Dirichlet [kernel functional]". Theorem 5.10 normalizes the eigenvector by
δ_N(ξ) = 1 — i.e. the Dirichlet-kernel evaluation functional applied to ξ equals 1
(finite-N substitute for point evaluation ξ(0) = 1; the λ→∞ Outlook normalization
is ξ(λ) = 1).

## Card hook (Mythos promotion/wall card)

Candidate named lemma for the S2·H2b wall:
  SIMPLE_EVEN(QW_λ): the smallest eigenvalue of QW_λ (exists by Thm 3.6) is simple,
  and its eigenvector ξ_λ is even.
Their feasibility anchor: simple-even holds for the prolate operator PW_λ for ALL λ
— and the prolate layer already lives on this bus (goals 016/019/020,
ProlateLayer.lean). K7: SIMPLE_EVEN is CONJECTURE-level for QW_λ (their own missing
step), THEOREM for PW_λ per their citation.
═══ FILE END: THM510SUPP: docs/routeB_bus/imports/THM510_SUPPLEMENT_S8_T36_DELTAN_2026-07-31.md ═══

═══ FILE BEGIN: PROSHKA-ROUTES: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUTES_DISAMBIGUATED_2026-07-31.md ═══
# PROSHKA VERDICT — ROUTES_DISAMBIGUATED; RH_REMAINS_OPEN
Date received: 2026-07-31
Channel: owner-relayed chat (Proshka has no write access)
Materialized by: conductor-CLI (Claude Code, Linux) on owner's direct order
Consumed by: route-map correction (three objects, not two roads); conductor MY_MISS
acknowledged ("two certificates + one citation" — REJECTED); smallest conceptual gap
MuntzV3_to_RouteBGate_Crosswalk registered; route-crosswalk template adopted for
future dispatches.
Transport artifacts note: payload verbatim as pasted by the owner; escaping/rendering
artifacts preserved ([ ]-fenced display math, ```markdown fences as received). The
final display-math block appears truncated in transport (no closing bracket) — noted,
not repaired. Semantic content untouched.

--- VERBATIM PAYLOAD BEGINS ---

# STATUS: PROVED — ROUTES_DISAMBIGUATED; RH_REMAINS_OPEN

```yaml
primary_verdict: H_BRIDGE_TAU0_ROUTE_CONFLATION_DETECTED

route_state:
  global_public_mainline: H_BRIDGE
  current_local_campaign: ROUTE_B_MUNTZ_V3
  route_b_status: CHALLENGER_NOT_RH
  bus_010: VOID

roof_status:
  legacy_Q3_Main_wrapper: CONDITIONAL_LEGACY_BROAD_CONE
  H_bridge_upper_roof: CONDITIONAL_MAINLINE_ARCHITECTURE
  Route_B_canonical_roof: LEAN_CHECKED_CONDITIONAL_THEOREM

brief_audit:
  "H-bridge = two certificates + one Weil citation": REJECTED
  historical_tau0_certificate_chain: DISTINCT_FROM_H_BRIDGE
  two_certificate_count: NOT_SUPPORTED_BY_CURRENT_RH_CLEAN

current_Muntz_work:
  directly_closes_H_bridge: false
  directly_closes_Route_B_roof: false
  role: UPSTREAM_ANALYTIC_SUPPLIER_AND_FALSIFIER_LAYER
  closed:
    - T4A_MELLIN_ANALYTICITY
    - POLE_SUBTRACTED_CONDITIONAL_SHELL
    - PL2_RAW_POLE_MISMATCH_FALSIFIER
  still_open_above_it:
    - H2A_EXACT_GROUND_STATE
    - H2B_THEOREM_510_REAL_ZERO_BRIDGE
    - S1_NORMAL_FAMILY_BOUND
    - S2_CLUSTER_IDENTIFICATION
```

## ROUTE MAP

Жёсткий ответ:

[
\boxed{\text{Да, крыша у нас была и есть.}}
]

Но **крыша — это условная теорема вида**

[
\text{«если все несущие стены доказаны, то RH».}
]

Она не означает, что стены уже построены.

И ещё важнее: в присланном описании смешаны **три разных объекта**, а не две аккуратные дороги.

| Объект                            | Что это на самом деле                                                         | Статус                                          |
| --------------------------------- | ----------------------------------------------------------------------------- | ----------------------------------------------- |
| `Q3.Main.RH_of_Weil_and_Q3`       | Старый скомпилированный broad-cone wrapper                                    | Не является исправленным Weil-square export     |
| Историческая `τ=0` PrimeCert-цепь | Weil-критерий плюс числовые cert-data axioms                                  | Отдельная старая certificate-road               |
| `T0-pd → H-bridge → H4 → RH`      | Текущая публичная corrected-cone mainline                                     | Основная архитектура, структурные стены открыты |
| Route B                           | Канонические аппроксиманты с вещественными нулями → cluster → (\Xi) → Hurwitz | Challenger, имеет собственную условную крышу    |
| Müntz v3 / PL2                    | Локальный аналитический слой Route B                                          | Не финальный мост и не H-bridge                 |

### 1. Старый `Q3.Main` — это не нынешний H-bridge

В текущем `Q3/Main.lean` действительно есть:

```lean
theorem RH_of_Weil_and_Q3 : Q3.RH
```

Но сам файл крупными комментариями предупреждает:

* это текущий **скомпилированный broad-cone route**;
* он не является замороженным публичным RH-контрактом после target-cone audit;
* он не является исправленным Weil-square export;
* его профиль содержит `Q3.Weil_criterion` и `Q3.prime_term_le_at_t_critical_axiom`.

То есть это **старая крыша на временных подпорках**. Она полезна как схема зависимостей, но её нельзя предъявлять как актуальный закрытый Q3-маршрут.

### 2. «Два сертификата + один критерий» — не H-bridge

Эта картина относится к старой `τ=0` PrimeCert-линии. Причём даже там текущий registry не подтверждает счёт «два сертификата»: он перечисляет один принимаемый `Weil_criterion_tau0` и **три** открытых cert-data axioms — grid arch, grid prime buckets и heat arch.

PrimeCert README также перечисляет три data-входа main chain:

```text
prime_b_grid_bounds_data
prime_heat_bounds_arch_data
prime_heat_sum_data
```

Следовательно, фраза:

> «официальный H-bridge остаток = два сертификата + одна цитата»

в текущем `rh_clean` **неверна дважды**:

1. это не H-bridge;
2. даже historical certificate count не сходится.

`[ABSTRACT][PAPER]`

## КАК ВЫГЛЯДИТ НАСТОЯЩИЙ H-BRIDGE

Публичная corrected-cone mainline сейчас зафиксирована как

[
\boxed{
T0\text{-}pd
\longrightarrow
H\text{-bridge}
\longrightarrow
H4
\longrightarrow
RH.
}
]

Внутри:

[
H1^f\to H2^f\to H3^f\to H4^f.
]

Причём сам H-bridge разбит на три двери:

```text
Door 1:
  mixed (+,-) block
  bulk exactness + boundary cancellation + cap remainder

Door 2:
  same-sign (++) block
  M++ − κQ++ = Hss + Ccap
  главный структурный kill-gate

Door 3:
  finite compression neutrality
  только controlled compression residue

then:
  H2f = tail/cap reduction
  H3f = filtered gap transfer
  H4f = Suzuki endpoint
  RH
```

Это **не certificate-only маршрут**. Его мясо — операторная декомпозиция, same-sign defect, compression и gap transfer.

Публичный tracker прямо говорит:

* corrected positive-definite/convolution-square cone — настоящий target;
* старый broad `Weil_cone` слишком широк;
* H-bridge — primary live route;
* PSD-pd — fallback;
* RH theorem остаётся условным, пока corrected-cone positivity и global lift не закрыты.

### H-bridge roof в человеческом виде

[
\boxed{
\text{точная positivity/ordering на corrected cone}
}
]

[
\Downarrow
]

[
\boxed{
\text{Suzuki/Yoshida filtered spectral bridge}
}
]

[
\Downarrow
]

[
\boxed{
H4\text{ endpoint statement}
}
]

[
\Downarrow
]

[
\boxed{RH}.
]

То есть крыша находится **над H4**, но до неё надо довести operator/form data через H-bridge.

## КАК ВЫГЛЯДИТ ROUTE B ROOF

Здесь крыша ещё более явная: она уже существует как hole-free Lean theorem

```lean
rh_of_canonical_strip_slots
```

Её входы:

```text
H1:
  fixed canonical family entire

H2a:
  selected ground state simple / isolated / even

Theorem 5.10 bridge:
  determinant + self-adjoint factorization
  → approximants have only real zeros

ANCHOR:
  nonzero normalization

S1 + Montel:
  locally bounded family
  → nonzero locally uniform cluster

S2:
  every cluster equals c · Xi · gamma
  with c ≠ 0 and gamma zero-free

then:
  Hurwitz / zero transfer
  → zeros of Xi are real in the centered strip
  → RH
```

Это именно то, что формально собирает `rh_of_canonical_strip_slots`.

В компактной форме:

[
\boxed{
\text{real-zero approximants}
+
\text{local uniform convergence to }c\Xi\gamma
\Rightarrow RH.
}
]

Это настоящая **Route B крыша**.

Но текущий compiler audit показывает, что надёжно закрыты лишь G1 и G4, G7 закрыт условно, а G2, G3, G5 и G6 остаются открытыми.

## ОТНОСИТСЯ ЛИ НЫНЕШНЯЯ MÜNTZ-РАБОТА К КРЫШЕ

Ответ:

[
\boxed{
\text{к Route B относится, но до крыши пока не дотягивается.}
}
]

### Что мы сейчас реально закрыли

Müntz v3 дал:

```text
T4a:
  Mellin transform analytic in Re s > 0

pole-subtracted layer:
  dslope
  residue-removed zeta factor
  analytic product
  correct pole value
  identity-theorem continuation

PL2:
  explicit witness proving that raw ζ·Mellin
  cannot be treated as continuous at the pole
```

Но theorem с названием `continued_window_identity_unconditional_mellin` снимает **только Mellin-analyticity hypothesis**. Он всё ещё принимает четыре серьёзных входа:

```lean
hG
hRm
hRp
habs
```

И даже после закрытия этой четвёрки получится **continued window identity**, а не автоматически:

* simple/even ground state;
* Theorem 5.10 real-zero bridge;
* S1 normal-family estimate;
* S2 cluster identification.

Текущий governor прямо фиксирует: PL2 закрыт как plant, T4a уже закрыт, но это нельзя переименовывать в полное закрытие Müntz v3 или Route B.

### Точная классификация

```text
Müntz T4a:
  настоящий supplier sublemma.

Pole-subtracted T5:
  условная аналитическая оболочка.

PL2:
  falsifier / hygiene theorem.

Route B G2/G3/G5/G6:
  не закрыты.

H-bridge:
  вообще не потребляет эти теоремы напрямую.
```

`[ABSTRACT][LEAN]`

Поэтому нынешняя работа **не бесполезна**, но её роль уже:

[
\boxed{
\text{укрепление фундамента отдельного Route B-дома}.
}
]

Она пока не является балкой, которая физически соединена с общей крышей.

## FINAL PROPOSAL

Вот как тебе надо держать карту в голове перед ответом Mythos.

### Дорога A — H-bridge mainline

```text
corrected Weil square cone
→ Suzuki/Yoshida operator/form bridge
→ same-sign + mixed-block classification
→ compression
→ filtered gap
→ H4
→ RH
```

Тип стены: **операторная positivity / spectral ordering**.

### Дорога B — Route B

```text
canonical spectral approximants
→ real-zero theorem
→ Montel cluster
→ cluster = c·Xi·gamma
→ Hurwitz
→ RH
```

Тип стены: **спектрально-комплексная аппроксимация**.

### Текущая Müntz ветка

```text
Mellin/window continuation
+ pole subtraction
+ plants
```

Это возможный analytic supplier для Route B, но пока отсутствует theorem:

```text
Muntz-v3 output
→ one of G2 / G3 / G5 / G6
```

Без такого crosswalk нельзя говорить, что текущая работа «закрывает крышу».

## STRONGEST ATTACK

Главный вопрос к любой будущей раздаче Mythos:

> **Назови точный consumer theorem. Какой именно открытый gate получает этот результат?**

Для нынешней Müntz-работы допустимые ответы должны выглядеть так:

```text
this theorem discharges hG
this theorem discharges hRm
this theorem discharges hRp
this theorem proves habs
this assembled identity feeds exact gate X through theorem Y
```

Недопустимый ответ:

```text
это приближает нас к RH вообще
```

Второй вопрос:

> **Какой target cone?**

Если Mythos покажет `RH_of_Weil_and_Q3` на старом `Weil_cone`, это broad-cone legacy wrapper, а не corrected H-bridge route.

Третий вопрос:

> **Покажи `#print axioms` и exact dependency chain.**

Если там:

```text
prime_term_le_at_t_critical_axiom
```

или старые PrimeCert data axioms, он обсуждает не текущую H-bridge mainline.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.

Before selecting between mainline and Route B, require a read-only route crosswalk:

ROUTE_ID:
TARGET_CONE:
FINAL_ROOF_THEOREM:
CURRENT_OPEN_SUPPLIERS:
EXACT_CONSUMER_OF_CURRENT_WORK:
AXIOM_PROFILE:
WHY_THIS_IS_NOT_THE_LEGACY_BROAD_CONE_ROUTE:
```

## META CLOSEOUT

**Что стало меньше:** путаница «две дороги» сведена к точной карте из legacy wrapper, H-bridge mainline и Route B challenger.

**Что убито:** тезис «H-bridge остаток — два сертификата плюс Weil citation».

**Что заморожено:** да, крыши существуют; обе они условные.

**Что нельзя повторять:** нельзя считать наличие theorem `... : RH` доказательством RH без аудита его предпосылок и аксиом.

**Текущий smallest conceptual gap:**

[
\boxed{
\texttt{MuntzV3_to_RouteBGate_Crosswalk}
}
]

То есть не ещё одна Mellin-лемма, а ответ:

> какой конкретный Route B gate потребляет собранный Müntz shell?

Одна фраза:

[
\boxed{
\text{Крыша есть. Но сейчас мы укрепляем фундамент другого дома, и балка к крыше ещё не проведена.}

--- VERBATIM PAYLOAD ENDS ---
═══ FILE END: PROSHKA-ROUTES: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUTES_DISAMBIGUATED_2026-07-31.md ═══

