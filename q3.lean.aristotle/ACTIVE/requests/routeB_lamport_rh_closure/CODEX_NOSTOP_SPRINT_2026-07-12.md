# CODEX NO-STOP SPRINT — 2026-07-12

Authority: owner-approved work queue. Status: `SPRINT_BRIEF / NOT_RH`.
Mode: **do not stop, do not wait, do not ask.** Work the queue top-down.
If an item requires owner authority → write ONE line to `SPRINT_LOG.md`
(`SKIPPED <item>: <reason>`) and move to the next item. A self-found FATAL is
reported as a result (with counterexample + repaired statement) and the sprint
CONTINUES with the remaining items.

Documentation budget: ≤1 page per item. No new audits of audits. One summary
at the end. Batch git commit at sprint end (do not push without owner).

Hard firewalls (violating any = FATAL, log and continue):
- no `WPrime` defined by the desired RHS (D0_7E_TAUTOLOGY);
- no `alpha :=`, `DeltaE :=`, `kappa`, `N(lambda)` selector, filter choice minted anywhere;
- no import of H3c/H4 theorems into D0;
- no `bCal` / `bCal^(-1)` aliasing (D0_7E_BCAL_BZEO_ALIAS_CONFLICT);
- no Bus 010.

## QUEUE (kill-power per cost, K2 order)

### T0 — WPrime consumer SOURCE MINING (unblocks critical path; search, not minting)
Answer `D0_7E_5A_CONSUMER_SOURCE_REQUEST.md` by corpus search, method of
ALPHA_DETECTOR_OBJECT_LOCK (verbatim lines or MISSING; self-citation excluded):
grep the full corpus — `H8ULBMAL/fulltext.md`, `PEN_3_3_G04_OBJECT_DICTIONARY.md`,
D0 draft F-lines, `docs/trackB/*`, research digests — for tokens:
`WPrime, W', W′, FZeo, F_Zeo, ZEO, tracking, |b|sqrt, b\cdot\sqrt`.
T0 IS NOT A STOP: after writing the candidates file, IMMEDIATELY continue with
T1–T5. Ratification arrives asynchronously via
`OWNER_STANDING_ORDER_RATIFICATION_2026-07-12.md`: candidates passing
checklist C with CONFIRMED from Прошка (V1) and from Claude-PRO
(`D0_7E_5A_PRO_VERDICT.md`, V2) become PROVISIONALLY_RATIFIED — then revisit
5a→5c at sprint end. Output `D0_7E_5A_CONSUMER_SOURCE_CANDIDATES.md`: each candidate = verbatim
quote + file:line locator + sha256 + classification
(DEFINITION / THEOREM / CONDITIONAL / HEURISTIC / OUTLOOK) + which of the 5
request questions it answers. If nothing qualifies: emit the explicit verdict
`NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE` (that verdict is progress —
it converts 5a into a one-decision owner input).
Acceptance: owner can ratify with one word.

### T1 — Pre-registered bDet judges (pure computation, K7-legal)
Run the four judges pre-registered in `D0_7E_OWNER_INPUT.md`:
1. per-cell interval certificate `bDet = sqrt(2 log λ)·c0/ζ(1/2)` at λ² ∈ {13,14,17},
   value AND sign, straight from persisted coefficient vectors;
2. N-stability at λ²=13: N=90 vs N=120 within factor 3;
3. two-way evaluation: stored-coefficient identity vs direct quadrature of
   ∫k1 du/u — machine-zero agreement;
4. PLANT: shadow copy with c0 zeroed must yield bDet=0 and trip
   `B_CENTRAL_ZERO_CELL`; a checker not tripping = `PLANT_INERT` (FATAL for the checker).
Output: `D0_7E_JUDGE_CERTIFICATES.json` + one-page note. Scores registered
prediction P3 (`|bDet|·sqrt(λ) ≈ const` within factor 3, FIT_NOT_LAW) and
feeds PO_B_BOUNDS empirics. No asymptotic claims.

### T2 — H3e tracking-shape CALIBRATION (falsify/calibrate/localize — never occupy a quantifier)
Numerically measure `sup_K |Fhat_(m,N) − bDet·Ξ|` on a small compact
K = {|Re z| ≤ 2, |Im z| ≤ 1/4} at the cells from T1; tabulate against the
WPrime-shaped RHS and against the raw bound `sqrt(L_m)·λ^a`. Questions to
answer numerically: (a) does the error track any WPrime-like quantity at all;
(b) where does the `sqrt(L)·λ^a` divergence bite first (which |Im z|).
Registered predictions BEFORE running (write them in the file header):
P2: the I-b2 lower bound alone cannot produce a constant A_K.
Output: `H3E_TRACKING_CALIBRATION.md` + raw table. This decides whether the
H3e theorem shape deserves pen-months BEFORE they are spent.

### T3 — Close D0.7e.5b (typing only)
Type `alpha ≥ 0`, `DeltaE > 0`, `delta_dict ≥ 0`, filter `F` as downstream
UNINSTANTIATED parameters on the two-parameter carrier (m,N). Validator +
certificate. Grep-guard in validator: no `:=` instantiation inside D0.7e.
Legal because it is interface typing, not definition.

### T4 — Close D0.7e.5d (migration correctness only)
Register the UNCHANGED `PO_D0_7E_XWALK` wording at H3e together with
`PO_XWALK_UNIFORM_EVAL`; prove migration correctness (same registered wording,
address change only, acyclic deps {D0, H3a, H3b, H3c, H4c, H4d}). No tracking
theorem content. Node label everywhere: `H3e_ExactWPrimeTrackingTheorem`
(ratified R2 name — fix any `UniformWPrimeZeoCrosswalk` drift, incl. map rev 10).

### T5 — Lean formalization of already-PROVED, self-contained pieces (PO-13 start)
Unconditional permanent progress; no owner input needed:
(a) `zeta_half_ne_zero`: η-series pairing ⇒ η(1/2)>0 ⇒ ζ(1/2)<0 ⇒ Ξ(0)≠0
    (Mathlib `riemannZeta`; no decimals);
(b) `bDet` finite definition + reality: real trial ⇒ c_(−n)=conj(c_n) ⇒ c0 ∈ ℝ;
(c) constant-mode identity `Fplus(0) = sqrt(L)·c0`.
Each lemma in its own file, `#print axioms` clean, no `sorry` left behind —
a lemma that cannot be finished is reverted and logged, not stubbed.

## END-OF-SPRINT REPORT (single message)
Table: item → CLOSED / BLOCKED(one-line reason) / FATAL(finding).
Plus exactly one line: "the single owner decision that would unblock the most".
Update STATE.json per closed item; certificates + validators required;
`routeb_status.py --check` green before commit.
