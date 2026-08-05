# PROSHKA REQUEST — G6 / SlotS2 identification: is the Müntz→S2 bridge legal at all?

```yaml
REQUEST_ID: G6_S2_IDENTIFICATION_LEGALITY_2026_08_05
PHASE_KEY_CLAIM:
  route_id: RouteB_TwoLevelSpectralLadder
  front_id: G6_SLOT_S2
  source_object_family_id: MUNTZ_V3_EXACT_CLASS
  terminal_consumer_id: SlotS2_of_CanonicalRHRouteSkeleton
  honesty_state: CHALLENGER_NOT_RH
  convention_lock_id: C09_PRECOMMIT_THIS_REQUEST
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HELD
G2_CCM_LINE: UNTOUCHED (owner fork still awaiting owner data)
ARISTOTLE_SUBMISSION: NONE
ASK: verdict on legality + reading + fitting-risk, NOT authorization to build
```

## 0. Why you and not Mythos

Mythos already answered the decomposition question and registered the missing seam
**S2-L2b**. What we need from you is different and is judge-work: whether the whole
identification move is **source-faithful**, or whether it is a surrogate dressed as a bridge.
We would rather be killed now than build a wall on an illegal foundation.

## 1. What is closed (facts on disk, verifiable at HEAD bb0e1d2b)

- Müntz supplier front **4/4**: `hG`, `hRp`, `hRm`, `habs` all proved on the exact v3 class;
  `continued_window_identity_v3Class` discharges all four. `lake build` 8055 jobs, 0 sorry,
  standard axiom triple.
- New, this session, `Q3/Proofs/RouteB/S2GaugeNonvanishing.lean` — 6 theorems, `lake build`
  PASS (7746 jobs), axioms exactly `[propext, Classical.choice, Quot.sound]`, no sorry:
  - `xiGauge s = (1/2)·s·(s−1)·Gammaℝ s` (Mathlib's `Gammaℝ s = π^(−s/2)·Γ(s/2)`);
  - `xiGauge_ne_zero_of_mem_strip` — gauge zero-free on the OPEN strip;
  - `riemannXi_eq_xiGauge_mul_riemannZeta` — `ξ = xiGauge · ζ` on the open strip;
  - `centeredGauge_ne_zero_of_mem_strip`, `centeredXi_eq_centeredGauge_mul_riemannZeta`;
  - `limit_eq_anchor` (generic) and `limit_at_zero_ne_zero`
    (`SlotAnchor` + proved `centeredXi_zero_ne_zero` ⟹ `D.limit 0 ≠ 0`).
- `centeredXi_zero_ne_zero` was proved 2026-08-04 (`CenteredXiZeroNonzero.lean:361`).

**These are bricks, not the wall.** `SlotS2` demands `D.limit z = c · centeredXi z · gamma z`
on the whole strip; identification of the limit is exactly what is missing.

## 2. The seam Mythos found, and what our scan says

Under reading **(ii)** ("fix the window h, let Λ→∞"), `limit = ζ · M(h)` and the required
zero-free `gamma` forces `M(h)` to have **no zeros strictly inside** `Re w ∈ (0,1)`.
Under reading **(i)**, one needs `M(h_k) → xiGauge` locally uniformly — a Müntz density lemma.

We ran the discriminator with exact symbolic algebra (not float64), 1468 v3 windows of the
form `Σ c_j u^{a_j}` on `(0,1]` (report: `docs/routeB_bus/S2_L2B_MELLIN_ZERO_SCAN_REPORT_2026-08-05.md`,
script `q3.lean.aristotle/scripts/s2_l2b_mellin_zero_scan.py`):

- Zero-mass is **literally** `M(1) = ∫h = 0`, so `w = 1` is ALWAYS a zero of `M(h)` for the
  v3 class — and `w = 1 ⇔ z = −i/2` lies on the **boundary**, harmless by construction.
- All 28 two-term windows: numerator reduces to a multiple of `(w−1)` — interior-zero-free
  **structurally**, not by sampling luck.
- Three-term: exactly **one** dirty case out of 480 — exponents `(2,3,5)`, coefficients
  `1, −11/4, 17/8`, numerator `(w−1)(3w−2)`, interior zero at `w = 2/3` (exact).
- Four-term: 0 dirty out of 960.

So Mythos's R1 (an interior zero exists) is confirmed, but his corollary ("(ii) dies, the
design must be (i)") does not follow as stated: `SlotS2` quantifies over `ClusterData` for a
**fixed** `C`, and `C` is ours to construct, so one good window suffices.

## 3. The four questions

**Q1 — LEGALITY (the one we most want killed if wrong).**
Is it source-faithful to *construct* the canonical approximation `C` from a chosen v3 window
— i.e. to set `Pstar.family i := ` normalized `Gwin h Λ_i` — or is the canonical family
already source-locked to a different object, so that substituting a Müntz window is a
**surrogate** and a C10 kill? If it is legal, state the exact source-lock conditions the
substitution must satisfy.

**Q2 — READING.** (i) or (ii)? Given §2, our reading is that (ii) survives and is far cheaper.
If you rule (i), we accept that G6 becomes a Müntz density obligation and drop the window hunt.

**Q3 — FITTING RISK (please be brutal).** We are choosing the window so that the nonvanishing
condition holds. Where is the line between *constructing* an object and *fitting* one to the
desired conclusion? Your codes `NO_FIT_NORMALIZATION_PASS` and `MASS_P_OUT_OF_RANGE_AS_LAW_JUDGE`
suggest you have adjudicated this exact species before. Concretely: if we pick the PL2 witness
`h(u) = u − (3/2)u²` — already in Lean as a *falsifier plant*, not as a supplier — because its
Mellin is interior-zero-free, is that construction or is it fitting?

**Q4 — ORDER OF REMAINING CHECKS.** Nonvanishing is 1 of 4. The other three for a candidate
window are: `SlotAnchor` (`family i 0 = centeredXi 0`), existence of the Λ→∞ limit with
`TendstoLocallyUniformlyOn`, and tail control (`Rminus`, `Rplus` → 0 locally uniformly).
Which one kills fastest if the path is doomed? We want the cheapest killer first, not the
easiest confirmation.

## 4. Appendix — one procedural question (cheap, answer in one line)

Twice this session we nearly rebuilt what already existed: `Gammaℝ` sits in Mathlib, and
`riemannXi_eq_completedRiemannZeta` + `completedRiemannZeta_eq_Gamma_mul_riemannZeta` were
already in `ClassicalXiInterface.lean`. Both were found by accident, not by search.

The owner then pointed out that a discovery instrument already exists, and he is right:
`q3.lean.aristotle/aristotle_db/aristotle_proofs.db` (tracked, still being updated by Codex —
last touched 2026-08-05) holds 94 docs / **1410 lemmas** with `status ∈ {proven, in_progress,
sorry}` and full statements, with a parser `parse_lean.py` beside it.

The failure is therefore **coverage, not absence**. Indexing is manual and per-file
(`parse_lean.py import <file> <doc_id> <approach> <priority>`), so the base has drifted:

- RouteB on disk: **124** `.lean` files — in the base: **38 docs / 252 lemmas** (~31%).
- Queries for `riemannXi`, `completedRiemannZeta`, `centeredXi`: **0 hits**.
- Missing entirely: `ClassicalXiInterface`, `CenteredXiZeroNonzero`,
  `PosDefSelfAdjointRealSpectrum` (the M1 keystone proved overnight), and today's
  `S2GaugeNonvanishing`.

So the instrument that would have caught both near-duplications exists, is alive, and simply
was not asked — and could not have answered, because the relevant files were never imported.

Question: does making this base **complete and consulted** — bulk re-parse of the tree,
auto-refresh on the phase boundary (same trigger as the cartographer), and a mandatory
pre-flight query receipt before issuing any new goal / brief / Aristotle input — fall inside
the already-ratified unified contour as part of **P5**, or does it need its own verdict?
Note that the same drift disease you already diagnosed applies here: the base is a
🟢ALIVE component that silently stopped covering the live front.

## 5. Boundaries

Nothing is promoted. RH is not claimed. Bus 010 stays VOID, Goal 055 stays held, the G2/CCM
line and the files you froze are untouched. No Aristotle submission has been made. This
request asks for adjudication only; any construction that follows goes through owner
per-action OK.
