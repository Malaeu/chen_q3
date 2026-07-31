# Goal 049 — EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz (canonical E*-bound, v3 class)

ISSUED: 2026-07-31, conductor-CLI on owner's order (Proshka reserved 049 for exactly
  this lemma; contour built from source-lock, not from a Mythos dispatch).
MODE: LOCAL_FIRST · NO_ARISTOTLE · SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen untouched
ROLE: this is Proshka's NEXT_LOAD_BEARING_GAP. Per the graph analysis it opens TWO
  canonical cells at once — hRm-canon (left-tail estimate near zero) and the habs
  technical hypotheses (MellinConvergent near zero). One lemma, two doors.

## ★ CONDUCTOR SOURCE-LOCK FINDING (read first — the hard math is already sealed)

The workhorse is ALREADY PROVED at the EXACT v3 class inside the sealed R6Export
(exported byte-preserved by Goal 044). File:
docs/routeB_bus/muntz_v3/RequestProject/R6Export/RiemannBoundaryCellBridge.lean:331

```lean
theorem riemannBoundaryCellBridge_Estar
    (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmeas : Measurable h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    ‖Estar h u‖ ≤ (K * b + (‖h 0‖ + K * b) + ‖h b‖) * Real.sqrt u
```

This is EXACTLY the v3 class: Icc 0 b support, LipschitzOnWith on Ico 0 b, direct
Measurable, NO `0<a`, NO global LipschitzWith. The R6 wrapper
`Estar_bounded_by_sqrt_of_zeroMass` (muntz_r6/…/Main.lean:63) only *packaged* it
behind `0<a` + global Lipschitz — the bridge underneath never needed them. Proshka
judged the wrapper, not the sealed bridge. Therefore the "only real mathematics of
the layer" is already done; Goal 049 is a thin naming/aliasing wrapper with the
EXPLICIT packed constant Proshka's A2 criterion demands (not `∃ C`).

## Target theorem (new file under muntz_v3/RequestProject/)

```lean
theorem EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      ‖Estar h u‖ ≤ (K * b + (‖h 0‖ + K * b) + ‖h b‖) * Real.sqrt u
```

Explicit packed constant C = K*b + (‖h 0‖ + K*b) + ‖h b‖ (Proshka A2: no `∃ C`).
Domain u ∈ Ioo 0 1 (matches the sealed bridge; consumers ask for (0, Λ⁻¹] ⊆ Ioo 0 1
under Λ ≥ 1 — confirm the inclusion is what the consumers need, do not silently widen).

## Proof route

1. Case b ≤ 0: then Icc 0 b is empty or {0}; hsupp forces h ≡ 0 off {0}, so Estar h u
   reduces to a trivial bound (handle explicitly; the RHS is ≥ 0). Or, if cleaner,
   take `hb : 0 < b` as a derived fact from a nonempty-support argument — but the
   b ≤ 0 branch must be closed, not assumed away.
2. Case 0 < b: direct application of the sealed
   `RequestProject.R6Export.riemannBoundaryCellBridge_Estar` with the v3 hypotheses
   passed through unchanged.
3. No re-derivation of the Riemann-sum estimate; the sealed bridge is the authority.

## Consumer hints (for the answer's ledger, NOT to be bundled into this goal)

- hRm-canon will consume this as the left-tail pointwise estimate feeding
  `mellin_differentiableAt_of_isBigO_rpow` (the √u gives the sub-(-1/2) decay R6
  used). The right tail is free by T1 (Estar ≡ 0 for u > b).
- habs-canon's technical hypothesis MellinConvergent near zero reduces to the same
  bound + T1 tail + measurability (per Goal 048 answer). EStarMellinAbsolute needs a
  separate standard per-dilate Dirichlet-summability wrapper (out of scope here).

## Mandatory plant (K1)

PLANT: instantiate the theorem on the PL1 witness h(u) = 1_Ioc(0,1]·u (b=K=1); it
touches zero, has an endpoint jump, nonzero mass — the theorem must accept it (its
mass hypothesis ∫h = 0 FAILS for PL1, so the plant is instead the DEPENDENCY-audit:
confirm the theorem's hypotheses are exactly the v3 class and that the proof calls
only the sealed bridge, no `0<a`/global-Lipschitz/R6-wrapper). If a zero-mass witness
is needed for a positive plant, use the PL2 witness (mass 0) and confirm acceptance.

## Forbidden

editing sealed R6Export/ or muntz_r6/; re-proving the bridge; adding `0<a` or global
LipschitzWith; `∃ C` in place of the explicit constant; taint; bundling hRm/habs
execution; promotion; Aristotle.

## Validation

```text
lake env lean <new-file>
lake build
taint scan
#print axioms EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz
axioms exactly [propext, Classical.choice, Quot.sound]
dependency scan: no 0<a, no LipschitzWith (global), no R6 wrapper call
  (only R6Export.riemannBoundaryCellBridge_Estar permitted)
```

## Success code

ESTAR_BOUND_V3CLASS_DISCHARGED

## Failure codes (exactly one, fail-closed)

ESTAR_BOUND_BLE0_BRANCH_GAP        (b ≤ 0 case not closable as stated)
ESTAR_BOUND_SEALED_BRIDGE_MISMATCH (sealed bridge type does not match — report diff)
ESTAR_BOUND_CONSTANT_MISMATCH      (packed C not derivable in explicit form)
LEAN_BUILD_FAIL

## Registered predictions

P049-C1 (conductor): closes as a ≤ 30-line wrapper over the sealed bridge; the only
  real work is the b ≤ 0 trivial branch, NOT the near-zero estimate.
P049-C2 (conductor): dependency scan clean — no 0<a, no global Lipschitz; the sealed
  bridge already carries the v3 class.
P049-HONEST (conductor, for judge re-scoring): this contradicts the earlier framing
  that E*-bound is "the only real remaining mathematics of the layer" — the math was
  already sealed in R6Export; the layer's remaining work is packaging, not analysis.
  Flag to Proshka: her P047-HRM ("main difficulty stays in the endpoint-aware
  zero-mass Riemann-sum estimate") is likely REFUTED by this source-lock.

## Answer requirements

049_estar_bounded_sqrt_zeromass_v3class.answer.md with MYTHOS_PROSHKA_HANDOFF +
ACTIONS LOG; explicit statement of which sealed lemma was consumed + its SHA;
dependency audit; b ≤ 0 branch shown; scoring P049-C1/C2/HONEST; goal consumed by
SHA-256; one non-promoting state row; ROUTE_B_STATE last; canon+mirror one
transaction; report — do not repair — any bridge-type divergence.
