```yaml
BASE_HEAD: 636e075d915449b382096a00843a7e91f5273dce
TASK_ID: H2A_4_1B_3C_1_12_SELECTED_FERRERS_ABEL_POISSON_L2_LOCK_LEAN
AUTHORIZED_BY: PROSHKA_VERDICT_REQ_2026_08_23_W_W3_DIRECTIVE_CONFLICT_RESOLUTION_2026-08-23.md
AUTHORIZING_COMMIT: 2fbd6690
MODE: ONE_GOAL_ONE_COMMIT_LEAN_SOURCE_TRANSACTION
LEAN_EDIT: true
NUMERICS: false
ARISTOTLE: false

AUTHOR_OF_LEAN_SOURCE: CODEX
GATES_RUN_BY: LINUX_CLAUDE
NOTE_ON_SEPARATION: >
  The Lean source was written by Codex; the three gates below were run
  independently by the Linux body. Neither is a semantic attestation: kernel
  green is not admission, and an author cannot audit himself.

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
LEAN_GIT_BLOB: a064544af242608b8d09b94931412d1bccd5c392
LEAN_SHA256: fcadf926f2bc57a019f9f61aade993e08f2af0c071bc7cde11ab3b3d4b0dd93f
LEAN_LINES: 2073
SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_12_SELECTED_FERRERS_ABEL_POISSON_L2_2026-08-23.md

PUBLIC_SURFACE:
  - selectedFerrersReflectedAbel
  - selectedFerrersAbelLimit
  - selectedFerrersReflectedAbel_memLp
  - selectedFerrersAbelLimit_memLp
  - selectedFerrersReflectedAbel_tendsto_L2

EXPECTED_AXIOM_PROFILES:
  selectedFerrersReflectedAbel_memLp: [propext, Classical.choice, Quot.sound]
  selectedFerrersAbelLimit_memLp: [propext, Classical.choice, Quot.sound]
  selectedFerrersReflectedAbel_tendsto_L2: [propext, Classical.choice, Quot.sound]
  full_endpoint_vs_midpoint_eStar_seam_plant: [propext, Classical.choice, Quot.sound]
  zero_mass_is_load_bearing_plant: [propext, Classical.choice, Quot.sound]
  pointwise_without_domination_does_not_give_l2_plant: [propext, Classical.choice, Quot.sound]
  complex_even_packet_does_not_require_real_valuedness_plant: [propext, Classical.choice, Quot.sound]

CLOSES:
  - W3_SELECTED_FERRERS_ABEL_REFLECTED_L2_LOCK
OPENS: []

VERIFICATION_HANDOFF:
  - WORKDIR: q3.lean.aristotle
    CMD: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
    RESULT: EXIT_0_ZERO_ERRORS_ZERO_WARNINGS_7_AXIOM_PRINTS
  - WORKDIR: q3.lean.aristotle
    CMD: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersAbelPoissonL2
    RESULT: EXIT_0_BUILD_COMPLETED_7850_JOBS
  - WORKDIR: repository root
    CMD: scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
    RESULT: EXIT_0_Q3_CHECK_OK

SORRY_ADMIT_NATIVE_DECIDE: ABSENT
NEXT_LOAD_BEARING_GAP: W4_FIXED_K_SHIFTED_ROOT_ENERGY

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

# LINUX SOURCE RECORD — REQ V_H2A_4_1B_3C_1_12_SELECTED_FERRERS_ABEL_POISSON_L2

DATE: 2026-08-24
EXECUTOR: Codex (Linux body), owner goal-scoped operational grant
VERDICT: PROSHKA_VERDICT_REQ_2026_08_23_W_W3_DIRECTIVE_CONFLICT_RESOLUTION_2026-08-23.md
TASK: H2A_4_1B_3C_1_12_SELECTED_FERRERS_ABEL_POISSON_L2_LOCK_LEAN (W3)

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
ARISTOTLE: false
NUMERICS: false

BASE_HEAD (pasted verbatim from `git rev-parse HEAD` before commit):
636e075d915449b382096a00843a7e91f5273dce

## Deliverable

LEAN_PATH: `q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean`

Public surface:

```lean
noncomputable def selectedFerrersReflectedAbel
    (k : ℕ) (r u : ℝ) : ℂ

noncomputable def selectedFerrersAbelLimit
    (k : ℕ) (u : ℝ) : ℂ

theorem selectedFerrersReflectedAbel_memLp
    (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
  MemLp (selectedFerrersReflectedAbel k r) 2
    (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k)))

theorem selectedFerrersAbelLimit_memLp (k : ℕ) :
  MemLp (selectedFerrersAbelLimit k) 2
    (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k)))

theorem selectedFerrersReflectedAbel_tendsto_L2 (k : ℕ) :
  Tendsto
    (fun r : ℝ =>
      ∫ u : ℝ,
        ‖selectedFerrersReflectedAbel k r u -
          selectedFerrersAbelLimit k u‖ ^ 2
        ∂(dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))))
    (𝓝[Set.Ioo (0 : ℝ) 1] 1)
    (𝓝 0)
```

Direct imports added for the primary route:
`Mathlib.MeasureTheory.Integral.PeakFunction`; the file also imports the W2
packet-variation certificate and the existing Fourier, interval-integral and
product-integral APIs.

## Proof route executed

1. Exact packet locks: production packet evenness, integrability, zero mass,
   compact support and a global norm bound are inherited from the selected W2
   packet and proved without a real-valuedness surrogate.
2. Finite periodization: the fixed integer window
   `[-(k+2), k+2]` covers every active translate for
   `u ∈ I_m(selectedFerrersPreAnchorIndex k)`. Its Fourier coefficient is
   exactly `u⁻¹ • 𝓕 f_k (n/u)`.
3. Local Poisson kernel: the closed form is expanded into the absolutely
   convergent positive/negative geometric Fourier series. Nonnegativity,
   continuity and unit mass on `[0,1]` are proved with exact `2π`
   normalization.
4. Exact identity: packet evenness identifies the positive and negative
   Fourier coefficients; packet zero mass removes the constant coefficient.
   This gives
   `selectedFerrersReflectedAbel = (sqrt u / 2) * selectedPoissonAverage`
   for `0 ≤ r < 1` on the selected window.
5. Endpoint seams: the exact production center is identified with
   `selectedFerrersAbelLimit`. A finite seam set contains every translate that
   can hit either support endpoint; its `dStar` measure is zero.
6. Approximate identity: `[0,1]` is split at `1/2`. On each half,
   `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto` is applied to
   twice the Poisson kernel, whose half-mass is one. Continuity at `0` and `1`
   off the seam set and exact periodic reindexing assemble the center limit.
7. Measurability and domination: the exact packet is represented as a
   measurable closed-carrier piecewise function; finite periodization is
   jointly strongly measurable, hence the parameterized Poisson integral is
   strongly measurable. Positivity and unit mass transfer the fixed packet
   translate bound to every `r`.
8. Public `L²` result: both the Abel family and the production endpoint limit
   are bounded `MemLp` functions on the finite `dStar` window. Off-seam
   pointwise convergence plus the fixed squared bound closes the stated
   integral limit by filter-form dominated convergence.

## Mandatory plants

- `full_endpoint_vs_midpoint_eStar_seam_plant`: two summable sequences agree
  away from one seam index but have full versus half weight there, so their
  pointwise sums differ.
- `zero_mass_is_load_bearing_plant`: a nonzero zero-frequency coefficient
  produces the nonzero correction
  `-(1/2) * a * (sqrt u)⁻¹` for every `u > 0`.
- `pointwise_without_domination_does_not_give_l2_plant`: moving unit vectors
  on natural-number counting measure converge pointwise to zero while every
  squared integral remains one.
- `complex_even_packet_does_not_require_real_valuedness_plant`: the compactly
  supported integrable even packet `Icc(-1,1).indicator I` has value `I` at
  zero.

All three public theorems and all four plants print exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Forbidden-list compliance

- No continuous-source periodization theorem is applied to the jumping
  production packet.
- No real-valuedness hypothesis replaces exact complex evenness.
- No `tsum` is formed at `r = 1`.
- No full-endpoint/midpoint pointwise equality is asserted at seams.
- No pointwise-to-`L²` shortcut is used without a measurable fixed dominator.
- No fitted constants, Dirichlet–Jordan theorem, root-energy claim,
  cofinal-rate claim, new axiom, `sorry`, `admit`, `exact?`, or
  `native_decide` occurs.

## Gates

1. `env -u LD_LIBRARY_PATH lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean`
   from `q3.lean.aristotle` → exit 0; all seven axiom prints are the standard
   three only.
2. `env -u LD_LIBRARY_PATH lake build Q3.Proofs.RouteB.G6N1SelectedFerrersAbelPoissonL2`
   → `Build completed successfully (7850 jobs)`, exit 0.
3. `env -u LD_LIBRARY_PATH scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean`
   from repository root → `q3_check ok`, exit 0.

CLOSES: [W3_SELECTED_FERRERS_ABEL_REFLECTED_L2_LOCK]
OPENS: []

## Goal-close repair and registered outputs

The first registered
`python3 orchestrator/spine.py --refresh --reason goal-close` stopped on a
pre-existing invalid closed-enum AUTOPSY tag in
`q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_DLMF_FULL_FINITE_SPECTRUM_CROSSWALK_CLOSEOUT_2026-08-14.md`:

```text
AUTOPSY: dropped=SPECTRAL_LIMIT
```

`SPECTRAL_LIMIT` is not an `AUTOPSY_TAG_V1` token.  The line was repaired to
the exact admissible mechanism tag `SPECTRAL_ORDERING`; its explanatory note
was left unchanged.  The repair was checked by:

```text
python3 -m unittest orchestrator.tests.test_autopsy_sensor
  Ran 11 tests — OK
python3 scripts/build_autopsy_map.py
  autopsy events=18 walls=7 new_flags=0
```

The repeated `goal-close` then completed with `P9_STRICT_PASS`, semantic index
`PASS`, tool manifest `PASS`, and zero new AUTOPSY namewatch flags.  Its
registered tracked outputs are the Route B atom/inventory maps, Spine state and
view, the AUTOPSY/dependency/numeric/proof/sorry/taint graph pairs, and the two
canonical tracked project databases.  No Route B state, task pointer, theorem
statement, promotion state, or RH claim was changed by that refresh.

## Semantic-admission boundary

STATUS: KERNEL_GREEN_AWAITING_INDEPENDENT_SEMANTIC_ADMISSION

The Lean kernel and registered gates accept the exact W3 source, but control
v9 does not permit any downstream node to consume these declarations until an
independent semantic receipt admits the exact task, source object, consumer,
normalization, domain, quantifiers, and `CLOSES`/`OPENS` scope.

OUTCOME: W3_SELECTED_FERRERS_ABEL_POISSON_L2_LOCK_LEAN_KERNEL_GREEN
