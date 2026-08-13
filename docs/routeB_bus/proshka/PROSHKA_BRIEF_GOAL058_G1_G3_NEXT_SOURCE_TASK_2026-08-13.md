# Proshka Context Pack
Generated: 2026-08-13T21:46:43
Repo: /Users/emalam/GitHub/rh_lean_01_2026
Branch: rh_clean
HEAD: 52d1c48d
Range: 6d7437e257c5101b06df9f5aff53dc8ff4984cc8..66ed3c3365e9b522dc28de6c92c38cf5743b4759

## Working tree
```text
## rh_clean...origin/rh_clean
```

## Commit list (oneline)
```text
66ed3c33 [MacOS][rh_clean][Cartographer] Index Goal058 connector
3d6d5f7d [MacOS][rh_clean][Goal058] Prove complex Hermitian P59 connector
f20ed021 [MacOS][rh_clean][Goal058] Record Aristotle connector project
d106a3f4 [MacOS][rh_clean][Goal058] Lock Proshka Hermitian connector task
ad754cb5 [MacOS][rh_clean][Cartographer] Refresh RouteB inventory after Goal058 preflight
fea0965e [MacOS][rh_clean][Goal058] Record source preflight and Aristotle task request
```

## Range diff summary
```text
docs/cartographer/inventory_RouteB.json            | 662 ++++++++++++++-
 ...AL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md | 260 ++++++
 ...TOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md | 551 +++++++++++++
 ...OAL058_ARISTOTLE_SOURCE_LOCK_STOP_2026-08-13.md |  72 ++
 ..._SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md | 910 +++++++++++++++++++++
 .../ACTIVE/pipeline/PROSHKA_REASONING_TIME_LOG.md  |  96 ++-
 ..._HERMITIAN_P59_CONNECTOR_CLOSEOUT_2026-08-13.md | 139 ++++
 ...TRIAL_LINE_SCHUR_PREFLIGHT_REPORT_2026-08-13.md | 244 ++++++
 .../CCMProposition59ComplexHermitianConnector.lean | 367 +++++++++
 ...MProposition59SourceTrialFeshbachPreflight.lean | 475 +++++++++++
 q3.lean.aristotle/aristotle_db/aristotle_proofs.db | Bin 1761280 -> 1802240 bytes
 ...ermitian_connector_proshka_prompt_2026_08_13.md | 509 ++++++++++++
 ...omplex_hermitian_connector_task_2026_08_13.lean |  88 ++
 q3.lean.aristotle/aristotle_input/project_ids.txt  |   1 +
 14 files changed, 4356 insertions(+), 18 deletions(-)
```

## Per-commit stats
```text
66ed3c33 [MacOS][rh_clean][Cartographer] Index Goal058 connector
 docs/cartographer/inventory_RouteB.json            | 395 ++++++++++++++++-----
 q3.lean.aristotle/aristotle_db/aristotle_proofs.db | Bin 1761280 -> 1802240 bytes
 2 files changed, 300 insertions(+), 95 deletions(-)
```
```text
3d6d5f7d [MacOS][rh_clean][Goal058] Prove complex Hermitian P59 connector
 ..._HERMITIAN_P59_CONNECTOR_CLOSEOUT_2026-08-13.md | 139 ++++++++
 .../CCMProposition59ComplexHermitianConnector.lean | 367 +++++++++++++++++++++
 q3.lean.aristotle/aristotle_input/project_ids.txt  |   2 +-
 3 files changed, 507 insertions(+), 1 deletion(-)
```
```text
f20ed021 [MacOS][rh_clean][Goal058] Record Aristotle connector project
 q3.lean.aristotle/aristotle_input/project_ids.txt | 1 +
 1 file changed, 1 insertion(+)
```
```text
d106a3f4 [MacOS][rh_clean][Goal058] Lock Proshka Hermitian connector task
 ...TOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md | 551 +++++++++++++++++++++
 ...OAL058_ARISTOTLE_SOURCE_LOCK_STOP_2026-08-13.md |  72 +++
 .../ACTIVE/pipeline/PROSHKA_REASONING_TIME_LOG.md  |  70 +++
 ...ermitian_connector_proshka_prompt_2026_08_13.md | 509 +++++++++++++++++++
 ...omplex_hermitian_connector_task_2026_08_13.lean |  88 ++++
 5 files changed, 1290 insertions(+)
```
```text
ad754cb5 [MacOS][rh_clean][Cartographer] Refresh RouteB inventory after Goal058 preflight
 docs/cartographer/inventory_RouteB.json | 459 +++++++++++++++++++++++++++++++-
 1 file changed, 447 insertions(+), 12 deletions(-)
```
```text
fea0965e [MacOS][rh_clean][Goal058] Record source preflight and Aristotle task request
 ...AL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md | 260 ++++++
 ..._SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md | 910 +++++++++++++++++++++
 .../ACTIVE/pipeline/PROSHKA_REASONING_TIME_LOG.md  |  26 +-
 ...TRIAL_LINE_SCHUR_PREFLIGHT_REPORT_2026-08-13.md | 244 ++++++
 ...MProposition59SourceTrialFeshbachPreflight.lean | 475 +++++++++++
 5 files changed, 1908 insertions(+), 7 deletions(-)
```

## Per-commit diffs

### 66ed3c33
```diff
commit 66ed3c3365e9b522dc28de6c92c38cf5743b4759
Author: kdl2026 <kdl2026@dfr.de>
Date:   Thu Aug 13 21:35:32 2026 +0200

    [MacOS][rh_clean][Cartographer] Index Goal058 connector

diff --git a/docs/cartographer/inventory_RouteB.json b/docs/cartographer/inventory_RouteB.json
index 0bdbf6f0..047ec029 100644
--- a/docs/cartographer/inventory_RouteB.json
+++ b/docs/cartographer/inventory_RouteB.json
@@ -2,16 +2,11 @@
   "scope": "RouteB",
   "museum_excluded": "PrimeCert",
-  "files_scanned": 206,
-  "declarations": 1813,
-  "in_docs": 738,
-  "in_lemma_db": 1770,
-  "orphans": 32,
-  "uncatalogued": 32,
-  "orphan_files_top": [
-    [
-      "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
-      32
-    ]
-  ],
+  "files_scanned": 207,
+  "declarations": 1834,
+  "in_docs": 755,
+  "in_lemma_db": 1834,
+  "orphans": 0,
+  "uncatalogued": 0,
+  "orphan_files_top": [],
   "items": [
     {
@@ -1931,5 +1926,5 @@
       "line": 374,
       "signature": "theorem ccmWeilMatFinite_commutator (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) : ccmModeDiagFinite N * ccmWeilMatFinite mProject N - ccmWeilMatFinite mProject N * ccmModeDiagFinite N = Matrix.vecMulVec (ccmBetaFinite mProject N) (ccmEtaFinite N) - Matrix.vecMulVec (ccmEtaFinite N) (ccmBetaFinite mProject N)",
-      "in_docs": false,
+      "in_docs": true,
       "in_lemma_db": true,
       "orphan": false
@@ -2945,4 +2940,214 @@
       "orphan": false
     },
+    {
+      "kind": "def",
+      "name": "complexTrialLineProjection",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 32,
+      "signature": "noncomputable def complexTrialLineProjection {ι : Type*} (q : ι → ℂ) : Matrix ι ι ℂ",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "sourceCCMGroundProjectionScalar",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 38,
+      "signature": "noncomputable def sourceCCMGroundProjectionScalar (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (xi : CCMModeFinite i.N → ℝ) : ℂ",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "sourceCCMGroundProjectionErrorSq",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 47,
+      "signature": "noncomputable def sourceCCMGroundProjectionErrorSq (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (xi : CCMModeFinite i.N → ℝ) : ℝ",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "proposition59CCMKernelL2",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 56,
+      "signature": "noncomputable def proposition59CCMKernelL2 (L : ℝ) (N : ℕ) (z : ℂ) : ℝ",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "complexTrialLineProjection_isHermitian",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 64,
+      "signature": "theorem complexTrialLineProjection_isHermitian {ι : Type*} (q : ι → ℂ) : (complexTrialLineProjection q).IsHermitian",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "complexTrialLineProjection_sq_of_unit",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 72,
+      "signature": "theorem complexTrialLineProjection_sq_of_unit {ι : Type*} [Fintype ι] (q : ι → ℂ) (hq : star q ⬝ᵥ q = 1) : complexTrialLineProjection q * complexTrialLineProjection q = complexTrialLineProjection q",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "complexRow_projection_error_identity",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 83,
+      "signature": "private theorem complexRow_projection_error_identity {ι : Type*} [Fintype ι] (row : ι → ℂ) (xi : ι → ℝ) (hrow : star row ⬝ᵥ row = 1) : xi ⬝ᵥ xi - Complex.normSq (star row ⬝ᵥ (fun j => (xi j : ℂ))) = ∑ j, Complex.normSq ((xi j : ℂ) - (star row ⬝ᵥ (fun j => (xi j : ℂ))) * row j)",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "sourceCCMGroundProjectionErrorSq_eq_sum_normSq",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 149,
+      "signature": "theorem sourceCCMGroundProjectionErrorSq_eq_sum_normSq (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (xi : CCMModeFinite i.N → ℝ) : sourceCCMGroundProjectionErrorSq S i xi = ∑ j, Complex.normSq ((xi j : ℂ) - sourceCCMGroundProjectionScalar S i xi * D0Pstar.sourceCCMComplexRow S i j)",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "proposition59CCM_mode_sum_cauchy_schwarz",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 164,
+      "signature": "private theorem proposition59CCM_mode_sum_cauchy_schwarz (L : ℝ) (N : ℕ) (w : CCMModeFinite N → ℂ) (z : ℂ) : ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ ≤ Real.sqrt (∑ j, Complex.normSq (w j)) * Real.sqrt (∑ j, Complex.normSq (proposition59PoleKernel L (-ccmModeFinite N j) z))",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "proposition59CCMTransform_sub_sourceProjection_le",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 198,
+      "signature": "theorem proposition59CCMTransform_sub_sourceProjection_le (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (L : ℝ) (hL : 0 < L) (xi : CCMModeFinite i.N → ℝ) : 0 ≤ sourceCCMGroundProjectionErrorSq S i xi ∧ ∀ z : ℂ, ‖proposition59CCMTransform L i.N xi z - sourceCCMGroundProjectionScalar S i xi * proposition59CCMComplexTransform L i.N (D0Pstar.sourceCCMComplexRow S i) z‖ ≤ proposition59CCMKernelL2 L i.N z * Real.sqrt (sourceCCMGroundProjectionErrorSq S i xi)",
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "goal058ConnectorPhasePlantRow",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 261,
+      "signature": "def goal058ConnectorPhasePlantRow : Fin 2 → ℂ",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058ConnectorPhasePlant_no_common_real_phase",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 265,
+      "signature": "theorem goal058ConnectorPhasePlant_no_common_real_phase : ¬ ∃ (phase : ℂ) (q : Fin 2 → ℝ), Complex.normSq phase = 1 ∧ ∀ j, phase * goal058ConnectorPhasePlantRow j = (q j : ℂ)",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "goal058ConnectorZeroOverlapRow",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 285,
+      "signature": "def goal058ConnectorZeroOverlapRow : Fin 2 → ℂ",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "goal058ConnectorZeroOverlapXi",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 288,
+      "signature": "def goal058ConnectorZeroOverlapXi : Fin 2 → ℝ",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058ConnectorZeroOverlapRow_unit",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 290,
+      "signature": "theorem goal058ConnectorZeroOverlapRow_unit : star goal058ConnectorZeroOverlapRow ⬝ᵥ goal058ConnectorZeroOverlapRow = 1",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058ConnectorZeroOverlapPlant_projection_zero",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 298,
+      "signature": "theorem goal058ConnectorZeroOverlapPlant_projection_zero : (star goal058ConnectorZeroOverlapRow ⬝ᵥ (fun j => (goal058ConnectorZeroOverlapXi j : ℂ))) = 0 ∧ goal058ConnectorZeroOverlapXi ⬝ᵥ goal058ConnectorZeroOverlapXi - Complex.normSq (star goal058ConnectorZeroOverlapRow ⬝ᵥ (fun j => (goal058ConnectorZeroOverlapXi j : ℂ))) = 1",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "goal058ConnectorOrientationPlantRow",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 310,
+      "signature": "def goal058ConnectorOrientationPlantRow : Fin 1 → ℂ",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "goal058ConnectorOrientationPlantXi",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 313,
+      "signature": "def goal058ConnectorOrientationPlantXi : Fin 1 → ℝ",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058ConnectorOrientationPlantRow_unit",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 315,
+      "signature": "theorem goal058ConnectorOrientationPlantRow_unit : star goal058ConnectorOrientationPlantRow ⬝ᵥ goal058ConnectorOrientationPlantRow = 1",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058ConnectorOrientationPlant_error_zero",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 323,
+      "signature": "theorem goal058ConnectorOrientationPlant_error_zero : (star goal058ConnectorOrientationPlantRow ⬝ᵥ (fun j => (goal058ConnectorOrientationPlantXi j : ℂ))) = -Complex.I ∧ goal058ConnectorOrientationPlantXi ⬝ᵥ goal058ConnectorOrientationPlantXi - Complex.normSq (star goal058ConnectorOrientationPlantRow ⬝ᵥ (fun j => (goal058ConnectorOrientationPlantXi j : ℂ))) = 0 ∧ ∀ j, (goal058ConnectorOrientationPlantXi j : ℂ) - (star goal058ConnectorOrientationPlantRow ⬝ᵥ (fun k => (goal058ConnectorOrientationPlantXi k : ℂ))) * goal058ConnectorOrientationPlantRow j = 0",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058ConnectorCommutatorPlant_checks_retained",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean",
+      "line": 351,
+      "signature": "theorem goal058ConnectorCommutatorPlant_checks_retained : lagCommutatorObservable goal058PlantD goal058PlantK goal058PlantQ = 0 ∧ ¬ ∃ mu : ℝ, goal058PlantK *ᵥ goal058PlantQ = mu • goal058PlantQ",
+      "in_docs": false,
+      "in_lemma_db": true,
+      "orphan": false
+    },
     {
       "kind": "def",
@@ -2951,7 +3156,7 @@
       "line": 33,
       "signature": "def phaseRealifies {ι : Type*} (phase : ℂ) (row : ι → ℂ) (q : ι → ℝ) : Prop",
-      "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -2961,7 +3166,7 @@
       "line": 41,
       "signature": "def sourceCCMPhaseRealification (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (phase : ℂ) (q : CCMModeFinite i.N → ℝ) : Prop",
-      "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -2972,5 +3177,5 @@
       "signature": "def sourceCCMHasRealEvenPhase (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) : Prop",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -2982,5 +3187,5 @@
       "signature": "theorem phaseOne_realPart_requires_exact_reality {ι : Type*} (row : ι → ℂ) (h : phaseRealifies 1 row (fun j => (row j).re)) : ∀ j, row j = (row j).re",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -2992,6 +3197,6 @@
       "signature": "theorem dotProduct_self_eq_one_of_phaseRealifies {ι : Type*} [Fintype ι] (phase : ℂ) (row : ι → ℂ) (q : ι → ℝ) (hrow : star row ⬝ᵥ row = 1) (hphase : phaseRealifies phase row q) : q ⬝ᵥ q = 1",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3002,6 +3207,6 @@
       "signature": "theorem sourceCCMRealRow_unit_of_phaseRealification (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (phase : ℂ) (q : CCMModeFinite i.N → ℝ) (hphase : sourceCCMPhaseRealification S i phase q) : q ⬝ᵥ q = 1",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3012,6 +3217,6 @@
       "signature": "theorem sourceCCMComplexRow_even_of_phaseRealification_even (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (phase : ℂ) (q : CCMModeFinite i.N → ℝ) (hphase : sourceCCMPhaseRealification S i phase q) (hqEven : ∀ j, q (ccmNegFinite i.N j) = q j) : ∀ j, D0Pstar.sourceCCMComplexRow S i (ccmNegFinite i.N j) = D0Pstar.sourceCCMComplexRow S i j",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3022,6 +3227,6 @@
       "signature": "def proposition59CCMComplexCoefficient (N : ℕ) (q : CCMModeFinite N → ℂ) (k : ℤ) : ℂ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3032,6 +3237,6 @@
       "signature": "@[simp] theorem proposition59CCMComplexCoefficient_neg_mode (N : ℕ) (q : CCMModeFinite N → ℂ) (i : CCMModeFinite N) : proposition59CCMComplexCoefficient N q (-ccmModeFinite N i) = q i",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3042,5 +3247,5 @@
       "signature": "def proposition59CCMComplexTransform (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) : ℂ → ℂ",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3051,7 +3256,7 @@
       "line": 179,
       "signature": "theorem proposition59CCMComplexTransform_eq_mode_sum (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) (z : ℂ) : proposition59CCMComplexTransform L N q z = ((Real.sqrt L : ℂ)⁻¹) * ∑ i, q i * proposition59PoleKernel L (-ccmModeFinite N i) z",
-      "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3062,6 +3267,6 @@
       "signature": "theorem proposition59CCMTransform_eq_phase_mul_complexTransform (L : ℝ) (N : ℕ) (phase : ℂ) (row : CCMModeFinite N → ℂ) (q : CCMModeFinite N → ℝ) (hreal : ∀ i, phase * row i = (q i : ℂ)) (z : ℂ) : proposition59CCMTransform L N q z = phase * proposition59CCMComplexTransform L N row z",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3072,6 +3277,6 @@
       "signature": "theorem sourceCCMProposition59Transform_eq_phase_mul_complexTransform (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (L : ℝ) (phase : ℂ) (q : CCMModeFinite i.N → ℝ) (hphase : sourceCCMPhaseRealification S i phase q) (z : ℂ) : proposition59CCMTransform L i.N q z = phase * proposition59CCMComplexTransform L i.N (D0Pstar.sourceCCMComplexRow S i) z",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3082,5 +3287,5 @@
       "signature": "def trialLineProjection {ι : Type*} (q : ι → ℝ) : Matrix ι ι ℝ",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3092,6 +3297,6 @@
       "signature": "def trialLineComplement {ι : Type*} [DecidableEq ι] (q : ι → ℝ) : Matrix ι ι ℝ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3102,5 +3307,5 @@
       "signature": "def trialRayleigh {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (q : ι → ℝ) : ℝ",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3112,5 +3317,5 @@
       "signature": "def trialCoupling {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ) (q : ι → ℝ) : ι → ℝ",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3122,6 +3327,6 @@
       "signature": "def ccmReflectionMatrix (N : ℕ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3132,6 +3337,6 @@
       "signature": "def ccmEvenProjection (N : ℕ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3142,6 +3347,6 @@
       "signature": "def ccmOddProjection (N : ℕ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3152,5 +3357,5 @@
       "signature": "def evenComplementBlock (N : ℕ) (K : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ) (q : CCMModeFinite N → ℝ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3162,5 +3367,5 @@
       "signature": "def oddSectorBlock (N : ℕ) (K : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3172,5 +3377,5 @@
       "signature": "def oddTrialMass (N : ℕ) (q : CCMModeFinite N → ℝ) : ℝ",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3182,6 +3387,6 @@
       "signature": "theorem trialLineProjection_sq {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : q ⬝ᵥ q = 1) : trialLineProjection q * trialLineProjection q = trialLineProjection q",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3192,5 +3397,5 @@
       "signature": "theorem full_trialLine_four_block_identity {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ) (q : ι → ℝ) : K = trialLineProjection q * K * trialLineProjection q + trialLineProjection q * K * trialLineComplement q + trialLineComplement q * K * trialLineProjection q + trialLineComplement q * K * trialLineComplement q",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3202,5 +3407,5 @@
       "signature": "theorem ccmWeilMatFinite_full_trialLine_four_block_identity (mProject N : ℕ) (q : CCMModeFinite N → ℝ) : ccmWeilMatFinite mProject N = trialLineProjection q * ccmWeilMatFinite mProject N * trialLineProjection q + trialLineProjection q * ccmWeilMatFinite mProject N * trialLineComplement q + trialLineComplement q * ccmWeilMatFinite mProject N * trialLineProjection q + trialLineComplement q * ccmWeilMatFinite mProject N * trialLineComplement q",
       "in_docs": true,
-      "in_lemma_db": false,
+      "in_lemma_db": true,
       "orphan": false
     },
@@ -3211,7 +3416,7 @@
       "line": 337,
       "signature": "def lagCommutatorObservable {ι : Type*} [Fintype ι] (D K : Matrix ι ι ℝ) (q : ι → ℝ) : ℝ",
-      "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3222,6 +3427,6 @@
       "signature": "theorem lagCommutatorObservable_zero_of_isSymm {ι : Type*} [Fintype ι] (D K : Matrix ι ι ℝ) (q : ι → ℝ) (hD : D.IsSymm) (hK : K.IsSymm) : lagCommutatorObservable D K q = 0",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3232,6 +3437,6 @@
       "signature": "theorem ccmLagCommutatorObservable_zero (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) (q : CCMModeFinite N → ℝ) : lagCommutatorObservable (ccmModeDiagFinite N) (ccmWeilMatFinite mProject N) q = 0",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3242,6 +3447,6 @@
       "signature": "def goal058SourceTrialPreflightStop : Goal058SourceTrialPreflightStop",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3252,6 +3457,6 @@
       "signature": "theorem goal058SourceTrialPreflightStop_eq : goal058SourceTrialPreflightStop = Goal058SourceTrialPreflightStop.sourceComplexRealGroundCrosswalkMismatch",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3262,6 +3467,6 @@
       "signature": "abbrev Goal058PlantCarrier",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3272,6 +3477,6 @@
       "signature": "def goal058PlantD : Matrix Goal058PlantCarrier Goal058PlantCarrier ℝ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3282,6 +3487,6 @@
       "signature": "def goal058PlantK : Matrix Goal058PlantCarrier Goal058PlantCarrier ℝ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3292,6 +3497,6 @@
       "signature": "def goal058PlantEta : Goal058PlantCarrier → ℝ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3302,6 +3507,6 @@
       "signature": "def goal058PlantBeta : Goal058PlantCarrier → ℝ",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3311,7 +3516,7 @@
       "line": 416,
       "signature": "def goal058PlantQ : Goal058PlantCarrier → ℝ",
-      "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3322,6 +3527,6 @@
       "signature": "theorem goal058Plant_commutator : goal058PlantD * goal058PlantK - goal058PlantK * goal058PlantD = Matrix.vecMulVec goal058PlantBeta goal058PlantEta - Matrix.vecMulVec goal058PlantEta goal058PlantBeta",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3332,6 +3537,6 @@
       "signature": "theorem goal058PlantQ_reflection_even : ∀ i, goal058PlantQ (ccmNegFinite 1 i) = goal058PlantQ i",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3341,7 +3546,7 @@
       "line": 433,
       "signature": "theorem goal058PlantQ_not_eigenvector : ¬ ∃ mu : ℝ, goal058PlantK *ᵥ goal058PlantQ = mu • goal058PlantQ",
-      "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3351,7 +3556,7 @@
       "line": 442,
       "signature": "theorem goal058Plant_lagCommutatorObservable_zero : lagCommutatorObservable goal058PlantD goal058PlantK goal058PlantQ = 0",
-      "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_docs": true,
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3362,6 +3567,6 @@
       "signature": "def goal058PlantClassification : Goal058CommutatorClassification",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
@@ -3372,6 +3577,6 @@
       "signature": "theorem goal058PlantClassification_eq : goal058PlantClassification = Goal058CommutatorClassification.lagSourceTautologicalZero",
       "in_docs": false,
-      "in_lemma_db": false,
-      "orphan": true
+      "in_lemma_db": true,
+      "orphan": false
     },
     {
diff --git a/q3.lean.aristotle/aristotle_db/aristotle_proofs.db b/q3.lean.aristotle/aristotle_db/aristotle_proofs.db
index 9751f230..69347c78 100644
Binary files a/q3.lean.aristotle/aristotle_db/aristotle_proofs.db and b/q3.lean.aristotle/aristotle_db/aristotle_proofs.db differ
```

### 3d6d5f7d
```diff
commit 3d6d5f7d1dc1f9c4708917008e9efa19e3d91237
Author: kdl2026 <kdl2026@dfr.de>
Date:   Thu Aug 13 21:34:31 2026 +0200

    [MacOS][rh_clean][Goal058] Prove complex Hermitian P59 connector

diff --git a/q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_CLOSEOUT_2026-08-13.md b/q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_CLOSEOUT_2026-08-13.md
new file mode 100644
index 00000000..5203f399
--- /dev/null
+++ b/q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_CLOSEOUT_2026-08-13.md
@@ -0,0 +1,139 @@
+# Goal 058 complex-Hermitian P59 connector closeout
+
+Date: 2026-08-13
+
+## Verdict
+
+```yaml
+TARGET_ID: GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR
+PRIMARY: ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR
+VERDICT: PASS_FINITE_EXACT_CONNECTOR
+SUCCESS: GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_PROVED
+SCOPE: FINITE_CELL
+G1: OPEN
+G3: OPEN
+ROUTE: CHALLENGER_NOT_RH
+ROUTE_PROMOTION: false
+RH_CLAIM: false
+```
+
+## Source lock and execution
+
+The authoritative Proshka verdict selected the exact theorem surface archived
+at:
+
+```text
+docs/routeB_bus/proshka/
+  PROSHKA_VERDICT_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md
+```
+
+The source-locked request packet was committed at
+`d106a3f4356664c871d1bf96c06f6e5324643e4e`.  Aristotle project
+`7e661f28-7943-4c6b-83e9-787c2eed4683`, task
+`f958ac79-9673-4110-b9f7-538ee6673d38`, completed after 25m02s with service
+summary `GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_PROVED`.
+
+Downloaded archive:
+
+```text
+q3.lean.aristotle/aristotle_output/
+  7e661f28-7943-4c6b-83e9-787c2eed4683.tar.gz
+sha256: 6a9868faef17dcdb52134b8379aa47232ba7ec6794efc1b52b67260b849702f1
+```
+
+Archive comparison against the submitted 54-file bundle found one new Q3
+source file only.  The temporary Aristotle-side Lean-4.28 compatibility edit to
+`QuotientByRadicalPosDefMatrix.lean` was absent from the returned diff; that
+dependency remained byte-identical to the submitted source.
+
+## Integrated theorem
+
+```text
+q3.lean.aristotle/Q3/Proofs/RouteB/
+  CCMProposition59ComplexHermitianConnector.lean
+sha256: dc5e858863647224c17256b3cf629efc000ca81cbea4fb9cfd02fef28a6bc4eb
+```
+
+The file proves the exact public head
+`Q3.RouteB.proposition59CCMTransform_sub_sourceProjection_le`:
+
+- `D0Pstar.sourceCCMComplexRow S i` is the literal complex unit source row;
+- `sourceCCMGroundProjectionScalar S i xi` is its Hermitian projection
+  coefficient against the real P59 row `xi`;
+- `sourceCCMGroundProjectionErrorSq S i xi` is exactly the finite sum of
+  coefficient residual norm-squares;
+- the P59 transform mismatch is bounded by the exact P59 kernel L2 norm times
+  the square root of that projective error;
+- the existing `source mode n -> P59 pole -n` coordinate is preserved.
+
+The theorem assumes no phase realification, source parity, eigenvector,
+bottomness, simplicity, spectral gap, complement coercivity, tracking rate,
+cofinal schedule, convergence, global positivity, or RH statement.  It does
+not assert that the projective error is small.
+
+Mandatory exact plants cover:
+
+1. a two-coordinate `[1, I]` row with no common realifying phase;
+2. a zero-overlap branch with no division by overlap;
+3. the one-coordinate `[I]` orientation where the coefficient is `-I` and the
+   error is zero;
+4. retention of the preflight scalar-commutator tautology/non-eigenvector
+   falsifiers as checks only.
+
+The Proshka validation regex forbade the commutator identifier while P3
+simultaneously required its exact retained check.  The two identifier hits in
+the final file occur only in the P3 plant theorem and its supplied lemma; no
+connector definition or proof consumes the commutator observable.
+
+## Validation
+
+```text
+direct lake env lean: PASS
+target lake build: PASS (7792 jobs)
+full lake build: PASS (7817 jobs)
+q3_check: PASS
+forbidden proof tokens: NONE
+git diff --check: PASS
+public theorem axioms: [propext, Classical.choice, Quot.sound]
+```
+
+One warning is retained honestly: the locked theorem head contains
+`hL : 0 < L`, but the proved estimate is uniform in `L`, so the proof does not
+consume that binder.
+
+## Residual Goal 058 obligations
+
+The connector removes the finite complex-source / real-P59 object mismatch.
+It does not supply either open wall:
+
+```text
+G1: uniform literal CCM spectral-gap source remains open.
+G3: a same-family cofinal theorem forcing
+    sourceCCMGroundProjectionErrorSq S_j i_j xi_j -> 0
+    (with the required compact P59 kernel control) remains open.
+```
+
+Finite numerics, including the earlier M1 control cell, do not discharge these
+cofinal suppliers.
+
+## Search flags and arsenal
+
+```yaml
+SEARCH_FLAGS:
+  - GOAL058_COMPLEX_HERMITIAN_CONNECTOR
+  - SOURCE_CCM_GROUND_PROJECTION_ERROR_SQ
+  - COFINAL_PROJECTIVE_ERROR_DECAY
+  - UNIFORM_LITERAL_CCM_SPECTRAL_GAP
+ARSENAL_USED:
+  - Proshka source-locked task design
+  - Aristotle exact Lean proof search
+  - Hermitian rank-one projection
+  - exact P59 mode-sum identities
+  - finite Cauchy-Schwarz
+  - production Lean 4.26 validation
+AUTOPSY: >-
+  The unavailable common-phase realification was not manufactured. The finite
+  object mismatch is now an exact inequality, exposing the true remaining G3
+  supplier as cofinal decay of the literal Hermitian projective error. G1 is
+  unchanged.
+```
diff --git a/q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean b/q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
new file mode 100644
index 00000000..672639e0
--- /dev/null
+++ b/q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
@@ -0,0 +1,367 @@
+import Q3.Proofs.RouteB.CCMProposition59SourceTrialFeshbachPreflight
+
+set_option linter.mathlibStandardSet false
+
+/-!
+# Goal 058 complex Hermitian Proposition-59 connector
+
+The literal CCM source coefficient row is complex and unit; the Proposition-59
+transform consumes a real row.  This file removes that object mismatch without
+any realification, parity, gap, tracking, or spectral hypothesis: it uses the
+exact Hermitian rank-one projection onto the literal complex source line.
+
+For a real row `xi` the scalar `sourceCCMGroundProjectionScalar S i xi` is the
+exact Hermitian projection coefficient of `xi` onto the literal complex source
+row, and `sourceCCMGroundProjectionErrorSq S i xi` is the exact squared
+coefficient-space distance from `xi` to that complex line.  The main theorem
+bounds the pointwise difference between the real Proposition-59 transform of
+`xi` and the projection-scaled complex source transform by the exact P59 kernel
+`L²`-norm times the square root of that projective error.
+
+Nothing here asserts that the projective error is small or that it decays.
+-/
+
+noncomputable section
+
+namespace Q3.RouteB
+
+open Matrix
+open scoped BigOperators
+
+/-- Hermitian rank-one matrix of the complex trial line spanned by `q`. -/
+noncomputable def complexTrialLineProjection
+    {ι : Type*} (q : ι → ℂ) : Matrix ι ι ℂ :=
+  Matrix.vecMulVec q (star q)
+
+/-- Exact Hermitian projection coefficient of the real row `xi` onto the
+literal complex CCM source line. -/
+noncomputable def sourceCCMGroundProjectionScalar
+    (S : D0Pstar.ProlateCanonicalSourceData)
+    (i : D0Pstar.PairIndex)
+    (xi : CCMModeFinite i.N → ℝ) : ℂ :=
+  star (D0Pstar.sourceCCMComplexRow S i) ⬝ᵥ
+    (fun j => (xi j : ℂ))
+
+/-- Exact squared coefficient-space distance from `xi` to the complex source
+line. -/
+noncomputable def sourceCCMGroundProjectionErrorSq
+    (S : D0Pstar.ProlateCanonicalSourceData)
+    (i : D0Pstar.PairIndex)
+    (xi : CCMModeFinite i.N → ℝ) : ℝ :=
+  xi ⬝ᵥ xi -
+    Complex.normSq (sourceCCMGroundProjectionScalar S i xi)
+
+/-- Exact `L²` size of the finite Proposition-59 pole kernel family, in the
+locked coordinate `source mode n → P59 pole -n`. -/
+noncomputable def proposition59CCMKernelL2
+    (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
+  ‖((Real.sqrt L : ℂ)⁻¹)‖ *
+    Real.sqrt
+      (∑ j : CCMModeFinite N,
+        Complex.normSq
+          (proposition59PoleKernel L (-ccmModeFinite N j) z))
+
+theorem complexTrialLineProjection_isHermitian
+    {ι : Type*} (q : ι → ℂ) :
+    (complexTrialLineProjection q).IsHermitian := by
+  show (complexTrialLineProjection q)ᴴ = complexTrialLineProjection q
+  ext i j
+  simp [complexTrialLineProjection, Matrix.conjTranspose_apply,
+    Matrix.vecMulVec_apply, mul_comm]
+
+theorem complexTrialLineProjection_sq_of_unit
+    {ι : Type*} [Fintype ι]
+    (q : ι → ℂ)
+    (hq : star q ⬝ᵥ q = 1) :
+    complexTrialLineProjection q * complexTrialLineProjection q =
+      complexTrialLineProjection q := by
+  rw [complexTrialLineProjection, Matrix.vecMulVec_mul_vecMulVec, hq, one_smul]
+
+/-- Generic Hermitian projective error identity for an arbitrary unit complex
+row.  This is a private helper: the public interface always hard-codes the
+literal source row. -/
+private theorem complexRow_projection_error_identity
+    {ι : Type*} [Fintype ι]
+    (row : ι → ℂ) (xi : ι → ℝ)
+    (hrow : star row ⬝ᵥ row = 1) :
+    xi ⬝ᵥ xi -
+        Complex.normSq (star row ⬝ᵥ (fun j => (xi j : ℂ))) =
+      ∑ j,
+        Complex.normSq
+          ((xi j : ℂ) -
+            (star row ⬝ᵥ (fun j => (xi j : ℂ))) * row j) := by
+  classical
+  set c : ℂ := star row ⬝ᵥ (fun j => (xi j : ℂ)) with hc
+  have hcdef : c = ∑ j, (starRingEnd ℂ) (row j) * (xi j : ℂ) := by
+    simp [hc, dotProduct]
+  have hrow' : ∑ j, (starRingEnd ℂ) (row j) * row j = 1 := by
+    simpa [dotProduct] using hrow
+  have hconj : (starRingEnd ℂ) c = ∑ j, row j * (xi j : ℂ) := by
+    rw [hcdef, map_sum]
+    exact Finset.sum_congr rfl fun j _ => by
+      simp [mul_comm]
+  have hxi : ((xi ⬝ᵥ xi : ℝ) : ℂ) = ∑ j, (xi j : ℂ) * (xi j : ℂ) := by
+    simp [dotProduct]
+  have hterm : ∀ j : ι,
+      ((Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ) =
+        (xi j : ℂ) * (xi j : ℂ) -
+          (starRingEnd ℂ) c * ((xi j : ℂ) * (starRingEnd ℂ) (row j)) -
+          c * (row j * (xi j : ℂ)) +
+          (c * (starRingEnd ℂ) c) *
+            ((starRingEnd ℂ) (row j) * row j) := by
+    intro j
+    rw [← Complex.mul_conj]
+    simp only [map_sub, map_mul, Complex.conj_ofReal]
+    ring
+  have hcast :
+      ((∑ j, Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ) =
+        ((xi ⬝ᵥ xi : ℝ) : ℂ) - ((Complex.normSq c : ℝ) : ℂ) := by
+    rw [Complex.ofReal_sum]
+    calc
+      (∑ j, ((Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ)) =
+          ∑ j,
+            ((xi j : ℂ) * (xi j : ℂ) -
+              (starRingEnd ℂ) c * ((xi j : ℂ) * (starRingEnd ℂ) (row j)) -
+              c * (row j * (xi j : ℂ)) +
+              (c * (starRingEnd ℂ) c) *
+                ((starRingEnd ℂ) (row j) * row j)) :=
+        Finset.sum_congr rfl fun j _ => hterm j
+      _ = (∑ j, (xi j : ℂ) * (xi j : ℂ)) -
+            (starRingEnd ℂ) c *
+              (∑ j, (xi j : ℂ) * (starRingEnd ℂ) (row j)) -
+            c * (∑ j, row j * (xi j : ℂ)) +
+            (c * (starRingEnd ℂ) c) *
+              (∑ j, (starRingEnd ℂ) (row j) * row j) := by
+        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
+          Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
+          Finset.mul_sum]
+      _ = ((xi ⬝ᵥ xi : ℝ) : ℂ) - ((Complex.normSq c : ℝ) : ℂ) := by
+        have hswap : (∑ j, (xi j : ℂ) * (starRingEnd ℂ) (row j)) = c := by
+          rw [hcdef]
+          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
+        rw [hswap, ← hconj, hrow', hxi, ← Complex.mul_conj]
+        ring
+  exact_mod_cast hcast.symm
+
+/-- The exact projective error of `xi` against the literal complex source line
+is the total squared coefficient residual after removing the Hermitian
+projection.  No realification or parity input is used. -/
+theorem sourceCCMGroundProjectionErrorSq_eq_sum_normSq
+    (S : D0Pstar.ProlateCanonicalSourceData)
+    (i : D0Pstar.PairIndex)
+    (xi : CCMModeFinite i.N → ℝ) :
+    sourceCCMGroundProjectionErrorSq S i xi =
+      ∑ j,
+        Complex.normSq
+          ((xi j : ℂ) -
+            sourceCCMGroundProjectionScalar S i xi *
+              D0Pstar.sourceCCMComplexRow S i j) := by
+  exact complexRow_projection_error_identity
+    (D0Pstar.sourceCCMComplexRow S i) xi
+    (D0Pstar.sourceCCMComplexRow_unit S i)
+
+/-- Finite Cauchy-Schwarz for the exact source-locked P59 mode sum. -/
+private theorem proposition59CCM_mode_sum_cauchy_schwarz
+    (L : ℝ) (N : ℕ) (w : CCMModeFinite N → ℂ) (z : ℂ) :
+    ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ ≤
+      Real.sqrt (∑ j, Complex.normSq (w j)) *
+        Real.sqrt
+          (∑ j,
+            Complex.normSq
+              (proposition59PoleKernel L (-ccmModeFinite N j) z)) := by
+  classical
+  calc
+    ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ ≤
+        ∑ j, ‖w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ :=
+      norm_sum_le _ _
+    _ = ∑ j, ‖w j‖ * ‖proposition59PoleKernel L (-ccmModeFinite N j) z‖ := by
+      exact Finset.sum_congr rfl fun j _ => norm_mul _ _
+    _ ≤ Real.sqrt (∑ j, ‖w j‖ ^ 2) *
+          Real.sqrt
+            (∑ j,
+              ‖proposition59PoleKernel L (-ccmModeFinite N j) z‖ ^ 2) :=
+      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
+    _ = Real.sqrt (∑ j, Complex.normSq (w j)) *
+          Real.sqrt
+            (∑ j,
+              Complex.normSq
+                (proposition59PoleKernel L (-ccmModeFinite N j) z)) := by
+      simp [Complex.normSq_eq_norm_sq]
+
+/-- Exact finite Hermitian connector.  The projective error is nonnegative, and
+the pointwise difference between the real Proposition-59 transform of `xi` and
+the projection-scaled complex source transform is bounded by the exact P59
+kernel `L²`-norm times the square root of that error.
+
+The positivity binder `hL` is part of the locked theorem head; the bound is in
+fact uniform in `L`, so the proof does not consume it. -/
+theorem proposition59CCMTransform_sub_sourceProjection_le
+    (S : D0Pstar.ProlateCanonicalSourceData)
+    (i : D0Pstar.PairIndex)
+    (L : ℝ) (hL : 0 < L)
+    (xi : CCMModeFinite i.N → ℝ) :
+    0 ≤ sourceCCMGroundProjectionErrorSq S i xi ∧
+    ∀ z : ℂ,
+      ‖proposition59CCMTransform L i.N xi z -
+          sourceCCMGroundProjectionScalar S i xi *
+            proposition59CCMComplexTransform L i.N
+              (D0Pstar.sourceCCMComplexRow S i) z‖
+        ≤ proposition59CCMKernelL2 L i.N z *
+            Real.sqrt (sourceCCMGroundProjectionErrorSq S i xi) := by
+  classical
+  set c : ℂ := sourceCCMGroundProjectionScalar S i xi with hc
+  set row : CCMModeFinite i.N → ℂ := D0Pstar.sourceCCMComplexRow S i with hrowdef
+  set w : CCMModeFinite i.N → ℂ := fun j => (xi j : ℂ) - c * row j with hw
+  have herr :
+      sourceCCMGroundProjectionErrorSq S i xi = ∑ j, Complex.normSq (w j) :=
+    sourceCCMGroundProjectionErrorSq_eq_sum_normSq S i xi
+  have hnonneg : 0 ≤ sourceCCMGroundProjectionErrorSq S i xi := by
+    rw [herr]
+    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
+  refine ⟨hnonneg, fun z => ?_⟩
+  have hsplit :
+      proposition59CCMTransform L i.N xi z -
+          c * proposition59CCMComplexTransform L i.N row z =
+        ((Real.sqrt L : ℂ)⁻¹) *
+          ∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z := by
+    rw [proposition59CCMTransform_eq_mode_sum,
+      proposition59CCMComplexTransform_eq_mode_sum]
+    have hsum :
+        (∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z) =
+          (∑ j, (xi j : ℂ) *
+              proposition59PoleKernel L (-ccmModeFinite i.N j) z) -
+            c * ∑ j, row j *
+              proposition59PoleKernel L (-ccmModeFinite i.N j) z := by
+      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
+      exact Finset.sum_congr rfl fun j _ => by simp [hw, sub_mul, mul_assoc]
+    rw [hsum]
+    ring
+  rw [hsplit, norm_mul, herr]
+  have hcs := proposition59CCM_mode_sum_cauchy_schwarz L i.N w z
+  have hnormnn : (0 : ℝ) ≤ ‖((Real.sqrt L : ℂ)⁻¹)‖ := norm_nonneg _
+  calc
+    ‖((Real.sqrt L : ℂ)⁻¹)‖ *
+        ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z‖ ≤
+        ‖((Real.sqrt L : ℂ)⁻¹)‖ *
+          (Real.sqrt (∑ j, Complex.normSq (w j)) *
+            Real.sqrt
+              (∑ j,
+                Complex.normSq
+                  (proposition59PoleKernel L
+                    (-ccmModeFinite i.N j) z))) := by
+      exact mul_le_mul_of_nonneg_left hcs hnormnn
+    _ = proposition59CCMKernelL2 L i.N z *
+          Real.sqrt (∑ j, Complex.normSq (w j)) := by
+      rw [proposition59CCMKernelL2]
+      ring
+
+/-! ### Mandatory falsifier plants -/
+
+/-- P2 plant: a two-coordinate complex row with entries `1` and `Complex.I`. -/
+def goal058ConnectorPhasePlantRow : Fin 2 → ℂ := ![1, Complex.I]
+
+/-- P2: no common unit phase turns the plant row into a real row, so the
+Hermitian connector may not presuppose one. -/
+theorem goal058ConnectorPhasePlant_no_common_real_phase :
+    ¬ ∃ (phase : ℂ) (q : Fin 2 → ℝ),
+        Complex.normSq phase = 1 ∧
+          ∀ j, phase * goal058ConnectorPhasePlantRow j = (q j : ℂ) := by
+  rintro ⟨phase, q, hunit, hreal⟩
+  have h0 := hreal 0
+  have h1 := hreal 1
+  simp [goal058ConnectorPhasePlantRow] at h0 h1
+  have hre : phase.re = 0 := by
+    have := congrArg Complex.im h1
+    simpa [Complex.ext_iff, Complex.mul_im, Complex.mul_re] using this
+  have him : phase.im = 0 := by
+    have := congrArg Complex.im h0
+    simpa using this
+  have : phase = 0 := by
+    apply Complex.ext <;> simp [hre, him]
+  rw [this] at hunit
+  simp at hunit
+
+/-- P5 plant: a unit complex row orthogonal to the tested real row. -/
+def goal058ConnectorZeroOverlapRow : Fin 2 → ℂ := ![1, 0]
+
+/-- P5 plant: the tested real row. -/
+def goal058ConnectorZeroOverlapXi : Fin 2 → ℝ := ![0, 1]
+
+theorem goal058ConnectorZeroOverlapRow_unit :
+    star goal058ConnectorZeroOverlapRow ⬝ᵥ goal058ConnectorZeroOverlapRow
+      = 1 := by
+  simp [goal058ConnectorZeroOverlapRow, dotProduct, Fin.sum_univ_succ]
+
+/-- P5: the Hermitian projection scalar vanishes on the orthogonal plant, and
+the projective error is the full mass of the tested row.  No division by the
+overlap occurs anywhere. -/
+theorem goal058ConnectorZeroOverlapPlant_projection_zero :
+    (star goal058ConnectorZeroOverlapRow ⬝ᵥ
+        (fun j => (goal058ConnectorZeroOverlapXi j : ℂ))) = 0 ∧
+      goal058ConnectorZeroOverlapXi ⬝ᵥ goal058ConnectorZeroOverlapXi -
+          Complex.normSq
+            (star goal058ConnectorZeroOverlapRow ⬝ᵥ
+              (fun j => (goal058ConnectorZeroOverlapXi j : ℂ))) = 1 := by
+  constructor <;>
+    simp [goal058ConnectorZeroOverlapRow, goal058ConnectorZeroOverlapXi,
+      dotProduct, Fin.sum_univ_succ]
+
+/-- P6 plant: a one-coordinate purely imaginary source row. -/
+def goal058ConnectorOrientationPlantRow : Fin 1 → ℂ := ![Complex.I]
+
+/-- P6 plant: the tested one-coordinate real row. -/
+def goal058ConnectorOrientationPlantXi : Fin 1 → ℝ := ![1]
+
+theorem goal058ConnectorOrientationPlantRow_unit :
+    star goal058ConnectorOrientationPlantRow ⬝ᵥ
+        goal058ConnectorOrientationPlantRow = 1 := by
+  simp [goal058ConnectorOrientationPlantRow, dotProduct]
+
+/-- P6: with the Hermitian (conjugate-left) orientation the projection scalar
+is `-I` and the coefficient error is exactly zero; a conjugation or orientation
+reversal would break this. -/
+theorem goal058ConnectorOrientationPlant_error_zero :
+    (star goal058ConnectorOrientationPlantRow ⬝ᵥ
+        (fun j => (goal058ConnectorOrientationPlantXi j : ℂ))) = -Complex.I ∧
+      goal058ConnectorOrientationPlantXi ⬝ᵥ
+            goal058ConnectorOrientationPlantXi -
+          Complex.normSq
+            (star goal058ConnectorOrientationPlantRow ⬝ᵥ
+              (fun j =>
+                (goal058ConnectorOrientationPlantXi j : ℂ))) = 0 ∧
+      ∀ j,
+        (goal058ConnectorOrientationPlantXi j : ℂ) -
+            (star goal058ConnectorOrientationPlantRow ⬝ᵥ
+              (fun k =>
+                (goal058ConnectorOrientationPlantXi k : ℂ))) *
+              goal058ConnectorOrientationPlantRow j = 0 := by
+  refine ⟨?_, ?_, ?_⟩
+  · simp [goal058ConnectorOrientationPlantRow,
+      goal058ConnectorOrientationPlantXi, dotProduct]
+  · simp [goal058ConnectorOrientationPlantRow,
+      goal058ConnectorOrientationPlantXi, dotProduct]
+  · intro j
+    fin_cases j
+    simp [goal058ConnectorOrientationPlantRow,
+      goal058ConnectorOrientationPlantXi, dotProduct]
+
+/-- P3: the exact commutator-tautology falsifiers of the preflight are retained
+here as checks only.  Neither the main connector nor any lemma it uses depends
+on them. -/
+theorem goal058ConnectorCommutatorPlant_checks_retained :
+    lagCommutatorObservable goal058PlantD goal058PlantK goal058PlantQ = 0 ∧
+      ¬ ∃ mu : ℝ, goal058PlantK *ᵥ goal058PlantQ = mu • goal058PlantQ :=
+  ⟨goal058Plant_lagCommutatorObservable_zero, goal058PlantQ_not_eigenvector⟩
+
+#print axioms complexTrialLineProjection_isHermitian
+#print axioms complexTrialLineProjection_sq_of_unit
+#print axioms sourceCCMGroundProjectionErrorSq_eq_sum_normSq
+#print axioms proposition59CCMTransform_sub_sourceProjection_le
+#print axioms goal058ConnectorPhasePlant_no_common_real_phase
+#print axioms goal058ConnectorZeroOverlapRow_unit
+#print axioms goal058ConnectorZeroOverlapPlant_projection_zero
+#print axioms goal058ConnectorOrientationPlantRow_unit
+#print axioms goal058ConnectorOrientationPlant_error_zero
+#print axioms goal058ConnectorCommutatorPlant_checks_retained
+
+end Q3.RouteB
diff --git a/q3.lean.aristotle/aristotle_input/project_ids.txt b/q3.lean.aristotle/aristotle_input/project_ids.txt
index 86721380..52c6b7d4 100644
--- a/q3.lean.aristotle/aristotle_input/project_ids.txt
+++ b/q3.lean.aristotle/aristotle_input/project_ids.txt
@@ -82,3 +82,3 @@ rho_oneK_tcritical_le_cstar_quarter.md: b644c90d-9934-4c95-a857-221e38620134  20
 2026-08-03 prolate_source_commutation_2026_08_03.md: 07a1765f-0457-4577-8247-5c13c64dc9bb SUBMITTED
 2026-08-05 054.1.a CCM Cell 13N2 receiver: 36061787-afe1-4d64-bb55-905fce1411a6 COMPLETE_WITH_ERRORS SURROGATE_OBJECT; task=10fe975e-764f-4dd1-b97e-1babefa7fa01; archive_sha256=96cf54311849458752416672e87dce83083dfdc9290ec7d756bfa09ddb29cd98; DO_NOT_INTEGRATE
-2026-08-13 GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR pinned d106a3f4356664c871d1bf96c06f6e5324643e4e: 7e661f28-7943-4c6b-83e9-787c2eed4683 SUBMITTED
+2026-08-13 GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR pinned d106a3f4356664c871d1bf96c06f6e5324643e4e: 7e661f28-7943-4c6b-83e9-787c2eed4683 COMPLETE task=f958ac79-9673-4110-b9f7-538ee6673d38 archive_sha256=6a9868faef17dcdb52134b8379aa47232ba7ec6794efc1b52b67260b849702f1 lean_sha256=dc5e858863647224c17256b3cf629efc000ca81cbea4fb9cfd02fef28a6bc4eb GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_PROVED
```

### f20ed021
```diff
commit f20ed0219e3ac4e097878ec1cf8d9dba0a4c79f4
Author: kdl2026 <kdl2026@dfr.de>
Date:   Thu Aug 13 21:04:03 2026 +0200

    [MacOS][rh_clean][Goal058] Record Aristotle connector project

diff --git a/q3.lean.aristotle/aristotle_input/project_ids.txt b/q3.lean.aristotle/aristotle_input/project_ids.txt
index 7f57ccc2..86721380 100644
--- a/q3.lean.aristotle/aristotle_input/project_ids.txt
+++ b/q3.lean.aristotle/aristotle_input/project_ids.txt
@@ -82,2 +82,3 @@ rho_oneK_tcritical_le_cstar_quarter.md: b644c90d-9934-4c95-a857-221e38620134  20
 2026-08-03 prolate_source_commutation_2026_08_03.md: 07a1765f-0457-4577-8247-5c13c64dc9bb SUBMITTED
 2026-08-05 054.1.a CCM Cell 13N2 receiver: 36061787-afe1-4d64-bb55-905fce1411a6 COMPLETE_WITH_ERRORS SURROGATE_OBJECT; task=10fe975e-764f-4dd1-b97e-1babefa7fa01; archive_sha256=96cf54311849458752416672e87dce83083dfdc9290ec7d756bfa09ddb29cd98; DO_NOT_INTEGRATE
+2026-08-13 GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR pinned d106a3f4356664c871d1bf96c06f6e5324643e4e: 7e661f28-7943-4c6b-83e9-787c2eed4683 SUBMITTED
```

### d106a3f4
```diff
commit d106a3f4356664c871d1bf96c06f6e5324643e4e
Author: kdl2026 <kdl2026@dfr.de>
Date:   Thu Aug 13 21:03:07 2026 +0200

    [MacOS][rh_clean][Goal058] Lock Proshka Hermitian connector task

diff --git a/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md b/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md
new file mode 100644
index 00000000..4ed9719e
--- /dev/null
+++ b/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md
@@ -0,0 +1,551 @@
+Ы.
+
+**PRIMARY: `ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR`**
+
+The request establishes that the literal source row is complex and unit, while current binders do not derive a common-phase real-even carrier. The kernel-checked preflight also proves the exact P59 phase transport conditionally, the full trial-line block identity, and the scalar commutator’s tautological vanishing.
+
+# STATUS: OPEN — ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR SELECTED
+
+```yaml
+PRIMARY: ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR
+PRIMARY_COUNT: 1
+
+SOURCE_LOCK:
+  REQUEST_COMMIT: fea0965e021ea4cbb65f7dc7ceacd67ab1b1be63
+  CURRENT_ORIGIN_TIP_REPORTED: ad754cb5bd69d7eba06c7d904a21f08c1c233aec
+  REQUEST_SHA256: f4eb768a71b3928d3a2310adc8499a14f8b58f7aebb04a08316d7c1c61b8dd57
+  PREFLIGHT_LEAN_SHA256: 0651ef147401f50510be301443236276f948179f0e7712a0e3500bbdadcf04bf
+  PREFLIGHT_REPORT_SHA256: 1ccf88965a7ef916c036695a100bce98c72753fb9bbeb9aee98064324fe23517
+
+SELECTED_THEOREM:
+  ID: GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR
+  CLASS: COMPLEX_HERMITIAN_TRIAL_LINE
+  SCOPE: FINITE_CELL
+  VERIFIER: LEAN
+  ROLE: EXACT_SOURCE_CONNECTOR_NOT_COFINAL_SUPPLIER
+
+CIRCULARITY_AUDIT:
+  assumes_gap: false
+  assumes_simplicity: false
+  assumes_ground_tracking: false
+  assumes_cofinal_decay: false
+  assumes_RH_or_global_positivity: false
+  assumes_source_realification: false
+  assumes_source_parity: false
+  uses_scalar_commutator: false
+
+EVIDENCE_BOUNDARY:
+  G1_CLOSED: false
+  G3_CLOSED: false
+  ROUTE_PROMOTION: false
+  RH_CLAIM: false
+  ARISTOTLE_EXECUTED_BY_THIS_VERDICT: false
+
+SUCCESS: GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_PROVED
+STOP: GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_TYPED_STOP
+```
+
+# AUTHORITATIVE ARISTOTLE PROMPT
+
+```yaml
+TARGET_ID: GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR
+
+PRIMARY_CLASS: ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR
+
+PIN:
+  AUTHORITATIVE_REQUEST_COMMIT: fea0965e021ea4cbb65f7dc7ceacd67ab1b1be63
+  CURRENT_ORIGIN_TIP_REPORTED: ad754cb5bd69d7eba06c7d904a21f08c1c233aec
+  EXECUTION_POLICY: >-
+    Work at the current clean rh_clean tip only after byte-relocking every
+    listed source file. If any hash differs, do not adapt the theorem to the
+    changed source. Return GOAL058_ARISTOTLE_SOURCE_RELOCK_MISMATCH.
+
+  LOCKED_SHA256:
+    docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md: f4eb768a71b3928d3a2310adc8499a14f8b58f7aebb04a08316d7c1c61b8dd57
+    docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md: 0a8e2e0a1b9423003d3d62ed7964cc22e17fc43c2642f43c164ca71c634aaa68
+    q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean: 0651ef147401f50510be301443236276f948179f0e7712a0e3500bbdadcf04bf
+    q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT_REPORT_2026-08-13.md: 1ccf88965a7ef916c036695a100bce98c72753fb9bbeb9aee98064324fe23517
+    q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/PARITY_SECTOR_GROUND_TO_TRIAL_BOUND_ONE_CONTROL_CELL_REPORT_2026-08-12.md: 32cde7e7b179bc81680cbc305f3c7475144d7c8fcdb190d446b1c93fb760e554
+    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean: c11fe72d9df1e7a81d73cdcb1beebfc016be82cb1d0bcc8ffc371fc748cfb497
+    q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean: 7597910a8cf2160c4ab9786144d25595a6c519395f64fc0846d84a249a96c016
+    q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean: bb9383bebfcd5d01423ff5e944a28545e835e2e03c8609ec69fde73dce5ab2c5
+    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean: d0bb820651c81ac6971985cb705bd3191584108f5d90ea19411e9a0884c11190
+    q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean: a79c30cdc11cc936838e7963eff1a3de1f2c9290cf5ce5ca516b9bbf093b5f90
+
+OWNED_FILE:
+  q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
+
+ALLOWED_IMPORTS:
+  - Q3.Proofs.RouteB.CCMProposition59SourceTrialFeshbachPreflight
+  - >-
+    No other Q3 project import is allowed. Mathlib declarations already
+    available transitively through this import may be used.
+
+FORBIDDEN_IMPORTS:
+  - Q3.Main
+  - Q3.Proofs.RouteB.H2aPenaltyCoercivity
+  - Q3.Proofs.RouteB.WeightedProjectiveEvaluationTransfer
+  - Q3.Proofs.RouteB.CompactEvaluationRateTransfer
+  - Q3.Proofs.RouteB.UniformDifferenceReferenceTransfer
+  - Q3.Proofs.RouteB.TempleResidualGapEnvelopeTransfer
+  - Q3.Proofs.RouteB.PerturbativeTrueGapLower
+  - Q3.Proofs.RouteB.AmbientResidualEnvelopeTransfer
+  - any GLOWER module
+  - any D0-mode-4 module
+  - any sectional or continuum-gap module
+  - any RH or route-export module
+
+EXACT_INPUT_OBJECTS:
+  - Q3.RouteB.D0Pstar.ProlateCanonicalSourceData
+  - Q3.RouteB.D0Pstar.PairIndex
+  - Q3.RouteB.CCMModeFinite
+  - Q3.RouteB.D0Pstar.sourceCCMComplexRow
+  - Q3.RouteB.D0Pstar.sourceCCMComplexRow_unit
+  - Q3.RouteB.proposition59CCMTransform
+  - Q3.RouteB.proposition59CCMTransform_eq_mode_sum
+  - Q3.RouteB.proposition59CCMComplexTransform
+  - Q3.RouteB.proposition59CCMComplexTransform_eq_mode_sum
+  - Q3.RouteB.proposition59PoleKernel
+  - Q3.RouteB.ccmModeFinite
+  - Matrix.vecMulVec
+  - Matrix.vecMulVec_mul_vecMulVec
+  - Matrix.mulVec
+  - Matrix.dotProduct
+  - Complex.normSq
+
+EXACT_BINDERS:
+  S: Q3.RouteB.D0Pstar.ProlateCanonicalSourceData
+  i: Q3.RouteB.D0Pstar.PairIndex
+  L: Real
+  hL: 0 < L
+  xi: Q3.RouteB.CCMModeFinite i.N -> Real
+
+EXACT_THEOREM_HEAD: |
+  namespace Q3.RouteB
+
+  noncomputable def complexTrialLineProjection
+      {ι : Type*} (q : ι → ℂ) : Matrix ι ι ℂ :=
+    Matrix.vecMulVec q (star q)
+
+  noncomputable def sourceCCMGroundProjectionScalar
+      (S : D0Pstar.ProlateCanonicalSourceData)
+      (i : D0Pstar.PairIndex)
+      (xi : CCMModeFinite i.N → ℝ) : ℂ :=
+    star (D0Pstar.sourceCCMComplexRow S i) ⬝ᵥ
+      (fun j => (xi j : ℂ))
+
+  noncomputable def sourceCCMGroundProjectionErrorSq
+      (S : D0Pstar.ProlateCanonicalSourceData)
+      (i : D0Pstar.PairIndex)
+      (xi : CCMModeFinite i.N → ℝ) : ℝ :=
+    xi ⬝ᵥ xi -
+      Complex.normSq (sourceCCMGroundProjectionScalar S i xi)
+
+  noncomputable def proposition59CCMKernelL2
+      (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
+    ‖((Real.sqrt L : ℂ)⁻¹)‖ *
+      Real.sqrt
+        (∑ j : CCMModeFinite N,
+          Complex.normSq
+            (proposition59PoleKernel L (-ccmModeFinite N j) z))
+
+  theorem proposition59CCMTransform_sub_sourceProjection_le
+      (S : D0Pstar.ProlateCanonicalSourceData)
+      (i : D0Pstar.PairIndex)
+      (L : ℝ) (hL : 0 < L)
+      (xi : CCMModeFinite i.N → ℝ) :
+      0 ≤ sourceCCMGroundProjectionErrorSq S i xi ∧
+      ∀ z : ℂ,
+        ‖proposition59CCMTransform L i.N xi z -
+            sourceCCMGroundProjectionScalar S i xi *
+              proposition59CCMComplexTransform L i.N
+                (D0Pstar.sourceCCMComplexRow S i) z‖
+          ≤ proposition59CCMKernelL2 L i.N z *
+              Real.sqrt (sourceCCMGroundProjectionErrorSq S i xi) := by
+    -- proof
+
+REQUIRED_AUXILIARY_LEMMAS:
+  - name: complexTrialLineProjection_isHermitian
+    exact_statement: |
+      theorem complexTrialLineProjection_isHermitian
+          {ι : Type*} (q : ι → ℂ) :
+          (complexTrialLineProjection q).IsHermitian
+
+  - name: complexTrialLineProjection_sq_of_unit
+    exact_statement: |
+      theorem complexTrialLineProjection_sq_of_unit
+          {ι : Type*} [Fintype ι]
+          (q : ι → ℂ)
+          (hq : star q ⬝ᵥ q = 1) :
+          complexTrialLineProjection q * complexTrialLineProjection q =
+            complexTrialLineProjection q
+
+  - name: sourceCCMGroundProjectionErrorSq_eq_sum_normSq
+    exact_statement: |
+      theorem sourceCCMGroundProjectionErrorSq_eq_sum_normSq
+          (S : D0Pstar.ProlateCanonicalSourceData)
+          (i : D0Pstar.PairIndex)
+          (xi : CCMModeFinite i.N → ℝ) :
+          sourceCCMGroundProjectionErrorSq S i xi =
+            ∑ j,
+              Complex.normSq
+                ((xi j : ℂ) -
+                  sourceCCMGroundProjectionScalar S i xi *
+                    D0Pstar.sourceCCMComplexRow S i j)
+
+  - name: proposition59CCM_mode_sum_cauchy_schwarz
+    visibility: private
+    required_role: >-
+      Apply finite Cauchy-Schwarz to the exact source-locked mode sum after
+      rewriting with proposition59CCMTransform_eq_mode_sum and
+      proposition59CCMComplexTransform_eq_mode_sum.
+
+EXPECTED_OUTPUT:
+  SUCCESS: >-
+    Return the complete contents of the single owned Lean file. It must contain
+    the three support definitions, the three named public auxiliary theorems,
+    the main theorem, the mandatory plants, and all required #print axioms
+    commands. Do not return prose in place of code.
+
+  TYPED_STOP: >-
+    If the exact theorem cannot be proved from the allowed imports, return
+    exactly one typed-stop code and the smallest missing Lean lemma signature.
+    Do not weaken the theorem, add a binder, or import a gap/tracking module.
+
+SUCCESS_CODE: GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_PROVED
+
+TYPED_STOP_CODES:
+  - GOAL058_ARISTOTLE_SOURCE_RELOCK_MISMATCH
+  - GOAL058_COMPLEX_TRIAL_PROJECTION_API_GAP
+  - GOAL058_COMPLEX_PROJECTIVE_ERROR_IDENTITY_GAP
+  - GOAL058_FINITE_COMPLEX_CAUCHY_SCHWARZ_API_GAP
+  - GOAL058_P59_SOURCE_MODE_SUM_CONNECTOR_GAP
+  - GOAL058_SOURCE_FAMILY_OBJECT_MISMATCH
+  - GOAL058_HIDDEN_REALIFICATION_OR_PARITY_ASSUMPTION
+  - GOAL058_COMMUTATOR_TAUTOLOGY_REINTRODUCED
+  - GOAL058_CIRCULAR_GAP_OR_TRACKING_PREMISE
+  - GOAL058_P59_COORDINATE_CONVENTION_MISMATCH
+  - GOAL058_ZERO_OVERLAP_BRANCH_MISSING
+  - GOAL058_COMPLEX_PROJECTION_ORIENTATION_MISMATCH
+  - GOAL058_AXIOM_GATE_FAILED
+  - GOAL058_VALIDATION_FAILED
+
+AXIOM_GATE:
+  REQUIRED_PRINT_HEADS:
+    - Q3.RouteB.complexTrialLineProjection_isHermitian
+    - Q3.RouteB.complexTrialLineProjection_sq_of_unit
+    - Q3.RouteB.sourceCCMGroundProjectionErrorSq_eq_sum_normSq
+    - Q3.RouteB.proposition59CCMTransform_sub_sourceProjection_le
+
+  ALLOWED_AXIOMS:
+    - propext
+    - Classical.choice
+    - Quot.sound
+
+  FORBIDDEN:
+    - sorryAx
+    - any new project axiom
+    - any opaque proof constant
+
+VALIDATION_COMMANDS:
+  - |
+    cd /Users/emalam/GitHub/rh_lean_01_2026
+    test "$(git rev-parse origin/rh_clean)" = \
+      "ad754cb5bd69d7eba06c7d904a21f08c1c233aec"
+
+  - |
+    cd /Users/emalam/GitHub/rh_lean_01_2026
+    cat <<'SHA256' | sha256sum -c -
+    f4eb768a71b3928d3a2310adc8499a14f8b58f7aebb04a08316d7c1c61b8dd57  docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md
+    0a8e2e0a1b9423003d3d62ed7964cc22e17fc43c2642f43c164ca71c634aaa68  docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md
+    0651ef147401f50510be301443236276f948179f0e7712a0e3500bbdadcf04bf  q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean
+    1ccf88965a7ef916c036695a100bce98c72753fb9bbeb9aee98064324fe23517  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT_REPORT_2026-08-13.md
+    32cde7e7b179bc81680cbc305f3c7475144d7c8fcdb190d446b1c93fb760e554  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/PARITY_SECTOR_GROUND_TO_TRIAL_BOUND_ONE_CONTROL_CELL_REPORT_2026-08-12.md
+    c11fe72d9df1e7a81d73cdcb1beebfc016be82cb1d0bcc8ffc371fc748cfb497  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean
+    7597910a8cf2160c4ab9786144d25595a6c519395f64fc0846d84a249a96c016  q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
+    bb9383bebfcd5d01423ff5e944a28545e835e2e03c8609ec69fde73dce5ab2c5  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean
+    d0bb820651c81ac6971985cb705bd3191584108f5d90ea19411e9a0884c11190  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean
+    a79c30cdc11cc936838e7963eff1a3de1f2c9290cf5ce5ca516b9bbf093b5f90  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean
+    SHA256
+
+  - |
+    cd /Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle
+    lake env lean \
+      Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
+
+  - |
+    lake build Q3.Proofs.RouteB.CCMProposition59ComplexHermitianConnector
+
+  - |
+    lake build
+
+  - |
+    cd /Users/emalam/GitHub/rh_lean_01_2026
+    bash scripts/q3_check.sh \
+      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
+
+  - |
+    rg -n \
+      '\bsorry\b|\badmit\b|exact\?|native_decide|^[[:space:]]*axiom\b|^[[:space:]]*opaque\b' \
+      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
+
+  - |
+    rg -n \
+      'sourceCCMHasRealEvenPhase|sourceCCMPhaseRealification|phaseRealifies|ccmLagCommutatorObservable|lagCommutatorObservable|H2aPenalty|Tendsto|RH|hbottom|hsimple|heig' \
+      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
+
+  - |
+    git diff --check -- \
+      q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
+
+    test "$(git diff --name-only | wc -l | tr -d ' ')" = "1"
+```
+
+## MATHEMATICAL INTERPRETATION
+
+The literal CCM trial row is complex and unit. The Proposition-59 ground row is real. Do not force the complex row through a nonexistent common-phase realification.
+
+Instead, use the **Hermitian rank-one projection** onto the complex source line.
+
+For a real row `xi`:
+
+```lean
+sourceCCMGroundProjectionScalar S i xi
+```
+
+is the exact Hermitian projection coefficient of `xi` onto the literal complex source row.
+
+The quantity:
+
+```lean
+sourceCCMGroundProjectionErrorSq S i xi
+```
+
+is the exact squared coefficient-space distance from `xi` to that complex source line.
+
+The theorem proves that the difference between:
+
+1. the exact real Proposition-59 transform of `xi`; and
+2. the exact complex source transform multiplied by that projection scalar
+
+is bounded by the exact P59 kernel norm times the square root of the projective error.
+
+## WHY THIS IS NOT A RENAMED G1 OR G3 ASSUMPTION
+
+The theorem assumes no:
+
+```text
+eigenvalue
+eigenvector equation
+bottomness
+simplicity
+spectral gap
+complement coercivity
+residual decay
+tracking rate
+cofinal schedule
+convergence
+RH
+global Weil positivity
+source realification
+source parity
+```
+
+It proves only:
+
+```text
+finite Hermitian coefficient projection error
+→ finite pointwise Proposition-59 transform error.
+```
+
+It does not assert that the error is small or tends to zero. A later source theorem must supply that decay.
+
+Therefore the theorem removes the exact **complex-source / real-ground object mismatch** inside G3 without occupying the substantive G3 quantifier.
+
+## EXACT EXISTING DECLARATIONS ARISTOTLE MAY CONSUME
+
+```text
+Q3.RouteB.D0Pstar.sourceCCMComplexRow
+Q3.RouteB.D0Pstar.sourceCCMComplexRow_unit
+Q3.RouteB.proposition59CCMTransform
+Q3.RouteB.proposition59CCMTransform_eq_mode_sum
+Q3.RouteB.proposition59CCMComplexTransform
+Q3.RouteB.proposition59CCMComplexTransform_eq_mode_sum
+Q3.RouteB.proposition59PoleKernel
+Q3.RouteB.ccmModeFinite
+Q3.RouteB.goal058Plant_lagCommutatorObservable_zero
+Q3.RouteB.goal058PlantQ_not_eigenvector
+```
+
+The last two declarations are falsifiers only. They may not enter the main theorem proof.
+
+## MANDATORY FALSIFIERS
+
+### P1 — Wrong family
+
+The public theorem must hard-code:
+
+```lean
+D0Pstar.sourceCCMComplexRow S i
+```
+
+It must not expose an arbitrary public `row` binder.
+
+Generic private helper lemmas are allowed.
+
+Any public substitution of a D0Pstar, GLOWER, mode-4, sectional, fitted, or independently optimized row returns:
+
+```text
+GOAL058_SOURCE_FAMILY_OBJECT_MISMATCH
+```
+
+### P2 — Hidden realification or parity
+
+The proof must not consume:
+
+```text
+sourceCCMHasRealEvenPhase
+sourceCCMPhaseRealification
+phaseRealifies
+source-row reflection-evenness
+xi reflection-evenness
+```
+
+Add a finite two-coordinate plant with entries `1` and `Complex.I` showing that a common realifying phase is not generally available.
+
+The main Hermitian connector must not require such a phase.
+
+Failure:
+
+```text
+GOAL058_HIDDEN_REALIFICATION_OR_PARITY_ASSUMPTION
+```
+
+### P3 — Commutator tautology
+
+Retain exact checks of:
+
+```lean
+goal058Plant_lagCommutatorObservable_zero
+goal058PlantQ_not_eigenvector
+```
+
+The main theorem and all auxiliary proofs must be independent of:
+
+```text
+lagCommutatorObservable
+ccmWeilMatFinite_commutator
+```
+
+Any use returns:
+
+```text
+GOAL058_COMMUTATOR_TAUTOLOGY_REINTRODUCED
+```
+
+### P4 — Circular gap or tracking premise
+
+The public theorem and support lemmas may not bind or import:
+
+```text
+epsilon
+heig
+hbottom
+hsimple
+gap or complement floor
+residual-decay hypothesis
+Tendsto or cofinal schedule
+ground-to-trial tracking
+RH or global Weil positivity
+```
+
+Any such premise returns:
+
+```text
+GOAL058_CIRCULAR_GAP_OR_TRACKING_PREMISE
+```
+
+### P5 — Zero-overlap branch
+
+Add a finite orthogonal-vector plant.
+
+The theorem must remain valid when the projection scalar is zero.
+
+No division by the overlap is allowed.
+
+Failure:
+
+```text
+GOAL058_ZERO_OVERLAP_BRANCH_MISSING
+```
+
+### P6 — Phase-orientation plant
+
+Add a one-coordinate plant with source row `Complex.I` and real row `1`.
+
+Verify that the Hermitian projection scalar makes the coefficient error exactly zero.
+
+This detects conjugation or orientation reversal.
+
+Failure:
+
+```text
+GOAL058_COMPLEX_PROJECTION_ORIENTATION_MISMATCH
+```
+
+### P7 — Proposition-59 coordinate lock
+
+The proof must rewrite through the existing exact mode-sum theorems and retain:
+
+```text
+source mode n → P59 pole -n
+```
+
+Do not define a sign-flipped coefficient transport.
+
+Failure:
+
+```text
+GOAL058_P59_COORDINATE_CONVENTION_MISMATCH
+```
+
+## FORBIDDEN PROOF MOVES
+
+```text
+sorry
+admit
+exact?
+native_decide
+new axiom
+opaque
+phase fitting
+real-part replacement of the source row
+post-hoc symmetrization
+numerical overlap or tolerance
+spectral-gap assumption
+tracking assumption
+finite-to-cofinal inference
+commutator scalar expectation
+editing any file except OWNED_FILE
+```
+
+## EVIDENCE BOUNDARY
+
+A successful theorem proves one exact finite connector only.
+
+It does not prove:
+
+```text
+G1
+G3
+source-row realification
+source-row parity
+simple-even ground existence
+spectral-gap lower bounds
+projective-defect decay
+cofinal convergence
+Route B promotion
+RH
+```
+
+[Download the byte-locked attachment-ready prompt](sandbox:/mnt/data/PROSHKA_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_PROMPT_2026-08-13.md)
diff --git a/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ARISTOTLE_SOURCE_LOCK_STOP_2026-08-13.md b/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ARISTOTLE_SOURCE_LOCK_STOP_2026-08-13.md
new file mode 100644
index 00000000..2b6673b5
--- /dev/null
+++ b/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ARISTOTLE_SOURCE_LOCK_STOP_2026-08-13.md
@@ -0,0 +1,72 @@
+# STATUS: FATAL — AUTHORITATIVE SOURCE LOCK UNAVAILABLE
+```yaml
+PRIMARY: WALL_GOAL058_ARISTOTLE_REQUEST_SOURCE_LOCK_UNAVAILABLE
+PRIMARY_COUNT: 1
+
+REQUEST:
+  path: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md
+  pin: fea0965e021ea4cbb65f7dc7ceacd67ab1b1be63
+  current_tip_reported: ad754cb5bd69d7eba06c7d904a21f08c1c233aec
+
+SOURCE_ACCESS:
+  github_connector_available: false
+  public_fetch_succeeded: false
+  request_bytes_read: false
+  same_commit_evidence_read: false
+
+RULING:
+  mathematical_adjudication_issued: false
+  inferred_theorem_head_used: false
+  prompt_fabricated_from_memory: false
+  Aristotle_execution_authorized: false
+
+ROUTE_STATE: CHALLENGER_NOT_RH
+G1: OPEN
+G3: OPEN
+ROUTE_PROMOTION: false
+RH_CLAIM: false
+
+SUCCESS: GOAL058_ARISTOTLE_SOURCE_LOCK_RESTORED
+STOP: GOAL058_ARISTOTLE_REQUEST_SOURCE_LOCK_UNAVAILABLE
+```
+
+# AUTHORITATIVE ATTACHMENT-READY ARISTOTLE PROMPT
+
+```text
+GOAL 058 — FAIL-CLOSED SOURCE-LOCK STOP
+
+DO NOT EXECUTE A LEAN TASK.
+
+Authoritative request expected at:
+  docs/routeB_bus/proshka/
+    PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md
+
+Required request pin:
+  fea0965e021ea4cbb65f7dc7ceacd67ab1b1be63
+
+Current branch tip reported by owner:
+  ad754cb5bd69d7eba06c7d904a21f08c1c233aec
+
+STOP REASON:
+  The mathematical judge did not receive the byte-exact request or its
+  same-commit kernel-checked evidence. Therefore the exact inputs, binders,
+  theorem head, owned file, imports, required lemmas, output surface,
+  plants, axiom gate, and validation commands are not source-verified.
+
+FORBIDDEN:
+  - do not infer a theorem statement from earlier Goal 058 summaries;
+  - do not reuse a prior phase-realification or Feshbach draft;
+  - do not replace the literal CCM/P59 source object with a nearby object;
+  - do not assume G1, G3, a spectral gap, ground-to-trial tracking, RH,
+    global Weil positivity, or desired convergence;
+  - do not create or edit Lean;
+  - do not submit to Aristotle;
+  - do not promote Route B;
+  - do not claim RH.
+
+RETURN EXACTLY:
+  GOAL058_ARISTOTLE_REQUEST_SOURCE_LOCK_UNAVAILABLE
+
+Execution may be reconsidered only after the byte-exact request and every
+same-commit evidence artifact are available to the judge.
+```
diff --git a/q3.lean.aristotle/ACTIVE/pipeline/PROSHKA_REASONING_TIME_LOG.md b/q3.lean.aristotle/ACTIVE/pipeline/PROSHKA_REASONING_TIME_LOG.md
index bf639bcb..6e4996c7 100644
--- a/q3.lean.aristotle/ACTIVE/pipeline/PROSHKA_REASONING_TIME_LOG.md
+++ b/q3.lean.aristotle/ACTIVE/pipeline/PROSHKA_REASONING_TIME_LOG.md
@@ -32,4 +32,74 @@ does not change Lean, route, or roof status.
 ## Runs

+### 2026-08-13 — Goal 058 exact complex-Hermitian connector task
+
+```yaml
+proof_address: RouteB.Goal058.G1G3.CofinalGroundTracking.ComplexHermitianConnector
+front: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
+transaction: GOAL058_PROSHKA_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR
+conversation_id: 6a7afc0e-2aec-83eb-a9ca-469b44c84f83
+sent_at: 2026-08-13T20:32:10+02:00
+completed_at: 2026-08-13T20:53:45+02:00
+wall_seconds: 1295
+wall_human: "UI reported 21m35s natural reasoning"
+answer_now_shown: true
+answer_now_clicked: false
+primary: ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR
+status: OPEN_SELECTED_FOR_ARISTOTLE_EXECUTION
+result_pointer: >-
+  docs/routeB_bus/proshka/
+  PROSHKA_VERDICT_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md
+clipboard_response_bytes: 18375
+clipboard_response_lines: 552
+archive_bytes: 18372
+archive_lines: 551
+archive_sha256: 5b71885d466b3a89ae9632064c833ea020ad13326da918279b423733db555ac5
+notes: >-
+  Same living Goal 058 phase chat, retried after the transport-only source-lock
+  stop. The exact request and nine same-commit evidence files were attached;
+  Proshka verified every declared SHA-256 and selected one finite-cell theorem:
+  a Hermitian complex-source projection-error bound for the exact P59 transform.
+  The archive is newline/whitespace-normalized from the exact clipboard text;
+  only two trailing spaces and one final blank line were removed. The selected
+  theorem assumes no phase realification, parity, gap, simplicity,
+  bottomness, tracking, cofinal decay, or RH statement. It does not close G1 or
+  G3 and does not authorize Route B promotion or an RH claim. Answer now was
+  shown and never clicked.
+```
+
+### 2026-08-13 — Goal 058 Aristotle-task source-lock stop
+
+```yaml
+proof_address: RouteB.Goal058.G1G3.CofinalGroundTracking.AristotleTask
+front: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
+transaction: GOAL058_PROSHKA_ARISTOTLE_EXACT_SOURCE_TASK
+conversation_id: 6a7afc0e-2aec-83eb-a9ca-469b44c84f83
+sent_at: 2026-08-13T20:09:10+02:00
+completed_at: 2026-08-13T20:23:33+02:00
+wall_seconds: 863
+wall_human: "UI reported 14m23s natural reasoning"
+answer_now_shown: true
+answer_now_clicked: false
+primary: WALL_GOAL058_ARISTOTLE_REQUEST_SOURCE_LOCK_UNAVAILABLE
+status: FATAL_TRANSPORT_ONLY_NO_MATHEMATICAL_ADJUDICATION
+result_pointer: >-
[truncated after 700 lines]
```

### ad754cb5
```diff
commit ad754cb5bd69d7eba06c7d904a21f08c1c233aec
Author: kdl2026 <kdl2026@dfr.de>
Date:   Thu Aug 13 20:07:11 2026 +0200

    [MacOS][rh_clean][Cartographer] Refresh RouteB inventory after Goal058 preflight

diff --git a/docs/cartographer/inventory_RouteB.json b/docs/cartographer/inventory_RouteB.json
index b4db77df..0bdbf6f0 100644
--- a/docs/cartographer/inventory_RouteB.json
+++ b/docs/cartographer/inventory_RouteB.json
@@ -2,11 +2,16 @@
   "scope": "RouteB",
   "museum_excluded": "PrimeCert",
-  "files_scanned": 205,
-  "declarations": 1770,
-  "in_docs": 721,
+  "files_scanned": 206,
+  "declarations": 1813,
+  "in_docs": 738,
   "in_lemma_db": 1770,
-  "orphans": 0,
-  "uncatalogued": 0,
-  "orphan_files_top": [],
+  "orphans": 32,
+  "uncatalogued": 32,
+  "orphan_files_top": [
+    [
+      "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      32
+    ]
+  ],
   "items": [
     {
@@ -1566,5 +1571,5 @@
       "line": 39,
       "signature": "theorem ccmReflectionEndFinite_involutive (N : ℕ) : (ccmReflectionEndFinite N).comp (ccmReflectionEndFinite N) = 1",
-      "in_docs": false,
+      "in_docs": true,
       "in_lemma_db": true,
       "orphan": false
@@ -1886,5 +1891,5 @@
       "line": 330,
       "signature": "theorem ccmWeilMatFinite_structured_offdiag (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) {i j : CCMModeFinite N} (hij : i ≠ j) : ccmWeilMatFinite mProject N i j = (ccmBetaFinite mProject N i - ccmBetaFinite mProject N j) / ((ccmModeFinite N i : ℝ) - (ccmModeFinite N j : ℝ))",
-      "in_docs": false,
+      "in_docs": true,
       "in_lemma_db": true,
       "orphan": false
@@ -1986,5 +1991,5 @@
       "line": 44,
       "signature": "noncomputable def ccmModeDiagFinite (N : ℕ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
-      "in_docs": false,
+      "in_docs": true,
       "in_lemma_db": true,
       "orphan": false
@@ -2940,4 +2945,434 @@
       "orphan": false
     },
+    {
+      "kind": "def",
+      "name": "phaseRealifies",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 33,
+      "signature": "def phaseRealifies {ι : Type*} (phase : ℂ) (row : ι → ℂ) (q : ι → ℝ) : Prop",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "sourceCCMPhaseRealification",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 41,
+      "signature": "def sourceCCMPhaseRealification (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (phase : ℂ) (q : CCMModeFinite i.N → ℝ) : Prop",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "sourceCCMHasRealEvenPhase",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 50,
+      "signature": "def sourceCCMHasRealEvenPhase (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) : Prop",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "phaseOne_realPart_requires_exact_reality",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 59,
+      "signature": "theorem phaseOne_realPart_requires_exact_reality {ι : Type*} (row : ι → ℂ) (h : phaseRealifies 1 row (fun j => (row j).re)) : ∀ j, row j = (row j).re",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "dotProduct_self_eq_one_of_phaseRealifies",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 68,
+      "signature": "theorem dotProduct_self_eq_one_of_phaseRealifies {ι : Type*} [Fintype ι] (phase : ℂ) (row : ι → ℂ) (q : ι → ℝ) (hrow : star row ⬝ᵥ row = 1) (hphase : phaseRealifies phase row q) : q ⬝ᵥ q = 1",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "sourceCCMRealRow_unit_of_phaseRealification",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 114,
+      "signature": "theorem sourceCCMRealRow_unit_of_phaseRealification (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (phase : ℂ) (q : CCMModeFinite i.N → ℝ) (hphase : sourceCCMPhaseRealification S i phase q) : q ⬝ᵥ q = 1",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "sourceCCMComplexRow_even_of_phaseRealification_even",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 128,
+      "signature": "theorem sourceCCMComplexRow_even_of_phaseRealification_even (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (phase : ℂ) (q : CCMModeFinite i.N → ℝ) (hphase : sourceCCMPhaseRealification S i phase q) (hqEven : ∀ j, q (ccmNegFinite i.N j) = q j) : ∀ j, D0Pstar.sourceCCMComplexRow S i (ccmNegFinite i.N j) = D0Pstar.sourceCCMComplexRow S i j",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "proposition59CCMComplexCoefficient",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 148,
+      "signature": "def proposition59CCMComplexCoefficient (N : ℕ) (q : CCMModeFinite N → ℂ) (k : ℤ) : ℂ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "proposition59CCMComplexCoefficient_neg_mode",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 155,
+      "signature": "@[simp] theorem proposition59CCMComplexCoefficient_neg_mode (N : ℕ) (q : CCMModeFinite N → ℂ) (i : CCMModeFinite N) : proposition59CCMComplexCoefficient N q (-ccmModeFinite N i) = q i",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "proposition59CCMComplexTransform",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 174,
+      "signature": "def proposition59CCMComplexTransform (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) : ℂ → ℂ",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "proposition59CCMComplexTransform_eq_mode_sum",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 179,
+      "signature": "theorem proposition59CCMComplexTransform_eq_mode_sum (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) (z : ℂ) : proposition59CCMComplexTransform L N q z = ((Real.sqrt L : ℂ)⁻¹) * ∑ i, q i * proposition59PoleKernel L (-ccmModeFinite N i) z",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "proposition59CCMTransform_eq_phase_mul_complexTransform",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 214,
+      "signature": "theorem proposition59CCMTransform_eq_phase_mul_complexTransform (L : ℝ) (N : ℕ) (phase : ℂ) (row : CCMModeFinite N → ℂ) (q : CCMModeFinite N → ℝ) (hreal : ∀ i, phase * row i = (q i : ℂ)) (z : ℂ) : proposition59CCMTransform L N q z = phase * proposition59CCMComplexTransform L N row z",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "sourceCCMProposition59Transform_eq_phase_mul_complexTransform",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 229,
+      "signature": "theorem sourceCCMProposition59Transform_eq_phase_mul_complexTransform (S : D0Pstar.ProlateCanonicalSourceData) (i : D0Pstar.PairIndex) (L : ℝ) (phase : ℂ) (q : CCMModeFinite i.N → ℝ) (hphase : sourceCCMPhaseRealification S i phase q) (z : ℂ) : proposition59CCMTransform L i.N q z = phase * proposition59CCMComplexTransform L i.N (D0Pstar.sourceCCMComplexRow S i) z",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "trialLineProjection",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 243,
+      "signature": "def trialLineProjection {ι : Type*} (q : ι → ℝ) : Matrix ι ι ℝ",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "trialLineComplement",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 248,
+      "signature": "def trialLineComplement {ι : Type*} [DecidableEq ι] (q : ι → ℝ) : Matrix ι ι ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "trialRayleigh",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 253,
+      "signature": "def trialRayleigh {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (q : ι → ℝ) : ℝ",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "trialCoupling",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 259,
+      "signature": "def trialCoupling {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ) (q : ι → ℝ) : ι → ℝ",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "ccmReflectionMatrix",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 265,
+      "signature": "def ccmReflectionMatrix (N : ℕ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "ccmEvenProjection",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 270,
+      "signature": "def ccmEvenProjection (N : ℕ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "ccmOddProjection",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 275,
+      "signature": "def ccmOddProjection (N : ℕ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "evenComplementBlock",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 280,
+      "signature": "def evenComplementBlock (N : ℕ) (K : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ) (q : CCMModeFinite N → ℝ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "oddSectorBlock",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 289,
+      "signature": "def oddSectorBlock (N : ℕ) (K : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ) : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "oddTrialMass",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 296,
+      "signature": "def oddTrialMass (N : ℕ) (q : CCMModeFinite N → ℝ) : ℝ",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "trialLineProjection_sq",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 301,
+      "signature": "theorem trialLineProjection_sq {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : q ⬝ᵥ q = 1) : trialLineProjection q * trialLineProjection q = trialLineProjection q",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "full_trialLine_four_block_identity",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 311,
+      "signature": "theorem full_trialLine_four_block_identity {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ) (q : ι → ℝ) : K = trialLineProjection q * K * trialLineProjection q + trialLineProjection q * K * trialLineComplement q + trialLineComplement q * K * trialLineProjection q + trialLineComplement q * K * trialLineComplement q",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "theorem",
+      "name": "ccmWeilMatFinite_full_trialLine_four_block_identity",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 323,
+      "signature": "theorem ccmWeilMatFinite_full_trialLine_four_block_identity (mProject N : ℕ) (q : CCMModeFinite N → ℝ) : ccmWeilMatFinite mProject N = trialLineProjection q * ccmWeilMatFinite mProject N * trialLineProjection q + trialLineProjection q * ccmWeilMatFinite mProject N * trialLineComplement q + trialLineComplement q * ccmWeilMatFinite mProject N * trialLineProjection q + trialLineComplement q * ccmWeilMatFinite mProject N * trialLineComplement q",
+      "in_docs": true,
+      "in_lemma_db": false,
+      "orphan": false
+    },
+    {
+      "kind": "def",
+      "name": "lagCommutatorObservable",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 337,
+      "signature": "def lagCommutatorObservable {ι : Type*} [Fintype ι] (D K : Matrix ι ι ℝ) (q : ι → ℝ) : ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "lagCommutatorObservable_zero_of_isSymm",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 344,
+      "signature": "theorem lagCommutatorObservable_zero_of_isSymm {ι : Type*} [Fintype ι] (D K : Matrix ι ι ℝ) (q : ι → ℝ) (hD : D.IsSymm) (hK : K.IsSymm) : lagCommutatorObservable D K q = 0",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "ccmLagCommutatorObservable_zero",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 371,
+      "signature": "theorem ccmLagCommutatorObservable_zero (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) (q : CCMModeFinite N → ℝ) : lagCommutatorObservable (ccmModeDiagFinite N) (ccmWeilMatFinite mProject N) q = 0",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "goal058SourceTrialPreflightStop",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 393,
+      "signature": "def goal058SourceTrialPreflightStop : Goal058SourceTrialPreflightStop",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058SourceTrialPreflightStop_eq",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 396,
+      "signature": "theorem goal058SourceTrialPreflightStop_eq : goal058SourceTrialPreflightStop = Goal058SourceTrialPreflightStop.sourceComplexRealGroundCrosswalkMismatch",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "abbrev",
+      "name": "Goal058PlantCarrier",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 401,
+      "signature": "abbrev Goal058PlantCarrier",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "goal058PlantD",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 403,
+      "signature": "def goal058PlantD : Matrix Goal058PlantCarrier Goal058PlantCarrier ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "goal058PlantK",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 409,
+      "signature": "def goal058PlantK : Matrix Goal058PlantCarrier Goal058PlantCarrier ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "goal058PlantEta",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 414,
+      "signature": "def goal058PlantEta : Goal058PlantCarrier → ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "goal058PlantBeta",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 415,
+      "signature": "def goal058PlantBeta : Goal058PlantCarrier → ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "goal058PlantQ",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 416,
+      "signature": "def goal058PlantQ : Goal058PlantCarrier → ℝ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058Plant_commutator",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 418,
+      "signature": "theorem goal058Plant_commutator : goal058PlantD * goal058PlantK - goal058PlantK * goal058PlantD = Matrix.vecMulVec goal058PlantBeta goal058PlantEta - Matrix.vecMulVec goal058PlantEta goal058PlantBeta",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058PlantQ_reflection_even",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 428,
+      "signature": "theorem goal058PlantQ_reflection_even : ∀ i, goal058PlantQ (ccmNegFinite 1 i) = goal058PlantQ i",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058PlantQ_not_eigenvector",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 433,
+      "signature": "theorem goal058PlantQ_not_eigenvector : ¬ ∃ mu : ℝ, goal058PlantK *ᵥ goal058PlantQ = mu • goal058PlantQ",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058Plant_lagCommutatorObservable_zero",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 442,
+      "signature": "theorem goal058Plant_lagCommutatorObservable_zero : lagCommutatorObservable goal058PlantD goal058PlantK goal058PlantQ = 0",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "def",
+      "name": "goal058PlantClassification",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 448,
+      "signature": "def goal058PlantClassification : Goal058CommutatorClassification",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
+    {
+      "kind": "theorem",
+      "name": "goal058PlantClassification_eq",
+      "file": "q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean",
+      "line": 451,
+      "signature": "theorem goal058PlantClassification_eq : goal058PlantClassification = Goal058CommutatorClassification.lagSourceTautologicalZero",
+      "in_docs": false,
+      "in_lemma_db": false,
+      "orphan": true
+    },
     {
       "kind": "structure",
@@ -16106,5 +16541,5 @@
       "line": 71,
       "signature": "theorem differentiable_proposition59PoleKernel (L : ℝ) (k : ℤ) : Differentiable ℂ (proposition59PoleKernel L k)",
-      "in_docs": false,
+      "in_docs": true,
       "in_lemma_db": true,
       "orphan": false
@@ -16206,5 +16641,5 @@
       "line": 125,
       "signature": "def proposition59CCMTransform (L : ℝ) (N : ℕ) (xi : CCMModeFinite N → ℝ) : ℂ → ℂ",
-      "in_docs": false,
+      "in_docs": true,
       "in_lemma_db": true,
       "orphan": false
@@ -16216,5 +16651,5 @@
       "line": 130,
       "signature": "theorem proposition59CCMTransform_eq_mode_sum (L : ℝ) (N : ℕ) (xi : CCMModeFinite N → ℝ) (z : ℂ) : proposition59CCMTransform L N xi z = ((Real.sqrt L : ℂ)⁻¹) * ∑ i, (xi i : ℂ) * proposition59PoleKernel L (-ccmModeFinite N i) z",
-      "in_docs": false,
+      "in_docs": true,
       "in_lemma_db": true,
       "orphan": false
```

### fea0965e
```diff
commit fea0965e021ea4cbb65f7dc7ceacd67ab1b1be63
Author: kdl2026 <kdl2026@dfr.de>
Date:   Thu Aug 13 20:06:35 2026 +0200

    [MacOS][rh_clean][Goal058] Record source preflight and Aristotle task request

diff --git a/docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md b/docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md
new file mode 100644
index 00000000..7e815f95
--- /dev/null
+++ b/docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ARISTOTLE_EXACT_SOURCE_TASK_2026-08-13.md
@@ -0,0 +1,260 @@
+# Proshka request — design the exact Aristotle task after the Goal 058 source preflight
+
+Date: 2026-08-13
+
+Requested role: Proshka is the mathematical judge and task designer. Aristotle
+will be the proof-search executor only after Proshka returns one exact
+source-locked task.
+
+## Phase key
+
+```yaml
+GOAL_ID: Goal058_G1_G3_CofinalGroundTracking
+PROOF_ADDRESS: RouteB.Goal058.G1G3.CofinalGroundTracking
+FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
+SOURCE_LOCK: literal ccmWeilMatFinite / sourceCCMComplexRow / Proposition59 family
+ASSUMPTION_BUDGET: no gap, simplicity, tracking, RH, global positivity, or off-line-zero assumptions
+PROMOTION_LEVEL: NONE
+```
+
+## Current pin
+
+```text
+repo: Malaeu/chen_q3
+branch: rh_clean
+base HEAD = origin/rh_clean = 6d7437e257c5101b06df9f5aff53dc8ff4984cc8
+strict startup: P9_STRICT_PASS
+Route B: CHECK: OK
+G1: OPEN
+G3: OPEN
+```
+
+The response must re-pin to the exact commit containing this request and the
+preflight artifacts before giving the Aristotle prompt.
+
+## Evidence to adjudicate
+
+Read in this same commit:
+
+1. `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md`
+2. `q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean`
+3. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT_REPORT_2026-08-13.md`
+4. `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/PARITY_SECTOR_GROUND_TO_TRIAL_BOUND_ONE_CONTROL_CELL_REPORT_2026-08-12.md`
+5. `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean`
+6. `q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean`
+7. `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean`
+8. `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean`
+9. `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean`
+
+The preflight is kernel-checked:
+
+```text
+direct Lean: PASS
+pinned 3x3 gap-collapse harness: PASS
+lake build: PASS (7817 jobs)
+q3_check: PASS
+proof-hole/new-axiom scans: PASS
+git diff --check: PASS
+public theorem axioms: [propext, Classical.choice, Quot.sound] or none
+```
+
+## Exact facts now proved
+
+### A. Missing literal real-even source carrier
+
+The exact source row is
+
+```lean
+D0Pstar.sourceCCMComplexRow S i : CCMModeFinite i.N -> Complex
+```
+
+and is exactly unit. Current source binders do not supply a single unit phase
+and a real reflection-even row `q` satisfying
+
+```lean
+forall j, phase * D0Pstar.sourceCCMComplexRow S i j = (q j : Complex).
+```
+
+Lean records this exact missing proposition as
+`sourceCCMHasRealEvenPhase`, without assuming it. Lean proves:
+
+- a unit phase realification preserves the exact unit Euclidean norm;
+- exact real-row evenness would force exact reflection-evenness of the
+  original complex source row;
+- choosing phase one and `Re(row)` requires the original row to be exactly
+  real coordinatewise.
+
+Typed stop:
+
+```text
+GOAL058_SOURCE_COMPLEX_REAL_GROUND_CROSSWALK_MISMATCH
+```
+
+### B. Conditional P59 phase transport
+
+On the exact `-N,...,N` carrier and source-locked pole order `n -> -n`, Lean
+proves
+
+```lean
+proposition59CCMTransform L N q z =
+  phase * proposition59CCMComplexTransform L N row z
+```
+
+under the exact coordinate realification equality. The existing
+`-L*z/(2*pi)` coordinate is preserved. This does not produce the missing
+phase-realification supplier.
+
+### C. Exact full trial-line algebra
+
+For `P = vecMulVec q q` and `Q = 1-P`, Lean proves `P*P=P` from
+`q dot q=1` and the exact identity
+
+```text
+K = P*K*P + P*K*Q + Q*K*P + Q*K*Q.
+```
+
+It specializes to literal `ccmWeilMatFinite` and defines
+`trialRayleigh`, `trialCoupling`, `evenComplementBlock`, `oddSectorBlock`, and
+`oddTrialMass`. No positivity, gap, rate, or cofinal theorem is present.
+
+### D. Scalar commutator candidate is exactly tautological
+
+Lean proves
+
+```text
+q dot ((D*K - K*D) * q) = 0
+```
+
+for every real `q` whenever `D` and `K` are symmetric. Hence this observable
+is zero for literal `ccmModeDiagFinite` and `ccmWeilMatFinite`, independently
+of eigenvector status. An exact `CCMModeFinite 1` real-even non-eigenvector
+plant verifies the same classification:
+
+```text
+LAG_SOURCE_TAUTOLOGICAL_ZERO
+```
+
+The independent pinned 3x3 harness additionally proves that the exact
+rank-two commutator is compatible with a nonsimple kernel.
+
+## Owner's requested move
+
+Design one exceptionally precise Aristotle task that gives Aristotle a real
+chance to find a non-obvious source-level connection. Do not ask Aristotle to
+solve Goal 058 or RH. Ask it to prove exactly one bounded theorem (or return an
+honest typed stop) whose truth can be checked by Lean in the present project.
+
+The task may be difficult and structurally clever, but its conclusion must be
+strong enough to materially reduce one of the two current walls:
+
+```text
+G1 = uniform literal CCM spectral-gap source
+G3 = same-family/cofinal ground-to-trial tracking source
+```
+
+## Candidate classes Proshka must compare
+
+Proshka must compare at least these four and may add one better class:
+
+1. `COMPLEX_HERMITIAN_TRIAL_LINE`
+   - avoid forcing the complex source row through an unavailable real-even
+     carrier;
+   - formulate a Hermitian rank-one projection with `vecMulVec q (star q)`;
+   - specify the exact bridge, if any, to the real Proposition-59 ground row;
+   - reject it if the bridge merely renames G3.
+
+2. `SOURCE_REALIFICATION_THEOREM`
+   - attempt a theorem deriving a common global phase and reflection relation
+     from the literal prolate / `E_star` definitions;
+   - identify the exact missing pointwise reality/conjugation binder;
+   - reject it if the conclusion is not derivable from current fields.
+
+3. `NONSCALAR_COMMUTATOR_OR_SCHUR_IDENTITY`
+   - replace the killed scalar expectation by an exact vector-, block-, norm-,
+     or bilinear-valued identity that survives a real-even non-eigenvector;
+   - it must contain new source information, not just `(K-mu I)q` or a renamed
+     complement-coercivity assumption.
+
+4. `LITERAL_SOURCE_OBSTRUCTION_OR_NO_GO`
+   - prove a bounded counterexample/no-go theorem showing that the current
+     source contract cannot imply the desired realification or non-tautological
+     observable;
+   - this is acceptable falsification progress if it decisively rules out a
+     family of future attempts.
+
+## Required response format
+
+Return exactly one primary:
+
+```text
+ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR
+ARISTOTLE_SOURCE_REALIFICATION
+ARISTOTLE_NONSCALAR_SOURCE_OBSERVABLE
+ARISTOTLE_SOURCE_NO_GO
+NO_SOUND_ARISTOTLE_TASK_AVAILABLE
+```
+
+Then return a single authoritative attachment-ready prompt with these fields:
+
+```yaml
+TARGET_ID:
+PRIMARY_CLASS:
+PIN:
+OWNED_FILE:
+ALLOWED_IMPORTS:
+FORBIDDEN_IMPORTS:
+EXACT_INPUT_OBJECTS:
+EXACT_BINDERS:
+EXACT_THEOREM_HEAD:
+REQUIRED_AUXILIARY_LEMMAS:
+EXPECTED_OUTPUT:
+SUCCESS_CODE:
+TYPED_STOP_CODES:
+AXIOM_GATE:
+VALIDATION_COMMANDS:
+```
+
+The prompt must also include:
+
+1. a plain-language mathematical interpretation of the theorem;
+2. why it is not a renamed G1/G3 assumption;
+3. exact existing declaration names Aristotle may consume;
+4. one owned Lean file only;
+5. no edits outside that file;
+6. no `sorry`, `admit`, `exact?`, `native_decide`, new `axiom`, or `opaque`;
+7. all required `#print axioms` heads;
+8. at least four mandatory falsifiers, including:
+   - wrong family;
+   - hidden realification/parity;
+   - commutator tautology;
+   - circular gap or tracking premise;
+9. exact validation through direct Lean, target build, full build, q3_check,
+   forbidden-token scan, and diff check;
+10. a strict evidence boundary: no G1/G3 close, route promotion, or RH claim.
+
+## Judge's strongest-attack obligation
+
+Before emitting the Aristotle prompt, Proshka must attack the selected theorem
+for:
+
+- binder non-derivability;
+- wrong-family substitution;
+- hidden real/even assumption;
+- a statement true only because a scalar commutator vanishes;
+- complement-coercivity or source-decay smuggled in as a hypothesis;
+- finite-to-cofinal substitution;
+- receiver relabeled as supplier.
+
+If the proposed theorem fails this attack, return
+`NO_SOUND_ARISTOTLE_TASK_AVAILABLE` rather than an attractive but circular
+prompt.
+
+## Execution boundary
+
+Proshka designs and judges the prompt. Codex will independently byte-lock the
+returned prompt, submit it through the current Aristotle workflow, download
+the result, scan it, compile it, and integrate only hole-free source-faithful
+proofs.
+
+This request does not authorize any G1/G3 closure, Bus creation, route
+promotion, PX claim, or RH claim.
diff --git a/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md b/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md
new file mode 100644
index 00000000..ee623c57
--- /dev/null
+++ b/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md
@@ -0,0 +1,910 @@
+# STATUS: FATAL — KILL_ALL_THREE_REQUIRES_NEW_THEORY
+
+```yaml
+PRIMARY: KILL_ALL_THREE_REQUIRES_NEW_THEORY
+PRIMARY_COUNT: 1
+
+LOCKED_PHASE:
+  route_id: RouteB_TwoLevelSpectralLadder
+  front_id: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
+  source_object_family_id: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
+  terminal_consumer_id: Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots
+  honesty_state: CHALLENGER_NOT_RH
+  convention_lock_id: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
+
+PIN:
+  REPO: /Users/emalam/GitHub/rh_lean_01_2026
+  BRANCH: rh_clean
+  HEAD: 08a2db998f2b5467d70effdfd135d3846189999c
+
+FRONT_RULINGS:
+  A_COMMUTATOR_ENVELOPE:
+    verdict: KILLED
+    reason:
+      - exact_rank_two_commutator_does_not_imply_positive_gap
+      - finite_Hilbert_bound_does_not_supply_cofinal_decay
+      - real_ground_vs_complex_trial_connector_missing
+    kill_code: GOAL058_COMMUTATOR_ALONE_NOT_GAP_SUPPLIER
+
+  D_ENDPOINT_SOURCE:
+    verdict: KILLED
+    reason:
+      - only_scalar_perturbation_receivers_exist
+      - literal_CCM_endpoint_supplier_absent
+      - surviving_model_gap_would_assume_G1
+    kill_code: GOAL058_LITERAL_CCM_ENDPOINT_SOURCE_MISSING
+
+  W_LEAKAGE_SOURCE:
+    verdict: KILLED
+    reason:
+      - only_abstract_residual_receivers_exist
+      - no_literal_CCM_projection_leakage_supplier
+      - same_family_leakage_premise_would_assume_G3
+    kill_code: GOAL058_LITERAL_CCM_LEAKAGE_SOURCE_MISSING
+
+ROUTE_FATAL: false
+G1: OPEN
+G3: OPEN
+
+NEW_THEORY:
+  name: CCM_P59_COFINAL_TRIAL_LINE_FESHBACH_SOURCE_BOUNDS
+  operative_class: FULL
+  source_operator: ccmWeilMatFinite
+  source_trial: exact_phase_realification_of_sourceCCMComplexRow
+  schedule: one_precommitted_P59_cofinal_schedule
+  second_diagonal: forbidden
+
+EXECUTION:
+  EXTERNAL_DISPATCH_NEEDED_NOW: false
+  CODEX_LOCAL_PREFLIGHT_FIRST: true
+  PRODUCTION_COFINAL_THEORY_AUTHORIZED_NOW: false
+  COMMIT_AUTHORIZED: false
+  ROUTE_PROMOTION: false
+  RH_CLAIM: false
+  BUS_010: VOID
+
+SUCCESS: GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT_PROVED
+STOP: GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_NEW_THEORY_MISSING
+
+ARSENAL_MANDATE: ACCEPTED
+CARDS_APPLIED:
+  - C04_SAME_COORDINATES_TWO_LAWS
+  - C07_PROBABILITY_WEIGHTED_ESTIMATE
+  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
+  - C10_FUNCTIONAL_NOT_SURROGATE
+
+PROGRESS_CLASS: FALSIFICATION_PROGRESS
+COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
+ROUTE_SCORE: 5
+```
+
+## ROUTE MAP
+
+### A — commutator envelope: killed
+
+The exact identity
+
+[
+[D_N,W_N]
+=========
+
+\beta_N\eta_N^{T}-\eta_N\beta_N^{T}
+]
+
+is a valid literal-CCM identity. It is not a gap theorem.
+
+The kernel-checked (3\times3) plant satisfies the exact rank-two commutator identity while its zero eigenspace is not one-dimensional. Thus the commutator is compatible with a collapsed ground gap. A discrete Hilbert inequality can bound an off-diagonal operator, but it cannot create:
+
+[
+\Delta_{\mathrm{even}}>0,
+]
+
+or a cofinal decay rate for the exact trial residual. It also does not repair the mismatch between the complex `sourceCCMComplexRow` and the real row consumed by the Proposition-59 ground transform.
+
+Therefore:
+
+[
+\boxed{\texttt{RATIFY_A_COMMUTATOR_ENVELOPE_FRONT}}
+]
+
+is rejected.
+
+### D — endpoint source: killed
+
+`PerturbativeTrueGapLower` consumes exact endpoint errors and a surviving model-gap budget. `D0Mode4HermitianSchurTailEnvelopes` consumes finite-left Schur envelopes.
+
+Neither file produces endpoint estimates for the literal family
+
+[
+\operatorname{ccmWeilMatFinite}.
+]
+
+Using a sectional, prolate, D0-mode-4, or GLOWER proxy would change the operator. Supplying the “surviving model gap” without an exact CCM source theorem would assume G1 in the premise.
+
+Therefore:
+
+[
+\boxed{\texttt{RATIFY_D_ENDPOINT_SOURCE_FRONT}}
+]
+
+is rejected.
+
+### W — leakage source: killed
+
+`AmbientResidualSplit` and `AmbientResidualEnvelopeTransfer` are receivers. Their binders contain no exact Goal-058 source family. They require a same-family projection-leakage estimate but do not derive one.
+
+Relabelling that premise as a supplier would assume the substantive G3 statement:
+
+[
+\text{finite ground row}
+\longrightarrow
+\text{projected CCM trial row}.
+]
+
+Therefore:
+
+[
+\boxed{\texttt{RATIFY_W_LEAKAGE_SOURCE_FRONT}}
+]
+
+is rejected.
+
+The controlling payload explicitly distinguishes these three receiver shelves from actual source suppliers and requires a new-theory directive when none survives.
+
+---
+
+## SELECTED NEW THEORY
+
+The replacement is not another scalar commutator estimate.
+
+It is a full-source trial-line **Schur/Feshbach** theorem for the literal CCM matrix family:
+
+[
+\boxed{
+\texttt{CCM_P59_CofinalTrialLineFeshbachSourceBounds}.
+}
+]
+
+### Operative class
+
+[
+\boxed{\texttt{FULL}}
+]
+
+The theorem retains:
+
+* the full literal matrix
+  [
+  W_{0,2}-W_{\mathbb R}-W_{\mathrm{prime}};
+  ]
+* both parity sectors;
+* the exact source trial line;
+* the full coupling to its orthogonal complement;
+* the exact Proposition-59 transform normalization.
+
+It is not a **SCALAR**, **DIAGONAL**, or independent (2\times2) surrogate.
+
+---
+
+## WHY THIS DOES NOT ASSUME G1 OR G3
+
+The new theory begins from definitions:
+
+[
+K_j
+===
+
+\operatorname{ccmWeilMatFinite}(m_j,N_j),
+]
+
+and one precommitted source trial row (q_j).
+
+It defines:
+
+[
+a_j=\langle q_j,K_jq_j\rangle,
+]
+
+[
+q_j=q_j^++q_j^-,
+]
+
+[
+b_j=P_{q_j^+{}^\perp}K_jq_j^+,
+]
+
+[
+C_j=
+P_{q_j^+{}^\perp}
+(K_j-a_jI)
+P_{q_j^+{}^\perp},
+]
+
+and the odd block:
+
+[
+O_j=P^-_j(K_j-a_jI)P^-_j.
+]
+
+The new theorem must **prove**, not assume:
+
+[
+C_j\ge\delta_j^+I,
+\qquad
+O_j\ge\delta_j^-I,
+]
+
+with:
+
+[
+\delta_j^\pm>0,
+]
+
+and:
+
+[
+\frac{|b_j|}
+{\min(\delta_j^+,\delta_j^-)}
+\longrightarrow0.
+]
+
+It must also prove the compact-transform budget:
+
+[
+C_K(m_j,N_j)
+\left(
+|q_j^-|
++
+\frac{|b_j|}
+{\min(\delta_j^+,\delta_j^-)}
+\right)
++
+\operatorname{Tail}_j(K)
++
+\operatorname{NormErr}_j(K)
+\longrightarrow0.
+]
+
+No hypothesis may contain:
+
+* a pre-existing CCM spectral gap;
+* simple ground-state existence;
+* ground-to-trial convergence;
+* RH;
+* global Weil positivity;
+* zero-location information;
+* the desired compact-open limit.
+
+Those are conclusions or downstream consequences.
+
+Thus G1/G3 are not hidden in the premises.
+
+---
+
+## EXACT THEOREM HEADS
+
+### Head 0 — exact real/complex source-row connector
+
+**Target file**
+
+```text
+q3.lean.aristotle/Q3/Proofs/RouteB/
+  CCMProposition59SourceTrialCrosswalk.lean
+```
+
+**Required public theorem**
+
+```lean
+theorem exists_sourceCCM_phase_real_trial_row
+    (S : ProlateCanonicalSourceData)
+    (i : S.Index) :
+    ∃ (phase : ℂ) (q : CCMModeFinite i.N → ℝ),
+      ‖phase‖ = 1 ∧
+      (∀ n,
+        phase * sourceCCMComplexRow S i n = (q n : ℂ)) ∧
+      q ⬝ᵥ q = 1 ∧
+      (∀ n, q (ccmNegFinite i.N n) = q n)
+```
+
+The exact repository field names may be substituted only definitionally. The conclusion must not be weakened to an approximate reality statement or a fitted phase.
+
+**Required transform connector**
+
+```lean
+theorem proposition59CCMTransform_source_real_trial
+    (S : ProlateCanonicalSourceData)
+    (i : S.Index)
+    (phase : ℂ)
+    (q : CCMModeFinite i.N → ℝ)
+    (hrow :
+      ∀ n,
+        phase * sourceCCMComplexRow S i n = (q n : ℂ)) :
+    proposition59CCMTransform
+        (Real.log i.m)
+        (fun n => (q n : ℂ))
+      =
+    phase • sourceCCMTrialTransform S i
+```
+
+The coordinate remains:
+
+[
+-\frac{\log(m_i)}{2\pi}z.
+]
+
+**Downstream consumer**
+
+```text
+Proposition59GroundLagrangeZeroSetBridge
+```
+
+and the new trial-line Schur family theorem below.
+
+### Head 1 — exact full trial-line block identity
+
+**Target file**
+
+```text
+q3.lean.aristotle/Q3/Proofs/RouteB/
+  CCMFiniteWeilTrialLineSchur.lean
+```
+
+**Required public theorem**
+
+```lean
+theorem ccmWeilMatFinite_trialLine_feshbach_identity
+    (mProject N : ℕ)
+    (q : CCMModeFinite N → ℝ)
+    (hq : q ⬝ᵥ q = 1) :
+    let K := ccmWeilMatFinite mProject N
+    let Pq := trialLineProjection q
+    let Qq := 1 - Pq
+    K =
+      Pq * K * Pq +
+      Pq * K * Qq +
+      Qq * K * Pq +
+      Qq * K * Qq
+```
+
+The theorem must use the literal matrix object. It may not replace (K) by a sectional, prolate, mode-4, midpoint, or fitted matrix.
+
+It must additionally export exact definitions of:
+
+```text
+trialRayleigh
+trialCoupling
+evenComplementBlock
+oddSectorBlock
+oddTrialMass
+```
+
+### Head 2 — new cofinal source theorem
+
+**Target file**
+
+```text
+q3.lean.aristotle/Q3/Proofs/RouteB/
+  CCMCofinalTrialLineFeshbachSourceBounds.lean
+```
+
+**Required theorem**
+
+```lean
+theorem ccmP59CofinalTrialLineFeshbachSourceBounds
+    (S : Proposition59CCMCofinalSourceData) :
+    (∀ᶠ j in Filter.atTop,
+      0 < S.evenComplementFloor j ∧
+      0 < S.oddSectorFloor j) ∧
+    Filter.Tendsto
+      (fun j =>
+        S.trialCouplingNorm j /
+          min
+            (S.evenComplementFloor j)
+            (S.oddSectorFloor j))
+      Filter.atTop
+      (nhds 0) ∧
+    Filter.Tendsto
+      S.oddTrialMass
+      Filter.atTop
+      (nhds 0) ∧
+    ∀ K,
+      IsCompact K →
+      K ⊆ shiftedStrip →
+      Filter.Tendsto
+        (fun j =>
+          S.compactEvaluationEnvelope K j *
+            (Real.sqrt (S.oddTrialMass j) +
+              S.trialCouplingNorm j /
+                min
+                  (S.evenComplementFloor j)
+                  (S.oddSectorFloor j)) +
+          S.projectionTail K j +
+          S.normalizationError K j)
[truncated after 700 lines]
```

## File snapshots

### docs/routeB_bus/proshka/PROSHKA_MYTHOS_REQUEST_GOAL058_NEXT_G1_G3_SOURCE_TASK_2026-08-13.md
```text
# Goal 058 joint request — next literal G1/G3 source task for Aristotle

Date: 2026-08-13

Roles:

- Proshka is the mathematical judge and must return the authoritative exact
  Aristotle prompt or an honest no-task stop.
- Mythos is the independent proof-architecture attacker and must try to break
  the selected source theorem before execution.
- Aristotle is only the later proof-search executor.

## Phase and source lock

```yaml
GOAL_ID: Goal058_G1_G3_CofinalGroundTracking
PROOF_ADDRESS: RouteB.Goal058.G1G3.CofinalGroundTracking
FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
SOURCE_OBJECT_FAMILY: literal ccmWeilMatFinite / sourceCCMComplexRow / Proposition59 family
BASE_HEAD: 66ed3c3365e9b522dc28de6c92c38cf5743b4759
BASE_BRANCH: rh_clean
BASE_ORIGIN: origin/rh_clean
CONTROL: P9_STRICT_PASS
CARTOGRAPHER: 207 RouteB files; 1834 declarations; missing 0; stale 0
ROUTE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
G1: OPEN
G3: OPEN
```

The response must re-pin to the exact commit containing this request before
emitting an executable task. A changed source must be re-read, not silently
adapted.

## New exact result already proved

Aristotle project `7e661f28-7943-4c6b-83e9-787c2eed4683`, task
`f958ac79-9673-4110-b9f7-538ee6673d38`, produced the kernel-checked file

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMProposition59ComplexHermitianConnector.lean
sha256 dc5e858863647224c17256b3cf629efc000ca81cbea4fb9cfd02fef28a6bc4eb
```

The public theorem
`Q3.RouteB.proposition59CCMTransform_sub_sourceProjection_le` proves, for the
literal complex unit row `D0Pstar.sourceCCMComplexRow S i` and a real P59 row
`xi`, that

```text
|P59(xi)(z) - projectionScalar * P59Complex(sourceRow)(z)|
  <= proposition59CCMKernelL2(L,N,z)
     * sqrt(sourceCCMGroundProjectionErrorSq(S,i,xi)).
```

It also proves the exact identity

```text
sourceCCMGroundProjectionErrorSq S i xi
  = sum_j normSq((xi_j : Complex) - projectionScalar * sourceRow_j).
```

The result assumes no realification, parity, eigenvector, bottomness,
simplicity, spectral gap, complement coercivity, tracking, rate, cofinal
schedule, global positivity, or RH statement. It is finite and does not assert
that the projective error is small.

Validation at production Lean 4.26:

```text
direct lake env lean: PASS
target lake build: PASS (7792 jobs)
full lake build: PASS (7817 jobs)
q3_check: PASS
forbidden proof tokens: NONE
public theorem axioms: [propext, Classical.choice, Quot.sound]
```

Closeout:

```text
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
  GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_CLOSEOUT_2026-08-13.md
sha256 9268197ca616da5b7a9c03a5dff887f9a4a11336c110f88a58173e78def7355a
```

## What remains, exactly

```text
G1: prove a uniform literal-CCM spectral separation for the selected finite
    simple-even bottom family; a generic receiver or a finite numerical gap is
    not a supplier.

G3: on the same precommitted cofinal family, prove
      sourceCCMGroundProjectionErrorSq S_j i_j xi_j -> 0
    with the compact P59 kernel control needed by the connector; an abstract
    tracking receiver or a trial residual with no true separation is not a
    supplier.
```

Exact repository and knowledge searches after integration found no declaration
whose conclusion is either source statement. The prior exact commutator is
compatible with a nonsimple kernel. The finite M1 cell is evidence only and
cannot be promoted to a cofinal theorem.

## Required decision

Select exactly one primary:

```text
ARISTOTLE_G1_LITERAL_CCM_GAP_SOURCE
ARISTOTLE_G3_LITERAL_PROJECTIVE_DECAY_SOURCE
ARISTOTLE_JOINT_LITERAL_FESHBACH_SOURCE
ARISTOTLE_LITERAL_SOURCE_NO_GO
NO_SOUND_ARISTOTLE_SOURCE_TASK_AVAILABLE
```

Preference is not a vote. Select the strongest theorem actually derivable from
the pinned source. A difficult or non-obvious theorem is welcome. A circular
theorem is not.

### A. G1 literal source

An admissible theorem must derive a nonzero separation or complement floor for
the literal `ccmWeilMatFinite` selected family. It may not take any renamed
spectral gap, endpoint envelope, complement coercivity, simplicity, or bottom
isolation as a premise.

### B. G3 literal source

An admissible theorem must derive an actual bound or cofinal decay for
`sourceCCMGroundProjectionErrorSq` on the exact same family. It may not take
ground-to-trial tracking, projective decay, residual decay divided by a supplied
gap, leakage decay, or a post-selected schedule as a premise.

### C. Joint literal Feshbach source

An admissible joint theorem may derive G1 and the finite projective estimate
from one full-source block/Feshbach argument. It must use the literal matrix,
literal complex trial line, literal ground row, and one precommitted family.
It may not hide the result in a positive complement block, small coupling,
small residual, or endpoint-envelope hypothesis unless that quantity is itself
proved in the same owned file from existing source declarations.

### D. Literal no-go

A bounded kernel-checked no-go theorem is admissible only if it decisively
proves that the current source contract cannot imply a proposed G1/G3 supplier,
and names the smallest genuinely new mathematical binder required next.

## Proshka output contract

After the strongest attack, return exactly one primary and one attachment-ready
Aristotle task with:

```yaml
TARGET_ID:
PRIMARY_CLASS:
PIN:
OWNED_FILE:
ALLOWED_IMPORTS:
FORBIDDEN_IMPORTS:
EXACT_EXISTING_DECLARATIONS:
EXACT_BINDERS:
EXACT_THEOREM_HEAD:
WHY_BINDERS_ARE_DERIVABLE:
REQUIRED_AUXILIARY_LEMMAS:
MANDATORY_FALSIFIER_PLANTS:
EXPECTED_OUTPUT:
SUCCESS_CODE:
TYPED_STOP_CODES:
AXIOM_GATE:
VALIDATION_COMMANDS:
EVIDENCE_BOUNDARY:
```

The task must own one new Lean file only and forbid edits elsewhere. It must
forbid `sorry`, `admit`, `exact?`, `native_decide`, new `axiom`, and `opaque`.
It must require direct Lean, target build, full build, `q3_check`, forbidden
token scan, `#print axioms`, and diff check.

Mandatory falsifiers must include at least:

1. wrong-family/operator substitution;
2. finite-cell-to-cofinal substitution;
3. hidden realification or parity;
4. scalar-commutator tautology;
5. renamed gap/complement-floor premise;
6. renamed tracking/projective-decay premise;
7. post-outcome schedule selection;
8. generic receiver relabeled as literal source supplier.

If no exact theorem survives, return
`NO_SOUND_ARISTOTLE_SOURCE_TASK_AVAILABLE` and the smallest missing source
lemma signature. Do not manufacture a task merely to keep Aristotle busy.

## Mythos attack contract

Independently inspect the same pinned evidence and return:

```yaml
MYTHOS_VERDICT: SURVIVES | REJECT | REVISE | NO_TASK
ATTACKED_PRIMARY:
FIRST_HIDDEN_BINDER_OR_OBJECT_MISMATCH:
COUNTEREXAMPLE_OR_REASON:
SMALLEST_REPAIR:
RECOMMENDED_EXACT_THEOREM_HEAD:
```

Mythos should prefer a concrete counterexample or binder audit over narrative
agreement. If it proposes a theorem, it must obey the same literal-source and
non-circularity rules.

## Evidence boundary

This request authorizes task design and architecture attack only. It does not
close G1 or G3, does not authorize Route B promotion, does not make a PX or RH
claim, and does not turn finite numerics into a uniform or cofinal theorem.
```

### q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean
```text
import Q3.Proofs.RouteB.CCMProposition59SourceTrialFeshbachPreflight

set_option linter.mathlibStandardSet false

/-!
# Goal 058 complex Hermitian Proposition-59 connector

The literal CCM source coefficient row is complex and unit; the Proposition-59
transform consumes a real row.  This file removes that object mismatch without
any realification, parity, gap, tracking, or spectral hypothesis: it uses the
exact Hermitian rank-one projection onto the literal complex source line.

For a real row `xi` the scalar `sourceCCMGroundProjectionScalar S i xi` is the
exact Hermitian projection coefficient of `xi` onto the literal complex source
row, and `sourceCCMGroundProjectionErrorSq S i xi` is the exact squared
coefficient-space distance from `xi` to that complex line.  The main theorem
bounds the pointwise difference between the real Proposition-59 transform of
`xi` and the projection-scaled complex source transform by the exact P59 kernel
`L²`-norm times the square root of that projective error.

Nothing here asserts that the projective error is small or that it decays.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- Hermitian rank-one matrix of the complex trial line spanned by `q`. -/
noncomputable def complexTrialLineProjection
    {ι : Type*} (q : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec q (star q)

/-- Exact Hermitian projection coefficient of the real row `xi` onto the
literal complex CCM source line. -/
noncomputable def sourceCCMGroundProjectionScalar
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) : ℂ :=
  star (D0Pstar.sourceCCMComplexRow S i) ⬝ᵥ
    (fun j => (xi j : ℂ))

/-- Exact squared coefficient-space distance from `xi` to the complex source
line. -/
noncomputable def sourceCCMGroundProjectionErrorSq
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) : ℝ :=
  xi ⬝ᵥ xi -
    Complex.normSq (sourceCCMGroundProjectionScalar S i xi)

/-- Exact `L²` size of the finite Proposition-59 pole kernel family, in the
locked coordinate `source mode n → P59 pole -n`. -/
noncomputable def proposition59CCMKernelL2
    (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  ‖((Real.sqrt L : ℂ)⁻¹)‖ *
    Real.sqrt
      (∑ j : CCMModeFinite N,
        Complex.normSq
          (proposition59PoleKernel L (-ccmModeFinite N j) z))

theorem complexTrialLineProjection_isHermitian
    {ι : Type*} (q : ι → ℂ) :
    (complexTrialLineProjection q).IsHermitian := by
  show (complexTrialLineProjection q)ᴴ = complexTrialLineProjection q
  ext i j
  simp [complexTrialLineProjection, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, mul_comm]

theorem complexTrialLineProjection_sq_of_unit
    {ι : Type*} [Fintype ι]
    (q : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    complexTrialLineProjection q * complexTrialLineProjection q =
      complexTrialLineProjection q := by
  rw [complexTrialLineProjection, Matrix.vecMulVec_mul_vecMulVec, hq, one_smul]

/-- Generic Hermitian projective error identity for an arbitrary unit complex
row.  This is a private helper: the public interface always hard-codes the
literal source row. -/
private theorem complexRow_projection_error_identity
    {ι : Type*} [Fintype ι]
    (row : ι → ℂ) (xi : ι → ℝ)
    (hrow : star row ⬝ᵥ row = 1) :
    xi ⬝ᵥ xi -
        Complex.normSq (star row ⬝ᵥ (fun j => (xi j : ℂ))) =
      ∑ j,
        Complex.normSq
          ((xi j : ℂ) -
            (star row ⬝ᵥ (fun j => (xi j : ℂ))) * row j) := by
  classical
  set c : ℂ := star row ⬝ᵥ (fun j => (xi j : ℂ)) with hc
  have hcdef : c = ∑ j, (starRingEnd ℂ) (row j) * (xi j : ℂ) := by
    simp [hc, dotProduct]
  have hrow' : ∑ j, (starRingEnd ℂ) (row j) * row j = 1 := by
    simpa [dotProduct] using hrow
  have hconj : (starRingEnd ℂ) c = ∑ j, row j * (xi j : ℂ) := by
    rw [hcdef, map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp [mul_comm]
  have hxi : ((xi ⬝ᵥ xi : ℝ) : ℂ) = ∑ j, (xi j : ℂ) * (xi j : ℂ) := by
    simp [dotProduct]
  have hterm : ∀ j : ι,
      ((Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ) =
        (xi j : ℂ) * (xi j : ℂ) -
          (starRingEnd ℂ) c * ((xi j : ℂ) * (starRingEnd ℂ) (row j)) -
          c * (row j * (xi j : ℂ)) +
          (c * (starRingEnd ℂ) c) *
            ((starRingEnd ℂ) (row j) * row j) := by
    intro j
    rw [← Complex.mul_conj]
    simp only [map_sub, map_mul, Complex.conj_ofReal]
    ring
  have hcast :
      ((∑ j, Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ) =
        ((xi ⬝ᵥ xi : ℝ) : ℂ) - ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ j, ((Complex.normSq ((xi j : ℂ) - c * row j) : ℝ) : ℂ)) =
          ∑ j,
            ((xi j : ℂ) * (xi j : ℂ) -
              (starRingEnd ℂ) c * ((xi j : ℂ) * (starRingEnd ℂ) (row j)) -
              c * (row j * (xi j : ℂ)) +
              (c * (starRingEnd ℂ) c) *
                ((starRingEnd ℂ) (row j) * row j)) :=
        Finset.sum_congr rfl fun j _ => hterm j
      _ = (∑ j, (xi j : ℂ) * (xi j : ℂ)) -
            (starRingEnd ℂ) c *
              (∑ j, (xi j : ℂ) * (starRingEnd ℂ) (row j)) -
            c * (∑ j, row j * (xi j : ℂ)) +
            (c * (starRingEnd ℂ) c) *
              (∑ j, (starRingEnd ℂ) (row j) * row j) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
      _ = ((xi ⬝ᵥ xi : ℝ) : ℂ) - ((Complex.normSq c : ℝ) : ℂ) := by
        have hswap : (∑ j, (xi j : ℂ) * (starRingEnd ℂ) (row j)) = c := by
          rw [hcdef]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [hswap, ← hconj, hrow', hxi, ← Complex.mul_conj]
        ring
  exact_mod_cast hcast.symm

/-- The exact projective error of `xi` against the literal complex source line
is the total squared coefficient residual after removing the Hermitian
projection.  No realification or parity input is used. -/
theorem sourceCCMGroundProjectionErrorSq_eq_sum_normSq
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) :
    sourceCCMGroundProjectionErrorSq S i xi =
      ∑ j,
        Complex.normSq
          ((xi j : ℂ) -
            sourceCCMGroundProjectionScalar S i xi *
              D0Pstar.sourceCCMComplexRow S i j) := by
  exact complexRow_projection_error_identity
    (D0Pstar.sourceCCMComplexRow S i) xi
    (D0Pstar.sourceCCMComplexRow_unit S i)

/-- Finite Cauchy-Schwarz for the exact source-locked P59 mode sum. -/
private theorem proposition59CCM_mode_sum_cauchy_schwarz
    (L : ℝ) (N : ℕ) (w : CCMModeFinite N → ℂ) (z : ℂ) :
    ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ ≤
      Real.sqrt (∑ j, Complex.normSq (w j)) *
        Real.sqrt
          (∑ j,
            Complex.normSq
              (proposition59PoleKernel L (-ccmModeFinite N j) z)) := by
  classical
  calc
    ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ ≤
        ∑ j, ‖w j * proposition59PoleKernel L (-ccmModeFinite N j) z‖ :=
      norm_sum_le _ _
    _ = ∑ j, ‖w j‖ * ‖proposition59PoleKernel L (-ccmModeFinite N j) z‖ := by
      exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    _ ≤ Real.sqrt (∑ j, ‖w j‖ ^ 2) *
          Real.sqrt
            (∑ j,
              ‖proposition59PoleKernel L (-ccmModeFinite N j) z‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ j, Complex.normSq (w j)) *
          Real.sqrt
            (∑ j,
              Complex.normSq
                (proposition59PoleKernel L (-ccmModeFinite N j) z)) := by
      simp [Complex.normSq_eq_norm_sq]

/-- Exact finite Hermitian connector.  The projective error is nonnegative, and
the pointwise difference between the real Proposition-59 transform of `xi` and
the projection-scaled complex source transform is bounded by the exact P59
kernel `L²`-norm times the square root of that error.

The positivity binder `hL` is part of the locked theorem head; the bound is in
fact uniform in `L`, so the proof does not consume it. -/
theorem proposition59CCMTransform_sub_sourceProjection_le
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (L : ℝ) (hL : 0 < L)
    (xi : CCMModeFinite i.N → ℝ) :
    0 ≤ sourceCCMGroundProjectionErrorSq S i xi ∧
    ∀ z : ℂ,
      ‖proposition59CCMTransform L i.N xi z -
          sourceCCMGroundProjectionScalar S i xi *
            proposition59CCMComplexTransform L i.N
              (D0Pstar.sourceCCMComplexRow S i) z‖
        ≤ proposition59CCMKernelL2 L i.N z *
            Real.sqrt (sourceCCMGroundProjectionErrorSq S i xi) := by
  classical
  set c : ℂ := sourceCCMGroundProjectionScalar S i xi with hc
  set row : CCMModeFinite i.N → ℂ := D0Pstar.sourceCCMComplexRow S i with hrowdef
  set w : CCMModeFinite i.N → ℂ := fun j => (xi j : ℂ) - c * row j with hw
  have herr :
      sourceCCMGroundProjectionErrorSq S i xi = ∑ j, Complex.normSq (w j) :=
    sourceCCMGroundProjectionErrorSq_eq_sum_normSq S i xi
  have hnonneg : 0 ≤ sourceCCMGroundProjectionErrorSq S i xi := by
    rw [herr]
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  refine ⟨hnonneg, fun z => ?_⟩
  have hsplit :
      proposition59CCMTransform L i.N xi z -
          c * proposition59CCMComplexTransform L i.N row z =
        ((Real.sqrt L : ℂ)⁻¹) *
          ∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z := by
    rw [proposition59CCMTransform_eq_mode_sum,
      proposition59CCMComplexTransform_eq_mode_sum]
    have hsum :
        (∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z) =
          (∑ j, (xi j : ℂ) *
              proposition59PoleKernel L (-ccmModeFinite i.N j) z) -
            c * ∑ j, row j *
              proposition59PoleKernel L (-ccmModeFinite i.N j) z := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp [hw, sub_mul, mul_assoc]
    rw [hsum]
    ring
  rw [hsplit, norm_mul, herr]
  have hcs := proposition59CCM_mode_sum_cauchy_schwarz L i.N w z
  have hnormnn : (0 : ℝ) ≤ ‖((Real.sqrt L : ℂ)⁻¹)‖ := norm_nonneg _
  calc
    ‖((Real.sqrt L : ℂ)⁻¹)‖ *
        ‖∑ j, w j * proposition59PoleKernel L (-ccmModeFinite i.N j) z‖ ≤
        ‖((Real.sqrt L : ℂ)⁻¹)‖ *
          (Real.sqrt (∑ j, Complex.normSq (w j)) *
            Real.sqrt
              (∑ j,
                Complex.normSq
                  (proposition59PoleKernel L
                    (-ccmModeFinite i.N j) z))) := by
      exact mul_le_mul_of_nonneg_left hcs hnormnn
    _ = proposition59CCMKernelL2 L i.N z *
          Real.sqrt (∑ j, Complex.normSq (w j)) := by
      rw [proposition59CCMKernelL2]
      ring

/-! ### Mandatory falsifier plants -/

/-- P2 plant: a two-coordinate complex row with entries `1` and `Complex.I`. -/
def goal058ConnectorPhasePlantRow : Fin 2 → ℂ := ![1, Complex.I]

/-- P2: no common unit phase turns the plant row into a real row, so the
Hermitian connector may not presuppose one. -/
theorem goal058ConnectorPhasePlant_no_common_real_phase :
    ¬ ∃ (phase : ℂ) (q : Fin 2 → ℝ),
        Complex.normSq phase = 1 ∧
          ∀ j, phase * goal058ConnectorPhasePlantRow j = (q j : ℂ) := by
  rintro ⟨phase, q, hunit, hreal⟩
  have h0 := hreal 0
  have h1 := hreal 1
  simp [goal058ConnectorPhasePlantRow] at h0 h1
  have hre : phase.re = 0 := by
    have := congrArg Complex.im h1
    simpa [Complex.ext_iff, Complex.mul_im, Complex.mul_re] using this
  have him : phase.im = 0 := by
    have := congrArg Complex.im h0
    simpa using this
  have : phase = 0 := by
    apply Complex.ext <;> simp [hre, him]
  rw [this] at hunit
  simp at hunit

/-- P5 plant: a unit complex row orthogonal to the tested real row. -/
def goal058ConnectorZeroOverlapRow : Fin 2 → ℂ := ![1, 0]

/-- P5 plant: the tested real row. -/
def goal058ConnectorZeroOverlapXi : Fin 2 → ℝ := ![0, 1]

theorem goal058ConnectorZeroOverlapRow_unit :
    star goal058ConnectorZeroOverlapRow ⬝ᵥ goal058ConnectorZeroOverlapRow
      = 1 := by
  simp [goal058ConnectorZeroOverlapRow, dotProduct, Fin.sum_univ_succ]

/-- P5: the Hermitian projection scalar vanishes on the orthogonal plant, and
the projective error is the full mass of the tested row.  No division by the
overlap occurs anywhere. -/
theorem goal058ConnectorZeroOverlapPlant_projection_zero :
    (star goal058ConnectorZeroOverlapRow ⬝ᵥ
        (fun j => (goal058ConnectorZeroOverlapXi j : ℂ))) = 0 ∧
      goal058ConnectorZeroOverlapXi ⬝ᵥ goal058ConnectorZeroOverlapXi -
          Complex.normSq
            (star goal058ConnectorZeroOverlapRow ⬝ᵥ
              (fun j => (goal058ConnectorZeroOverlapXi j : ℂ))) = 1 := by
  constructor <;>
    simp [goal058ConnectorZeroOverlapRow, goal058ConnectorZeroOverlapXi,
      dotProduct, Fin.sum_univ_succ]

/-- P6 plant: a one-coordinate purely imaginary source row. -/
def goal058ConnectorOrientationPlantRow : Fin 1 → ℂ := ![Complex.I]

/-- P6 plant: the tested one-coordinate real row. -/
def goal058ConnectorOrientationPlantXi : Fin 1 → ℝ := ![1]

theorem goal058ConnectorOrientationPlantRow_unit :
    star goal058ConnectorOrientationPlantRow ⬝ᵥ
        goal058ConnectorOrientationPlantRow = 1 := by
  simp [goal058ConnectorOrientationPlantRow, dotProduct]

/-- P6: with the Hermitian (conjugate-left) orientation the projection scalar
is `-I` and the coefficient error is exactly zero; a conjugation or orientation
reversal would break this. -/
theorem goal058ConnectorOrientationPlant_error_zero :
    (star goal058ConnectorOrientationPlantRow ⬝ᵥ
        (fun j => (goal058ConnectorOrientationPlantXi j : ℂ))) = -Complex.I ∧
      goal058ConnectorOrientationPlantXi ⬝ᵥ
            goal058ConnectorOrientationPlantXi -
          Complex.normSq
            (star goal058ConnectorOrientationPlantRow ⬝ᵥ
              (fun j =>
                (goal058ConnectorOrientationPlantXi j : ℂ))) = 0 ∧
      ∀ j,
        (goal058ConnectorOrientationPlantXi j : ℂ) -
            (star goal058ConnectorOrientationPlantRow ⬝ᵥ
              (fun k =>
                (goal058ConnectorOrientationPlantXi k : ℂ))) *
              goal058ConnectorOrientationPlantRow j = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [goal058ConnectorOrientationPlantRow,
      goal058ConnectorOrientationPlantXi, dotProduct]
  · simp [goal058ConnectorOrientationPlantRow,
      goal058ConnectorOrientationPlantXi, dotProduct]
  · intro j
    fin_cases j
    simp [goal058ConnectorOrientationPlantRow,
      goal058ConnectorOrientationPlantXi, dotProduct]

/-- P3: the exact commutator-tautology falsifiers of the preflight are retained
here as checks only.  Neither the main connector nor any lemma it uses depends
on them. -/
theorem goal058ConnectorCommutatorPlant_checks_retained :
    lagCommutatorObservable goal058PlantD goal058PlantK goal058PlantQ = 0 ∧
      ¬ ∃ mu : ℝ, goal058PlantK *ᵥ goal058PlantQ = mu • goal058PlantQ :=
  ⟨goal058Plant_lagCommutatorObservable_zero, goal058PlantQ_not_eigenvector⟩

#print axioms complexTrialLineProjection_isHermitian
#print axioms complexTrialLineProjection_sq_of_unit
#print axioms sourceCCMGroundProjectionErrorSq_eq_sum_normSq
#print axioms proposition59CCMTransform_sub_sourceProjection_le
#print axioms goal058ConnectorPhasePlant_no_common_real_phase
#print axioms goal058ConnectorZeroOverlapRow_unit
#print axioms goal058ConnectorZeroOverlapPlant_projection_zero
#print axioms goal058ConnectorOrientationPlantRow_unit
#print axioms goal058ConnectorOrientationPlant_error_zero
#print axioms goal058ConnectorCommutatorPlant_checks_retained

end Q3.RouteB
```

### q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_CLOSEOUT_2026-08-13.md
```text
# Goal 058 complex-Hermitian P59 connector closeout

Date: 2026-08-13

## Verdict

```yaml
TARGET_ID: GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR
PRIMARY: ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR
VERDICT: PASS_FINITE_EXACT_CONNECTOR
SUCCESS: GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_PROVED
SCOPE: FINITE_CELL
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Source lock and execution

The authoritative Proshka verdict selected the exact theorem surface archived
at:

```text
docs/routeB_bus/proshka/
  PROSHKA_VERDICT_GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_CONNECTOR_2026-08-13.md
```

The source-locked request packet was committed at
`d106a3f4356664c871d1bf96c06f6e5324643e4e`.  Aristotle project
`7e661f28-7943-4c6b-83e9-787c2eed4683`, task
`f958ac79-9673-4110-b9f7-538ee6673d38`, completed after 25m02s with service
summary `GOAL058_COMPLEX_HERMITIAN_P59_CONNECTOR_PROVED`.

Downloaded archive:

```text
q3.lean.aristotle/aristotle_output/
  7e661f28-7943-4c6b-83e9-787c2eed4683.tar.gz
sha256: 6a9868faef17dcdb52134b8379aa47232ba7ec6794efc1b52b67260b849702f1
```

Archive comparison against the submitted 54-file bundle found one new Q3
source file only.  The temporary Aristotle-side Lean-4.28 compatibility edit to
`QuotientByRadicalPosDefMatrix.lean` was absent from the returned diff; that
dependency remained byte-identical to the submitted source.

## Integrated theorem

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  CCMProposition59ComplexHermitianConnector.lean
sha256: dc5e858863647224c17256b3cf629efc000ca81cbea4fb9cfd02fef28a6bc4eb
```

The file proves the exact public head
`Q3.RouteB.proposition59CCMTransform_sub_sourceProjection_le`:

- `D0Pstar.sourceCCMComplexRow S i` is the literal complex unit source row;
- `sourceCCMGroundProjectionScalar S i xi` is its Hermitian projection
  coefficient against the real P59 row `xi`;
- `sourceCCMGroundProjectionErrorSq S i xi` is exactly the finite sum of
  coefficient residual norm-squares;
- the P59 transform mismatch is bounded by the exact P59 kernel L2 norm times
  the square root of that projective error;
- the existing `source mode n -> P59 pole -n` coordinate is preserved.

The theorem assumes no phase realification, source parity, eigenvector,
bottomness, simplicity, spectral gap, complement coercivity, tracking rate,
cofinal schedule, convergence, global positivity, or RH statement.  It does
not assert that the projective error is small.

Mandatory exact plants cover:

1. a two-coordinate `[1, I]` row with no common realifying phase;
2. a zero-overlap branch with no division by overlap;
3. the one-coordinate `[I]` orientation where the coefficient is `-I` and the
   error is zero;
4. retention of the preflight scalar-commutator tautology/non-eigenvector
   falsifiers as checks only.

The Proshka validation regex forbade the commutator identifier while P3
simultaneously required its exact retained check.  The two identifier hits in
the final file occur only in the P3 plant theorem and its supplied lemma; no
connector definition or proof consumes the commutator observable.

## Validation

```text
direct lake env lean: PASS
target lake build: PASS (7792 jobs)
full lake build: PASS (7817 jobs)
q3_check: PASS
forbidden proof tokens: NONE
git diff --check: PASS
public theorem axioms: [propext, Classical.choice, Quot.sound]
```

One warning is retained honestly: the locked theorem head contains
`hL : 0 < L`, but the proved estimate is uniform in `L`, so the proof does not
consume that binder.

## Residual Goal 058 obligations

The connector removes the finite complex-source / real-P59 object mismatch.
It does not supply either open wall:

```text
G1: uniform literal CCM spectral-gap source remains open.
G3: a same-family cofinal theorem forcing
    sourceCCMGroundProjectionErrorSq S_j i_j xi_j -> 0
    (with the required compact P59 kernel control) remains open.
```

Finite numerics, including the earlier M1 control cell, do not discharge these
cofinal suppliers.

## Search flags and arsenal

```yaml
SEARCH_FLAGS:
  - GOAL058_COMPLEX_HERMITIAN_CONNECTOR
  - SOURCE_CCM_GROUND_PROJECTION_ERROR_SQ
  - COFINAL_PROJECTIVE_ERROR_DECAY
  - UNIFORM_LITERAL_CCM_SPECTRAL_GAP
ARSENAL_USED:
  - Proshka source-locked task design
  - Aristotle exact Lean proof search
  - Hermitian rank-one projection
  - exact P59 mode-sum identities
  - finite Cauchy-Schwarz
  - production Lean 4.26 validation
AUTOPSY: >-
  The unavailable common-phase realification was not manufactured. The finite
  object mismatch is now an exact inequality, exposing the true remaining G3
  supplier as cofinal decay of the literal Hermitian projective error. G1 is
  unchanged.
```
```

### q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean
```text
import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual
import Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge
import Q3.Proofs.RouteB.CCMFiniteWeilParity
import Q3.Proofs.RouteB.CCMFiniteWeilSourceCommutator

set_option linter.mathlibStandardSet false

/-!
# Goal 058 full-source trial-line / Schur preflight

This file deliberately separates the algebra that is already available from
the missing source theorem.  The exact D0Pstar source row is complex.  The
Proposition-59 ground transform is real.  A unit phase realification is
therefore recorded as an explicit proposition rather than synthesized by
taking real parts or by choosing a numerical phase.

The results below prove the exact consequences of such a realification, the
phase-adjusted P59 transform identity, the full trial-line four-block identity,
and a kernel-checked non-eigenvector commutator plant.  They do not prove that
the literal source row has the required phase realification, and they make
no positivity, gap, cofinal, route, or RH claim.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- Exact unit-phase realification, with no numerical phase choice and no
replacement of the complex row by its real part. -/
def phaseRealifies
    {ι : Type*}
    (phase : ℂ) (row : ι → ℂ) (q : ι → ℝ) : Prop :=
  Complex.normSq phase = 1 ∧
    ∀ j, phase * row j = (q j : ℂ)

/-- The precise missing source-to-real carrier proposition for the literal
D0Pstar coefficient row. -/
def sourceCCMPhaseRealification
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (phase : ℂ)
    (q : CCMModeFinite i.N → ℝ) : Prop :=
  phaseRealifies phase (D0Pstar.sourceCCMComplexRow S i) q

/-- The exact existential source statement required before the complex trial
can be used as the real-even Proposition-59 row. -/
def sourceCCMHasRealEvenPhase
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) : Prop :=
  ∃ (phase : ℂ) (q : CCMModeFinite i.N → ℝ),
    sourceCCMPhaseRealification S i phase q ∧
      ∀ j, q (ccmNegFinite i.N j) = q j

/-- Taking real parts with phase one is not a construction: it requires the
original complex row to be exactly real coordinatewise. -/
theorem phaseOne_realPart_requires_exact_reality
    {ι : Type*} (row : ι → ℂ)
    (h : phaseRealifies 1 row (fun j => (row j).re)) :
    ∀ j, row j = (row j).re := by
  intro j
  simpa using h.2 j

/-- A unit phase realification preserves the exact Euclidean unit norm of a
complex row. -/
theorem dotProduct_self_eq_one_of_phaseRealifies
    {ι : Type*} [Fintype ι]
    (phase : ℂ) (row : ι → ℂ) (q : ι → ℝ)
    (hrow : star row ⬝ᵥ row = 1)
    (hphase : phaseRealifies phase row q) :
    q ⬝ᵥ q = 1 := by
  rcases hphase with ⟨hunit, hreal⟩
  have hphaseNorm : star phase * phase = 1 := by
    have hunitC : ((Complex.normSq phase : ℝ) : ℂ) = 1 := by
      exact_mod_cast hunit
    rw [Complex.normSq_eq_conj_mul_self] at hunitC
    exact hunitC
  have hcomplex :
      star (fun j => phase * row j) ⬝ᵥ (fun j => phase * row j) = 1 := by
    have hterm (j : ι) :
        star (phase * row j) * (phase * row j) =
          (star phase * phase) * (star (row j) * row j) := by
      rw [StarMul.star_mul]
      ring
    calc
      star (fun j => phase * row j) ⬝ᵥ (fun j => phase * row j) =
          (star phase * phase) * (star row ⬝ᵥ row) := by
        classical
        simp only [dotProduct, Pi.star_apply, hterm]
        rw [Finset.mul_sum]
      _ = 1 := by
        rw [hrow, mul_one, hphaseNorm]
  have hcast : ((q ⬝ᵥ q : ℝ) : ℂ) = 1 := by
    calc
      ((q ⬝ᵥ q : ℝ) : ℂ) =
          star (fun j => (q j : ℂ)) ⬝ᵥ (fun j => (q j : ℂ)) := by
        classical
        simp [dotProduct]
      _ = star (fun j => phase * row j) ⬝ᵥ
          (fun j => phase * row j) := by
        congr 1
        · funext j
          simp only [Pi.star_apply]
          rw [hreal j]
        · funext j
          exact (hreal j).symm
      _ = 1 := hcomplex
  exact_mod_cast hcast

/-- The literal source row therefore yields a real unit row whenever the
missing phase-realification proposition is supplied. -/
theorem sourceCCMRealRow_unit_of_phaseRealification
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (phase : ℂ)
    (q : CCMModeFinite i.N → ℝ)
    (hphase : sourceCCMPhaseRealification S i phase q) :
    q ⬝ᵥ q = 1 := by
  exact dotProduct_self_eq_one_of_phaseRealifies
    phase (D0Pstar.sourceCCMComplexRow S i) q
    (D0Pstar.sourceCCMComplexRow_unit S i) hphase

/-- Exact reflection-evenness of a realified row would force exact
reflection-evenness of the original complex source row.  This is the
necessary source theorem that the current D0Pstar contract does not export. -/
theorem sourceCCMComplexRow_even_of_phaseRealification_even
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (phase : ℂ)
    (q : CCMModeFinite i.N → ℝ)
    (hphase : sourceCCMPhaseRealification S i phase q)
    (hqEven : ∀ j, q (ccmNegFinite i.N j) = q j) :
    ∀ j,
      D0Pstar.sourceCCMComplexRow S i (ccmNegFinite i.N j) =
        D0Pstar.sourceCCMComplexRow S i j := by
  rcases hphase with ⟨hunit, hreal⟩
  have hphase0 : phase ≠ 0 := by
    intro hzero
    subst phase
    simp at hunit
  intro j
  apply mul_left_cancel₀ hphase0
  rw [hreal, hqEven, hreal]

/-- Complex coefficient transport to the exact P59 pole order. -/
def proposition59CCMComplexCoefficient
    (N : ℕ) (q : CCMModeFinite N → ℂ) (k : ℤ) : ℂ :=
  if hk : k ∈ Finset.Icc (-(N : ℤ)) N then
    q ((ccmModeFiniteEquivIcc N).symm
      ⟨-k, neg_mem_Icc_of_mem_Icc hk⟩)
  else 0

@[simp] theorem proposition59CCMComplexCoefficient_neg_mode
    (N : ℕ) (q : CCMModeFinite N → ℂ) (i : CCMModeFinite N) :
    proposition59CCMComplexCoefficient N q (-ccmModeFinite N i) = q i := by
  have hi : -ccmModeFinite N i ∈ Finset.Icc (-(N : ℤ)) N :=
    neg_mem_Icc_of_mem_Icc
      (Finset.mem_Icc.mpr (ccmModeFinite_range N i))
  rw [proposition59CCMComplexCoefficient, dif_pos hi]
  congr 1
  let e := ccmModeFiniteEquivIcc N
  have hsub :
      (⟨-(-ccmModeFinite N i),
        neg_mem_Icc_of_mem_Icc hi⟩ :
          {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N}) = e i := by
    apply Subtype.ext
    simp [e, ccmModeFiniteEquivIcc]
  change e.symm _ = i
  rw [hsub, e.symm_apply_apply]

/-- The exact finite P59 transform of a complex CCM row. -/
def proposition59CCMComplexTransform
    (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) : ℂ → ℂ :=
  proposition59RawTransform L (Finset.Icc (-(N : ℤ)) N)
    (proposition59CCMComplexCoefficient N q)

theorem proposition59CCMComplexTransform_eq_mode_sum
    (L : ℝ) (N : ℕ) (q : CCMModeFinite N → ℂ) (z : ℂ) :
    proposition59CCMComplexTransform L N q z =
      ((Real.sqrt L : ℂ)⁻¹) *
        ∑ i, q i * proposition59PoleKernel L (-ccmModeFinite N i) z := by
  classical
  unfold proposition59CCMComplexTransform proposition59RawTransform
  congr 1
  let e := ccmPoleModeEquivIcc N
  calc
    (∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        proposition59CCMComplexCoefficient N q k *
          proposition59PoleKernel L k z) =
        ∑ k : {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) N},
          proposition59CCMComplexCoefficient N q k.1 *
            proposition59PoleKernel L k.1 z := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach (Finset.Icc (-(N : ℤ)) N)
          (fun k => proposition59CCMComplexCoefficient N q k *
            proposition59PoleKernel L k z)).symm
    _ = ∑ i : CCMModeFinite N,
          proposition59CCMComplexCoefficient N q (e i).1 *
            proposition59PoleKernel L (e i).1 z := by
      simpa using (e.sum_comp
        (fun k => proposition59CCMComplexCoefficient N q k.1 *
          proposition59PoleKernel L k.1 z)).symm
    _ = ∑ i, q i *
          proposition59PoleKernel L (-ccmModeFinite N i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [e, ccmPoleModeEquivIcc]

/-- The real P59 transform is exactly the unit-phase-adjusted transform of the
same complex source row.  This theorem is conditional only on the exact
realification equality; it does not manufacture that equality. -/
theorem proposition59CCMTransform_eq_phase_mul_complexTransform
    (L : ℝ) (N : ℕ)
    (phase : ℂ) (row : CCMModeFinite N → ℂ)
    (q : CCMModeFinite N → ℝ)
    (hreal : ∀ i, phase * row i = (q i : ℂ))
    (z : ℂ) :
    proposition59CCMTransform L N q z =
      phase * proposition59CCMComplexTransform L N row z := by
  rw [proposition59CCMTransform_eq_mode_sum,
    proposition59CCMComplexTransform_eq_mode_sum]
  simp_rw [← hreal, mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- Source-specialized exact P59 connector. -/
theorem sourceCCMProposition59Transform_eq_phase_mul_complexTransform
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (L : ℝ) (phase : ℂ) (q : CCMModeFinite i.N → ℝ)
    (hphase : sourceCCMPhaseRealification S i phase q)
    (z : ℂ) :
    proposition59CCMTransform L i.N q z =
      phase * proposition59CCMComplexTransform L i.N
        (D0Pstar.sourceCCMComplexRow S i) z := by
  exact proposition59CCMTransform_eq_phase_mul_complexTransform
    L i.N phase (D0Pstar.sourceCCMComplexRow S i) q hphase.2 z

/-- Rank-one trial-line matrix.  It is an orthogonal projection when `q` is
real and `q dot q = 1`. -/
def trialLineProjection
    {ι : Type*} (q : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.vecMulVec q q

/-- Algebraic complement of the trial line. -/
def trialLineComplement
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) : Matrix ι ι ℝ :=
  1 - trialLineProjection q

/-- Exact trial Rayleigh scalar. -/
def trialRayleigh
    {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℝ) (q : ι → ℝ) : ℝ :=
  q ⬝ᵥ (K *ᵥ q)

/-- Exact coupling of the trial line into its algebraic complement. -/
def trialCoupling
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (q : ι → ℝ) : ι → ℝ :=
  trialLineComplement q *ᵥ (K *ᵥ q)

/-- Matrix of the exact CCM reflection permutation. -/
def ccmReflectionMatrix (N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  fun i j => if j = ccmNegFinite N i then 1 else 0

/-- Exact even-sector projection for the CCM reflection. -/
def ccmEvenProjection (N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  (2 : ℝ)⁻¹ • (1 + ccmReflectionMatrix N)

/-- Exact odd-sector projection for the CCM reflection. -/
def ccmOddProjection (N : ℕ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  (2 : ℝ)⁻¹ • (1 - ccmReflectionMatrix N)

/-- The even part of the complement-to-complement block. -/
def evenComplementBlock
    (N : ℕ)
    (K : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ)
    (q : CCMModeFinite N → ℝ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  ccmEvenProjection N * trialLineComplement q * K *
    trialLineComplement q * ccmEvenProjection N

/-- Exact odd-sector compression of the same matrix. -/
def oddSectorBlock
    (N : ℕ)
    (K : Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ) :
    Matrix (CCMModeFinite N) (CCMModeFinite N) ℝ :=
  ccmOddProjection N * K * ccmOddProjection N

/-- Exact squared mass of the odd part of a trial row. -/
def oddTrialMass
    (N : ℕ) (q : CCMModeFinite N → ℝ) : ℝ :=
  let qOdd := ccmOddProjection N *ᵥ q
  qOdd ⬝ᵥ qOdd

theorem trialLineProjection_sq
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq : q ⬝ᵥ q = 1) :
    trialLineProjection q * trialLineProjection q =
      trialLineProjection q := by
  rw [trialLineProjection, Matrix.vecMulVec_mul_vecMulVec, hq]
  simp

/-- Exact four-block decomposition relative to the trial line and its
complement.  No spectral inequality is hidden in this identity. -/
theorem full_trialLine_four_block_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (q : ι → ℝ) :
    K =
      trialLineProjection q * K * trialLineProjection q +
      trialLineProjection q * K * trialLineComplement q +
      trialLineComplement q * K * trialLineProjection q +
      trialLineComplement q * K * trialLineComplement q := by
  unfold trialLineComplement
  noncomm_ring

/-- Literal CCM specialization of the exact four-block identity. -/
theorem ccmWeilMatFinite_full_trialLine_four_block_identity
    (mProject N : ℕ) (q : CCMModeFinite N → ℝ) :
    ccmWeilMatFinite mProject N =
      trialLineProjection q * ccmWeilMatFinite mProject N *
          trialLineProjection q +
      trialLineProjection q * ccmWeilMatFinite mProject N *
          trialLineComplement q +
      trialLineComplement q * ccmWeilMatFinite mProject N *
          trialLineProjection q +
      trialLineComplement q * ccmWeilMatFinite mProject N *
          trialLineComplement q := by
  exact full_trialLine_four_block_identity (ccmWeilMatFinite mProject N) q

/-- Scalar commutator observable tested by the exact plant below. -/
def lagCommutatorObservable
    {ι : Type*} [Fintype ι]
    (D K : Matrix ι ι ℝ) (q : ι → ℝ) : ℝ :=
  q ⬝ᵥ ((D * K - K * D) *ᵥ q)

/-- For symmetric real matrices the scalar expectation of a commutator is
identically zero, independently of whether the tested row is an eigenvector. -/
theorem lagCommutatorObservable_zero_of_isSymm
    {ι : Type*} [Fintype ι]
    (D K : Matrix ι ι ℝ) (q : ι → ℝ)
    (hD : D.IsSymm) (hK : K.IsSymm) :
    lagCommutatorObservable D K q = 0 := by
  have hDK :
      q ⬝ᵥ (D *ᵥ (K *ᵥ q)) = (D *ᵥ q) ⬝ᵥ (K *ᵥ q) := by
    calc
      q ⬝ᵥ (D *ᵥ (K *ᵥ q)) = (q ᵥ* D) ⬝ᵥ (K *ᵥ q) :=
        dotProduct_mulVec q D (K *ᵥ q)
      _ = (D.transpose *ᵥ q) ⬝ᵥ (K *ᵥ q) := by
        rw [Matrix.mulVec_transpose]
      _ = (D *ᵥ q) ⬝ᵥ (K *ᵥ q) := by rw [hD.eq]
  have hKD :
      q ⬝ᵥ (K *ᵥ (D *ᵥ q)) = (K *ᵥ q) ⬝ᵥ (D *ᵥ q) := by
    calc
      q ⬝ᵥ (K *ᵥ (D *ᵥ q)) = (q ᵥ* K) ⬝ᵥ (D *ᵥ q) :=
        dotProduct_mulVec q K (D *ᵥ q)
      _ = (K.transpose *ᵥ q) ⬝ᵥ (D *ᵥ q) := by
        rw [Matrix.mulVec_transpose]
      _ = (K *ᵥ q) ⬝ᵥ (D *ᵥ q) := by rw [hK.eq]
  rw [lagCommutatorObservable, Matrix.sub_mulVec, dotProduct_sub,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDK, hKD,
    dotProduct_comm, sub_self]

/-- Literal CCM specialization: the proposed scalar commutator expectation is
tautologically zero for every row, so it cannot be a new source observable. -/
theorem ccmLagCommutatorObservable_zero
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N)
    (q : CCMModeFinite N → ℝ) :
    lagCommutatorObservable
      (ccmModeDiagFinite N) (ccmWeilMatFinite mProject N) q = 0 := by
  apply lagCommutatorObservable_zero_of_isSymm
  · exact Matrix.isSymm_diagonal _
  · exact ccmWeilMatFinite_transpose_eq mProject N hm hN

/-- Three-valued classification required by the Goal-058 preflight. -/
inductive Goal058CommutatorClassification where
  | nonTautologicalSourceObservable
  | lagSourceTautologicalZero
  | commutatorEqualsUncontrolledEigenResidual
  deriving DecidableEq

/-- Typed stop returned by this preflight: the current source contract does
not provide `sourceCCMHasRealEvenPhase`. -/
inductive Goal058SourceTrialPreflightStop where
  | sourceComplexRealGroundCrosswalkMismatch
  deriving DecidableEq

def goal058SourceTrialPreflightStop : Goal058SourceTrialPreflightStop :=
  .sourceComplexRealGroundCrosswalkMismatch

theorem goal058SourceTrialPreflightStop_eq :
    goal058SourceTrialPreflightStop =
      Goal058SourceTrialPreflightStop.sourceComplexRealGroundCrosswalkMismatch :=
  rfl

abbrev Goal058PlantCarrier := CCMModeFinite 1

def goal058PlantD : Matrix Goal058PlantCarrier Goal058PlantCarrier ℝ :=
  !![-1, 0, 0;
      0, 0, 0;
      0, 0, 1]

/-- Exact symmetric, centrosymmetric, source-commutator-shaped plant matrix. -/
def goal058PlantK : Matrix Goal058PlantCarrier Goal058PlantCarrier ℝ :=
  !![0, 1, 1;
     1, 2, 1;
     1, 1, 0]

def goal058PlantEta : Goal058PlantCarrier → ℝ := ![1, 1, 1]
def goal058PlantBeta : Goal058PlantCarrier → ℝ := ![-1, 0, 1]
def goal058PlantQ : Goal058PlantCarrier → ℝ := ![1, 1, 1]

theorem goal058Plant_commutator :
    goal058PlantD * goal058PlantK - goal058PlantK * goal058PlantD =
      Matrix.vecMulVec goal058PlantBeta goal058PlantEta -
        Matrix.vecMulVec goal058PlantEta goal058PlantBeta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [goal058PlantD, goal058PlantK, goal058PlantBeta,
      goal058PlantEta, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Fin.sum_univ_succ]

theorem goal058PlantQ_reflection_even :
    ∀ i, goal058PlantQ (ccmNegFinite 1 i) = goal058PlantQ i := by
  intro i
  fin_cases i <;> norm_num [goal058PlantQ, ccmNegFinite]

theorem goal058PlantQ_not_eigenvector :
    ¬ ∃ mu : ℝ, goal058PlantK *ᵥ goal058PlantQ = mu • goal058PlantQ := by
  rintro ⟨mu, hmu⟩
  have h0 := congrFun hmu (0 : Goal058PlantCarrier)
  have h1 := congrFun hmu (1 : Goal058PlantCarrier)
  norm_num [goal058PlantK, goal058PlantQ, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at h0 h1
  linarith

theorem goal058Plant_lagCommutatorObservable_zero :
    lagCommutatorObservable goal058PlantD goal058PlantK goal058PlantQ = 0 := by
  norm_num [lagCommutatorObservable, goal058PlantD, goal058PlantK,
    goal058PlantQ, Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_succ]

def goal058PlantClassification : Goal058CommutatorClassification :=
  .lagSourceTautologicalZero

theorem goal058PlantClassification_eq :
    goal058PlantClassification =
      Goal058CommutatorClassification.lagSourceTautologicalZero :=
  rfl

#print axioms dotProduct_self_eq_one_of_phaseRealifies
#print axioms phaseOne_realPart_requires_exact_reality
#print axioms sourceCCMRealRow_unit_of_phaseRealification
#print axioms sourceCCMComplexRow_even_of_phaseRealification_even
#print axioms proposition59CCMComplexTransform_eq_mode_sum
#print axioms proposition59CCMTransform_eq_phase_mul_complexTransform
#print axioms sourceCCMProposition59Transform_eq_phase_mul_complexTransform
#print axioms trialLineProjection_sq
#print axioms full_trialLine_four_block_identity
#print axioms ccmWeilMatFinite_full_trialLine_four_block_identity
#print axioms lagCommutatorObservable_zero_of_isSymm
#print axioms ccmLagCommutatorObservable_zero
#print axioms goal058Plant_commutator
#print axioms goal058PlantQ_reflection_even
#print axioms goal058PlantQ_not_eigenvector
#print axioms goal058Plant_lagCommutatorObservable_zero
#print axioms goal058PlantClassification_eq
#print axioms goal058SourceTrialPreflightStop_eq

end Q3.RouteB
```

### q3.lean.aristotle/Q3/Proofs/RouteB/TempleResidualGapEnvelopeTransfer.lean
```text
import Q3.Proofs.RouteB.WeightedSpectralTempleCore

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- A Temple residual-square envelope carrying two copies of the common
exponential envelope, divided by a true-gap lower envelope carrying one copy,
yields the single-envelope SafeAlphaUpper rate. -/
theorem safe_alpha_envelope_of_temple_residual_gap_bounds
    {scale envelope alpha etaSq gap C_eta c_Delta r_eta r_Delta : ℝ}
    (hscale : 0 < scale)
    (henvelope : 0 < envelope)
    (hCeta : 0 ≤ C_eta)
    (hcDelta : 0 < c_Delta)
    (halpha : 0 ≤ alpha)
    (hhalf : 2 * alpha ≤ gap)
    (htemple : alpha * (gap - alpha) ≤ etaSq)
    (heta : etaSq ≤ C_eta * scale ^ r_eta * envelope ^ 2)
    (hgap : c_Delta * scale ^ r_Delta * envelope ≤ gap) :
    alpha ≤
      (2 * C_eta / c_Delta) *
        scale ^ (r_eta - r_Delta) * envelope := by
  have hden : 0 < c_Delta * scale ^ r_Delta * envelope := by
    positivity
  have hgap_pos : 0 < gap := hden.trans_le hgap
  have htemple_bound : alpha ≤ 2 * etaSq / gap :=
    rayleigh_excess_le_two_mul_residual_sq_div_gap
      halpha hgap_pos hhalf htemple
  have hnum_nonneg :
      0 ≤ C_eta * scale ^ r_eta * envelope ^ 2 := by
    positivity
  have hratio :
      etaSq / gap ≤
        (C_eta * scale ^ r_eta * envelope ^ 2) /
          (c_Delta * scale ^ r_Delta * envelope) :=
    div_le_div₀ hnum_nonneg heta hden hgap
  calc
    alpha ≤ 2 * etaSq / gap := htemple_bound
    _ = 2 * (etaSq / gap) := by ring
    _ ≤ 2 *
        ((C_eta * scale ^ r_eta * envelope ^ 2) /
          (c_Delta * scale ^ r_Delta * envelope)) := by
      gcongr
    _ = (2 * C_eta / c_Delta) *
        scale ^ (r_eta - r_Delta) * envelope := by
      rw [Real.rpow_sub hscale]
      field_simp

/-- Nonvacuous one-filter form of the Temple residual/gap envelope transfer. -/
theorem eventually_safe_alpha_envelope_of_temple_residual_gap_bounds
    {ι : Type*} {l : Filter ι} [NeBot l]
    (scale envelope alpha etaSq gap : ι → ℝ)
    (C_eta c_Delta r_eta r_Delta : ℝ)
    (hCeta : 0 ≤ C_eta)
    (hcDelta : 0 < c_Delta)
    (hscale : ∀ᶠ i in l, 0 < scale i)
    (henvelope : ∀ᶠ i in l, 0 < envelope i)
    (halpha : ∀ᶠ i in l, 0 ≤ alpha i)
    (hhalf : ∀ᶠ i in l, 2 * alpha i ≤ gap i)
    (htemple : ∀ᶠ i in l,
      alpha i * (gap i - alpha i) ≤ etaSq i)
    (heta : ∀ᶠ i in l,
      etaSq i ≤ C_eta * scale i ^ r_eta * envelope i ^ 2)
    (hgap : ∀ᶠ i in l,
      c_Delta * scale i ^ r_Delta * envelope i ≤ gap i) :
    ∀ᶠ i in l,
      alpha i ≤
        (2 * C_eta / c_Delta) *
          scale i ^ (r_eta - r_Delta) * envelope i := by
  filter_upwards
    [hscale, henvelope, halpha, hhalf, htemple, heta, hgap] with
    i hsi hei hai hhi hti heti hgi
  exact safe_alpha_envelope_of_temple_residual_gap_bounds
    hsi hei hCeta hcDelta hai hhi hti heti hgi

/-- A single-envelope residual-square estimate cannot replace the required
squared-envelope estimate.  All Temple/half-gap and lower-gap premises below
hold, but `alpha ≤ envelope` fails. -/
theorem one_envelope_residual_gap_bounds_do_not_force_safe_alpha :
    let envelope : ℝ := 1 / 16
    let gap : ℝ := 1 / 4
    let alpha : ℝ := 1 / 8
    let etaSq : ℝ := 1 / 64
    0 < envelope ∧
      0 ≤ alpha ∧
      2 * alpha ≤ gap ∧
      alpha * (gap - alpha) ≤ etaSq ∧
      etaSq ≤ envelope ∧
      envelope ≤ gap ∧
      ¬ alpha ≤ envelope := by
  norm_num

#print axioms safe_alpha_envelope_of_temple_residual_gap_bounds
#print axioms eventually_safe_alpha_envelope_of_temple_residual_gap_bounds
#print axioms one_envelope_residual_gap_bounds_do_not_force_safe_alpha

end Q3.RouteB
```

### q3.lean.aristotle/Q3/Proofs/RouteB/H2aPenaltyCoercivity.lean
```text
import Mathlib

/-!
Aristotle project `16535289-f016-4f62-bfbd-be83d826b4da`, imported
2026-07-22 from `RequestProject/H2aPenalty.lean`.

The source file is preserved verbatim under `aristotle_output/`; this local
copy raises only the heartbeat budget needed by Lean 4.26.  It is a generic
receiver conditional on a penalty certificate, not an exact Route-B family
instantiation and not an RH theorem.
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder

/-!
# H2a — Simple even ground state from penalty coercivity

This file proves a **basis-invariant finite-dimensional** theorem underlying slot `H2a`
of the RH route.  It concerns the generalized (Hermitian pencil) eigenproblem
`K x = λ (G x)` with `G` positive definite.

Given a self-adjoint `K`, a positive-definite `G`, an involution `J` commuting with the
pencil, a `J`-even, `G`-normalized vector `q` with Rayleigh value `a := q* K q`, and a
**penalty/coercivity certificate**
`K - β G + τ (Gq)(Gq)* ⪰ 0`  with `a < β`,
we prove:

* the pencil has a **lowest generalized eigenvalue** `λ₁ ≤ a`, and `λ₁` is the minimum
  of the whole spectrum;
* the lowest eigenvalue is **simple** (its generalized eigenspace is one-dimensional);
* there is a **spectral gap** `λ₂ - λ₁ ≥ β - a > 0` (every other eigenvalue is `≥ β`),
  hence `λ₁` is isolated;
* **every** lowest eigenvector is `J`-even.

The proof route is: whiten by `G^{1/2}` for existence of the lowest eigenpair (isolated
in `exists_lowest`), then derive `β`-coercivity on the `G`-orthogonal complement of `q`
from the certificate, and finish with elementary pencil linear algebra plus the
`J`-invariance/`G`-orthogonality of odd vectors.
-/

namespace H2aPenalty

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A **generalized eigenpair** of the Hermitian pencil `(K, G)`: a nonzero `x` with
`K x = μ (G x)` and real eigenvalue `μ`. -/
def GEig (K G : Matrix n n ℂ) (μ : ℝ) (x : n → ℂ) : Prop :=
  x ≠ 0 ∧ K *ᵥ x = (μ : ℂ) • (G *ᵥ x)

/-! ## Elementary quadratic-form facts. -/

/-
The quadratic form of a Hermitian matrix is real.
-/
theorem qf_isHermitian_im (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  have h_real : star x ⬝ᵥ A *ᵥ x = star (star x ⬝ᵥ A *ᵥ x) := by
    simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum ];
    rw [ Finset.sum_comm ] ; congr ; ext i ; congr ; ext j ; rw [ ← hA.apply ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  exact Complex.conj_eq_iff_im.mp h_real.symm

/-
Reading off the Rayleigh quotient from an eigenpair: `x* K x = μ (x* G x)`.
-/
theorem geig_quad {K G : Matrix n n ℂ} {μ : ℝ} {x : n → ℂ}
    (h : GEig K G μ x) :
    star x ⬝ᵥ (K *ᵥ x) = (μ : ℂ) * (star x ⬝ᵥ (G *ᵥ x)) := by
  convert congr_arg ( fun y => star x ⬝ᵥ y ) h.2 using 1 ; simp +decide [ Matrix.mulVec_smul ]

/-
Eigenvectors of the pencil for distinct eigenvalues are `G`-orthogonal.
-/
theorem geig_Gorth_of_ne {K G : Matrix n n ℂ} (hK : K.IsHermitian) (hG : G.IsHermitian)
    {μ ν : ℝ} {x y : n → ℂ}
    (hx : GEig K G μ x) (hy : GEig K G ν y) (hμν : μ ≠ ν) :
    star x ⬝ᵥ (G *ᵥ y) = 0 := by
  -- Use the fact that $K$ is Hermitian to rewrite the inner product.
  have h_inner : star x ⬝ᵥ (K *ᵥ y) = star (K *ᵥ x) ⬝ᵥ y := by
    simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm ];
    rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; rw [ ← hK.apply ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  have h_inner : star x ⬝ᵥ (K *ᵥ y) = (ν : ℂ) * (star x ⬝ᵥ (G *ᵥ y)) := by
    simp +decide [ hy.2, Matrix.mulVec_smul ]
  have h_inner' : star (K *ᵥ x) ⬝ᵥ y = (μ : ℂ) * (star (G *ᵥ x) ⬝ᵥ y) := by
    convert congr_arg ( fun z => star z ⬝ᵥ y ) hx.2 using 1 ; simp +decide [ Matrix.mulVec_smul ]
  have h_inner_eq : (ν : ℂ) * (star x ⬝ᵥ (G *ᵥ y)) = (μ : ℂ) * (star x ⬝ᵥ (G *ᵥ y)) := by
    have h_inner_eq : star (G *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (G *ᵥ y) := by
      simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, hG.eq ];
      rw [ Finset.sum_comm ] ; congr ; ext i ; congr ; ext j ; rw [ ← hG.apply ] ; ring;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
    grobner
  have h_inner_zero : (star x ⬝ᵥ (G *ᵥ y)) = 0 := by
    exact Classical.not_not.1 fun h => hμν <| by simpa [ h ] using h_inner_eq.symm;
  exact h_inner_zero

/-
**β-coercivity on `q^{⊥_G}`.**  From the penalty certificate, any vector `x`
that is `G`-orthogonal to `q` satisfies `β (x* G x) ≤ x* K x`.
-/
theorem coercivity {G K : Matrix n n ℂ} {q : n → ℂ} {β τ : ℝ} (hG : G.IsHermitian)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    {x : n → ℂ} (hx : star q ⬝ᵥ (G *ᵥ x) = 0) :
    (β : ℂ) * (star x ⬝ᵥ (G *ᵥ x)) ≤ star x ⬝ᵥ (K *ᵥ x) := by
  have := hcert.2;
  have h_pos : star x ⬝ᵥ ((K - β • G + τ • (vecMulVec (G *ᵥ q) (star (G *ᵥ q)))) *ᵥ x) = star x ⬝ᵥ (K *ᵥ x) - β * star x ⬝ᵥ (G *ᵥ x) := by
    have h_pos : star x ⬝ᵥ (vecMulVec (G *ᵥ q) (star (G *ᵥ q)) *ᵥ x) = (star (G *ᵥ q) ⬝ᵥ x) * (star x ⬝ᵥ (G *ᵥ q)) := by
      simp +decide [ Matrix.vecMulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      simp +decide [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    have h_pos : star (G *ᵥ q) ⬝ᵥ x = star q ⬝ᵥ G *ᵥ x := by
      simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
      rw [ Finset.sum_comm ];
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [ ← Matrix.IsHermitian.apply hG ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    simp_all +decide [ Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_eq_diagonal_mul ];
    simp_all +decide [ Matrix.mulVec, dotProduct ];
    simp_all +decide [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  convert sub_nonneg.mp ( show 0 ≤ star x ⬝ᵥ ( K *ᵥ x ) - ↑β * ( star x ⬝ᵥ G *ᵥ x ) from ?_ ) using 1;
  convert this ( Finsupp.equivFunOnFinite.symm x ) using 1;
  convert h_pos.symm using 1;
  simp +decide [ Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ]

/-
Two directions can always be combined into a nonzero coefficient pair that lands
in `q^{⊥_G}` (one homogeneous linear equation in two unknowns).
-/
theorem exists_combo_Gorth (G : Matrix n n ℂ) (q x y : n → ℂ) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧
      s * (star q ⬝ᵥ (G *ᵥ x)) + t * (star q ⬝ᵥ (G *ᵥ y)) = 0 := by
  by_cases hb : star q ⬝ᵥ G *ᵥ y = 0;
  · exact ⟨ 0, 1, by simp +decide, by simp +decide [ hb ] ⟩;
  · refine' ⟨ -star q ⬝ᵥ G *ᵥ y, star q ⬝ᵥ G *ᵥ x, _, _ ⟩ <;> simp_all +decide [ mul_comm ]

/-! ## `J`-symmetry facts. -/

/-
The involution `J` maps generalized eigenvectors to generalized eigenvectors with the
same eigenvalue.
-/
theorem J_geig {K G J : Matrix n n ℂ} {μ : ℝ} {x : n → ℂ}
    (hJ : J * J = 1) (hJG : Jᴴ * G * J = G) (hJK : Jᴴ * K * J = K)
    (h : GEig K G μ x) :
    GEig K G μ (J *ᵥ x) := by
  refine' ⟨ _, _ ⟩;
  · intro h';
    apply_fun fun y => J *ᵥ y at h' ; simp_all +decide [ Matrix.mulVec_mulVec ];
    exact h.1 rfl;
  · have hOp : K * J = Jᴴ * K ∧ G * J = Jᴴ * G := by
      apply_fun ( fun m => m * J ) at hJK hJG; simp_all +decide [ mul_assoc ] ;
    simp_all +decide [ ← Matrix.mul_assoc, GEig ];
    simp_all +decide [ ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul ]

/-
A `J`-odd vector is `G`-orthogonal to the `J`-even vector `q`.
-/
theorem odd_Gorth {G J : Matrix n n ℂ} {q x : n → ℂ}
    (hJG : Jᴴ * G * J = G) (hJq : J *ᵥ q = q) (hodd : J *ᵥ x = -x) :
    star q ⬝ᵥ (G *ᵥ x) = 0 := by
  -- From `hJG : Jᴴ * G * J = G`, rewrite `G *ᵥ x = (Jᴴ * G * J) *ᵥ x`. Using `Matrix.mulVec_mulVec` (`(A*B) *ᵥ v = A *ᵥ (B *ᵥ v)`), this is `Jᴴ *ᵥ (G *ᵥ (J *ᵥ x))`. By `hodd : J *ᵥ x = -x`, `G *ᵥ (J *ᵥ x) = G *ᵥ (-x) = -(G *ᵥ x)`. So `G *ᵥ x = - (Jᴴ *ᵥ (G *ᵥ x))`.
  have hGx : G *ᵥ x = - (star J *ᵥ (G *ᵥ x)) := by
    convert congr_arg ( fun m => m *ᵥ x ) hJG.symm using 1;
    simp +decide [ ← Matrix.mulVec_mulVec, hodd ];
    simp +decide [ Matrix.mulVec, funext_iff ];
    exact fun x_2 => Complex.ext rfl rfl;
  -- By `hodd : J *ᵥ x = -x`, we have `star q ⬝ᵥ (Jᴴ *ᵥ (G *ᵥ x)) = star (J *ᵥ q) ⬝ᵥ (G *ᵥ x)`.
  have hstarJq : star q ⬝ᵥ (star J *ᵥ (G *ᵥ x)) = star (J *ᵥ q) ⬝ᵥ (G *ᵥ x) := by
    simp +decide [ Matrix.mulVec, dotProduct ];
    simp +decide only [mul_comm, Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  replace hGx := congr_arg ( fun z => star q ⬝ᵥ z ) hGx; norm_num at *;
  grind

/-! ## Existence of the lowest eigenpair (whitening + spectral theorem). -/

/-
**Variational lowest eigenvalue of a Hermitian matrix.**  A Hermitian matrix `M`
on a nonempty index has a lowest eigenvalue `lam` with eigenvector `v ≠ 0`, and
`lam` is a Rayleigh lower bound: `lam (w* w) ≤ w* M w` for all `w`.
-/
theorem hermitian_min_eig [Nonempty n] {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ (lam : ℝ) (v : n → ℂ), v ≠ 0 ∧ M *ᵥ v = (lam : ℂ) • v ∧
      ∀ w : n → ℂ, lam * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (M *ᵥ w)).re := by
  -- Let $\mu$ be the smallest eigenvalue of $M$.
  obtain ⟨μ, hμ⟩ : ∃ μ ∈ Set.range (fun j => hM.eigenvalues j), ∀ ν ∈ Set.range (fun j => hM.eigenvalues j), μ ≤ ν := by
    exact ⟨ Finset.min' ( Set.toFinset ( Set.range fun j => hM.eigenvalues j ) ) ⟨ _, Set.mem_toFinset.mpr ( Set.mem_range_self ( Classical.arbitrary n ) ) ⟩, Set.mem_toFinset.mp ( Finset.min'_mem _ _ ), fun ν hν => Finset.min'_le _ _ ( Set.mem_toFinset.mpr hν ) ⟩;
  obtain ⟨ j, rfl ⟩ := hμ.1;
  refine' ⟨ hM.eigenvalues j, hM.eigenvectorBasis j, _, hM.mulVec_eigenvectorBasis j, _ ⟩;
  · exact ne_of_apply_ne ( fun x => ‖x‖ ) ( by simp +decide [ hM.eigenvectorBasis.orthonormal.ne_zero ] );
  · intro w
    set y := (hM.eigenvectorUnitary : Matrix n n ℂ).conjTranspose.mulVec w
    have h_y_norm : (star w ⬝ᵥ w).re = ∑ i, ‖y i‖^2 := by
      have h_y_norm : (star w ⬝ᵥ w) = (star y ⬝ᵥ y) := by
        simp +zetaDelta at *;
        simp +decide [ Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.star_mulVec ];
        simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
      simp_all +decide [ Complex.normSq, Complex.sq_norm, dotProduct ]
    have h_y_Mw : (star w ⬝ᵥ (M *ᵥ w)).re = ∑ i, hM.eigenvalues i * ‖y i‖^2 := by
      have h_y_Mw : (star w ⬝ᵥ (M *ᵥ w)) = ∑ i, hM.eigenvalues i * (star (y i) * y i) := by
        have h_y_Mw : (star w ⬝ᵥ (M *ᵥ w)) = (star y ⬝ᵥ (Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) *ᵥ y)) := by
          have h_y_Mw : M = (hM.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) * (hM.eigenvectorUnitary : Matrix n n ℂ).conjTranspose := by
            convert hM.spectral_theorem using 1;
          simp +zetaDelta at *;
          conv_lhs => rw [ h_y_Mw ];
          simp +decide [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.star_mulVec ];
        simp_all +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
        simp +decide [ Matrix.diagonal, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      simp_all +decide [ Complex.normSq, Complex.sq_norm ];
    rw [ h_y_norm, h_y_Mw, Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( hμ.2 _ ( Set.mem_range_self i ) ) ( sq_nonneg _ )

/-
**Lowest generalized eigenpair.**  For the pencil `(K, G)` with `G` positive definite,
there is a lowest eigenvalue `lam` with eigenvector `x ≠ 0`, and `lam` is a generalized
Rayleigh lower bound: `lam (z* G z) ≤ z* K z` for all `z`.  (Proved by whitening
`M := G^{-1/2} K G^{-1/2}` and applying `hermitian_min_eig`.)
-/
theorem exists_lowest [Nonempty n] {G K : Matrix n n ℂ}
    (hG : G.PosDef) (hK : K.IsHermitian) :
    ∃ (lam : ℝ) (x : n → ℂ), x ≠ 0 ∧ K *ᵥ x = (lam : ℂ) • (G *ᵥ x) ∧
      ∀ z : n → ℂ, lam * (star z ⬝ᵥ (G *ᵥ z)).re ≤ (star z ⬝ᵥ (K *ᵥ z)).re := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℂ, S.IsHermitian ∧ S * S = G ∧ S.PosDef := by
    convert hG.posDef_sqrt using 1;
    constructor <;> intro h;
    · convert hG.posDef_sqrt;
    · refine' ⟨ _, _, _, h ⟩;
      · convert h.1 using 1;
      · convert hG.posSemidef.sqrt_mul_self;
  obtain ⟨lam, v, hv_ne_zero, hv_eigen, hv_var⟩ : ∃ lam : ℝ, ∃ v : n → ℂ, v ≠ 0 ∧ (S⁻¹ * K * S⁻¹) *ᵥ v = lam • v ∧ ∀ w : n → ℂ, lam * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ ((S⁻¹ * K * S⁻¹) *ᵥ w)).re := by
    apply hermitian_min_eig;
    simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
    rw [ Matrix.conjTranspose_nonsing_inv, hS.1 ];
  refine' ⟨ lam, S⁻¹ *ᵥ v, _, _, _ ⟩;
  · intro h; have := hS.2.2.det_pos; simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit, isUnit_iff_ne_zero ] ;
    apply_fun S.mulVec at h; simp_all +decide [ isUnit_iff_ne_zero, ne_of_gt ] ;
  · convert congr_arg ( fun x => S *ᵥ x ) hv_eigen using 1;
    · simp +decide [ Matrix.mul_assoc, hS.2.2.det_pos.ne' ];
    · simp +decide [ ← hS.2.1, Matrix.mulVec_smul ];
      rw [ Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ];
      · simp +decide [ Matrix.mulVec, funext_iff ];
      · exact isUnit_iff_ne_zero.mpr hS.2.2.det_pos.ne';
  · intro z
    specialize hv_var (S *ᵥ z);
    convert hv_var using 1;
    · simp +decide [ ← hS.2.1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hS.1.eq ];
      simp +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hS.1.eq ];
    · simp +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hS.1.eq, hS.2.1, hS.2.2.det_pos.ne' ]

/-! ## The three conclusion clauses. -/

/-
**Simplicity.**  If `lam < β`, the generalized eigenspace for `lam` is
one-dimensional: any two `lam`-eigenvectors are proportional.
-/
theorem simplicity_clause {G K : Matrix n n ℂ} {q : n → ℂ} {β τ lam : ℝ}
    (hG : G.PosDef)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    (hlamβ : lam < β) :
    ∀ x y, GEig K G lam x → GEig K G lam y → ∃ c : ℂ, y = c • x := by
  intro x y hx hy
  obtain ⟨s, t, hst, hcombo⟩ := exists_combo_Gorth G q x y
  set z := s • x + t • y with hz_def
  have hz_eigen : K *ᵥ z = (lam:ℂ) • (G *ᵥ z) := by
    simp_all +decide [ mul_add, add_mul, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.mulVec_add, Matrix.mulVec_smul ];
    rw [ hx.2, hy.2 ] ; ext ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  have hz_orthogonal : star q ⬝ᵥ (G *ᵥ z) = 0 := by
    simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ]
  have hz_zero : z = 0 := by
    have hz_zero : (β : ℂ) * (star z ⬝ᵥ (G *ᵥ z)) ≤ star z ⬝ᵥ (K *ᵥ z) := by
      apply coercivity hG.1 hcert hz_orthogonal;
    by_cases hz_nonzero : z ≠ 0;
    · have hz_pos : 0 < (star z ⬝ᵥ (G *ᵥ z)).re := by
        apply hG.dotProduct_mulVec_pos hz_nonzero |>.1;
      simp_all +decide [ Complex.le_def ];
      nlinarith;
    · exact Classical.not_not.mp hz_nonzero
  have ht_nonzero : t ≠ 0 := by
    contrapose! hst; simp_all +decide [ funext_iff ] ;
    exact Classical.not_not.1 fun hs => hx.1 <| funext fun i => Or.resolve_left ( hz_def i ) hs
  use (-(s * (t⁻¹)));
  simp_all +decide [ ← eq_sub_iff_add_eq', funext_iff, smul_smul ];
  grind

/-
**Spectral gap.**  Given a `lam`-eigenvector `x₁` with `lam < β`, every eigenvalue
`μ ≠ lam` satisfies `β ≤ μ`.
-/
set_option maxHeartbeats 1600000 in
theorem gap_clause {G K : Matrix n n ℂ} {q : n → ℂ} {β τ lam : ℝ}
    (hG : G.PosDef) (hK : K.IsHermitian)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    (hlamβ : lam < β) {x₁ : n → ℂ} (hx₁ : GEig K G lam x₁) :
    ∀ μ y, GEig K G μ y → μ ≠ lam → β ≤ μ := by
  intro μ y hy hμ_ne_lam
  obtain ⟨s, t, hst, hcombo⟩ := exists_combo_Gorth G q x₁ y
  obtain ⟨hx₁_ne_zero, hx₁_eq⟩ := hx₁
  obtain ⟨hy_ne_zero, hy_eq⟩ := hy
  have hxy : star x₁ ⬝ᵥ (G *ᵥ y) = 0 := by
    apply geig_Gorth_of_ne hK hG.1 ⟨hx₁_ne_zero, hx₁_eq⟩ ⟨hy_ne_zero, hy_eq⟩ (Ne.symm hμ_ne_lam)
  have hyx : star y ⬝ᵥ (G *ᵥ x₁) = 0 := by
    convert geig_Gorth_of_ne hK hG.1 ⟨ hy_ne_zero, hy_eq ⟩ ⟨ hx₁_ne_zero, hx₁_eq ⟩ hμ_ne_lam using 1
  have hx1_gt_zero : 0 < (star x₁ ⬝ᵥ (G *ᵥ x₁)).re := by
    convert hG.dotProduct_mulVec_pos hx₁_ne_zero using 1;
    simp +decide [ Complex.lt_def ];
    exact fun _ => qf_isHermitian_im _ hG.1 _ ▸ rfl
  have hy_gt_zero : 0 < (star y ⬝ᵥ (G *ᵥ y)).re := by
    convert hG.dotProduct_mulVec_pos hy_ne_zero using 1;
    rw [ Complex.lt_def ] ; norm_num;
    have := hG.1;
    exact fun _ => Eq.symm ( qf_isHermitian_im G this y )
  by_cases hβ_gt_μ : β > μ;
  · -- Let $z := s • x₁ + t • y$. Then $z ≠ 0$ and $star q ⬝ᵥ (G *ᵥ z) = 0$.
    set z : n → ℂ := s • x₁ + t • y
    have hz_ne_zero : z ≠ 0 := by
      have hz_ne_zero : star x₁ ⬝ᵥ (G *ᵥ z) = s * (star x₁ ⬝ᵥ (G *ᵥ x₁)) + t * (star x₁ ⬝ᵥ (G *ᵥ y)) := by
        simp +decide [ z, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ];
      aesop
    have hqz : star q ⬝ᵥ (G *ᵥ z) = 0 := by
      convert hcombo using 1;
      simp +decide [ z, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ];
    -- Now apply `coercivity hG.isHermitian hcert hqz : (β:ℂ) * (star z ⬝ᵥ G*ᵥz) ≤ star z ⬝ᵥ K*ᵥz` and take real parts with `Complex.le_def`.
    have hcoercivity : (β : ℂ) * (star z ⬝ᵥ (G *ᵥ z)) ≤ star z ⬝ᵥ (K *ᵥ z) := by
      convert coercivity hG.1 hcert hqz using 1;
    -- Expand `star z ⬝ᵥ (G *ᵥ z)` and `star z ⬝ᵥ (K *ᵥ z)` using bilinearity and the two orthogonalities `hxy, hyx`.
    have hGzz : star z ⬝ᵥ (G *ᵥ z) = (starRingEnd ℂ s * s) * (star x₁ ⬝ᵥ (G *ᵥ x₁)) + (starRingEnd ℂ t * t) * (star y ⬝ᵥ (G *ᵥ y)) := by
      simp +zetaDelta at *;
      simp +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, mul_assoc, hxy, hyx ]
    have hKzz : star z ⬝ᵥ (K *ᵥ z) = (starRingEnd ℂ s * s) * ((lam : ℂ) * (star x₁ ⬝ᵥ (G *ᵥ x₁))) + (starRingEnd ℂ t * t) * ((μ : ℂ) * (star y ⬝ᵥ (G *ᵥ y))) := by
      simp +zetaDelta at *;
      simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct ];
      ring;
    simp_all +decide [ Complex.le_def ];
    -- Since $s \neq 0$ or $t \neq 0$, we have $(s.re * s.re + s.im * s.im) > 0$ or $(t.re * t.re + t.im * t.im) > 0$.
    have h_pos : (s.re * s.re + s.im * s.im) > 0 ∨ (t.re * t.re + t.im * t.im) > 0 := by
      contrapose! hst; simp_all +decide [ Complex.ext_iff ] ;
      exact ⟨ ⟨ by nlinarith only [ hst.1 ], by nlinarith only [ hst.1 ] ⟩, ⟨ by nlinarith only [ hst.2 ], by nlinarith only [ hst.2 ] ⟩ ⟩;
    cases' h_pos with h_pos h_pos <;> nlinarith [ mul_pos h_pos hx1_gt_zero, mul_pos h_pos hy_gt_zero, mul_lt_mul_of_pos_left hlamβ hx1_gt_zero, mul_lt_mul_of_pos_left hβ_gt_μ hy_gt_zero ];
  · linarith

/-
**Evenness.**  If the `lam`-eigenspace is simple and `lam < β`, every
`lam`-eigenvector is `J`-even.
-/
theorem even_clause {G K J : Matrix n n ℂ} {q : n → ℂ} {β τ lam : ℝ}
    (hG : G.PosDef)
    (hJ : J * J = 1) (hJG : Jᴴ * G * J = G) (hJK : Jᴴ * K * J = K) (hJq : J *ᵥ q = q)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    (hlamβ : lam < β)
    (hsimple : ∀ x y, GEig K G lam x → GEig K G lam y → ∃ c : ℂ, y = c • x) :
    ∀ x, GEig K G lam x → J *ᵥ x = x := by
  intro x hx
  have hJx : GEig K G lam (J *ᵥ x) := by
    convert J_geig hJ hJG hJK hx using 1
  obtain ⟨c, hc⟩ := hsimple x (J *ᵥ x) hx hJx
  have hc_sq : c^2 = 1 := by
    have hc_sq : J *ᵥ (J *ᵥ x) = x := by
      simp +decide [ ← Matrix.mul_assoc, hJ ];
    simp_all +decide [ sq, Matrix.mulVec_smul ];
    obtain ⟨ i, hi ⟩ := Function.ne_iff.mp hx.1; replace hc_sq := congr_fun hc_sq i; simp_all +decide [ mul_assoc, smul_smul ] ;
    exact mul_left_cancel₀ hi <| by linear_combination' hc_sq;
  have hc_cases : c = 1 ∨ c = -1 := by
    exact sq_eq_one_iff.mp hc_sq
  cases' hc_cases with hc1 hc_neg1;
  · aesop;
  · have h_odd_Gorth : star q ⬝ᵥ (G *ᵥ x) = 0 := by
      apply odd_Gorth hJG hJq; simp [hc_neg1, hc];
    have h_coercivity : β * (star x ⬝ᵥ (G *ᵥ x)).re ≤ (star x ⬝ᵥ (K *ᵥ x)).re := by
      have := coercivity hG.1 hcert h_odd_Gorth;
      convert Complex.le_def.mp this |>.1 using 1;
      simp +decide [ dotProduct, Complex.ext_iff ];
    have h_rayleigh : star x ⬝ᵥ (K *ᵥ x) = lam * (star x ⬝ᵥ (G *ᵥ x)) := by
      convert geig_quad hx using 1;
    have h_pos : 0 < (star x ⬝ᵥ (G *ᵥ x)).re := by
      convert hG.dotProduct_mulVec_pos hx.1 using 1;
      have := qf_isHermitian_im G hG.1 x; simp_all +decide [ Complex.ext_iff ] ;
      rw [ ← Complex.re_add_im ( star x ⬝ᵥ G *ᵥ x ) ] ; aesop;
    norm_num [ h_rayleigh ] at h_coercivity; nlinarith;

/-! ## Main theorem. -/

/-
**H2a: simple, isolated, `J`-even ground state from penalty coercivity.**

Given `G = G* > 0`, `K = K*`, an involution `J` with `J* G J = G`, `J* K J = K`, a
`J`-even `G`-unit vector `q` (`J q = q`, `q* G q = 1`) with Rayleigh value `a = q* K q`,
`a < β`, and the penalty certificate `K - β G + τ (Gq)(Gq)* ⪰ 0`, the generalized
eigenproblem `K x = λ (G x)` has:

* a lowest eigenvalue `λ₁ ≤ a`, which is the minimum of the spectrum;
* a spectral gap: every eigenvalue `μ ≠ λ₁` satisfies `β - a ≤ μ - λ₁` (so `λ₂ - λ₁ ≥ β - a`
  and `λ₁` is isolated);
* simplicity: the `λ₁`-eigenspace is one-dimensional;
* evenness: every `λ₁`-eigenvector is `J`-even.
-/
theorem H2a_SimpleEvenGround_FromPenaltyCoercivity
    (G K J : Matrix n n ℂ) (q : n → ℂ) (a β τ : ℝ)
    (hG : G.PosDef) (hK : K.IsHermitian)
    (hJ : J * J = 1) (hJG : Jᴴ * G * J = G) (hJK : Jᴴ * K * J = K)
    (hJq : J *ᵥ q = q)
    (hq : star q ⬝ᵥ (G *ᵥ q) = 1)
    (ha : star q ⬝ᵥ (K *ᵥ q) = (a : ℂ))
    (hab : a < β)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef) :
    ∃ lam : ℝ,
      (∃ x, GEig K G lam x) ∧
      lam ≤ a ∧
      (∀ μ y, GEig K G μ y → lam ≤ μ) ∧
      (∀ μ y, GEig K G μ y → μ ≠ lam → β - a ≤ μ - lam) ∧
      (∀ x y, GEig K G lam x → GEig K G lam y → ∃ c : ℂ, y = c • x) ∧
      (∀ x, GEig K G lam x → J *ᵥ x = x) := by
  obtain ⟨lam, x, hx⟩ : ∃ lam : ℝ, ∃ x : n → ℂ, GEig K G lam x ∧ lam ≤ a := by
    have h_nonempty : Nonempty n := by
      contrapose! hq; aesop;
    have := exists_lowest hG hK;
    obtain ⟨ lam, x, hx₁, hx₂, hx₃ ⟩ := this; use lam, x; simp_all +decide [ GEig ] ;
    specialize hx₃ q; simp_all +decide [ Complex.ext_iff ] ;
  use lam;
  refine' ⟨ ⟨ x, hx.1 ⟩, hx.2, _, _, _, _ ⟩;
  · intro μ y hy;
    by_cases hμlam : μ = lam;
    · rw [ hμlam ];
    · apply gap_clause hG hK hcert (by linarith) hx.left μ y hy hμlam |> le_trans (by linarith);
  · intro μ y hy hne; have := gap_clause hG hK hcert ( by linarith ) hx.1 μ y hy hne; linarith;
  · apply simplicity_clause hG hcert (by linarith);
  · apply even_clause hG hJ hJG hJK hJq hcert (by linarith) (simplicity_clause hG hcert (by linarith))

/-!
## Next step: family instantiation

The abstract theorem `H2a_SimpleEvenGround_FromPenaltyCoercivity` above is the finite,
basis-invariant engine of slot `H2a`.  The next lemma to prove is the **family
instantiation** feeding it into the RH route (`RequestProject/Main.lean`):

theorem `SIEG_of_penalty` : given `RHRoute.Approx P` and index `j`, the concrete finite
data `(n, G, K, J, q, a, β, τ)` attached to the `j`-th approximant `F_j` satisfying the
eight hypotheses of `H2a_SimpleEvenGround_FromPenaltyCoercivity` (in particular the
penalty certificate `K - β G + τ (Gq)(Gq)* ⪰ 0` with `a < β`), together with a bridge
relating this `(K, G)`-pencil eigenproblem to the transform used by the abstract predicate
`RHRoute.SIEG`, yields `RHRoute.SIEG P j`.  Its proof applies
`H2a_SimpleEvenGround_FromPenaltyCoercivity` to obtain the simple, isolated, `J`-even
lowest generalized eigenvalue, then transports that conclusion across the bridge.  That
lemma, plus the actual construction of `(G_j, K_j, J_j, q_j)` and a verified certificate
for each `j`, is what discharges `RHRoute.supply_H2a`.
-/

end H2aPenalty
```
