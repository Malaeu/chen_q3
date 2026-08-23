# SOURCE RECORD — H2A.4.1B.3C.1.10 source log-window Fourier integral crosswalk (Linux-тело за Codex)

```yaml
PRIMARY: H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_ACTUAL_INTEGRAL_LEAN
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 4fa4a981 — CODEX DIRECTIVE (W1)
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 545cc3f93a465072ed17896c5fcded12af0da01a   # live git rev-parse HEAD, pasted verbatim; fetch clean, no new [Proshka] commits
COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh x4 (sourceLogWindowFourierL2Isometry actual Fourier /
  logWindowZeroExtension / L2 finite measure L1 / tendstoInMeasure Lp
  uniqueness) — no existing supplier; nearest disk objects are the
  isometry file itself and the completeness bridge"

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierIntegralCrosswalk.lean
LEAN_GIT_BLOB: 21692df075aca7467503c5d49671691c1a1a1db7
LEAN_SHA256: b1ab6e27ae880c99b2617e016c60d08fa43de06e734706cf27665c72f4e46ae8
LEAN_LINES: 827

PUBLIC_SURFACE:   # exactly the three verdict declarations
  - Q3.RouteB.D0Pstar.sourceLogWindowZeroExtension
    # indicator (Icc 0 (L_m i)) of the chosen representative of
    # (logWindowL2Equiv i).symm x — the ADDITIVE coordinate, per the C04 repair
  - Q3.RouteB.D0Pstar.sourceLogWindowZeroExtension_integrable
    # via MemLp.integrable on the finite additive window + integrable_indicator
  - Q3.RouteB.D0Pstar.coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension
    # a.e. identity; proof route exactly as mandated (see PROOF_ROUTE)

PRIVATE_DECLARATIONS:
  - one_mode_agreement_without_complete_basis_does_not_identify_maps_plant
    # REQUIRED Fin-2 plant: two linear maps agree on e0, differ on e1
  - local_logWindow_measurePreserving   # literal local copy of the private
    # upstream change-of-variables fact (pattern ratified in 3C.0)
  - additiveWindow_isFiniteMeasure / additiveWindow_measure_univ
  - restrictL2_integrable / restrictL2_l1_le   # exact constant sqrt(L_m) via
    # eLpNorm_le_eLpNorm_mul_rpow_measure_univ (verdict repair honored;
    # measure = ofReal(L_m), not an ambiguous |I_m|)
  - lp_coeFn_finsetSum   # finite-induction Lp coeFn sum (no pinned API)
  - fourier_kernel_smul_integrable / fourier_apply_eq / fourier_congr_ae /
    fourier_sub_norm_le / fourier_finsetSum   # self-contained via
    # Real.fourier_eq' + RCLike.inner_apply; L1→C0 bound by
    # norm_integral_le_integral_norm; NO Plancherel, NO new Fourier API
  - logWindowMode_integrable   # local copy of the standard indicator argument
  - additiveMode_memLp / additiveModeLp / logWindowL2Equiv_additiveModeLp /
    symm_V_n_m_eq_additiveModeLp / indicator_additiveModeLp_ae /
    sourceLogWindowZeroExtension_finsetSum_ae / crosswalk_on_finsetSum

PROOF_ROUTE_AS_MANDATED:
  - "1. additive zero extension from (logWindowL2Equiv i).symm x — literal"
  - "2. integrability from the finite interval measure ofReal(L_m)"
  - "3. approximation by finite sums in the complete V_n_m_hilbertBasis
     (dense_span → Metric.mem_closure_iff → Finsupp.mem_span_range_iff_exists_finsupp;
     approximants chosen with error < 1/(k+1))"
  - "4. finite sums: public mode theorem + Fourier linearity
     (fourier_finsetSum, integral_finset_sum)"
  - "5. L1 convergence with the exact constant sqrt(L_m i)
     (restrictL2_l1_le; indicator/integral_indicator transport)"
  - "6. uniform Fourier convergence: fourier_sub_norm_le (L1→C0)"
  - "7. isometry continuity → whole-line L2 convergence"
  - "8. identification via tendstoInMeasure_of_tendsto_Lp +
     TendstoInMeasure.exists_seq_tendsto_ae + tendsto_nhds_unique —
     an a.e.-subsequence, exactly the verdict-permitted route; uniform
     convergence on the whole line is NEVER relabeled as L2 convergence"
  - "9. Fin-2 plant proved"
  - "10. #print axioms for all three public declarations and the plant"

FORBIDDEN_CHECK:
  plancherel_or_unpinned_Lp_fourier_api: none (self-contained kernel lemmas)
  ferrers_abel_bv_dirichlet_jordan_root_energy_imports: none (generic bridge only)
  sourceLogWindowFourierL2Isometry_redefined: no (imported, untouched)
  pointwise_instead_of_ae: no (statement and proof are a.e.)
  fourier_of_multiplicative_representative: no (additive object only, C04)
  hilbert_density_as_form_core: not used
  integrable_g_as_new_public_hypothesis: none (integrability is PROVED)
  shifted_form_membership_or_gamma_rate_claimed: no
  sorry_admit_native_decide_axiom_weakening: none (grep = 0)

LEDGER:
  CLOSES:
    - SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK
  OPENS: []

GATE:
  ROUNDS: 4 (inner-product notation suffix unparseable in this scope — kernel
    rewritten via Real.fourier_eq' + RCLike.inner_apply; ℝ≥0∞ needed scoped
    ENNReal open; private upstream logWindow_measurePreserving — local copy;
    no Lp.coeFn_sum at the pin — finite-induction lemma written;
    HilbertBasis.dense_span is a topologicalClosure equation, not Dense —
    membership derived via Submodule.topologicalClosure_coe;
    Finsupp namespace for mem_span_range_iff_exists_finsupp; two stray
    Finset.sum_apply rewrites removed.  Judge's predicted failure class
    LP_RESTRICTED_REPRESENTATIVE_OR_TENDSTO_IN_MEASURE_NORMAL_FORM:
    PARTIALLY OBSERVED — the actual frictions were notation/API-name issues;
    the tendsto-in-measure step itself compiled on the first attempt)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierIntegralCrosswalk.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierIntegralCrosswalk — Build completed successfully (7769 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierIntegralCrosswalk.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: all three public declarations and the plant:
    [propext, Classical.choice, Quot.sound]; sorryAx NONE (grep = 0)

SUCCESS_CODE: H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_ACTUAL_INTEGRAL_LEAN
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
NEXT_PER_VERDICT: W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE
```
