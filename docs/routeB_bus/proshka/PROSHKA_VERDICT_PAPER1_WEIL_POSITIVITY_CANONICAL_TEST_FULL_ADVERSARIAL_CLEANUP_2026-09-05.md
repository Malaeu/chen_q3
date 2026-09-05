# STATUS: TRY_PAPER1_AFTER_LISTED_PROOF_AND_SCOPE_REPAIRS
```yaml
OPERATIVE_CLASS: TRY_PAPER1_AFTER_LISTED_PROOF_AND_SCOPE_REPAIRS
PRIMARY_COUNT: 1
RESULT: READY_AFTER_LISTED_FIXES
MANUSCRIPT_AS_SUBMITTED: NOT_READY
REQUEST_ID: REQ-2026-09-05-PAPERCLEAN
BOUNDARY_ID: PAPER1_WEIL_POSITIVITY_CANONICAL_TEST_FULL_ADVERSARIAL_CLEANUP
REQUEST_LOCK:
  COMMIT: 586d6edd5fc1c248fb324041703d7778d6c08aee
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_PAPER1_WEIL_POSITIVITY_CANONICAL_TEST_FULL_ADVERSARIAL_CLEANUP_2026-09-05.txt
  GIT_BLOB: b9a62d0a4f556ad17983028d784dad214c30fa84
  SHA256: 138450097079acbb45641cc4bb4f7c3c422c119d423764a9167efded88f04ebe
  BYTES: 10526
  LINES: 99
  FINAL_LF: true
  SHA256_INDEPENDENTLY_RECOMPUTED: true
  GIT_OBJECT_SHA1_INDEPENDENTLY_RECOMPUTED: true
MANUSCRIPT_LOCK:
  COMMIT: 0f9c7cbc81bbd69ba691c862d24d32b359c0ffa1
  VERSION: v3
  TEX_SOURCES_READ: all_files_in_request_section_1
  REFEREE_REPORTS_READ: [round_1, round_2]
  STYLE_AND_NOVELTY_REPORTS_READ: true
  SOURCE_GIT_BLOB_PREFIXES_MATCHED: true
  ALL_MANUSCRIPT_SHA256_PREFIXES_INDEPENDENTLY_RECOMPUTED: false
  POST_BASE_MANUSCRIPT_CHANGES_USED: false
PHASE:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: PAPER1_STRUCTURE_PAPER_WEIL_POSITIVITY
  MUTATED: false
FINDINGS:
  GROUPING: independent_root_causes_not_each_occurrence
  CRITICAL: 0
  HIGH: 9
  MEDIUM: 7
  LOW: 3
  WORDING: 1
  TOTAL: 20
CORE:
  RIEMANN_FOURIER_NORMALIZATION: SURVIVES
  CUTOFF_ARGUMENT: SURVIVES_WITH_EXACT_CONSTANTS_AND_R_NONNEGATIVE
  RADICAL_CONTAINMENT: SURVIVES_AFTER_CONVOLUTION_ENVELOPE_REPAIR
  GROUND_STATE_IDENTITY: SURVIVES
  FINITE_STENCIL_OBSTRUCTION: SURVIVES
  COUNTABLE_FINITE_STENCIL_SOS_OBSTRUCTION: SURVIVES
  NO_FIXED_X_MARGIN_ON_DENSE_SPAN: SURVIVES
  NO_ARBITRARY_SUM_OF_SQUARES: NOT_ESTABLISHED
  NO_LOCALIZATION_OF_RESTRICTED_SONIN_MINORANT: NOT_ESTABLISHED
  INDEFINITENESS_OF_THE_WEIL_FORM: NOT_ESTABLISHED
  KERNEL_B_AS_NEW_DENSITY: PRIOR_ART_COMPONENT
READINESS:
  AFTER_ALL_PATCHES: suitable_for_author_readthrough_and_arXiv_math_NT
  JOURNAL_ACCEPTANCE_PREDICTED: false
  MAIN_PUBLICATION_UNIT: global_finite_stencil_obstruction_with_concrete_radical_application
  NUMERICS_IN_REPAIRED_PAPER: reported_diagnostics_not_certificates
  NO_ADDITIONAL_ANALYTIC_HYPOTHESIS_INTRODUCED: true
AUDIT_LIMITS:
  MANUSCRIPT_PDF_RENDERED: false
  FIGURE_ASSETS_AND_RAW_CERTIFICATES_REVERIFIED: false
  LEAN_KERNEL_RERUN: false
  OTHER_TWELVE_COMPANION_LEAN_FILES_REAUDITED: false
  BOMBIERI_AND_YOSHIDA_COMPLETE_PRIMARY_SCANS_RETRIEVED: false
  PRIMARY_TEXT_FOR_KEY_NORMALIZATIONS: CCM_and_Suzuki
  PRIMARY_PDF_FORMULAS_VISUALLY_CHECKED: Suzuki_2606_09096_and_Connes_2602_04022
  NUMERICAL_WORK: small_arithmetic_and_polynomial_checks_only
CLOSES:
  - REQ-2026-09-05-PAPERCLEAN
CLOSES_ANALYTIC_SUPPLIERS: []
OPENS: []
AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PAPER1_WEIL_POSITIVITY_CANONICAL_TEST_FULL_ADVERSARIAL_CLEANUP_2026-09-05.md
MANUSCRIPT_EDIT_PERFORMED: false
LEAN_EDIT_PERFORMED: false
ROUTE_PROMOTION: false
SCOPE: ABSTRACT
VERIFIER: PAPER
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and evidence boundary

The core paper survives. It is not ready as v3. It becomes a defensible structural preprint after the replacements below: the main theorem concerns **fixed finite sampling stencils on the unrestricted compact test class**, not all local methods, all sums of squares, or localization of a theorem on a different restricted test class. The signed ground-state identity and the abstract obstruction have correct proofs. The convolution-envelope argument needs a real repair, not a stylistic edit.

`READY_AFTER_LISTED_FIXES` is a mathematical/editorial assessment of the patched text. It does not certify an unbuilt PDF, undisclosed numerical enclosures, the author's affiliation, journal acceptance, or any new Lean theorem. The replacements deliberately remove claims that would require unavailable certificates. No unresolved mathematical obligation is hidden behind the readiness code.

All manuscript quotations below refer to the pinned v3 source. The two earlier referees are evidence about the editing history, not authorities establishing truth. In particular, a numerical residual does not prove a proposition, and agreement between two agents is not independent mathematical certification. The section-specific proof audits below are this review's paper checks. `[ABSTRACT][PAPER]`

### Repository evidence keys

`M-main`, `M-setup`, etc. mean `paper_weil/main.tex`, `paper_weil/sections/setup.tex`, etc., at `0f9c7cbc81bbd69ba691c862d24d32b359c0ffa1`. The matched Git blob prefixes are:

| Key | File | Git blob prefix |
|---|---|---|
| M-main | main.tex | 84864c116067 |
| M-abstract | sections/abstract.tex | 2e67d282a916 |
| M-intro | sections/intro.tex | 6da9b2e3f9a1 |
| M-setup | sections/setup.tex | 65d4bf83b0a6 |
| M-canonical | sections/canonical.tex | 0cfad4b74514 |
| M-GS | sections/groundstate.tex | 41528b832796 |
| M-obstruction | sections/obstruction.tex | fe98a4b5dd30 |
| M-windows | sections/windows.tex | 8b57cc12de09 |
| M-ledger | sections/ledger.tex | 7728a254411a |
| M-disclosure | sections/disclosure.tex | c412aed6d40f |
| M-constants | sections/app_constants.tex | 07c500d4991d |
| M-Lean | sections/app_lean.tex | 007d2ea8e07c |
| M-bib | references.bib | 3c6f2b760315 |
| L-stencil | q3.lean.aristotle/Q3/Proofs/RouteB/NoFiniteStencilMinorant.lean | e6fd9dc2f713 |

Full L-stencil blob: `e6fd9dc2f71332a8ebd1050fc30860bfb1fc24c0`. Its five printed export names and their actual hypotheses were inspected; its reported green gate was not rerun.

## 1. Severity table

The replacement column points to complete, verbatim LaTeX blocks in section 4. Apply whole-file replacements where specified; do not also apply a conflicting historical style patch. The 20 rows group root causes, not every occurrence of a repeated error.

| ID | Severity | File / theorem | Finding | Verbatim replacement |
|---|---|---|---|---|
| F01 | HIGH | canonical.tex, Proposition 3.4 | A translate of a double-exponential envelope cannot be absorbed into a constant multiplying the same envelope. The diameter of supp h also loses the location of that support. | P04c, support radius H and exponent a_H |
| F02 | MEDIUM | Theorem 3.2; Lemmas 3.3, 5.1; Appendix A | M2=6011.8 is below the stated majorant's approximately 6011.8222; numerical A is not a certified denominator; Cq's numerator is not exactly 150925. Use exact definitions, not rounded equalities. Quantify R>=0. | P04a-b, P07b, P11 |
| F03 | MEDIUM | setup.tex, control space | Completion needs an injective function-space realization before evaluating representatives. C_{g,v} is undefined. The decimal sum 3.9325 is not the value of -zeta'(3/2). A fully analytic bound is easy. | P03 |
| F04 | MEDIUM | Theorem 4.1, measure notation | The density has infinite mass near zero; it is not a locally finite signed measure on all R. Define it on the punctured line and define the difference integral absolutely. Define b_+, b_- and C0 before use. | P06b-d |
| F05 | HIGH | intro.tex; groundstate.tex | Calling Q an indefinite form assumes a negative direction not established here. Calling the result a Dirichlet form imports nonnegativity/Markov properties not proved. | P02, P06a |
| F06 | HIGH | abstract, introduction, obstruction opening | No finite-stencil SOS is not no SOS. The global no-minorant theorem does not exclude a local estimate on Connes' restricted Sonin test class. The cited transform zero is i/2, not 2i. | P01, P02, P07a,c |
| F07 | HIGH | priority; groundstate.tex; bibliography | Differentiating Suzuki's printed screw function already gives b and the atoms. Section 3.5 is in arXiv:2206.03682, not arXiv:2301.00421. | P02, P06c, P13 |
| F08 | HIGH | setup.tex; windows.tex | CCM matrices use Fourier modes, not a prolate basis. N is a cutoff, full dimension 2N+1. Finite projected trial, continuum k_lambda, and their transforms are conflated. inf Q is not a normalized bottom. | P03, P08 |
| F09 | HIGH | windows.tex, final paragraph | 1.35 and 1.33 are Rayleigh ratios, not ||xi-q||/sqrt(lambda1). The displayed statistic is a different object by many orders of magnitude. | P08 |
| F10 | MEDIUM | windows.tex, text and captions | 1.7e-220 is about 46.2%, not 20%, below 10^-219.5. Nonzero delta and p are described as equality/vanishing. A trial/Xi ratio is only local away from Xi zeros. | P08 |
| F11 | HIGH | figures, windows, disclosure, constants | Use of arb does not certify matrix entries, spectral enclosures and omitted-source tails automatically. Finite stabilization is not continuum saturation. A sum over 3000 listed zeros is not the full zero-side certificate. No such enclosures were supplied to this review. | P01, P06e, P08, P10, P11 |
| F12 | HIGH | ledger.tex, item 1 | D-c_A H >= -c_A H, so the archimedean part is not unbounded below on the unit sphere. Replacing Lambda(n) by 1 is not replacing the prime measure by continuous density. No theorem rules out all separate estimates. | P09 |
| F13 | HIGH | ledger; introductory literature generalizations | Newman/Nicolas do not prove a zero-margin theorem for every RH equivalent. The GORZ result is not merely degree<=8. No proof here excludes all deformations or imports. The absolute literature claim about the log 2 boundary conflicts with the cited Zhu preprint's stated claim. | P02, P03, P09 |
| F14 | MEDIUM | Appendix B / Theorem 5.3 | Lean H2 uses ENNReal.ofReal(Q)=the positive part of Q, not Q itself. The paper's hypothesis implies the formal one, but they are not literally equal. | P12 |
| F15 | MEDIUM | disclosure; Appendix B | The no-minorant proof is not just finite algebra: it uses integration, limits and Fatou. Five printed exports are not all declarations. Neither the concrete Weil budget nor the entire paper is formalized by this file. | P10, P12 |
| F16 | MEDIUM | canonical.tex, Remark 3.5 | No identification of X/rad with Suzuki's completed Hilbert space is proved. Bombieri's zero-indexed matrices are not all CCM truncations. The finite radical belongs to the shifted form under simplicity, not the unshifted Weil matrix. | P04d |
| F17 | LOW | Remark 5.6; quantitative margin paragraph | The measurable-family extension needs nonzero/distinct-stencil and measurability hypotheses. In the quantitative paragraph choose 0<eta<infinity, not just eta>0. | P07d-e |
| F18 | LOW | Remark 5.10 | The local small-t estimate does not rule out all test-independent comparisons. Calling the paragraph a remark does not validate its universal impossibility sentence. | P07f |
| F19 | WORDING | disclosure; priority | Personal checking of every proof/literature claim is not established by the supplied logs. An elementary noncoercivity consequence should not be advertised as a distinct priority breakthrough. | P02, P10 |
| F20 | LOW | global notation; Appendix B | Use Fourier cutoff / finite projected trial consistently, distinguish fit coefficient from b(t), define digamma, do not retain stale path/rectangle references, and distinguish approximate constants from exact bounds. | P03, P08, P11, P12 |

No false central theorem or unrepairable central proof was found. This is not a claim that v3 contains no false sentences: F05, F09 and F12 are substantive false or unsupported assertions, and F01 is an invalid proof estimate. The readiness decision depends on actually replacing them.

## 2. K1-K6 adjudication

### K1. Every mathematical proof

| Result | Verdict | Check |
|---|---|---|
| Definition 2.1 and source form | SURVIVES / exposition FIX | Signs, factor 2 in prime correlations, pole polarization, and c_A agree with the geometric explicit formula. P03 supplies the analytic normalization check. |
| Definition 3.1 / Theorem 3.2 | FIX, conclusion SURVIVES | Phi=2 Phi_P(x/2); the Jacobian gives 4 in the full-line integral. H0=Xi(z/2)/8 is correct. Gaussian series gives real analyticity; positivity on x>=0 is termwise and elsewhere uses evenness. Use exact M_j, not uncertified rounded majorants. |
| Lemma 3.3 | FIX | All three bounds follow for R>=0. The y^{-3/4} factor in the weighted L1 estimate must be bounded only on y>=e^{2R}>=1. D's H1 bound is correct. P04b gives the details and an admissible smooth cutoff construction. |
| Proposition 3.4, f0 | SURVIVES | Two integrations by parts yield the weighted |z|^{-2} bound. Xi(0)!=0; the zero multiset has summable inverse squares. Boundedness of the other transform on the closed strip gives dominated convergence. Then use continuity in X. No RH is used. |
| Proposition 3.4, translates | SURVIVES | Polarized simultaneous translation invariance, not Q(f0)=0 alone, gives radical membership. U_q is bounded on X. |
| Proposition 3.4, convolution | FIX | Replace the false same-exponent estimate by a_H=(pi/2)e^{-2H}, H=max|supp h|. This proves membership and the same cutoff passage. |
| Theorem 4.1 | SURVIVES | The newly symmetric pole expression is correct for complex s without assuming |s|^2 even. It gives -2 integral cosh(t/2) E_s. D gives integral a E_s; the prime term gives w_n E_s, not 2w_n; H cancels. Clarify the punctured measure, not the identity. |
| Lemma 4.2 | SURVIVES | b's sign is the opposite of y^3-y-1 for y=e^t>1. This polynomial is strictly increasing there, hence the root is unique. |
| Corollary 4.3 | SURVIVES | Multiplication/division by the smooth strictly positive f0 is a bijection of compact smooth tests. Apply the full complex Weil criterion. |
| Lemma 5.1 | FIX numerical equality only | Radical membership cancels both mixed terms, so Q(U_qf0-e_R)=Q(e_R). Combining the norm bounds gives the symbolic Cq in P07b exactly. |
| Lemma 5.2 | SURVIVES | Continuity passes rational shifts to real shifts; the Fourier transform is nonzero near zero; a finite exponential polynomial then has a nonsingular Vandermonde system. No differentiability of f is required. |
| Theorem 5.3 | SURVIVES | Fatou along integer R, eventual stabilization at every finite sample, countable rational shifts, and translate independence prove W=0 a.e. H1 is not derived from abstract properties of Q0; it is a real hypothesis. |
| Corollary 5.4 | SURVIVES | The smooth ratio cutoffs are legal compact tests. Lemma 5.1 supplies H1. |
| Corollary 5.5 | SURVIVES in stated finite-stencil class | Each nonnegative summand is a minorant. For the bump, prime correlations vanish; the pole term is positive; D>=e^{-1/2}log(1/ell), hence Q>=1 under the printed ell bound. This is not a no-nonlocal-SOS theorem. |
| Example 5.7 | SURVIVES | The Gaussian pair has Fourier transform zero at pi/2; its translates are radical vectors for the positive rank-one global functional. This is also a control against reading the obstruction as negativity of Q. |
| Remark 5.8 | SURVIVES | Finite PSD with zero row sums admits zero-mean spectral squares; positive edge squares are a smaller cone. The positive (1,3) entry of (1,-2,1)(1,-2,1)^T is a valid distinction. |
| Proposition 5.9 | SURVIVES | Continuity extends a fixed X-margin from a dense span; evaluation at the nonzero radical vector contradicts it. No quotient-norm conclusion follows. |
| Remark 5.10 | FIX | Keep the proved delta^2/4 local energy asymptotic; delete the extrapolated general Schur impossibility. |
| Conjectural trial jet | NOT A THEOREM | Keep explicitly conjectural and identify the finite projected test actually sampled; the displayed fit is not a tail estimate. |

These are paper audits. Only the abstract no-stencil core has the supplied Lean status. `[ABSTRACT][PAPER]`

#### Two short computations that change the verdict

First, the exact expression given in Appendix A, evaluated using its printed approximation to A, gives approximately

    M0 = 23.9099836156, M1 = 325.4253185750, M2 = 6011.82220718.

This is not proof that the true derivative violates the smaller 6011.8 bound; it proves that the stated majorant argument does not deliver that rounded constant. Defining M_j by the exact expression repairs the proof without relying on any numerical enclosure of A. With the printed rounded M0 and M1, the numerator in Lemma 5.1 is approximately 150924.9442333, not exactly 150925.

Second, 1.7e-220 / 10^-219.5 is approximately 0.5375872. The relative difference from the prediction is about 46.24%. The quoted p at (13,120) gives a phase-aligned vector distance approximately sqrt(p), so dividing it by sqrt(3.484e-59) is of order 10^25, not 1.35. These are arithmetic checks, not new spectral experiments. `[FINITE_CELL][PAPER]`

### K2. The explicit formula and the test class

The conjugations in (EF) are correct with antilinearity in the first slot and the paper's minus-sign Fourier transform. For g* (x)=conjugate(g(-x)), the transform of g* * v is conjugate(ghat(bar z)) vhat(z). The zero multiset must include multiplicity. For compact smooth tests both transforms decay sufficiently fast on the zero strip, so the series is absolutely convergent; pairing conjugate zeros makes the quadratic value real without RH.

The source normalization can be checked analytically, not on a null test. With psi_d the digamma function,

    2 integral_0^infinity a(t)(1-cos(ut)) dt
      = Re psi_d(1/4+iu/2) - psi_d(1/4),
    psi_d(1/4) = -gamma - pi/2 - 3 log 2.

Therefore the Fourier multiplier of D-c_A H is Re psi_d(1/4+iu/2)-log pi, with Plancherel factor 1/(2pi). Together with the two pole evaluations and the two prime translates this is the classical geometric explicit formula in the stated convention. P03 spells out the transport. This also explains why checking Q(f0) approximately zero cannot determine an overall multiplicative normalization: any rescaling preserves a zero test value.

The reference to Bombieri's formulation transported and polarized is reasonable background, but the paper must print the transport it actually uses. The present audit checked that transport against CCM (3.5)-(3.11) and Suzuki's printed explicit formula. It did not independently retrieve the complete original Bombieri scan, and does not claim to have audited all his conventions from that scan. `[ABSTRACT][PAPER]`

### K3. Attribution, novelty and publication priority

| Claim | Verdict | Attribution boundary |
|---|---|---|
| N1: canonical ground-state substitution | SURVIVES as a specific application, not a new general method | Ground-state algebra is classical and represented by Frank-Seiringer; Suzuki supplies the signed distribution. The manuscript proves its application to this radical vector. |
| N1: new closed density | DELETE independent-novelty claim | Suzuki 2606.09096v2 (1.3) already determines this density explicitly by two differentiations. |
| N1: plastic threshold | SURVIVES as an elementary observation | y^3-y-1 arises immediately from that known density. No priority guarantee is warranted. |
| N2: concrete radical in X | SURVIVES after P04 | The concrete domain/cutoff verification is useful; the vanishing transform mechanism follows from the explicit formula. Do not equate X/rad with another completed Hilbert space without a theorem. |
| N3: global finite-stencil obstruction | SURVIVES; no exact prior formulation found in checked sources | The proof combines classical translate independence and Fatou. Bombieri's infinite zero-indexed independence problem is not this finite lemma. The restricted Sonin theorem is outside the no-go's hypotheses. |
| N4: no dense fixed margin | SURVIVES, demote priority claim | It is an immediate consequence of a continuous form with a nonzero radical vector. It is not an independent major novelty claim. |
| N5: cutoff extension | SURVIVES after explicit estimates | Present as a needed analytic justification, not a new form of Weil's explicit formula. |

**Decisive prior-art calculation.** In Suzuki 2606.09096v2 (1.3), on t>0 the second derivative of the pole term is -2 cosh(t/2). The second derivative of the Lerch-series term is sum_{k>=0} exp(-(2k+1/2)t)=a(t), and that of each (t-log n)_+ term is w_n delta_{log n}. Thus, away from the origin,

    g_scr'' = b(t) dt + sum_n w_n delta_{log n}.

The contact distribution at zero is not included in this punctured identity. It is removed in the manuscript's difference/radical subtraction. The same distributional relation is discussed in **Suzuki, Aspects of the screw function corresponding to the Riemann zeta-function, arXiv:2206.03682v4, section 3.5**, published in JLMS 108 (2023), 1448-1487, DOI 10.1112/jlms.12785. It is not section 3.5 of *On the Hilbert space derived from the Weil distribution* (2301.00421). This corrects the novelty pass itself, not only v3. `[ABSTRACT][PAPER]`

Other named references were treated as follows:

- **Riemann; Rodgers-Tao; Polymath15:** retain the classical Phi and H_t normalization. They do not supply the paper's no-stencil result. Polymath's and Rodgers-Tao's theorems do not establish a general statement that every equivalent criterion lacks a uniform margin.
- **Weil; Yoshida; Bombieri:** retain attribution for the explicit formula, criterion and local forms. Do not identify Bombieri's matrices indexed by zeros with the CCM Fourier compressions. The original full Yoshida and Bombieri scans were not independently retrieved during this pass; unsupported exact comparisons to Lemma 10 are removed rather than accepted on an agent's assertion.
- **Connes-Consani; CCM; Connes-Moscovici:** distinguish the local archimedean/Sonin theorem, the Fourier compression of the Weil form, and the prolate operator/trial. Their spectra and bases are not interchangeable. Connes 2602.04022 Theorem 7.1 is on a restricted test class; its printed vanishing condition is at i/2 and 0, not 2i and 0. P07 does not need to reproduce that convention-dependent condition at all.
- **Suzuki 2023 and 2026:** correct the article and section, give the existing kernel its credit, and do not assert an unproved identification of topologies/completions.
- **Frank-Seiringer:** legitimate methodological reference, not a positivity theorem for this signed kernel. The finite algebra of the transform must still be proved here, as it is.
- **Li:** existence of a related positive Hilbert-Schmidt operator does not establish positivity of the Weil form; no such implication is used in the repair.
- **Freedman and Groskin:** the stated arXiv records and titles exist. They may be cited explicitly as unrefereed related preprints. Neither is needed as a proof dependency. The canonical Fourier representation is not to be credited as a 2026 discovery.
- **Zhu:** 2608.24827v2 reports a certified extension to tests supported in [-0.8,0.8] and calls its large-window law empirical. This audit does not validate those certificates. One cannot cite that preprint and simultaneously assert that no literature goes past the classical log 2 autocorrelation boundary, or call the empirical law an established theorem. The claimed numerical cross-implementation match is removed.
- **GORZ:** the cited work concerns asymptotic hyperbolicity in each fixed degree, not merely d<=8. It is not a theorem excluding this paper's open problem. **Farmer** is not a universal no-go theorem for all imports. **Nicolas** and **Broughan** do not justify the paper's blanket margin conclusion. These decorative negative comparisons are removed from the ledger.
- **Tao / Leiden Declaration:** Tao's arXiv record exists; use the Declaration itself for the disclosure rule. It calls for transparency and responsibility, not for presenting numerical checks as proofs.
- **Earlier author preprint / Mathlib:** no mathematical result of the old preprint is imported. The exact old Zenodo metadata was not independently resolved in this pass. The repaired text does not pronounce the old proof impossible by reference to the false ledger item. Mathlib and the stated toolchain are provenance, not evidence for the unformalized analytic lemmas.

This is a bounded prior-art search, not proof of uniqueness of the new formulation. No full prior proof of Theorem 5.3 in its exact abstract form was found in the sources read. `[ABSTRACT][PAPER]`

### K4. Lean and disclosure

The formal core is sound at the interface level inspected. H1 is an assumption of the abstract theorem, and the paper must prove its concrete Weil instance separately. The code's H2 is a nonnegative extended integral bounded by `ENNReal.ofReal(Q(...))`, namely max(Q(...),0) represented in [0,infinity]. The manuscript's real inequality with Q itself implies this, so its application is valid. Calling them identical is not valid.

The formal theorem allows extended nonnegative W; the paper may use finite real-valued W as a specialization. The code uses real f and real stencil coefficients, with complex-valued profiles; the paper's theorem makes the same real-stencil restriction. Its separate independence lemma permits complex coefficients. The Gaussian nonvacuity theorem uses Q=0 and W=0. It demonstrates consistency of the abstract hypotheses, not existence of a positive nonzero Weil minorant.

The exact five printed exports are listed in P12. Other lemmas in the file exist; five is not its total declaration count. The proof contains Fourier integrals, continuity, rational density, Fatou and almost-everywhere reasoning. Calling the formalized part only finite algebra is inaccurate.

The logs establish automated drafting/review roles and reported computations, not personal checking by the author of every cited proof. The sentence 'the author checked them numerically' is particularly misleading when its antecedent includes the universal no-minorant theorem. P10 gives an adequate disclosure without certifying an unobserved human action. The author must independently read and accept the final mathematics before release. `[ABSTRACT][PAPER; L-stencil source inspected, kernel status reported]`

### K5. Notation and consistency

P01-P13 retain the existing macros and theorem labels. The changes consistently use:

- f0 for the normalized canonical test; Phi for its unnormalized version; A=||Phi||_2; A_+ and A_- only for pole functionals.
- Exact M_j from Appendix A; all listed decimal evaluations use approximately, not equality.
- rho_p for the plastic root and z in Z(Xi) for the centered zeros; xi(s)=s(s-1)pi^{-s/2}Gamma(s/2)zeta(s)/2 explicitly.
- b(t) for the signed density and beta_fit for a regression slope; digamma is defined where used.
- S for the finite stencil, and 'Sonin projection' in prose, avoiding a second undeclared S.
- E_s for the ratio-difference energy, E(h) only for the CCM summation transform.
- N for a Fourier cutoff, full carrier dimension 2N+1; q_{m,N} for the finite normalized projected trial; k_lambda for the unprojected continuum packet.
- mu_lambda for the infimum of the **normalized** Rayleigh quotient. A finite evaluated pair is a cell; an interval is a window; finite stabilization is a diagnostic, not an equality with mu_lambda.

The aliascnt/cleveref correction in main.tex survives. The manuscript PDF and embedded figure files were not rendered here, so layout, figure tick labels and caption/data agreement still require the ordinary post-edit build/read-through. This does not hide a mathematical input. `[ABSTRACT][PAPER]`

### K6. Placement

After these repairs, the realistic unit is a **short structural number-theory / analysis paper** centered on Theorem 5.3 and its explicit Weil-form application. Research in Number Theory is a reasonable scope match; its stated scope requires significant original number-theoretic work, so novelty and significance will be the editorial hurdle, not merely correctness. A specialist analysis/number-theory journal is another plausible home. Journal of Number Theory is not an automatic consequence of having an RH-related title. No acceptance probability is certified.

Experimental Mathematics becomes a stronger match only with a reproducible numerical package and genuine end-to-end interval enclosures; the present approximate table alone is not enough computational substance. Its official scope emphasizes experiments that produce mathematical insight, not certification by software name.

The first sentence a skeptical referee should reject in v3 is the abstract's claim that the result 'shows that the known nonlocal (Sonin-space) positivity cannot be localised'. The theorem's quantifiers do not cover the restricted Sonin class. The unqualified 'no sum-of-squares representation exists' is the next problem.

A shortened ledger containing only proved scope restrictions helps. A catalogue of alleged failures of other RH programs hurts. A brief, accurate disclosure helps; a narrative of agents, predictions and unspecified personal verification distracts. P09-P10 implement that distinction. `[ABSTRACT][PAPER; editorial assessment]`

## 3. Application instructions for the verbatim replacements

Only this verdict is committed. The blocks below are replacement manuscript text, not claims that edits or a build have already occurred. Whole-file replacements preserve their stated labels. Fragment replacements name an exact environment or opening sentence. Apply the bibliography addition before compiling the new citations. The repaired mathematical core needs no new conjecture, axiom, source estimate or numerical certificate.

## 4. Verbatim LaTeX replacements

### P01 — replace sections/abstract.tex in full

```latex
We study the Weil form on compact smooth tests and on a specified weighted
completion that contains Riemann's canonical function. If $f_0$ is the
$L^2$-normalisation of the function whose Fourier transform is $\Xi$, then
$f_0$, its translates and its convolutions with compact smooth functions
belong to the radical of the extended form. The substitution $g=f_0s$
gives a signed difference-form identity: its continuous density changes
sign at the logarithm of the plastic number, and its discrete terms occur
at prime-power distances. This identity rewrites Weil's positivity
criterion without proving its positivity. Our main result is an abstract
obstruction: a nonnegative weighted square of a nonzero finite sampling
stencil cannot be a minorant on the full compact test class when the
translated ratio cutoffs have vanishing form value. Consequently, the
Weil form in these ratio coordinates has no countable representation by
such nonnegative finite-stencil energies. The conclusion does not exclude
nonlocal factors or estimates on a restricted support class. We also
record the elementary obstruction to a fixed coercive margin in the
ambient weighted norm. The abstract Fatou--translate-independence core
has a Lean~4 formalisation; the concrete analytic input and the signed
representation are proved on paper. Finite-window computations are
reported only as diagnostics.
```

### P02 — replace sections/intro.tex in full

```latex
\section{Introduction}\label{sec:intro}

Weil's criterion relates the Riemann hypothesis to nonnegativity of a
Hermitian form on compactly supported smooth tests
\cite{Weil1952,BOMBIERI-WEILQF-2000}. We use its logarithmic-variable
version, with archimedean, pole and prime contributions. Localized forms
and their variational properties occur in the work of Yoshida,
Bombieri, Connes--Consani and Connes--Consani--Moscovici
\cite{YOSHIDA-HERMITIAN-1992,BOMBIERI-WEILQF-2000,CC-WEILPOS-2020,CCM-ZST-2025}.
The finite CCM matrices are Fourier compressions of a windowed form;
they are not matrices in a prolate eigenfunction basis. Their lowest
eigenvalues give upper bounds for the corresponding full-window
Rayleigh infimum. A finite list of positive upper bounds establishes no
global positivity statement.

We fix Riemann's function $\Phi$, in the convention
$\widehat\Phi=\Xi$, and put $f_0=\Phi/\|\Phi\|_2$
\cite{Riemann1859,CCM-ZST-2025}. The function $f_0$ is smooth and strictly
positive. We specify a completion $\Xf$ on which the Weil form extends
continuously and prove that all translates of $f_0$, and all $f_0*h$ with
$h\in C_c^\infty$, belong to its radical (\Cref{prop:radical}). The cutoff
argument is essential: the explicit formula is not initially being
applied to a compactly supported canonical test.

The substitution $g=f_0s$ yields
\[
 \Q(f_0s)=\int_0^\infty b(t)E_s(t)\,dt
          +\sum_{n\ge2}\frac{\Lam(n)}{\sqrt n}E_s(\log n),
 \qquad
 E_s(t)=\int_{\R}f_0(x)f_0(x+t)|s(x+t)-s(x)|^2dx.
\]
This is a signed difference-form representation, not an assertion of the
positivity or Markov property of a Dirichlet form. The distributional
kernel is already present in Suzuki's screw-function formulas
\cite[\S3.5]{Suzuki2023Screw}\cite[\S2.5]{Suzuki2026}. Ground-state
representations are a classical method, including the nonlocal versions
of Frank and Seiringer \cite{FrankSeiringer2008}. Here we verify the
substitution for a radical vector of a form whose sign is not assumed.
The elementary expression for $b(t)$ follows from the known kernel;
its zero is characterized by the plastic-number equation.
\Cref{cor:DOM} records the resulting three-term positivity inequality.

The main result is \Cref{thm:nominorant}. A fixed nonzero finite sampling
stencil, with a measurable nonnegative weight, cannot minorize
$\Q(f_0s)$ for every compact smooth profile $s$. The proof uses compact
cutoffs of $f_0(\cdot-q)/f_0$, Fatou's lemma, countably many rational
translations and finite translate independence. It applies to an
arbitrary functional with the specified vanishing cutoff values; the
Weil form is a concrete instance. \Cref{cor:noCSS} excludes countable
sums of these finite-stencil energies, not arbitrary sums of squares.
\Cref{ex:control} shows why the obstruction does not imply that the
underlying form has a negative direction.

The quantifier over all compact profiles matters. The known Sonin-space
minorant is imposed on a different, restricted support and moment class
\cite{Connes2026,CC-WEILPOS-2020}; our result does not rule out estimates
on that class. Similarly, \Cref{prop:trade} concerns a fixed margin in
the ambient $\Xf$ norm and says nothing about coercivity in a quotient
norm. The short ledger in \Cref{sec:ledger} keeps these boundaries
explicit. \Cref{sec:windows} reports finite computations and a
conjectural trial-jet expansion, without using them in any proof.
\Cref{sec:disclosure,app:lean} delimit the formalised result and describe
the use of automated tools. No positivity estimate establishing RH is
claimed.

\paragraph{Attribution and scope of the contribution.}
The canonical Fourier representation is classical; the CCM notation
makes its relation to the prolate trial explicit. The same logarithmic
expansion is also recorded in the unrefereed preprint
\cite{Freedman2026}. The signed kernel belongs to the existing
Weil--Suzuki framework, and the ground-state algebra is not a new
general method. The concrete weighted-domain verification and the
global finite-stencil obstruction are the statements developed here.
We have not found the latter in this precise formulation in the sources
cited, but make no exhaustive priority claim. The no-margin proposition
is included as an elementary consequence, not as a separate major
novelty. Related positive-operator and finite-dictionary constructions
\cite{Li2024,Groskin2026} are not inputs asserting positivity of this
Weil form.
```

### P03 — replace sections/setup.tex in full

```latex
\section{The Weil form in the logarithmic variable}\label{sec:setup}

Tests are complex-valued. We use
\[
 \widehat g(z)=\int_{\R}g(x)e^{-izx}dx,\quad
 (U_qg)(x)=g(x-q),\quad g^*(x)=\overline{g(-x)},\quad
 \xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),\quad
 \Xi(z)=\xi(\tfrac12+iz).
\]
The change of variable $x=\log u$ carries $du/u$ to $dx$ and
multiplicative convolution and involution to the displayed additive
ones. We write $\Lam$ for the von Mangoldt function,
$w_n=\Lam(n)/\sqrt n$, and $Z(\Xi)$ for the zero multiset, with
multiplicity. The constant $\gamma$ below is the Euler--Mascheroni
constant.

\begin{definition}[source form]\label{def:Q}
For $g\in C_c^\infty(\R;\C)$ set
\[
 H(g)=\|g\|_2^2,\quad
 C_g(t)=\Re\int_{\R}\overline{g(x)}g(x+t)dx,\quad
 A_\pm(g)=\int_{\R}g(x)e^{\pm x/2}dx,
\]
\[
 a(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 c_A=\gamma+\log(8\pi)+\frac\pi2,\quad
 \D(g)=\int_0^\infty a(t)\|g(\cdot+t)-g\|_2^2dt.
\]
Define
\begin{equation}\label{eq:Q}
 \Q(g)=\D(g)-c_AH(g)
 +2\Re\bigl(A_+(g)\overline{A_-(g)}\bigr)
 -2\sum_{n\ge2}w_nC_g(\log n).
\end{equation}
The Hermitian polarisation $\B$ is antilinear in its first argument.
For use below, put
\[
 C_{g,v}(t)=\frac12\int_{\R}
  \bigl(\overline{g(x)}v(x+t)+\overline{g(x+t)}v(x)\bigr)dx;
 \qquad C_{g,g}=C_g.
\]
\end{definition}

The prime sum is finite on compact tests: if the support of a test has
diameter at most $L$, its autocorrelation is supported in $[-L,L]$.
In this convention the polarized explicit formula is
\begin{equation}\label{eq:EF}
 \B(g,v)=\sum_{z\in Z(\Xi)}
          \overline{\widehat g(\bar z)}\widehat v(z),
 \qquad g,v\in C_c^\infty(\R;\C).
\end{equation}
This is Weil's formula, in the compact-test formulation and
normalisation used in
\cite{BOMBIERI-WEILQF-2000,CCM-ZST-2025,Suzuki2023Screw}.
Indeed, $\widehat{g^**v}(z)=
\overline{\widehat g(\bar z)}\widehat v(z)$.
For an analytic check of the archimedean constant, let $\psi_{\rm d}$
denote the digamma function. Its integral representation gives
\[
 2\int_0^\infty a(t)(1-\cos(ut))dt
   =\Re\psi_{\rm d}(\tfrac14+\tfrac{iu}2)-\psi_{\rm d}(\tfrac14),
 \qquad
 \psi_{\rm d}(\tfrac14)=-\gamma-\tfrac\pi2-3\log2.
\]
Thus the Fourier multiplier of $\D-c_AH$, with Plancherel factor
$1/(2\pi)$, is
$\Re\psi_{\rm d}(1/4+iu/2)-\log\pi$.
The two pole evaluations and the two prime translations then give
\eqref{eq:Q}. This checks the normalization without testing a vector
whose form value vanishes. Smooth compact support gives absolute
convergence of the zero sum. Under RH it becomes
$\Q(g)=\sum_z|\widehat g(z)|^2$; that rewriting is not used
unconditionally. Weil's criterion is
$\Q(g)\ge0$ for every complex $g\in C_c^\infty(\R)$ if and only if RH.

\paragraph{Control space.}
Let $\Xf$ be the completion of $C_c^\infty(\R;\C)$ for
\[
 \|g\|_{\Xf}^2=\|e^{|x|}g\|_2^2+\D(g).
\]
This completion has an injective realization as a space of functions.
To see this, set
$Jg(x,t)=a(t)^{1/2}(g(x+t)-g(x))$ for $t>0$.
If $g_j$ is Cauchy in this norm, then $g_j$ converges in weighted $L^2$
and $Jg_j$ converges in $L^2(dx\,dt)$. On each strip
$\delta\le t\le T$, translation continuity in $L^2$ identifies the
second limit with $Jg$; exhaustion identifies it for all $t>0$.
In particular a zero weighted-$L^2$ limit has zero second limit.
We use this realization of the completion, not an unproved claim that
it equals every function with finite displayed norm.

The mixed translation energy is bounded by
$\D(g)^{1/2}\D(v)^{1/2}$. Moreover,
\[
 |A_\pm(g)|\le\frac2{\sqrt3}\|e^{|x|}g\|_2,
 \qquad
 |C_{g,v}(t)|\le e^{-|t|}
       \|e^{|x|}g\|_2\|e^{|x|}v\|_2.
\]
The prime coefficient sum is at most
$\sum_{n\ge2}(\log n)n^{-3/2}<5$, by comparison with the
integral of the decreasing function $(\log x)x^{-3/2}$ on $[2,\infty)$.
Consequently
\[
 |\B(g,v)|\le C_{\Xf}\|g\|_{\Xf}\|v\|_{\Xf},
 \qquad C_{\Xf}=|c_A|+14,
\]
since $1+8/3+10<14$ bounds the three other contributions.
This constructs the continuous extension of $\B$.
Translations extend boundedly, with
$\|U_qg\|_{\Xf}\le e^{|q|}\|g\|_{\Xf}$, because $\D$ is
translation-invariant. Membership of the noncompact functions used
below is established by their cutoff estimates, not assumed.

\paragraph{Finite windows.}
Write $L=\log m=2\log\lambda$. On
$J_L=[-L/2,L/2]$, the translated CCM Fourier basis is
\[
 V_n(x)=L^{-1/2}\exp(2\pi in(x+L/2)/L)\mathbf1_{J_L}(x).
\]
The full compression on $|n|\le N$ has dimension $2N+1$.
It is not a prolate eigenfunction expansion; prolate functions enter
separately as trial functions \cite{CCM-ZST-2025,ConnesMoscovici2021}.
A cell is one pair $(m,N)$, with $N$ a Fourier cutoff.
The full-window bottom is the infimum of
$\Q(g)/\|g\|_2^2$ over nonzero vectors of the window form domain.
For fixed $m$, the lowest eigenvalues of the full Fourier compressions
decrease to this infimum, denoted $\mu_\lambda$
\cite[Proposition 3.4]{CCM-ZST-2025}. A finite compression therefore
provides an upper bound, not a positivity certificate for $\mu_\lambda$.
Nonnegativity on every window is equivalent to the full Weil criterion;
the monotonicity in \cite[Corollary 3.7]{CCM-ZST-2025} also transfers
cofinal nonnegativity to all smaller windows.
Classical short-support positivity is discussed in
\cite{YOSHIDA-HERMITIAN-1992,BOMBIERI-WEILQF-2000,CC-WEILPOS-2020}.
The recent preprint \cite{XUEFENGZHU-2026} reports a larger certified
bounded-support range; those certificates are not a dependency of the
present paper and are not verified here.
```

### P04a — Theorem 3.2 statement and exact/approximate constants

Replace the theorem environment headed `thm:FPhi` by:

```latex
\begin{theorem}\label{thm:FPhi}
$\Phi$ is even, real-analytic and strictly positive. With the exact
constants $M_j$ defined in \Cref{app:constants},
\[
 |\Phi^{(j)}(x)|\le A M_j
          \exp\bigl(-\tfrac\pi2e^{2|x|}\bigr)
 \quad(x\in\R,\ j=0,1,2),
 \qquad \widehat\Phi(z)=\Xi(z)\quad(z\in\C).
\]
\end{theorem}
```

Keep the correct Riemann/Phi_P factor calculation in its proof. Replace its final envelope sentence, beginning `The envelope is the n=1 term`, by:

```latex
The differentiated Gaussian series and the exact monomial majorants
in \Cref{app:constants} give the displayed envelopes. Local uniform
convergence of the series and its derivatives proves real analyticity.
The super-exponential envelope makes the Fourier integral entire in
$z$, so the Fourier identity initially obtained on the real axis holds
on $\C$ by analytic continuation.
```

Replace `A=0.565466013092` and `Xi(0)/A=0.8791346724` in the following prose by `A\approx0.565466013092` and `Xi(0)/A\approx0.8791346724`, preserving the math delimiters. Replace the opening sentence `Cref{thm:FPhi} is ... in the logarithmic variable` by:

```latex
The source function $h$ is the one in
\cite[(7.1)--(7.2), Lemma 7.1]{CCM-ZST-2025}. In the standard
normalisation of $\xi$ fixed in \Cref{sec:setup}, the preceding
calculation fixes the scalar as $\Phi(x)=4E(h)(e^x)$.
```

### P04b — replace Lemma 3.3 and its proof

```latex
\begin{lemma}[cutoff norms]\label{lem:cutoffnorm}
For $R\ge0$ choose smooth cutoffs $0\le\chi_R\le1$, equal to $1$
on $[-R,R]$ and to $0$ outside $[-R-1,R+1]$, with
$|\chi_R'|\le c_\chi=2$ and $|\chi_R''|\le c_\chi'=8$.
For $q\in\R$ put $e_R=(1-\chi_R)U_qf_0$ and
$a_q=(\pi/2)e^{-2|q|}$. Then
\[
 \|e^{|x|}e_R\|_2^2
 \le\frac{M_0^2}{2a_q}e^{-2a_qe^{2R}},\qquad
 \|e_R'\|_2^2
 \le\frac{M_1^2+c_\chi^2M_0^2}{a_q}e^{-2a_qe^{2R}},
\]
\[
 \|e_R''\|_{L^1(e^{|x|/2}dx)}
 \le\frac{M_2+2c_\chi M_1+c_\chi'M_0}{a_q}
          e^{-a_qe^{2R}}.
\]
For $u\in H^1(\R)$,
\[
 \D(u)\le\tfrac23\|u'\|_2^2+\tfrac{32}3\|u\|_2^2.
\]
In particular $\|e_R\|_{\Xf}\to0$ and the displayed weighted
$L^1$ norm tends to zero. Thus $U_qf_0\in\Xf$.
\end{lemma}
\begin{proof}
The inequality $|x-q|\ge|x|-|q|$ gives
$|(U_qf_0)^{(j)}(x)|\le M_j e^{-a_qe^{2|x|}}$.
For $a>0$, $R\ge0$, substitution $y=e^{2x}$ on each half-line gives
\[
 \int_{|x|\ge R}e^{2|x|}e^{-2ae^{2|x|}}dx
       =\frac1{2a}e^{-2ae^{2R}},
\]
\[
 \int_{|x|\ge R}e^{-2ae^{2|x|}}dx
       \le\frac1{2a}e^{-2ae^{2R}},\qquad
 \int_{|x|\ge R}e^{|x|/2}e^{-ae^{2|x|}}dx
       \le\frac1a e^{-ae^{2R}}.
\]
The last two bounds use $y^{-1}\le1$ and $y^{-3/4}\le1$ for
$y\ge e^{2R}\ge1$. Expand $e_R'$ and use
$|v+w|^2\le2|v|^2+2|w|^2$. Expand
\[
 e_R''=(1-\chi_R)(U_qf_0)''
          -2\chi_R'(U_qf_0)'-\chi_R''U_qf_0
\]
and apply the third integral bound. This proves all three estimates.
For the energy, use
$\|u(\cdot+t)-u\|_2\le\min(t\|u'\|_2,2\|u\|_2)$,
$a(t)\le4/(3t)$ on $(0,1]$ and
$a(t)\le(4/3)e^{-t/2}$ on $[1,\infty)$.
Integration gives the stated constants.

For completeness the cutoff derivative bounds are attainable: the
quintic step $1-10t^3+15t^4-6t^5$ on $[0,1]$, extended constantly,
has first derivative bounded by $15/8$ and second derivative bounded
by $10/\sqrt3$. Shrink its transition to $[1/100,99/100]$ and
convolve with a nonnegative smooth mollifier supported in
$[-1/200,1/200]$. The derivative bounds remain below $2$ and $8$,
respectively, and the step is constant near both endpoints. Applying
this step to $|x|-R$ gives the required smooth $\chi_R$.
\end{proof}
```

### P04c — Proposition 3.4 convolution paragraph

Replace the paragraph fragment from `For f_0*h with h in C_c^infty the same cutoff argument applies` through `also vanishes on Z(Xi)` by:

```latex
For $h\in C_c^\infty$, the case $h=0$ is immediate. Otherwise choose
$H\ge0$ with $\supp h\subset[-H,H]$ and put
$a_H=(\pi/2)e^{-2H}$. For $j=0,1,2$,
\[
 |(f_0*h)^{(j)}(x)|
 \le\|h\|_1 M_j\exp(-a_He^{2|x|}).
\]
Indeed $|x-y|\ge|x|-H$ on $\supp h$. Repeating the proof of
\Cref{lem:cutoffnorm} with $a_H$ and $\|h\|_1M_j$ proves that the
cutoffs converge in $\Xf$ and in the required weighted second-derivative
norm. The same source-side and zero-side limit argument therefore
applies to $f_0*h$. Its Fourier transform is $\Xi\widehat h/A$ and
vanishes on $Z(\Xi)$.
```

### P04d — replace Remark 3.5 in full

```latex
\begin{remark}[the enlarged class and the shifted finite form]
Under RH the Weil form is positive definite on nonzero compact smooth
tests \cite{BOMBIERI-WEILQF-2000,Suzuki2025}. This does not conflict
with \Cref{prop:radical}, whose exhibited vectors are noncompact.
The radical of the continuous form on $\Xf$ is closed and contains
the closed span of the displayed translates and convolutions. We do
not identify this weighted completion, or its quotient topology, with
Suzuki's Hilbert-space completion.

In the finite CCM construction the one-dimensional radical is that of
$T=K-\lambda_1I$ when the lowest eigenvalue is simple, not of the
unshifted matrix $K$ without an additional hypothesis
\cite[\S5.2]{CCM-ZST-2025}. The prolate packet is a proposed trial
for the lowest vector, not an exact identification of that vector.
Reported near-zero evaluations of $\Q(f_0)$ and $\B(f_0,v)$ are
numerical checks only; the proof of radical membership is the cutoff
argument above.
\end{remark}
```

### P06a — groundstate.tex opening paragraph

Replace the opening paragraph before Theorem 4.1 by:

```latex
Since $f_0>0$, every compact smooth test is uniquely $g=f_0s$ with
$s\in C_c^\infty$. Suzuki describes the Weil form by the
distributional kernel $-g_{\rm scr}''(x-y)$
\cite[\S3.5]{Suzuki2023Screw}\cite[\S2.5]{Suzuki2026}; for complex
tests the associated double pairing includes
$\overline{v(x)}v(y)$. The following calculation is a ground-state
substitution in the algebraic sense of
\cite{FrankSeiringer2008}. Here $f_0$ is a radical vector and the
sign of the original form is not assumed. The result is a signed
difference-form identity, not a claim that the resulting form is a
nonnegative Markovian Dirichlet form.
```

### P06b — clarify the signed measure in Theorem 4.1

In the double-integral display replace the inner domain R by `\R\setminus\{0\}`. Immediately after (eq:nu), before the theorem ends, insert:

```latex
Here $\nu$ is a signed Radon measure on $(0,\infty)$ and
$\tilde\nu$ is its reflected extension on $\R\setminus\{0\}$.
The displayed integral means the sum of the density integral and the
atomic series; after multiplication by the difference energy it is
absolutely convergent. No locally finite extension of the positive
part through $t=0$ is asserted.
```

Retain the corrected symmetric pole step and the coefficient w_n in the proof. Replace the final convergence/numerical-check sentences of that proof by:

```latex
For convergence, $E_s(t)=O(t^2)$ at zero. If
$C_0(t)=\int f_0(x)f_0(x+t)dx$, then
$E_s(t)\le4\|s\|_\infty^2C_0(t)$ and
$C_0(t)\le e^{-|t|}\|e^{|x|}f_0\|_2^2$.
These bounds control the growing negative density and the atomic
series, since $\sum_n\Lam(n)n^{-3/2}<\infty$.
Thus all subtractions and symmetrisations above are justified.
```

### P06c — replace the density-novelty sentence

Replace `The density b is an elementary evaluation ... appear to be new` by:

```latex
The density is already determined by differentiating Suzuki's explicit
screw function \cite[(1.3)]{Suzuki2026}: away from zero, the second
derivative of its Lerch-series term is $a(t)$, the pole contribution
is $-2\cosh(t/2)$, and the prime hinges give the atoms $w_n$.
The following sign calculation is an elementary observation about
that known density, rather than a claim of a new distributional kernel.
```

In Lemma 4.2's proof append, after the cubic equation:

```latex
For $y>1$, $y^3-y-1$ is strictly increasing, is negative at $1$ and
tends to infinity. Since $b(t)$ has the opposite sign to this cubic,
the asserted strict sign alternatives follow.
```

### P06d — masses paragraph

Replace the paragraph immediately before (eq:masses) by:

```latex
Put $b_+(t)=\max(b(t),0)$, $b_-(t)=\max(-b(t),0)$ and
$C_0(t)=\int f_0(x)f_0(x+t)dx$. \Cref{fig:nu,fig:f0} illustrates
the density and canonical test. The negative part and atoms are
integrable against $C_0$, whereas the positive part has logarithmically
infinite mass at zero. In the following display the finite decimal
values are reported numerical approximations, not certified bounds;
the logarithmic coefficient is exact.
```

In (eq:masses) replace the equalities to `0.083642` and `0.037599` by `\approx`. Keep the exact asymptotic `\tfrac12\log(1/\eps)+O(1)`. Replace the following mass-comparison sentence by:

```latex
These reported masses do not decide \eqref{eq:DOM}, whose integrands
also contain the test-dependent differences. In particular, comparing
scalar masses cannot replace an inequality for every profile $s$.
```

### P06e — replace the Plane waves paragraph

```latex
\paragraph{Plane waves.}
For a fixed real $\xi$ take $s(x)=e^{i\xi x}$. Although $s$ is not
compactly supported, $f_0s$ and its first two derivatives obey the
same type of super-exponential estimates, so cutoffs extend both
\eqref{eq:GS} and \eqref{eq:EF} to this test. Thus
\[
 E_s(t)=2(1-\cos(\xi t))C_0(t),\qquad
 \sigma(\xi)=\Q(f_0e^{i\xi x})
 =A^{-2}\sum_{z\in Z(\Xi)}
      \overline{\Xi(\bar z-\xi)}\Xi(z-\xi).
\]
The sum is over the full zero multiset. For nonreal zeros its terms
are not nonnegative absolute squares. A computation using a finite
list of known zeros is a truncated diagnostic, not a verification of
the full identity or its sign. Even nonnegativity of every
$\sigma(\xi)$ would check only the diagonal of the two-frequency
kernel, not positivity of all its finite quadratic combinations.
```

### P07a — obstruction.tex opening, before Lemma 5.1

```latex
We consider minorants
$\int W(x)|(Ss)(x)|^2dx\le\Q(f_0s)$ imposed for every
$s\in C_c^\infty(\R;\C)$, where $S$ is one fixed finite sampling
stencil and $W$ is measurable and nonnegative. The conclusion below
also excludes countable sums of such nonnegative energies.
It does not exclude nonlocal positive factors or local inequalities
on a smaller class of tests.

In particular, the Sonin-space minorant of
\cite[Theorem 7.1]{Connes2026} is stated with restricted support and
additional transform conditions. The translated cutoff profiles used
in this section are not confined to that class. Our theorem therefore
neither contradicts that result nor proves that it cannot be localized.
The finite translate-independence argument below is self-contained;
it is not a solution of Bombieri's different, infinite zero-indexed
linear-independence question.
```

### P07b — Lemma 5.1 constant

Replace its displayed definition of C_q by the exact expression, with no numerical equality:

```latex
\begin{equation}\label{eq:budget}
 |\Q(f_0s_{q,R})|
 \le C_{\Xf}C_q^2e^{-2a_qe^{2R}},\qquad
 C_q^2=
 \frac{\frac{35}{3}M_0^2+\frac43(M_1^2+c_\chi^2M_0^2)}{2a_q},
 \quad c_\chi=2.
\end{equation}
```

In that block the source string `+\frac43` is intended in the numerator; the complete numerator is `(35/3)M0^2+(4/3)(M1^2+c_chi^2 M0^2)`. Use the exact M_j of P11. The existing proof of Lemma 5.1 then applies without an additional estimate.

### P07c — Corollary 5.5 title and scope sentence

Replace its optional title `[no sum-of-squares representation]` by:

```latex
[no countable finite-stencil sum of squares]
```

Keep its statement and bump proof, which already specify the finite-stencil family. Immediately after its proof insert:

```latex
This conclusion concerns the displayed class of nonnegative
finite-stencil energies. It is not a prohibition of nonlocal
sum-of-squares representations; \Cref{ex:control} illustrates the
distinction.
```

### P07d — replace Remark 5.6

```latex
\begin{remark}
The countable-family conclusion needs no uniform bound on stencil
size or diameter: each nonnegative summand is separately a minorant.
An integral over an uncountable parameter space would require joint
measurability and a measurable specification of the nonzero stencils
and their distinct sample points. We make no such extension here.
\end{remark}
```

### P07e — quantitative certificate paragraph

Replace the paragraph beginning `Quantitatively, if a proposed summand` up to its displayed inequality by:

```latex
Quantitatively, suppose a proposed nonzero stencil has $W>0$ on a
set of positive measure. The translate-independence argument implies
that for some rational $q$, $W|Sr_q|^2$ is positive on a set of
positive measure. By restricting this set to a bounded subset and
to a finite level of the integrand, choose a bounded measurable $E$
with $0<\eta:=\int_EW|Sr_q|^2dx<\infty$.
For $R$ covering $E+\{\tau_\ell\}$ the stencil has stabilized there.
If also
$e^{2R}>(2a_q)^{-1}\log(1+2C_{\Xf}C_q^2/\eta)$, then
```

Keep (eq:certkill) and the sentence distinguishing a negative certificate margin from a negative value of Q.

### P07f — replace Remark 5.10

```latex
\begin{remark}[pointwise comparisons]\label{rem:schur}
For a fixed compact smooth $s$, Taylor expansion and dominated
convergence give
\[
 E_s(t)=t^2\int f_0(x)^2|s'(x)|^2dx+o(t^2),\qquad
 \int_0^\delta b_+(t)E_s(t)dt
   =\frac{\delta^2}{4}\int f_0^2|s'|^2+o(\delta^2).
\]
Thus the infinite scalar mass of $b_+$ at zero cannot simply be
counted as an infinite positive energy for a fixed test. This
observation is not a theorem excluding all Schur-type or
pointwise-majorization arguments. Any such impossibility claim would
have to specify and analyze a class of comparison operators.
\end{remark}
```

### P08 — replace sections/windows.tex in full

```latex
\section{Finite windows: diagnostics and their limits}\label{sec:windows}

The following numbers reproduce reported high-precision computations.
They are not used in the analytic proofs. We do not supply here
end-to-end enclosures for matrix entries, omitted source tails,
eigenvalue isolation and every derived statistic. Accordingly all
printed numerical values in this section are interpreted as
approximations, not as certified bounds on a continuum infimum.

\begin{figure}[t]\centering
\includegraphics[width=.8\linewidth]{figures/fig3_window_bottoms.pdf}
\caption{Reported smallest eigenvalues of finite CCM compressions as
the Fourier cutoff $N$ increases, at $m=\lambda^2=13,23,43$.
The full carrier has $2N+1$ modes. The apparent finite-cutoff
stabilization is a numerical observation, not a proof of equality
with the continuum bottom.}\label{fig:bottoms}
\end{figure}

\paragraph{Finite bottoms.}
For the full compression $K(m,N)$, let $\lambda_1(m,N)$ be its least
eigenvalue. It is an upper bound for the normalized window infimum
$\mu_\lambda$ (\Cref{sec:setup}). The records associated with
\Cref{fig:bottoms} report stabilization near
$N^*/m\approx4.6,6.3,8$ and values approximately
$3.48\cdot10^{-59},1.8\cdot10^{-112},1.7\cdot10^{-220}$.
This does not prove convergence along a varying-window schedule or
provide a lower enclosure for $\mu_\lambda$.
The last printed value is about $46\%$ below $10^{-219.5}$, so it
does not support a claimed agreement within $20\%$.
No cross-implementation identity or asymptotic decay law is inferred
from this comparison.

\paragraph{Which trial is measured.}
The continuum prolate packet $k_\lambda$ of
\cite[\S7]{CCM-ZST-2025} is distinct from its finite projection.
Write $q_{m,N}$ for the unit coefficient row of the projected packet
in the same Fourier basis as $K(m,N)$, and $\xi_{m,N}$ for the unit
lowest row used in the finite computation. All overlaps below refer
to these two finite rows. For a row $v$ with $F_v(0)\ne0$, define
$\kappa(v)=-F_v''(0)/(2F_v(0))$ using its finite P59 transform.
We use
\[
 \kappa_\Xi=\tfrac12(\log\xi)''(\tfrac12)
 =\tfrac12\left[-8+\tfrac14\psi_{\rm d}'(\tfrac14)
                  +(\zeta'/\zeta)'(\tfrac12)\right]
 \approx0.0231049931,
\]
where $\psi_{\rm d}$ is the digamma function.
A formal continuum perturbation calculation suggests, for the
measured diagonal $N=m$, the conjecture
\begin{equation}\label{eq:trialjet}
 \kappa(q_{m,m})=\kappa_\Xi-\frac1{16\pi m}
                     -\frac{13}{256\pi^2m^2}+O(m^{-3}).
\end{equation}
We do not prove this expansion or the finite-projection error bound
needed to obtain it from a continuum calculation. A ratio to
$\Xi(z)/\Xi(0)$ is interpreted only near the nonzero anchor, not
across an unproved cancellation of all zeros of $\Xi$.

The reported values of
$a_m=m(\kappa_\Xi-\kappa(q_{m,m}))$ are
$0.020307,0.020123,0.020016,0.019957$ at $m=13,23,43,83$.
A least-squares fit $a_\infty+\beta_{\rm fit}/m$ gives approximately
$(0.019891,0.00540)$, compared with the proposed
$(1/(16\pi),13/(256\pi^2))\approx(0.019894,0.005145)$.
The discrepancy in the second coefficient is about $5\%$.
These rounded observations do not establish either coefficient or
the stated remainder. The $m=83$ datum concerns the trial coefficient
only and is not a row of \Cref{tab:jet}.

\begin{table}[t]\centering\small
\begin{tabular}{@{}rrrrrrr@{}}\toprule
$(m,N)$ & $T_{m,N}$ & $\kappa(\xi)-\kappa_\Xi$
 & $\kappa(q)-\kappa_\Xi$ & $\delta_{m,N}$
 & $\delta_{m,N}/T_{m,N}$ & $p_{m,N}$\\ \midrule
(13,13) & $1.234\cdot10^{-2}$ & $+2.791\cdot10^{-3}$ & $-1.562\cdot10^{-3}$ & $+4.353\cdot10^{-3}$ & 0.353 & $3.66\cdot10^{-3}$\\
(23,23) & $1.059\cdot10^{-2}$ & $+3.158\cdot10^{-3}$ & $-0.875\cdot10^{-3}$ & $+4.033\cdot10^{-3}$ & 0.381 & $2.98\cdot10^{-3}$\\
(43,43) & $8.236\cdot10^{-3}$ & $+2.738\cdot10^{-3}$ & $-0.466\cdot10^{-3}$ & $+3.204\cdot10^{-3}$ & 0.389 & $1.86\cdot10^{-3}$\\
(13,120) & $1.383\cdot10^{-3}$ & $-1.567\cdot10^{-3}$ & $-1.562\cdot10^{-3}$ & $-4.6\cdot10^{-6}$ & $-0.003$ & $4.69\cdot10^{-9}$\\
\bottomrule\end{tabular}
\caption{Reported rounded diagnostics, with
$\delta_{m,N}=\kappa(\xi_{m,N})-\kappa(q_{m,N})$,
$p_{m,N}=1-|\langle\xi_{m,N},q_{m,N}\rangle|^2$ and
$T_{m,N}=L^2(4\pi^2)^{-1}\sum_{k>N}k^{-2}$.
Rows with small nonzero $p$ are closely aligned directions, not equal
vectors. Small nonzero $\delta$ is not a vanishing theorem. Entries
are rounded separately.}\label{tab:jet}
\end{table}

\begin{figure}[t]\centering
\includegraphics[width=.6\linewidth]{figures/fig4_trial_jet.pdf}
\caption{Reported finite-trial second-jet coefficient $a_m$ against
$1/m$, compared with the conjectural expansion \eqref{eq:trialjet}.}
\label{fig:jet}\end{figure}

\paragraph{The relative statistic and the positivity boundary.}
On cells where $\lambda_1(m,N)>0$, the reported values approximately
$1.35$ and $1.33$ refer to
\[
 \frac{R_{m,N}(q_{m,N})}{\lambda_1(m,N)},\qquad
 R_{m,N}(q)=\frac{\langle q,K(m,N)q\rangle}{\langle q,q\rangle},
\]
at $(13,120)$ and $(23,160)$. They do not refer to
$\|\xi-q\|_2/\sqrt{\lambda_1}$, and they are not denoted by a
continuum-limit subscript. A ratio inequality cannot be multiplied
by an unknown-sign denominator to infer positivity.
If nonnegativity of the true window bottoms were independently
proved cofinally, CCM's monotonicity would imply nonnegativity on
every fixed smaller window and hence the Weil criterion. Proving
such a premise would be legitimate; assuming it would not be a
proof. The finite observations here establish neither that premise
nor a continuum saturation estimate.
```

### P09 — replace sections/ledger.tex in full

```latex
\section{Proved obstructions and the remaining question}\label{sec:ledger}

The proved exclusions in this paper have specific scopes.
\Cref{thm:nominorant,cor:noCSS} concern fixed finite sampling stencils
and nonnegative weighted energies required to work on the full
compact profile class. \Cref{prop:trade} excludes a fixed positive
margin in the ambient $\Xf$ norm on a dense linear span. Neither
result excludes nonlocal factors, restricted-class estimates,
cutoff-dependent approximate certificates, or coercivity in a
suitable quotient norm. \Cref{rem:schur} records a local asymptotic
observation, not a general Schur impossibility theorem.

Separate source estimates must be assessed on their actual errors.
In particular, the archimedean part satisfies the unconditional bound
$\D(g)-c_A\|g\|_2^2\ge-c_A\|g\|_2^2$; it is not unbounded below on
the unit sphere as the window grows. Replacing a discrete prime
measure by a continuous density changes the form, and is not the
same operation as replacing every $\Lam(n)$ by $1$. No exclusion of
all separate-estimate methods is proved here.

Checking the sign on plane waves does not check mixed-frequency
quadratic combinations. Likewise the de Bruijn--Newman flow, Jensen
polynomials and other equivalents have their own hypotheses and
scales. Their partial results are not used here to assert a universal
absence of margins or to rule out all possible imports into the
Weil-form problem.

\begin{problem}\label{prob:DOM}
Prove \eqref{eq:DOM} for every $s\in C_c^\infty(\R;\C)$.
\end{problem}

Two classes of approaches are not excluded. One is a nonlocal
positive factorisation of the full form, with its behavior on the
radical justified in the topology where it acts. The other is a
family of all-vector finite-matrix bounds
$K_m+e_mI\succeq0$ with independently proved $e_m\ge0$, $e_m\to0$,
together with recovery of every fixed compact test from the finite
windows. Neither approach is supplied by the present paper, and no
finite list of evaluated cells establishes its universal premise.
```

### P10 — replace sections/disclosure.tex in full

```latex
\section{Formalisation, provenance and tool disclosure}\label{sec:disclosure}

\paragraph{Machine-checked part.}
The file \texttt{NoFiniteStencilMinorant.lean} formalises the abstract
translate-independence and Fatou argument underlying
\Cref{thm:nominorant}. The concrete vanishing cutoff budget is an
explicit hypothesis of that theorem, not a formalised theorem about
the Weil form. \Cref{app:lean} states the interface precisely,
including the positive-part convention in the Lean inequality.
The recorded toolchain is Lean~4 \texttt{v4.26.0} with the project's
pinned Mathlib dependency \cite{Mathlib}; the five printed exports
are reported to have only \texttt{propext},
\texttt{Classical.choice} and \texttt{Quot.sound} as axioms.
This does not constitute a formalisation of
\Cref{thm:FPhi,lem:cutoffnorm,prop:radical,thm:GS,lem:budget}.
Those are paper arguments, with the explicit formula imported from
the literature. Other repository files concerning finite transforms
and matrices are companion work, not additional machine-checked
proofs of this paper's analytic statements.

\paragraph{Numerical part.}
The tables and figures reproduce reported computations, including
calculations using \texttt{arb} and \texttt{mpmath}. The use of an
interval-arithmetic library is distinguished from an end-to-end
certificate for a particular quantity. Such a certificate must
include input and truncation bounds as well as output intervals.
No omitted-tail certificate for the entire set of numerical claims
is supplied here, so the numerical material is diagnostic and is not
used to prove a theorem. Sums over a finite list of known zeta zeros
are not identified with complete zero-side sums.

\paragraph{Automated tools and responsibility.}
Large language models assisted with draft arguments, literature
searches, adversarial review and Lean proof scripts. Separate review
passes exposed errors and led to revisions. Numerical checks of
specific formulas and kernel checking of formal proofs are different
forms of validation; neither establishes all the unformalised
analytic claims. This disclosure follows the transparency and
responsibility principles of the Leiden Declaration
\cite{LeidenDeclaration2026}. The author is solely responsible for
the mathematical claims, the source attributions and the final text;
a model's output or another model's agreement is not a proof.

\paragraph{Relation to earlier work.}
No asserted proof of RH in the author's earlier work is a dependency
of this paper. The present structural results neither verify such a
proof nor show that every separate-estimate approach is impossible.
They stand only on the definitions, cited results and proofs given
here.
```

### P11 — replace sections/app_constants.tex in full

```latex
\section{Exact constants and approximate evaluations}\label{app:constants}

The constants used in proofs are defined exactly. Put
\[
 P_0(y)=4y^2-6y,\qquad
 P_{j+1}(y)=\tfrac12P_j(y)+2y(P_j'(y)-P_j(y)).
\]
Then
\[
 P_1(y)=-8y^3+30y^2-15y,\qquad
 P_2(y)=16y^4-112y^3+165y^2-\tfrac{75}{2}y.
\]
Writing $P_j(y)=\sum_r p_{j,r}y^r$, define
\[
 M_j=\frac{\pi^{-1/4}}{A(1-e^{-3\pi/2})}
       \sum_r|p_{j,r}|
       \left(\frac{2(r+1/4)}{e}\right)^{r+1/4},
 \qquad j=0,1,2.
\]
For $x\ge0$, let $y_n=\pi n^2e^{2x}$. Direct differentiation gives
\[
 \Phi^{(j)}(x)=\pi^{-1/4}\sum_{n\ge1}
             n^{-1/2}y_n^{1/4}P_j(y_n)e^{-y_n}.
\]
For each monomial,
$y^{r+1/4}e^{-y/2}\le[2(r+1/4)/e]^{r+1/4}$.
The other half of the Gaussian obeys
\[
 e^{-y_n/2}\le e^{-(\pi/2)e^{2x}}e^{-(\pi/2)(n^2-1)},
 \qquad n^2-1\ge3(n-1).
\]
Sum the geometric majorant and use evenness, with the corresponding
parity for derivatives. This proves
$|\Phi^{(j)}(x)|\le AM_j e^{-(\pi/2)e^{2|x|}}$.
No rounded evaluation of $A$ is needed for this bound.

The exact cutoff constants are $c_\chi=2$, $c_\chi'=8$, and the exact
budget constant is the symbolic $C_q$ in \eqref{eq:budget}.
For orientation only, inserting the reported approximation of $A$
into the exact expressions gives
$M_0\approx23.90998$, $M_1\approx325.42532$ and
$M_2\approx6011.82221$. These decimals are not definitions or
outward-rounded certificates.

\begin{center}\small
\begin{tabular}{@{}lll@{}}\toprule
quantity & approximate value & exact definition or role\\ \midrule
$A$ & $0.565466013092$ & $\|\Phi\|_2$\\
$\int f_0$ & $0.8791346724$ & $\Xi(0)/A$\\
$c_A$ & $5.3721834192$ & $\gamma+\log(8\pi)+\pi/2$\\
$\pl$ & $1.3247179572$ & unique root $>1$ of $y^3-y-1$\\
$t_0$ & $0.2811995743$ & $\log\pl$\\
$N_-$ & $0.083642$ & reported mass in \eqref{eq:masses}\\
$\sum_nw_nC_0(\log n)$ & $0.037599$ & reported atomic mass\\
$\kappa_\Xi$ & $0.0231049931$ & $\tfrac12(\log\xi)''(1/2)$\\
$1/(16\pi)$ & $0.0198944$ & conjectural leading coefficient\\
$13/(256\pi^2)$ & $0.0051452$ & conjectural second coefficient\\
fit $(a_\infty,\beta_{\rm fit})$ & $(0.019891,0.00540)$ & four reported cells\\
\bottomrule\end{tabular}
\end{center}
The table distinguishes numerical evaluations from proof constants.
In particular no numerical residual on a truncated zero sum is used
as an error bound for \eqref{eq:EF}.
```

### P12 — replace sections/app_lean.tex in full

```latex
\section{The formalised abstract interface}\label{app:lean}

The relevant source is \texttt{NoFiniteStencilMinorant.lean} in
\texttt{Q3/Proofs/RouteB/}, in repository \texttt{Malaeu/chen\_q3},
at the manuscript source revision \texttt{0f9c7cbc81bb}.
Its Git blob begins \texttt{e6fd9dc2f713}.
The following five exports are printed in the file's axiom audit:
\begin{itemize}[leftmargin=2em]
\item \texttt{independence\_of\_translates};
\item \texttt{independence\_of\_translates\_apply};
\item \texttt{stencil\_energy\_limit\_eq\_zero};
\item \texttt{no\_positive\_finite\_stencil\_minorant};
\item \texttt{no\_positive\_finite\_stencil\_minorant\_hypotheses\_satisfiable}.
\end{itemize}
Five is the number of these audited exports, not the number of all
helper declarations. The proof includes real and complex analysis,
Fourier integrals, Fatou's lemma and almost-everywhere reasoning as
well as finite Vandermonde algebra.

In the principal theorem, $f:\R\to\R$ is continuous, integrable and
strictly positive; $Q:(\R\to\C)\to\R$ is arbitrary; the cutoffs are
measurable and equal to $1$ on $[-R,R]$; the real coefficient stencil
is nonzero and its shifts are distinct. The weight $W$ takes values
in the extended nonnegative reals. With
$r_q(x)=f(x-q)/f(x)$, the hypotheses are:
\[
 \text{(H1)}\quad Q(f\chi_Rr_q)\longrightarrow0
       \quad\text{for every rational }q,
\]
\[
 \text{(H2)}\quad
 \int W|S(\chi_Rr_q)|^2
       \le\max\{Q(f\chi_Rr_q),0\}
       \quad(q\in\mathbb Q,\ R\ge1),
\]
where the integral and inequality in (H2) are represented in
$[0,\infty]$. In Lean the right-hand side is
\texttt{ENNReal.ofReal}. The conclusion is $W=0$ almost everywhere.
The real-valued minorant inequality in \Cref{thm:nominorant} implies
this formal hypothesis, but is not literally the same expression.
For the concrete Weil application (H1) is supplied by the paper
proof of \Cref{lem:budget}, not by this Lean file.

The independence result allows complex coefficients and proves the
finite exponential-polynomial step by sampling and a Vandermonde
matrix. The nonvacuity export uses a Gaussian, the zero functional
and zero weight; it is not a nonzero Weil certificate. The recorded
axiom profiles of the five exports are
\texttt{[propext, Classical.choice, Quot.sound]}.
No claim is made that the explicit formula, the canonical analytic
test, its concrete cutoff budget or the ground-state identity has
been formalised by these exports. Companion matrix and transform
files are outside this paper's formal theorem claim.
```

### P13 — bibliography and citation edits

Add these verified records to references.bib:

```bibtex
@article{Suzuki2023Screw,
  author = {Suzuki, Masatoshi},
  title = {Aspects of the screw function corresponding to the {R}iemann zeta-function},
  journal = {Journal of the London Mathematical Society},
  volume = {108},
  number = {4},
  pages = {1448--1487},
  year = {2023},
  doi = {10.1112/jlms.12785},
  note = {arXiv:2206.03682v4}
}
@misc{LeidenDeclaration2026,
  title = {Leiden Declaration on Artificial Intelligence and Mathematics},
  year = {2026},
  howpublished = {Community declaration, 2 June 2026},
  doi = {10.5281/zenodo.20302944}
}
```

The existing `Suzuki2025` key continues to denote the Hilbert-space article; do not globally replace it by the new screw-function key. P02 and P06 place the corrected section citation explicitly. Retain Frank-Seiringer as background to the method; its verified article is JFA 255 (2008), 3407-3430, DOI 10.1016/j.jfa.2008.05.015. Bibliographic completion of those fields is optional, not a mathematical dependency.

The replacements remove the unsupported use of the old author preprint and the blanket Newman/Nicolas/GORZ comparisons. BibTeX will not print uncited entries in the present setup; do not introduce a nocite-all command to preserve decorative references. The proof uses neither Freedman's nor Groskin's unrefereed claims; their related-work status is explicit. No unverified new citation is required to apply the repair.

## 5. Remaining checks, non-overclaim boundary, and one directive

All required text-level defects above have replacements. In P07b, use the ordinary LaTeX numerator exactly as stated: the string is `(35/3)M_0^2+(4/3)(M_1^2+c_chi^2 M0^2)`; do not preserve the old decimal equality. This review has not built the patched source. A source build and visual check are ordinary integration gates, not additional mathematical assumptions.

**One directive:** apply P01-P13 to a working copy of the pinned paper, preserving theorem labels and the owner's sole authorship; build; read the paper once with the severity table; return only the changed source list, build output, unresolved-reference report, and a check that every displayed finite number is now labeled diagnostic unless accompanied by its actual enclosure. Do not edit the Lean source or reopen the RH route.

Suggested integration commands, not executed by this judge:

```text
WORKDIR: paper_weil
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
  bibtex main
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

No new Lean gate applies to this documentation-only verdict. An optional independent rerun of the existing L-stencil file should print each of the five named exports, not merely the last theorem. It must not be represented as verification of the concrete paper lemmas.

Two alternatives remain if the integration review finds the numerical section distracting: retain P08's explicitly diagnostic section, or delete its figures/table and retain only its object and positivity-boundary paragraphs. The former has higher reproducibility cost and preserves empirical context; the latter is cheaper and gives a cleaner structural note. Neither changes the mathematical result or authorizes a new numerical run. This is an editorial alternative, not an unresolved proof branch.

## 6. Prediction scoring and independent-check registration

Frozen observer wording and probabilities are preserved:

| Prediction | p | Fate | Basis |
|---|---:|---|---|
| P_CLEAN_NO_CRITICAL | 0.75 | CONFIRMED | No false central theorem or unrepairable central proof found. Repairable invalid proof estimates and false surrounding prose are itemized, not ignored. |
| P_CLEAN_HIGH_LE_2 | 0.55 | REFUTED | Nine independent HIGH root causes. |
| P_CLEAN_PRIORITY_HIT | 0.35 | CONFIRMED_WITH_SCOPE | The advertised new density component of N1 follows explicitly from Suzuki (1.3), and the correct 2023 section was missed. No prior theorem for the full N3 formulation is asserted. |
| P_CLEAN_ARXIV_READY_AFTER_FIXES | 0.60 | CONFIRMED | RESULT=READY_AFTER_LISTED_FIXES, conditional on actually applying the printed replacements and ordinary build/read-through. |
| P_CLEAN_LEMMA_3_3_OR_4_1_FIX | 0.45 | CONFIRMED | Lemma 3.3 is replaced with explicit R>=0, exact majorants and the cutoff estimates. The substantive pole/prime calculation of Theorem 4.1 survives. |

No blind probability was registered by this judge before the checks in this pass. The following are **new predictions for future independent checks**, not retroactive scores:

```yaml
P_PAPERCLEAN_INDEPENDENT_GS_FACTORS_SURVIVE:
  probability: 0.97
  test: independently_expand_polarized_pole_and_prime_terms_on_complex_two_bump_profiles
  fate: PENDING
P_PAPERCLEAN_INDEPENDENT_CUTOFF_AND_CONVOLUTION_BOUNDS_SURVIVE:
  probability: 0.94
  test: verify_symbolic_Mj_R_nonnegative_integrals_and_support_radius_exponent
  fate: PENDING
P_PAPERCLEAN_ABSTRACT_STENCIL_APPLICATION_SURVIVES:
  probability: 0.97
  test: match_paper_minorant_to_Lean_positive_part_H2_and_recheck_countable_null_sets
  fate: PENDING
P_PAPERCLEAN_PATCHED_TEX_BUILDS_WITHOUT_UNDEFINED_REFERENCES:
  probability: 0.85
  test: apply_nonoverlapping_replacement_blocks_and_run_four_build_commands
  fate: PENDING
```

A numerical zero residual remains a diagnostic. The discriminators for actual analytic defects are an incorrect exact coefficient, a failed integrable majorant, or an illegal quantifier/domain transfer. These must not be scored from a fit or an agent's confidence.

## 7. K8A and closeout

**Downstream consumer:** the owner's v3 manuscript as a publishable structural paper, not a route-promotion or RH theorem.

**Actual requirement:** correct proofs, precise scope, fair priority, reproducible epistemic labels and paste-ready repairs. **Original requested object:** all-v3 hostile cleanup. **Original object necessity:** the correctness and scope checks are necessary; retaining all numerical narrative and broad proof-strategy claims is not.

**Weaker acceptable interface:** the same core results with the diagnostic section trimmed and unsupported priority/no-go claims removed. **Failure type:** proof-estimate and scope/attribution defects, not evidence against the main canonical-test or stencil statements. **Epistemic status:** repaired paper arguments; raw numerical certification remains unverified and is no longer claimed in the repaired text. **Novelty axis:** a concrete radical application of an abstract global finite-stencil obstruction, not discovery of the Weil kernel. **Reopen trigger:** an independent counterexample to a patched statement, a failure in the cutoff/EF extension, or prior art establishing the exact general no-stencil theorem.

No route-family kill is made. The rejected theorem shapes are the unqualified no-SOS/localization conclusions and the unproved universal majorization claim. The explicit positive rank-one control and the distinct restricted Sonin domain explain their scope failures. No negative value of the genuine Weil form has been established.

**What became smaller?** The publication claim is reduced to what the proofs actually deliver. **What was removed?** False basis/statistic identifications, broad local/SOS/Schur prohibitions, and unsupported certification and priority claims. **What must not recur?** Carrying a scalar factor or a function-space domain through a change of object without proof; replacing an exact bound by a rounded equality; or treating a theorem on all compact tests as one on a restricted support class.

**Next decisive check:** independent verification of P04b-c and P06's polarized algebra, followed by the patched LaTeX build. **Progress class:** FALSIFICATION_PROGRESS. **Cognitive operator:** COUNTEREXAMPLE_HUNT. **Route score:** 4. **Analytic supplier count change:** zero.

```yaml
iteration:
  target: REQ-2026-09-05-PAPERCLEAN
  status: PROGRESS
  failed_strategy: declaring_v3_clean_from_two_referees_and_a_style_pass
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  invariant_learned: global_test_quantifiers_and_actual_numeric_objects_must_match_every_summary
  forbidden_future_move: promoting_restricted_prior_art_or_rounded_constants_into_global_exact_claims
  next_decisive_test: independent_patch_proof_check_then_manuscript_build
```

## 8. Primary-source and write receipt notes

Primary texts checked for load-bearing external facts include CCM, arXiv:2511.22755v1, sections 2-3 and 5-8; Suzuki, arXiv:2606.09096v2, (1.3) and section 2.5; Suzuki, arXiv:2206.03682v4, section 3.5 and its published JLMS record; and Suzuki, arXiv:2301.00421v3 for the Hilbert-space distinction. The relevant Suzuki and Connes PDF formulas were visually inspected. Connes, arXiv:2602.04022, Theorem 7.1, supplies the restricted Sonin comparison; Frank-Seiringer, arXiv:0803.0503, supplies methodological background. Riemann/Phi_P normalization was cross-checked with Rodgers-Tao 1801.05914 and Polymath15 1904.12438. The new bibliography entries have verified arXiv/publisher or official Declaration records. Recent related preprints were checked for existence and their stated claims, not accepted as certified mathematics. Journal-scope statements were checked against the publishers' aims-and-scope material.

The original Bombieri and Yoshida complete scans, all numerical certificates, the thirteen-file build as a whole, and the manuscript's figure assets were not independently reverified. These limits are reflected in the replacements rather than hidden by an unconditional endorsement.

Only the expected new verdict path is written, on rh_clean with a [Proshka] commit prefix. The request hash was independently recomputed from the fetched UTF-8 text, including its final LF. Read the verdict back at the returned commit and compare the changed-file list before intake. Its own commit SHA is returned in the delivery receipt, not embedded recursively in this file. The source manuscript, previous reports, queue, route state and Lean files remain untouched by this adjudication.

## 9. Dated integration addendum — 2026-09-05, before delivery

This addendum completes the literal application of F02, F04, F17 and F20 after reading the replacement anchors back against v3. The earlier verdict, probabilities and finding classification stand. Apply P14 in addition to P01-P13. These clauses specify deletions that must not survive a partial edit; they do not introduce a new analytic hypothesis or change the readiness decision.

### P14a — replace the entire (eq:masses) display

The old second equality `=1.1513 log_10(1/eps)+O(1)` is not an exact asymptotic: a nonzero error in the logarithmic coefficient cannot be absorbed into O(1). This is another instance of F02, not a new counted root cause. Replace the whole equation environment by:

```latex
\begin{equation}\label{eq:masses}
\begin{aligned}
 N_-&=\int_{t_0}^\infty b_-(t)C_0(t)dt\approx0.083642,\qquad
 \sum_{n\ge2}w_nC_0(\log n)\approx0.037599,\\
 \int_\eps^{t_0}b_+(t)C_0(t)dt
 &=\tfrac12\log(1/\eps)+O(1)
  =\frac{\log10}{2}\log_{10}(1/\eps)+O(1)
   \qquad(\eps\downarrow0).
\end{aligned}
\end{equation}
```

The coefficient is exactly `(log 10)/2`; its optional numerical evaluation is only approximately 1.1512925465. Similarly, in Lemma 4.2 replace the sentence beginning `Thus t_0=...` by:

```latex
Thus $t_0=\log\pl\approx0.2811995743$. Since $1<\pl<2$,
every prime-power distance $\log n\ge\log2$ lies strictly beyond
$t_0$, where the continuous density is negative.
```

### P14b — remove the residual full-line measure wording

P06b's insertion must not coexist with the old sentence `where tilde nu is the even extension to R of the signed measure`. Replace that sentence, immediately before (eq:nu), by:

```latex
where $\tilde\nu$ is obtained by reflection from the following
signed Radon measure on $(0,\infty)$:
```

Keep P06b's punctured-line integral and its absolute-convergence definition. This resolves F04 without asserting a signed measure with locally finite mass at the origin.

### P14c — the hypothesis concerns all rational translates

Replace the paragraph immediately before Theorem 5.3, beginning `The theorem is best stated in the generality`, by:

```latex
The theorem is stated in an abstract form. Its analytic input is a
positive continuous integrable function together with vanishing
functional values on compact cutoffs of every rational translate.
No positivity or quadratic-form property of the functional is
assumed. The formal version uses a slightly weaker positive-part
minorant hypothesis, as explained in \Cref{app:lean}.
```

In Example 5.7, immediately before its final sentence `Its positive factor is a global integral`, insert:

```latex
For each fixed $q$, dominated convergence gives
$\int\chi_R(x)F(x-q)e^{-i\omega x}dx
 \to e^{-i\omega q}\widehat F(\omega)=0$.
Thus its translated cutoff values satisfy the hypothesis of
\Cref{thm:nominorant}.
```

### P14d — do not re-import the discarded coercivity/finite-window comparison

Replace the full paragraph following the proof of Proposition 5.9, beginning `For proof design this means`, by:

```latex
This excludes a fixed positive margin in the specified ambient
$\Xf$ norm on a dense span. It does not exclude coercivity in a
quotient norm, a margin depending on the window, or a sequence of
vanishing error bounds. Finite eigenvalue observations are not used
in this argument and are not a quantitative version of its
$\Xf$-norm conclusion.
```

The title and proof of Proposition 5.9 remain unchanged. No conclusion about a quotient or about the sign of the Weil form is added.

### Integration consistency note

The actual v3 preamble defines the `problem` environment and all macros used by these replacements. Existing cross-referenced theorem labels were checked against `groundstate.tex` and `obstruction.tex`; the new `prob:DOM` in the fully replaced ledger is a new local label. Keep `sec:gs` on the unchanged groundstate section. All previous prediction probabilities and fates remain exactly as registered above; the added clauses are part of the required patch set for READY_AFTER_LISTED_FIXES.
