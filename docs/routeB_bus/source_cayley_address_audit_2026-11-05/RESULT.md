# Source Cayley address audit

Route B = CHALLENGER / NOT_RH. DIAG only, not interval-certified.

**All fixed numerical gates pass at45 and70dps, in both the independent implementation and the unmodified Appendix A replay.** No `DIAG_FORMULA_OR_NORMALIZATION_FAILURE` occurred. The audit confirms computability and the direction of this finite off-axis discriminator only. It is **not** a positive Frobenius for ℚ, a cofinal floor, a threshold law m(β), or an RH claim.

## Gate table

The table gives worst errors over both published replays; each precision retains its original tolerance. All four DH addresses and the plant were tested at both ε values. The independent implementation additionally tests ζ and the curve at the planted complex points, which Appendix A does not serialize.

| Gate |45dps|70dps|
|---|---:|---:|
|2ε<positive DH/plant defect<6ε|PASS|PASS|
|each ratio approaches1 as ε shrinks|PASS|PASS|
|real-axis unitarity error, DH/plant|≤4.080e−43 <1e−30|≤4.963e−69 <1e−50|
|DH functional-equation relative error|≤3.944e−43 <1e−30|≤1.911e−68 <1e−50|
|ζ and E/F₃ defects at the same complex points|nonpositive|nonpositive|
|direct Cayley defect vs(7.7), maximum absolute error|≤2.888e−46|≤3.333e−71|

The explicit gate layer checks288 scalar assertions; all pass. GATE_TABLE.csv records every point, precision, both compared quantities and tolerance. GATES.json preserves gate details and zero failures. Successful process exit of Appendix A alone was not counted as passing these assertions: the appendix computes values but does not enforce the registered inequalities itself.

## Ratio deviations

For each ε, the maximum below is over all four DH addresses and the planted quartet. Both implementations agree at the displayed precision. The worst case is the DH address γ=166.479305913168… at both ε values.

| ε | max absolute ratio deviation,45dps |70dps|
|---:|---:|---:|
|10⁻³|0.00892703537511394774|0.00892703537511394774|
|10⁻⁴|0.000881757724770636929|0.000881757724770636929|

Every individual address improves, not just the maximum. RATIO_DEVIATIONS.csv gives each backend/precision maximum. Full direct defects, M,S and identity right sides are retained in INDEPENDENT_RESULTS.json; APPENDIX_REPLAY.json is the unmodified script's raw output.

The independent program uses the Hurwitz combination H(s) and its analytic derivative H′(s), then D′/D=H′/H−log5. The appendix instead uses numerical differentiation mp.diff(dh,s). Both include the DH conductor5 and odd Gamma factor and **no ζ pole**. The ζ control uses the full mpmath ζ logarithmic derivative in(7.1), including pole and Gamma terms; no truncated Euler product is used. The curve uses M_E=log3·tan(log3·z). The planted source adds all four logarithmic poles to Xi with the correct minus sign in M.

For clarity about coordinates: the refined upper s-plane zero is ρ=β+iγ. The positive address w=γ+i(β−1/2) maps under s=1/2−iz to its conjugate β−iγ, also a DH zero by real-type symmetry. This conjugation is explicit; the sign is not silently reversed.

## Independent versus Appendix A

All88 common physical mathematical fields agree within the preregistered scaled tolerance1e−29. The maximum scaled difference is **4.926e−32**, consistent with Appendix A's32-significant-digit serialization. Compared fields are refined β,γ, DH/plant defects, ratios and the available ζ/curve defects. REPLAY_COMPARISON.csv contains both sides and differences. Root residuals and arithmetic-error diagnostics are retained as numerical diagnostics; unitarity, functional-equation and identity errors are tested against their actual fixed gates rather than required to have identical roundoff. Elapsed time is excluded.

The independent implementation completed in about3.76s; the published Appendix A receipt reports6.66s. Both use mpmath1.3.0, so this is an independently written implementation, not an independent arithmetic backend or an interval proof. The near-zero residuals do not certify root existence, uniqueness or multiplicity. The ratio4ε is the registered simple-zero finite test.

## Saved address-match table

Each cell shows **j0 : saved event j indices**, where j0=round(γlogm/(2π)); “—” means no saved event among the valid j0−1,j0,j0+1, and “out” means none of those indices lies in1…m. This uses exactly the requested integer-neighbor rule; it is not a new continuous-distance threshold.

| address γ |74|75|206|207|621|622|2000|
|---:|---|---|---|---|---|---|---|
|85.6993484854|59 : —|59 : 58|73 : —|73 : 72|88 : 87|88 : 87|104 : 103|
|114.1633427308|out (78)|out (78)|97 : —|97 : —|117 : —|117 : 116|138 : 139|
|240.4046723514|out (165)|out (165)|204 : —|204 : 205|246 : 247|246 : 247|291 : 290|
|166.4793059132|out (114)|out (114)|141 : —|141 : —|170 : —|170 : —|201 : —|

The complete28summary cells and66valid neighbor rows are in ADDRESS_TABLE.csv, ADDRESS_MATCHES.json and ADDRESS_NEIGHBORS.csv. Each saved hit retains its original diagonal/minor flags and margins, plus the saved nearest-zero fields; non-events retain **no fabricated margins**. The event definition in the saved screen is Ajj<0 OR a failed corner-sharing minor. It is not the same as requiring a positive raw Schur ratio to exceed1.

Only the pinned18,811-row event CSV and its saved SUMMARY were read. Its Git blob and count were checked before lookup; no source matrix, selected-entry formula or eigensystem was recomputed. Absence means no row in that frozen failure-event table, under the saved screen's declared completeness. The numerical DH census is inherited NUMERICAL_NOT_CERTIFIED data, not newly certified here.

The selected transitions reproduce the85.699 address hit at75, the240.405 hit at207, and the114.163 hit at622. The166.479 address has no selected saved hit even at2000, despite its off-axis Cayley defect passing the same positive gate. The85.699 address has no hit at206 but does at207, so these particular event matches must not be read as monotone persistence after a first m. No individual zero's causal contribution is identified.

## Registration, scores and execution chronology

PREDICTIONS.md copies the verdict's registered threshold line and threshold paragraph verbatim, and adds C1–C4 with probabilities. It was committed before numerical runs in immutable object **a1919fbf165da30b9cc4cbd2575a6f43be5fb6ed**, without moving rh_clean. The final branch delivery carries the same prediction blob. The upstream registration/design SHA256 identifiers are preserved exactly as declared in the pinned YAML; their preimages were not independently reconstructed.

C1(.95), C2(.90), C3(.95) and C4(.85) all PASS_DIAGNOSTIC. C4 is the narrowly registered saved-row prediction:3of4addresses have a selected hit at m2000. It is not a new statistical or spectral law.

An initial Appendix A launch started prematurely in parallel. Its result was quarantined, not sent to the independent implementer and not used for any comparison or design choice. The published receipt comes only from the repeat after independent.py was frozen and its run completed. APPENDIX_REPLAY.md records that ordering correction and the unchanged executable hash. Thresholds, seeds, precision settings and formulas in the appendix were never edited.

INPUTS.json pins the verdict, census, saved event table, saved report/SUMMARY and the unexecuted analytic-source reference. FORMULA_REVIEW.md records a bounded independent read-only formula/implementation review. The audit supplies no positive ℚ Frobenius, no cofinal floor, no threshold law m(β), no route-state change and no RH export.
