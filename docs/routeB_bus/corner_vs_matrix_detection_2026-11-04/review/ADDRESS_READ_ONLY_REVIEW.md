# Independent B++ address review

**Verdict: PASS for the finite address diagnostic payload bound below; no blocking finding.** CHALLENGER_NOT_RH; PX_RH_CLAIM: NOT_MADE; D0 unchanged. This review does not certify zero-census completeness, every numerical strict sign, a mathematical detector law, remote Git history, or publication.

Exact address-payload binding: `ADDRESS_REVIEWED_PAYLOAD.json`, 26 file rows, SHA-256 `680285a52603effc2648b1551fad9693b73039f31859e633472cb240e4ce1aef`. It includes address source/inputs/outputs, current root preregistration and receipt, the historical predictions resolver, and root README. It excludes review artifacts, SHA256SUMS and interpreter caches. Address RESULT.md is SHA-256 `eae0a9ac4140d12f56d9af6fb2ac7eeef1a2e1a328c7a140dfe75ad5b61e7507`; address_probe.py is SHA-256 `b41779f63e72ec4328c6875b636eb180a875ff5a43bd504de4f7855d29a04b41`.

## Historical review and preregistration

The original `FINAL_READ_ONLY_REVIEW.md` and `FINAL_REVIEWED_PAYLOAD.json` remain unchanged historical records. Independent comparison found exactly one changed path among their 282 bindings: root PREDICTIONS.md, which received the preregistered append. Its exact previously reviewed bytes, SHA-256 `3469417703b775a3b758173a7521511ef8cea480e030b76eb04bf622a65333e1`, are preserved in `producer_history/PREDICTIONS_before_address.md`. All other main/B+ bound files, including RESULT.md and analyze_results.py, remain unchanged.

Current PREDICTIONS.md matches the address pre-run receipt hash. The parent-supplied preregistration commit is `5500edb57a9f8963de4f721e2cba4b2b371f06a4`; remote push chronology is not independently established by this reviewer. All eight transported address input files match both SHA-256 and Git blob identities in inputs/SOURCE_PINS.json, including the numerical zero census blob `35396541cbc976d0dc8a1c76bf45802c8602bb84`.

## Source and statistical-method inspection

The producer loads the original calc/trigamma AST function bodies, changing only the final return to expose existing intermediates. The DH arithmetic operations, coefficient source and selected-entry formulas are retained. Every integer m=2..2000 is count-gated against the saved dense screen before scoring. There are no new eigenproblems. Event definition is the strict union Ajj<0 OR determinant<0, unique per (m,j), with both flags and raw margins retained. A00 is checked separately.

Nearest-address distances divide absolute frequency difference by the actual grid step 2*pi/log(m). Off-line beta is sigma_right, while beta-1/2 is separately recorded. The source census is explicitly numerical and bounded at 900. Both all-event census statistics and the omega<=900 subset are reported. Upper-edge flags correctly identify when an unseen zero above 900 might change a nearest address.

AD2 implements the preregistered conjunction of off-line hit rate at least on-line hit rate and off-line median no larger than on-line median. Its paired closer fraction is also retained. The lower weighted empirical median convention is explicitly documented in the final report; this resolves the initial wording concern about the even-sample median convention.

The PCG64 control uses the fixed seed and 1000 draws per event m, reweighted by that m's event count. The zeta control uses exactly 20 original physical diagonals per event m, allows j=0, and preserves both equal-m and event-count weighting. Both use the same DH census. The report explains the different frequency distributions of these controls. Fresh control validation and the three selected 320-bit example confirmations are limited to their actual scopes.

Per-pair first detection tests ANY event mode within one step of that pair, independently of nearest-neighbor assignment. Separate diagonal/minor firsts and seven right-censored pairs are retained. AD3 uses only the 19 observed pairs for its primary statistic. The 2001 substitution and height-adjusted partial-rank calculation are explicitly sensitivity diagnostics. The descriptive p-value is not presented as evidence from independent samples or a significant law.

## Independent saved-data verification

No source matrices, selected-entry screen or eigenproblems were rerun by this reviewer. Cheap independent checks used the saved rows, input hashes, NumPy/SciPy statistics and deterministic random-frequency regeneration.

- Checked every one of the 18,811 event identities for uniqueness, strict event flags, frequency/bin, nearest identities and distances, beta/displacement and both census flags.
- Checked all 1999 count-gate rows against saved dense counts and event flags, with A00 nonnegative. The union contains 18,799 overlapping events and 12 minor-only events, with no diagonal-only event, on 1828 distinct m.
- Independently recomputed all 26 pair firsts and separate diagonal/minor firsts from the complete event table. Observed/censored counts are 19/7. Primary Spearman correlation is exactly -0.32280701754385965; the all-pair 2001 sensitivity is exactly -0.7114588441306405.
- Regenerated all 1,828,000 PCG64 frequency draws using an independent sorted-zero binary-search nearest-distance calculation. Every per-m hit fraction agrees. Global event-weighted rates and medians agree with SUMMARY.json to at most 1.2e-16, using integer-scaled event weights for an independent weighted-quantile check.
- Checked all 36,560 zeta-control rows for per-m count, frequency, event weight and census distances. Equal-m and event-weighted hit rates/medians match the summary.

The resulting AD1 all-event hit rate is 0.6819945776407421; the in-range rate is 0.8487033606774279. Both fail 0.90. AD2's stated comparison passes both overall and in range. AD3 has the predicted negative sign only as the declared observed-pair statistic. The report accurately retains the failures, censoring, dependence and numerical limitations.

## Post-run censor-bound review

CENSOR_BOUND.json is correctly labelled a posthoc deterministic bound, not a replacement preregistered test. There are 15,116 in-range events with 12,829 known one-step off-line hits and 3695 events above 900. No in-range event has an off-line nearest-address upper-census ambiguity. As an additional direct check, every in-range nonhit is more than 9.697 frequency steps below the height-900 boundary, so a zero strictly above 900 cannot make it a one-step hit.

Consequently, conditional on completeness of the supplied census below 900, granting a hit to every event above 900 gives the valid optimistic bound (12,829+3695)/18,811 = 0.8784221997767264 < 0.90. This arithmetic strengthens the finite AD1 failure against missing higher zeros without certifying the sub900 census. RESULT.md states this condition explicitly.

The owner-example narrative is also accurate: (m,j)=(463,234) is closer to the supplied on-line zero than to its off-line address. Its negative minor cannot be used alone as exclusive off-line attribution. The final address narrative and root index keep this lane separate from the unchanged main/B+ conclusions and make no proof or route-state promotion.
