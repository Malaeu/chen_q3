# Final independent read-only diagnostic review

**Verdict: PASS for the finite diagnostic payload identified below; no outstanding blocking finding.** This is review of source formulas, numerical methods, saved evidence, scoring and reporting. It is not proof admission, an interval certificate, a cofinal positivity claim, a route promotion, or a Git publication receipt. Route B remains CHALLENGER_NOT_RH; PX_RH_CLAIM: NOT_MADE. D0 is unchanged.

The reviewed payload is bound by all 282 file rows in `FINAL_REVIEWED_PAYLOAD.json`, SHA-256 `9857e827cc7618e3b8e198bfff16528434f6694d17a31670bff3b6113ef0aa34`. The manifest excludes review artifacts, the subsequently generated SHA256SUMS, and interpreter caches. RESULT.md is SHA-256 `1aed981043ac406d1ca76e3d469556ad6759a3bf877cf262dea01240db3b221e`; analyze_results.py is SHA-256 `6fd7a87ea2b8bebdcd3424c8b829bfc29caf0574aafcfc9d00cf483c05256683`. A change to a bound file requires review of the change and a refreshed binding; adding publication inventory outside this manifest does not assert it was independently reviewed here.

## Findings and their disposition

The initial read-only report correctly identified that the original admission-only matrix stage plus sparse checkpoints could not establish later first thresholds. The completed matrix_prefix.py visits every integer through each case's first strict trigger; independently checking its saved data found 390 relevant parameter/integer rows with no missing predecessor or earlier trigger. This resolves the initial finding. The selective continuation retains all admissible a=0 controls and every requested unresolved positive pair; later checkpoint calls restore the complete admissible grid.

A subsequent review found the preregistered fresh predecessor recheck missing. It is now present in recheck_predecessors.py and predecessor_recheck.json: all nine later-than-admission thresholds have freshly reconstructed predecessors above or equal to -1e-6. Differences from saved minima are at roundoff scale. The receipt explicitly limits this check to floating-point ordering. This resolves the subsequent finding.

No tolerance, source normalization, cutoff, frequency criterion or K scoring rule was changed to hide an unfavorable result. Initial float-control failure and the bounded-prefix cap remain preserved history.

## Source, normalization and witness review

- Both analytic_source.py copies match the pinned SHA-256 `4e26ed90c8ef7305699802c02490bb0cea0da26be49891c98d387b5210eb8f63`. The scale builder retains dimension m+1, signs and factor four, literal unscaled A, source endpoint and archimedean terms, all prime powers, tails and source-native even pole. It neither clips eigenvalues nor replaces A by a positive Gram form.
- The gate independently projects the physical kernel over the full physical interval in the basis carrying (-1)^j. It agrees with the 80-digit coefficient construction at the fixed absolute entrywise tolerance. The a=0 gate is explicitly Q-only; the main data supply the separate A+Q controls. The historical gate code and original predictions bytes still match their recorded hashes, and the portable historical-integrity verifier passes.
- Core assembly uses A=H+pp^T-B. Physical p-null vectors z become normalized vectors y perpendicular to S p, where S=W^-1/2. Householder restriction, the separate literal normalized p-perp convention, and the independent small generalized-eigenvalue gate implement this distinction consistently. The reported core constraint residual is at most 6.045e-16. The literal convention is never reported as physically pole-null.
- An added quartet changes the effective arithmetic form to B_eff=B-Q. The signs of both normalized rank-two updates are correct. Original-prime B rows remain separate. DH uses its own signed full Dirichlet recurrence, conductor 5, odd gamma factor and p_D=0; no zeta pole is inserted.
- Main high-precision checks freshly build the pinned source, promote fixed binary64 vector coefficients, and normalize by their squared physical coefficient norm. All 12 trigger witnesses satisfy the strict -1e-6 criterion, and all saved-vector hashes match.
- auxiliary_checks.py evaluates the arithmetic quadratic form independently by the shifted physical cosine overlap integral, retaining the source coefficients. For weak witnesses, A(0.9)+Q=A+0.1B+Q is divided by the W norm after enforcing the selected MP constraint. All 14 saved-vector hashes match and all 14 witnesses satisfy the strict detector threshold. These are point-arithmetic negative Rayleigh witnesses; they do not certify high-precision ordering of all eigenvalues or predecessor positivity.

## Independent saved-data checks and scoring

No new matrix assembly or eigensolver scan was run by this reviewer. Cheap verification consisted of hashing, standard-library/NumPy data checks, direct Decimal reconstruction, and the historical-integrity verifier.

All 44,264 main scalar CSV rows agree with their summaries in case domains, consecutive integer sequences, first negatives and counts. The only observed positive-a corner crossing is (a=1/3,gamma=14) at m=208; the other eleven are correctly censored >3000. The 147 actual main matrix dimensions and unplanted floors pass. All 528 admissible a=0 matrix controls are present and nontriggering with nonnegative corners.

All 23,865 B+ scalar rows have the complete declared admission domains and correct strict-sign flags. Their rounded values independently reconstruct H00+pole00-uB00+Q00 to less than 1e-80 with Decimal arithmetic; DH pole00 is exactly zero. No weak or DH corner crosses through 3000. Scalar-driver and core-driver/builder pins match their result records. Every DH integer 16..55 is present and only m55 triggers the specified threshold; the fresh own-source MP witness is negative.

Independent recomputation of the raw saved-series fits agrees with SCORES.json and RESULT.md:

- D1 supports all 12 comparisons with eleven censored corners. D2's operational delay test passes 4/12 and D3's literal one-bin test passes 3/12; the universal predictions fail as reported.
- K1 is only supported on the 25 tested core m, with maximum original-zeta C*=0.005633405980079711. No all-integer or cofinal inference is made.
- K2 uses positive RAW effective C* on the actual nine tested tail points and no baseline subtraction. Gamma14 slope 0.4633816578708903 passes; gamma50 slope 0.0882055039380422 fails. Their endpoint ratios are 2.231808140982825 and 1.2966206265081028.
- K3 is supported as a finite conjunction. The unplanted u=0.9 form already triggers, so RESULT correctly rejects specificity to added off-line quartets. This changed form is not used as an original-zeta control.
- K4 fails: DH ratio C*(3000)/C*(512)=0.7055068254948652 and tail slope=-0.07176611316857448. No tested DH C*>16 occurs. Raw DH matrix negativity does not become a claim of core growth.

RESULT.md distinguishes integer scalar coverage, consecutive matrix prefixes, subsequent checkpoints, finite core grid, censoring, exact physical constraints, failed predictions and point-arithmetic limits. Its reported largest Ritz residual, 4.856e-14, matches the saved rows. Main and B+ preregistration commit/push history is supplied by parent receipts; this reviewer independently checks their transported content hashes, not remote Git history.
