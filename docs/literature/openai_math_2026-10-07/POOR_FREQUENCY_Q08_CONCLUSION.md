# Poor-frequency Q8: exact cancellation, no full exponent gain

2026-10-09. RH/SP/MB34 OPEN. Native RH goal ACTIVE.

## Evidence and scope

Same living chat: https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ac86908-1f94-83eb-bcff-37c9bbe87118 . Request sent once 11:38UTC; terminal response and original observed 12:19UTC. Original read completely, 1292 lines, unchanged download retained beside this conclusion. No further question sent.

- Request `PROSHKA_POOR_FREQUENCY_JOINT_Q08.txt`: 979619 bytes, 19778 LF, SHA256 `91f0b6f9b7c03cd505bd19fc36a2072bd4f35d417dbe4e683bc45ecb18997873`.
- Original `PROSHKA_VERDICT_POOR_FREQUENCY_JOINT_Q08.md`: 95404 bytes, 1292 LF, SHA256 `1f70ec4f7f216313565f3ff5a6b739c94717804f1498b88d4fe2a0c471314f44`.
- Pinned source paper SHA256 `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`, corpus commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Appendix C code SHA256 `d4325c809388bc1bb5985d94cbafa27e8e76b9c91e7ee71ba3d066ff454121e4`.

## Accepted exact result

QC4–QC8 retain the unique full decomposition h=v t², with squarefree ideal (v), unrestricted ideal t, and all six units in v. Shared primes between v and t and squareful t must remain. The original poor selector depends only on t. The quadratic part has common conductor k=nm, but its accompanying cubic coefficient still depends on v; a pure quadratic large sieve cannot simply discard it.

QC11–QC14 sum the complete squarefree-kernel sieve before taking moduli. The convolution mu*P_F is supported at j=f², with lambda_F(f)=sum over r|f, q_r<F of mu(f/r). In particular lambda_F(1)=1. The exact poor sum equals the full character sum S_beta(J), plus the signed f>=F fourth-power correction. Absolute rearrangement is justified; S-primes cancel from j but remain in the inner variable.

QC17 returns that f=1 term to the ORIGINAL short correlator with coefficient one, not to the true n=m diagonal. Units, Gauss signs and zero extensions survive the two Poisson transformations. QC18 is exactly the original poor-frequency JP20 with all g/a/d/e sums, both profiles, wP and signs retained. Its required one-sided estimate QC19 remains open.

## Quantitative result and limits

QC13–QC16 give the direct envelope P(UL+L² U^(-1/10)), up to the stated epsilon/height factors and inherited negligible frequency tail. After every outer sum its minimum exponent deficit relative to H U^(-1/200) is 19217/18750. This upper envelope is too large; it is NOT a lower bound or a counterexample to the desired estimate.

The complete normalized local character convolution has norm one. This rules out automatic contraction of that specific local kernel; it does not rule out cancellation in the actual signed aggregate.

The previously conditional full estimate and inverse gain are unchanged. Centering, principal and masked-diagonal returns retain their previous costs. Inverse margin 5887/1200000 and height margin 1087/1200000 remain conditional on their original analytic inputs; no new K estimate is proved. Linux zeta Comparator remains a report, not a Mac rerun. No moving-Hecke uniformity is imported.

## Verification

Root extracted the original Appendix C code and registration into `/tmp/q08-root-check`, ran `python3 /tmp/q08-root-check/check_q08.py`, and compared parsed JSON with Appendix D: exact match, 60 Boolean checks. Coverage: nine good finite fields, 2401 zero-extended phase cases, 1728 divisor-convolution cases and all 10890 nonzero Eisenstein elements of norm<=3000. The finite radial weight is explicitly a diagnostic, not source rho-tilde and not a moment certificate.

Independent read-only agent `q05_moment_audit` returned PASS for QC1–QC18 against the pinned source: decomposition, convolution support, lambda_F(1) return, units/zeros/S-powers, complete outer budget and unchanged signed remainder. No sign or mask deletion found. This mathematical audit is not Lean certification of source P/M/R/K.

## Decision

Close Q8 as NO_PROGRESS for the required full arithmetic exponent. Do not repeat the free quadratic projection or claim the unit return is a paid diagonal. Next admissible research target is the actual cubic divisor vector aggregated against its common quadratic column before absolute values, with both profiles and all original weights. A completed cubic-reflection source is only a candidate until its full completion/decompletion cost and coefficient map are supplied. No Q9 sent; no supplier accepted. RH remains OPEN.
