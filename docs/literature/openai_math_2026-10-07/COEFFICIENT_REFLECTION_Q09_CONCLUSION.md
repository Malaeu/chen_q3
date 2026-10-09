# Q9: paired coefficient repair and incomplete matrix bound

2026-10-09. RH/SP/MB34 OPEN. No full inverse/high exponent gain.

## Evidence

Same living chat Совместная арифметическая оценка, https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ac86908-1f94-83eb-bcff-37c9bbe87118 . Request sent once12:36UTC; live running checks12:56 and13:16; terminal/download observed13:36UTC. Original read completely,1346lines, preserved unchanged.

- Request PROSHKA_COEFFICIENT_JOINT_REFLECTION_Q09.txt:1053134bytes,20590LF,SHA25683cf64cd4905f3280ca5683d985691db24b0784b7ba4d035cfc45e522c54a4da.
- Original PROSHKA_VERDICT_COEFFICIENT_JOINT_REFLECTION_Q09.md:99267bytes,1346LF,SHA2560a4b1bdb68b95368bd0f2ad79c98f974fab62d976bad2d03b122418cb4723258.
- Pinned source paper SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3; corpus adc7f1241b42e322a6451854ab7e4b4c146bf78a.
- Appendix C code SHA25623f6912e879c0e0f62d289b18dadd41795b56a2f505172199a95b6df512b0d62. Root ran extracted code and registration in /tmp/q09-root-check:49 checks, parsed JSON exactly matches Appendix D. Finite cyclotomic arithmetic,876 row visits in nested disks,1632 orbit states are diagnostics, not cofinal certificates.

## Exact coefficient repair and its limit

CF5 uses the actual twisted Gauss product: a0(n) conjugate(a0(m)) beta_m(v0)=Q_k(v0) a0(nv0) conjugate(a0(mv0)). For good squarefree v0 all collision zeros are preserved by extending a0 to zero on nonsquarefree good indices. All six units and the squarefree S-part are retained in explicit finite sectors.

The fused pair N=nv0,M=mv0 has normalization q_v0/sqrt(q_N q_M), both windows at scale q_v0 L, and symbols on the QUOTIENT indices N/v0,M/v0. Substitution of whole-index symbols adds erroneous zeros, also when t meets v0 but not k. Scalar completed reflection has not been mapped to this paired matrix. No added cubic series was introduced and then discarded.

## New quantitative bound, insufficient full return

CF10 squarefree inversion plus the complementary coprimality mask reduces the true incomplete character sum to primitive Poisson sums. The bound min(T,sqrt(q_r)), summed over square divisors and mask divisors, gives CF11/12:

    |G_ml(J;Phi)| <= C_(Phi,eps) q_k^eps min(J, sqrt(J) q_r^(1/4)), m!=l,

where r is the actual symmetric-difference cubic conductor and the k/r zero mask remains. The radial transform need not be positive; the weighted matrix is not silently replaced by a positive Gram.

Its diagonal is an ORIENTATION diagonal, not the original k=1 diagonal. The mixed common-quadratic row is the original primitive sextic character modulo k. Its direct bound followed by the complete t-sum gives sqrt(Q/Y) Q^(1/4) times a logarithm. After prefactor Y/(L sqrtQ), all pairs, d,e,g and all amplifiers, CF17 is

    |U_poor| <= P sqrt(U) L^(3/2) times declared losses + H U^(-1+eps) times height loss.

The d-price is q_d^-3 and the g/e-price q_g^-5/2 sum_(e|g)q_e^-1/2; both converge. The minimum exponent deficit is80243/75000. This envelope is weaker than Q8 and is NOT a lower bound or a counterexample to the target. CF20 remains exactly full QC18/JP20; mu(k) occurs once. Old conditional bound CF22 and all centered/principal/diagonal/inverse/height returns remain unchanged.

CF8/9 prove only a model statement: the three specified pure length reflections cannot decrease any coordinate from the stated positive chamber. Reduced commuting R1/R2 blocks alternate with R3, each remaining block increasing its coordinates. This is not a theorem about all analytic transformations, conductor lowering or joint cancellation.

## Review and decision

Independent read-only q05_moment_audit: scoped PASS for CF5, CF10–13, CF17, CF20 and abstract CF8–9, against pinned source575–582 and935–1051. One wording correction: original line430 says the diagonal N_k is not zero by definition; read this only as a retained term, NOT a claim of nonzero value. With a signed profile N_k can vanish (as original line465 itself permits). Original bytes remain unchanged; this qualification governs our use. No substantive algebraic or budget defect found.

Close Q9 as NO_DERIVATION / NO_PROGRESS for the full arithmetic exponent. Preserve CF5 and CF12 as scoped algebraic/analytic results only. Do not repeat whole-index fused substitution, omitted q_v, orientation-diagonal credit or pure length loops. Next admissible target is a genuine paired transform with quotient symbols and shared divisibility, or simultaneous k/orientation dispersion before taking absolute values. Neither has a proved full bound. No Q10 sent. Source P/M/R/K/high premises conditional; Linux Comparator report-only, no Mac rerun or moving-Hecke import. Native goal ACTIVE.
