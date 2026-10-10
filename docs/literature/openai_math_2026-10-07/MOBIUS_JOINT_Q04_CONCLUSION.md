# Q4 — finite reciprocal contour, full edge return, surviving poles

2026-10-10. ROOT AND INDEPENDENT BOUNDED AUDITS PASS. RH/SP/MB34/SB1 OPEN. No new full exponent, inverse or high gain; inherited P/M/R/K/high remain CONDITIONAL. Linux Comparator report-only, no Mac rerun.

Request `PROSHKA_MOBIUS_JOINT_Q04.txt`: 1582529 bytes, 27526 LF, SHA256 `2e3a3c9f86dcda29740f1f120e3f8252aeb31c3efc63878a779c292437b5da2b`; sent once03:13UTC in the existing MB34 chat. Terminal observed04:33UTC. Original `PROSHKA_VERDICT_MOBIUS_JOINT_Q04.md`: 115483 bytes, 1426 LF, SHA256 `d73a6d3cc732342c9b4ce5661c27ec8a4555ce4ccc78e1bba9f18fec8f1c2273`; byte-exact Downloads copy, fully read. Baseline5172e392. No Q5 sent.

## Root mathematical audit

1. MQ10–13 retain all removed Euler factors. On Re(s)=-1/4 the primitive functional equation reflects to5/4, where the inverse Euler series converges absolutely. The reciprocal gamma ratio gives (1+|t|)^(-3/2), conductor Q^(-3/4), and the removed factors give q_E^(-1/4+epsilon). No nonvanishing in a moving critical strip is used. Pinned source1437–1443 and prior AD5–6 conductor dictionary checked directly.
2. MQ15–17: the horizontal join has top-right minus bottom-right orientation; right-up minus left-up minus join equals residues. Thus M=A+e with every primitive/Euler pole, full multiplicities and all joins. T is a common avoiding finite height; no quantitative separation or smallness of joins follows from its existence.
3. Physical conductor sum is O(U^(-1/10+epsilon)): good radical C>=cU^(1/5), multiplicity O(C^epsilon), and sum_C C^(-3/2+epsilon). Raw decomposition v=u0*b^6 retains S, units, common factors and u0=1. Its conductor sum is O(H^(1/6)); the Euler product has first exponent5/3. Hence MQ21–24 include every physical and raw row and the entire absolute-line tail.
4. MQ26 uses the exact cross against M, not an assumed small residue vector. The elementary full bounds E_M,lambda R_H<=CPUL suffice. Consequently
   |E_edge| << P[U^(9/20)L^(-1/4)+U H^(-5/12)L^(-1/4)]U^epsilon.
   The minimum margin below H U^(-1/200) is15737/18750. Common norm twists shift the Mellin argument; the left multiplier is bounded and the right tails satisfy |t+t0|>=|t|/2. No hidden T1 derivative loss is needed for these estimates.
5. MQ29–34: every late physical row has pole order at0 at most1+|S|+omega(a), eventually <(1/24)logU/loglogU. Actual raw rows b^6 with b a product of k=floor(logU/(12loglogU)) primes in one fixed nu-trivial ray class lie in the original ball and have order>=k>(1/16)logU/loglogU, with Omega=0. Every maximal-order row therefore has weight -lambda. The highest double Laurent coefficient is -lambda*sum|c_v|^2<0. This rejects automatic holomorphic pole erasure only; it is not an MB34 lower bound or a sign bound on the whole integral.
6. The ORIGINAL diagonal generating function is zeta_F(s+t)/zeta_F(2s+2t) times finite factors (1+q_p^(-s-t))^(-1), summed with the original w_v. It is holomorphic near(0,0), so cannot cancel the preceding highest pole. Fixed nonzero Mellin profiles have finite zero order and cannot remove an unbounded maximal pole order. No uniform zero-order assertion for all moving twists is used.
7. MQ35–46 retain the full signed residue-plus-join square and the original diagonal. This is the first unpaid quantity. PLQ28/SI31 and SB38 return all projection cross and nonsquarefree terms; J_I and K_pr are not credited twice. CF20 keeps strict g/poor cutoffs and closed frequency caps. The elementary full fallback is PUL; the best inherited full bound is still CF22. At L=D its target deficits are46/9375 and5887/1200000 at the r-endpoints. No complete target is closed.

## Classical source checks and reproducibility

Root verified [Kedlaya, Theorems2.4.5 and2.4.7](https://kskedlaya.org/cft/sec_zeta.html): analytic continuation and qualitative L(1,chi)!=0 for nontrivial finite ray characters. Combined with the classical functional equation over the imaginary quadratic field this gives the simple zero at0; the principal zeta value at0 is nonzero. No quantitative inverse bound at1 is imported.

Root verified [Thorner–Zaman, arXiv1803.02823v3, Theorem1.1, PDFp2](https://arxiv.org/pdf/1803.02823): the exceptional-zero term is retained. For ONE fixed ray-class extension its exponent is fixed below1, yielding the required late prime count and q_pi_j=O(j logj). No moving-conductor uniformity is inferred. The HTML fetch failed; the PDF statement was read.

Inspected and extracted AppendixB registration and AppendixC code into `/tmp/q04-root-audit`; standard-library-only arithmetic script exits0 with empty stderr and stdout byte-identical to the original appendix. Code SHA256 `cd272f3445ebbb31f886b39ddf7a512e3c7f9d8758a4386a598d39b36624932e`; stdout `44e02897749c3cf5b0e42cb882bc2d6a2fab7bff70ff4fe580f59a951a47d695`. These checks establish only rational exponent arithmetic and a non-Hecke two-zero diagnostic, not the analytic moment.

Independent read-only reviewer `/root/q04_independent_audit` returned bounded PASS: no concrete defect in MQ1, MQ29–34, or full inherited return. Essential scope: every S-prime exponent in u^(6) is also0,...,5; allowing unbounded S-exponents would invalidate the stated conductor counting argument. Compact sigma-range and fixed common profile seminorms are retained. Reviewer did not run Lean or diagnostics; root ran the arithmetic reproduction. This admits only the new paper edge/pole-form claims, not P/M/R/K/high or full MB34.

## Next mathematical action

Automatic pole erasure by centering/diagonal subtraction is rejected in the precise MQ29–34 form. Full pole-retaining paths remain possible but MQ35 has no supplier. Preserve the original joint signed mechanism: the next own attempt must bound that whole functional or work directly with the finite original CF20 coefficients and all caps, before another Pro question. Merely regrouping poles or making the left edge smaller cannot improve CF22.
