# Full finite-path allocation is incompatible with the canonical translated radical

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete. Analytic route audit, not a sign proof.
Source base: eef0c3f8343431a7d885f18ccb209cd45e8c57a4.
Canonical admission: NONE; full V and RH remain open.

## A0. Reconciliation and exact dependency boundary

This is an explicit consequence of existing September 5–11 arguments, not a new ground-state transform or a literature novelty claim. It tests a stronger scope than the retained-central-allocation obstruction: can ANY fixed measurable law of finite paths, using the original positive edges and nonnegative charges, pay ALL the negative demand? The answer proved below is no. It does not assume the earlier central law is retained.

All paths below are relative to the research checkout at the source base:

| Key | File | SHA256 | Used locations |
|---|---|---|---|
| X | docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.md | 93db2de6357821918211a8033b2c8f34e7f684320a25e5623e1f24d33ed58fe9 | X/CONT/CAN/ENV/EF/RAD/GS |
| C | docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_COUPLED_SIGNED_SQUARE_CERTIFICATE_FOR_THE_CANONICAL_KERNEL_2026-09-05.md | e51a0e6327e93f31c8e61931ea6c9e180c643ce721e63785b3c8380aebd6f1af | C3.1–C3.6, translated radicals, compact cutoff budget, finite translate independence and measurable finite-stencil obstruction |
| F | docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FLOW_2026-09-10.md | 629431c76e40a1af5fcb5f2b6721ae7be8dba3bfe71a2e8f238e6fd32e07e28d | F1–F2 exact signed edge measures; F22–F24; finite-path sufficient interface |
| R | docs/routeB_bus/FLOW_INDEPENDENT_CHECK_2026-09-11.md | 17bd247cc4c995a239e22136cb3ba899c0c20d337e8ec1cff49cd65b440c533f | S1–S7 and acceptance receipts: retaining the central slack makes the residual domination false |
| S | docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SLACK_2026-09-11.md | 1d658eb3d6d828d3bc651967087dabf8e2f9774d179b02c7607f25c7ffe54588 | SL1–SL3: topology, full radical and L2-kernel obstruction |

The explicit-formula theorem behind X's radical remains an inherited published dependency. No new external theorem is imported, no source spectrum is inferred from finite checks, and no new interval computation is needed. R already supersedes the naive idea of completing FLOW merely by increasing the number of paths. This audit makes the class obstruction independent of keeping that particular central construction.

## A1. Unchanged signed form and source properties

Let f=Phi/||Phi||2 be the full positive even theta source. Define

    alpha(t)=exp(-t/2)/(1-exp(-2t)),
    b(t)=alpha(t)-2 cosh(t/2),
    w_n=Lambda(n)/sqrt(n),
    c_t(x)=f(x)f(x+t).

Let tau>0 be the unique zero of b; equivalently exp(tau) is the positive root of z^3-z-1=0. Positive receiving edges (y,u), u>0, carry

    C_+(dy,du)=1_(0<u<tau) b(u)c_u(y) dy du
                 + sum_(n>=2) w_n c_(log n)(y) dy delta_(log n)(du).

Negative demand carries

    D_-(dx,dt)=1_(t>tau) (-b(t))c_t(x) dx dt.

Both are sigma-finite Borel measures. C_+ has infinite local mass near u=0, but its squared-difference energy is finite on each compact smooth test. D_- has a strictly positive density for every x and t>tau. For s in C_c^infinity(R;C), write D(s)=Q(fs). The already proved exact identity is

    D(s)= integral |s(y+u)-s(y)|^2 dC_+
           - integral |s(x+t)-s(x)|^2 dD_-.                 (A1)

Both integrals are separately finite on this class. The two poles are part of b; every prime power has its actual von Mangoldt weight. No source replacement occurs.

For q rational let r_q(x)=f(x-q)/f(x). There are real compact smooth cutoffs chi_N equal to 1 on [-N,N] such that

    s_(q,N)=chi_N r_q is compact smooth,
    D(s_(q,N)) -> 0.                                      (A2)

This is the X-continuous radical/cutoff result of C3.1–C3.2. It does not assume D>=0. It never substitutes r_q directly into the whole noncompact form.

At any finite set of distinct points z_1,...,z_k, the vectors

    (r_q(z_1),...,r_q(z_k)), q in Q,

span C^k. Indeed a vector annihilating them gives a finite translate identity for f, with coefficients divided by the positive f(z_j). Continuity extends q to R. Fourier transform gives a finite exponential polynomial vanishing on an interval where f-hat is nonzero; the Vandermonde argument makes every coefficient zero. This is exactly C3.3.

## A2. Exact proposed certificate class

For D_--almost every demand (x,t), choose a measurable probability law on FINITE paths p=(v_0,...,v_m; a_1,...,a_m), where

    m>=1, v_0=x, v_m=x+t, 0<=a_j<infinity.

Lengths, path counts, vertices, probabilities and charges may depend on the demand. Repeated vertices/edges, both orientations, cycles and unbounded finite m are allowed. Zero-length edges may be removed because they cost no energy. All data live in the countable union of finite-dimensional Borel spaces. The law and charges are fixed independently of the tested function s and its cutoff N.

Each path must satisfy the individual inequality for EVERY assignment of complex values to its distinct vertices:

    |z(v_m)-z(v_0)|^2 <= sum_j a_j |z(v_j)-z(v_(j-1))|^2. (A3)

The same condition follows if it is required for every compact smooth s: arbitrary values at a finite set can be interpolated by such an s. In particular this includes the usual weighted Cauchy path inequalities.

Let nu be demand measure times this probability kernel. Let Gamma be the total charge on unoriented nonzero receiving edges, pushing a_j dnu through

    (p,j) -> (min(v_(j-1),v_j), |v_j-v_(j-1)|)

and summing ALL occurrences. The proposed global capacity statement is

    Gamma <= C_+ as measures.                             (A4)

This is the positive path-allocation mechanism being tested. Without A4, no source capacity has been paid. Infinite limits with cutoff-dependent laws, signed combinations of path inequalities, or cancellations between path slacks are not asserted to satisfy A2–A4.

## A3. The translated radical forces every path slack to vanish identically

Suppose A4 held. For a path p define its nonnegative Hermitian quadratic slack

    H_p(s)=sum_j a_j |s(v_j)-s(v_(j-1))|^2
                   - |s(v_m)-s(v_0)|^2 >=0.

Tonelli, A1 and the total-charge definition give on every compact smooth s

    D(s)= integral H_p(s) dnu(p)
              + integral |Delta s|^2 d(C_+-Gamma).        (A5)

All quantities are finite: the charged energy is at most the finite C_+ energy, the demand energy is finite, and the residual measure is nonnegative. Hence

    0 <= integral H_p(s) dnu <= D(s).

Apply this to s_(q,N). For each fixed finite path, all vertices eventually lie in [-N,N], so H_p(s_(q,N))=H_p(r_q) eventually. Fatou and A2 imply

    integral H_p(r_q) dnu = 0  for every rational q.       (A6)

There are countably many q. Thus for nu-almost every path, the PSD quadratic matrix H_p annihilates in quadratic value ALL these vectors at once. For a PSD finite matrix, z*H_p z=0 implies H_p z=0. After repeated vertices are combined, A1's finite-value spanning property therefore yields

    H_p = 0 as a quadratic form on all its vertex values. (A7)

No uniform vertex bound, uniform path length, compact support for the law, measurable eigenvector selection, or interchange of a signed noncompact integral was used. Sigma-finiteness and the countable rational family suffice.

## A4. A zero slack would require a forbidden direct receiving edge

At the distinct path vertices, the identity A7 reads

    sum_j a_j L_(v_(j-1),v_j) = L_(x,x+t),              (A8)

where L_(a,b) is the two-point edge Laplacian: its two off-diagonal entries equal -1, its endpoint diagonal entries equal 1, and all other entries are zero. Every a_j is nonnegative. Comparing the off-diagonal entry for the unordered pair {x,x+t} in A8 forces

    sum_(j: {v_(j-1),v_j}={x,x+t}) a_j = 1.             (A9)

No other unordered pair can cancel that entry. In fact every other nonzero edge has total coefficient zero by the other off-diagonal entries, although this stronger observation is not needed.

Let

    U=(0,tau) union {log n : n>=2, Lambda(n)>0}.

The complement of U has zero C_+ mass in the edge-length coordinate. A4 and nonnegative charge consequently force, for nu-almost every path, every edge with a_j>0 to have length in U. But D_- is absolutely continuous in t, supported on t>tau; the countable prime-power lengths have zero D_- measure. Thus t is NOT in U for nu-almost every path. Equation A9 forces an edge with positive coefficient and length exactly t. Contradiction.

Therefore no law in A2–A4 exists. This is a strict incompatibility of the global finite-path certificate class with the actual canonical form, not just failure to find a law.

## A5. Why the conclusion is consistent and what it changes

The existing positive central/tail allocations remain valid on their proper subregions. They produce positive slacks; the full form can compensate those slacks through a signed remainder. This theorem concerns paying ALL negative demand through separate nonnegative path inequalities with Gamma<=C_+. It strengthens the explicit operational scope of R's retained-central obstruction; its mathematical engine is the already proved C3 finite-stencil obstruction.

Control: on three vertices with positive unit edges 01 and 12 and demand (1/2) on 02, the two-edge inequality with coefficients (2,2) exactly pays capacity and leaves (1/2)|z_0-2z_1+z_2|^2. Its null space consists of affine vertex data, not vectors spanning all three vertex values. Thus the finite-path construction is perfectly valid there; the crucial canonical obstruction is the rich translated radical, not the mere presence of a null function.

The theorem does NOT establish negative Q or negative original V, does not rule out signed global compensation, and does not rule out a cutoff-dependent sequence with a proved vanishing error and fixed-test recovery. It does not establish that any such alternative works. Nonlocal factors that vanish on the entire translated radical are outside the finite-path argument, although S's separate L2-kernel obstruction must also be respected.

Decision if independently accepted: do not launch another source-exact global finite-path capacity search, including variants that redesign rather than retain the central allocation. The original full sign objective remains unchanged. No new theorem/consumer edge is admitted to canonical controls. This audit is a corollary/reconciliation with a precise decision effect, not a fresh proof of positivity or a reset of the original source-sign counter.

## Independent acceptance

Verdict: ACCEPT_FIXED_MEASURABLE_FINITE_PATH_ALLOCATION_OBSTRUCTION_ONLY.
Candidate SHA256: 80684d3ccdf853866c94869db80b3161a87f7116a46315bd775d2446c2fafe33.
Complete review SHA256: 300e6f4c86071858b198993b8e8cbffb0c256ceda2195ea261c7170c28b9f44f.
Complete parent check SHA256: c154135c6821f64227164f3e4038e08ed17618cb78ec9d5cbbdc1322b4dc0bbb.
The parent read the full review and checked the measure difference, variable finite-path Fatou step, finite-value spanning, PSD null argument and direct-edge contradiction. The certificate embeds both checks. This accepts a corollary excluding a certificate class; no original sign theorem or negative V witness is supplied.
