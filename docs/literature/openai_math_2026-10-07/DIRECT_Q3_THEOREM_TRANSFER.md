# Direct analytic use of the OpenAI 7/8 theorem in Q3

Owner steering2026-10-07: combine the external theorem with the existing Q3 work before trying to strengthen the external proof internally. Q6 is already processed and pushed at9ca818e5; Q7 has NOT been sent. This note changes the next research target, not the RH status.

## External premise and verification boundary

Call the premise ZF78: zeta(s) has no zero for Re s>7/8 at every height. Pinned OpenAI paper.tex106–119 states this and the stronger family statement for all Dirichlet L-functions and finite-order Hecke characters over Q(sqrt(-3)); principal poles are allowed. Source commitadc7f1241b42e322a6451854ab7e4b4c146bf78a, SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3. Primary: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex . Functional equation gives all NONTRIVIAL zeros in the CLOSED strip[1/8,7/8]; it does not eliminate zeros inside it. The alternate11/12 theorem is weaker.

The separate Landau–Siegel manuscript's Theorem1 states (1-beta)log q>=c>0 for real zeros of primitive nonprincipal real characters, q>=3. It is not a statement that all real zeros in(0,1) vanish, nor a substitute for RH. Primary: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026/build/paper.tex .

Local declaration OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re in lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean has the intended unconditional statement and delegates to ProbeFinalAssemblyUnconditional.zeta_nonzero. This is statement inspection only. Local lean/formalization.yaml914–915 says scope Partial progress and1662–1663 review status unchecked. No fresh build, comparator or transitive axiom audit was performed here. The local snapshot log has Initial commit2026-10-06; this does not prove that nobody elsewhere has checked it. All deductions below are conditional on ZF78 until the external proof boundary is accepted or verified.

## 1. Original full CCM: improved floor, exact kernel retained

Use docs/routeB_bus/source_observability_2026-09-28/PROSHKA_JOINT_HILBERT_INLINE_2026-10-06.md, equations(2),(3),(12)–(15).
The original signed measure includes every Lambda(n)/sqrt(n) atom and both continuous pole terms. Its uniform primitive is

Phi_m(w;y)=sum_(n<=y)Lambda(n)n^(-1/2-iw)
 -(y^(1/2-iw)-1)/(1/2-iw)+(1-y^(-1/2-iw))/(1/2+iw),
R_m=sup_(|w|<=2pi m/log m,1<=y<=m)|Phi_m(w;y)|.

Fix eta in(0,1/8). In the EXISTING twisted Perron proof, take T=m² and move the contour to Re s=3/8+eta. Its zeta argument s+1/2+iw lies to the right of7/8 by eta, uniformly through heights O(m²). ZF78 plus the standard local zero-count/log-derivative bound gives zeta'/zeta=O_eta(log m) on the relevant sides (the pole at1 is separated explicitly). No zeta zero is crossed. The crossed pole cancels the same continuous growing term. The half-integer cutoff and endpoint costs remain at most5. Hence

R_m <<_eta 1+m^(3/8+eta)(log m)²+sqrt(m)(log m)²/m²
    <<_epsilon m^(3/8+epsilon).

The existing full-carrier inequality ||C_m||<=4R_m and W(f)>=D_arch(f)-(c_A+4R_m)||f||² therefore give

lambda_min(K_m)>=-c_A-C_epsilon m^(3/8+epsilon).

This is for the SAME full matrix, schedule and complex carrier. It improves the previous exponent1/2-o(1); it does not establish SP, which needs every positive exponent. The own off-critical witness for a zero beta=1/2+delta is -c m^delta/(log m)^(2delta). The imported floor excludes only delta>3/8, already excluded by ZF78. There is no iterative improvement from these two bounds alone.

Important: inserting a bare Chebyshev error into absolute partial summation would incur a growing |w| loss. The twisted Perron proof avoids it by putting n^(-iw) into coefficients before contour movement. A fixed finite-height check cannot supply this asymptotic result; heights must cover O(m²).

## 2. Existing scalar source: shifted positivity and exact growth

Suzuki, arXiv:2206.03682v4, equation(11.1) and Theorem11.1, https://arxiv.org/html/2206.03682v4#S11, applies to the SAME Psi used by our SCALAR_RESERVE_OWN_2026-10-07.md. Define

Psi_omega(t)=exp(-omega*t)Psi(t)
 +2omega int_0^t exp(-omega*u)Psi(u)du
 +omega² int_0^t (t-u)exp(-omega*u)Psi(u)du.

ZF78 directly supplies Psi_(3/8)(t)>=0 for all t>=0, using Suzuki's forward implication preceding Theorem11.1. This is a genuine positive object from the external input; Psi_0>=0 remains unproved.

For h>0 the exact downward-shift identity is
Psi_(omega-h)(t)=exp(ht)Psi_omega(t)
 -2h int_0^t exp(hu)Psi_omega(u)du
 +h² int_0^t(t-u)exp(hu)Psi_omega(u)du.
The negative middle term is the precise unpaid signed quantity. Positivity at one shift alone cannot be used as positivity at a smaller shift.

Independently, Suzuki(1.3) gives Psi(t)=sum_gamma(1-cos(gamma*t))/gamma². ZF78 gives |Im gamma|<=3/8, and sum_gamma|gamma|^-2 converges. Thus |Psi(t)|<=C exp(3t/8), without epsilon. This controls size, not sign. In the full prime-power scalar kernel W(x) already recorded in JOINT_LATTICE_AUDIT, the standard Chebyshev consequence gives |W(x)|<<_epsilon x^(3/8+epsilon); no part of the prehistory is discarded.

## 3. Old ground/trial chain: weaker sufficient tracking rate

Keep ALL matched T1–T6 hypotheses of source_observability's SOURCE_TRANSFER and its simple ground state, same full K_m, same selected row and original cofinal sequence. Alpha_m=||(I-P_0,m)qhat_m|| is the reference-row angle error; it is not supplied by ZF78.
The already checked bound in CRITICAL_STRIP_PROJECTION_SOURCE_AUDIT_2026-10-06.md206–242 is

sup_(z inK)|F_m(z)-T_m(z)|<=C m^(H/2)sqrt(log m)(alpha_m+4t_m),

where K lies in |Im z|<=H and the matched t_m decays faster than every power. Our centeredXi(z)=xi(1/2+iz) sends rho=beta+i gamma to z=gamma+i(1/2-beta). ZF78 confines every possible off-real centered zero to |Im z|<=3/8.

Therefore any fixed a>3/16 and finite A with alpha_m=O(m^-a(log m)^A) now suffices: choose3/8<H<min(2a,1/2). The bound tends to zero on that open strip; the same-shell trial limit and real-zero entire ground approximants then let Hurwitz exclude every remaining off-real zero. Boundarybeta7/8 is included because H>3/8. The endpointa=3/16 is not justified by this argument.

This reduces the previous sufficient quarter-power tracking target to any exponent strictly larger than3/16. It does not prove that rate, supply G1, restore a killed constant gap, or allow two different families. A restricted-strip version of the final Lean consumer would need to be written after the paper inputs are supplied; the current whole-strip wrapper cannot simply be invoked with a smaller domain.

## Audit and next decision

squarefree_conductor_check independently verified the full twisted-Perron-to-CCM transfer and scalar consequences; root reread the actual primitive, contour, endpoint and full-form inequalities. growth_symbol_attempt independently verified the coordinate map and conditional tracking-rate relaxation, including the strict boundary. No Lean verification claimed.

Priority is now direct use of ZF78 in these ORIGINAL Q3 consumers. The strongest genuine new inputs are Psi_(3/8)>=0 and the weaker tracking threshold; the CCM floor is useful but alone only recovers the imported strip. Before another Pro question, choose an exact signed downward-shift estimate or an actual source-angle estimate and test it using existing source structure. The previous internal OpenAI mixed-period continuation is deferred, not disproved. RH, SP, G1/G3 and the unshifted scalar reserve remain OPEN.
