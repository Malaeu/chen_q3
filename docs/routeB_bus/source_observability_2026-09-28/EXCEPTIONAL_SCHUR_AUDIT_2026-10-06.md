# Exceptional Schur reduction: accepted scope and next obstruction

Same full CCM growth phase. Exact answer4:
PROSHKA_EXCEPTIONAL_SCHUR_INLINE_2026-10-06.md.
Exact question4: JOINT_HILBERT_AUDIT_2026-10-06.md.
No RH/SP claim; G1/G3 remain open; no Lean run.

## One bounded independent pass per part

causal_algebra_audit accepted (1)-(5),(17)-(19),(27)-(35): phases of
M_psi, signed pair Gram decomposition, endpoint-jump mollification in E
without an H1 assumption, full-space order, D_F sign, coherent band gluing,
regular block, exact Schur, and residual inequalities. Dependencies are
the already accepted signed explicit formula and source E-continuity.

growth_symbol_attempt accepted (6)-(16),(20)-(26): disk subharmonicity,
weighted multiplicity overlap, near strip constants, uniform p>=2 zero
tail moment, increasing derivative order with exact Omega^J, endpoint
rows, alpha tuning, density exponent and codimension.
Root read Chourasiya–Simonic v2 Cor1 p2 and its explicit following bound;
uniform sigma range is verified. Source and hash:
docs/literature/exceptional_density_2026-10-06/README.md.

## What is established

Write H(r)=S(r)-T, K=H(0)+E, ||E||<=C0=cA+28.
The full signed zero formula gives W=G-minus negative difference rows,
with G>=0 from critical-line evaluations and off-line pair sum rows.
All zeros and multiplicities are retained; no assumption of an off-line
zero's existence or absence is made.

Take alpha=8logL/L, Tcut=mL², J=ceil(L/(2logL)). Lsrc stacks the weighted
negative pair-difference rows Re(w)>alpha, |Im(w)|<=Tcut and the J
weighted actual endpoint-jet rows. Its definition is source-based,
not a negative-eigenvector projector. Then eventually
 H(r)>=G+(r-epsilon_m)I-Lsrc*Lsrc,
 epsilon_m<=C L^10 logL, rank(Lsrc)<=C m/L^5.
The near-line and high-zero remainder bounds are uniform over ALL carrier
vectors. The endpoint jets remain in Lsrc; they are not set to zero.

On R=ker Lsrc the form is >=r-epsilon. At r>=2epsilon, its actual block
A is invertible and ||A^-1||<=1/(r-epsilon). With E_src=ran Lsrc*,
 H(r)=[A B; B* C] is PSD iff Schur(r)=C-B*A^-1B is PSD.
The remaining dimension is <=C m/L^5. All band cross terms and regular-
exceptional coupling remain. The regular subspace is the same for all eta.
This proves a spectral COUNT/bulk bound, not a new bottom-eigenvalue bound.

For v in E_src,y in R, e=Ay+Bv, the exact discriminator is
 J_r(v,y)-||e||²/(r-epsilon)<=<v,Schur(r)v><=J_r(v,y).
The required sign at r=C_eta m^eta on arbitrarily large original cells
is still OPEN. Neither density nor codimension supplies it.

## Own attempt before question5

The positive Gram inequality yields a concrete sufficient row-space test.
Let t=r-epsilon>0 and Q=G+tI>0. Then
 Q-Lsrc*Lsrc>=0 iff
 Lsrc Q^-1 Lsrc*<=I
(on the finite row space; zero/dependent rows cause no inverse problem).
Indeed conjugation by Q^-1/2 gives I-U*U>=0 iff UU*<=I, with
U=Lsrc Q^-1/2. This is the finite Birman–Schwinger/norm comparison, not
an independent estimate and not equivalent to the ACTUAL Schur sign:
the tail/near-line majorants can make it strictly stronger.
The elementary bound Q^-1<=t^-1I only asks ||Lsrc||²<=t, which is
unsupplied and loses the interaction with positive sum rows. No such
bound is inferred from the small number of rows.

Negative control for a rank-only inference (NOT the CCM source):
diag(-m^delta,0,...,0), fixed 0<delta<1/2, has one bad direction,
a regular codimension-one subspace with nonnegative form, and obeys
the earlier m^(1/2-o(1)) floor, yet fails the subpolynomial target.
The exceptional Schur block also is not another source CCM matrix;
reapplying the density theorem recursively to it has no source map.
Thus smaller dimension alone cannot be the next claimed closure.

The actual conditional off-zero separator already established in this
phase continues to test the exact Schur: for 0<eta<delta it gives unit
f_m with <f_m,H(C_eta m^eta)f_m><0 eventually. Decompose f=y+v in R+E_src.
Then v!=0 because A>0; completing the square gives
 <v,Schur v><=<f,Hf><0.
This is only conditional on that zero; it is not a new contradiction,
a detected zero, or a lower bound on an actual exceptional effect.
Next work must estimate the real positive/negative row interaction,
including endpoint rows, or give a new independent source identity.

## Exact question5

Continuation 5/10, SAME negative-bottom-growth phase. Answer4 is processed and independently checked: signed Gram and E-domain extension, near-line/tail estimates, growing J, density tuning, exact Schur and residual inequality accepted. Root fetched/read Chourasiya–Simonic arXiv2507.15184v2 (30Sep2025), Corollary1 printed p2 and its following explicit display: uniform sigma in [.500,.625], T>=3e12, constants8.185/9.461/167.8 as used. No global RH premise. Hence the common regular subspace, epsilon_m=O(L^10 logL), d_m=O(m/L^5) and all coupling are legitimate PAPER progress. No new bottom floor or SP was obtained.

Own attempt before this question:
From H(r)>=G+(r-epsilon)I-Lsrc*Lsrc, set t=r-epsilon>0 and Q=G+tI. The sufficient exact comparison
Q-Lsrc*Lsrc>=0 iff Lsrc Q^-1 Lsrc*<=I
follows by conjugating with Q^-1/2 (zero/dependent source rows are harmless). This finite row-space Birman–Schwinger test keeps the positive pair-sum rows and all endpoint rows. It is ONLY SUFFICIENT for the actual Schur sign, because your near-line and tail majorants can be strict. The crude Q^-1<=t^-1 I reduces it to ||Lsrc||²<=t, which is not supplied and throws away precisely the source interaction we need. Small rank gives no such norm bound.

Negative control to avoid a rank-only loop: diag(-m^delta,0,...,0), fixed0<delta<1/2, has a codimension-one nonnegative regular subspace and satisfies the previously accepted m^(1/2-o(1)) whole-matrix floor, but violates SP. This is abstract, not a CCM counterexample. Nor can the density theorem be recursively applied to the smaller Schur matrix: it is not another original CCM source with a smaller cutoff.

Also the old conditional off-zero separator remains visible to the exact Schur, not eliminated by rank reduction. If a fixed off-line zero delta>0 exists and eta<delta, a unit original f_m has <f,H(C_eta m^eta)f><0 eventually. Decompose f=y+v into kerLsrc and ranLsrc*. Since A>0, v!=0; completion of squares gives <v,Schur v><=<f,Hf><0. This is conditional, not an observed zero or a new RH result. Please do not re-prove it.

NEXT mathematical task: estimate the ACTUAL exceptional Schur form (34) from its source rows, preserving the off-line-pair/endpoint coupling. Try the Q-based comparison above only if it provides a genuinely new source bound; distinguish its failure from failure of the exact target. The positive Gram G has critical-line rows and pair sums; Lsrc has pair differences and endpoint jets. Derive and prove a quantitative relationship between these particular row families on the original finite carrier, strong enough for Schur(C_eta m^eta)>=0 on arbitrarily large original cells for each eta>0, or isolate a strictly smaller noncircular missing inequality with a source-specific discriminator. A finite-rank rewrite, new names for interpolation, another density improvement without magnitude/sign control, or dropping the regular correction B*A^-1B will not advance the goal.

Pay endpoint overestimation explicitly: if the sufficient Q comparison is artificially obstructed by the jet majorant, sharpen the HIGH-ZERO joint contribution or return to the actual Schur, rather than declaring the source route killed. Do not assume absence of off-line zeros, RH-strength interpolation/sampling, inverse conditioning, or a positive Gram floor not established for these rows. Source mathematical work first; no plan-only answer. We need the sign/magnitude interaction that the rank theorem deliberately leaves open. Same full complex V_m, same m=N schedule, full Weil form, no RH claim.

Question5 sent 2026-10-06 20:56 UTC, same living Pro chat. Live browser
readback shows full question, Pro, ChatGPT antwortet, Stoppen, empty
composer. No resend. Next useful observation around 21:16 UTC or completion.
