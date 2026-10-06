# Causal joint pole/prime dressing: answer1 audit

Source: PROSHKA_CAUSAL_DRESSING_INLINE_2026-10-06.md. Same full K_m,
original m=N, L=log m, translated complex carrier on [0,L]. SP and RH OPEN.
This is within FULL_CCM_NEGATIVE_BOTTOM_GROWTH, not a new phase.

## Root check and own next attempt

For the actual causal integer sum Z and R kernel exp(-s/2), define
F=(I-R)Z. Its causal distribution kernel on the half-line is

 delta_0 + sum_(n>=2) n^-1/2 delta_(log n)
   -exp(-s/2)floor(exp s) ds.

Restriction to [0,L] gives exactly the finite-window F, with translations
past L acting as zero. The Laplace transform in Re z>1/2 converges absolutely:

 Fhat(z)=((z-1/2)/(z+1/2)) zeta(z+1/2),
 -Fhat'(z)/Fhat(z)
   =-zeta'(z+1/2)/zeta(z+1/2)-1/(z-1/2)+1/(z+1/2).

The latter is the transform of P-R_++R, agreeing with answer1 (30).
This half-plane calculation identifies the source, not a bounded inverse
on the critical line. Moving it to Re z=0 needs estimates not present here.
The all-integer cancellation is exact; its inverse exposes arithmetic again.

Writing F=VM, Y=V*XV and H=log M is valid for each finite L, since F is
bounded invertible there. The proposed remaining operator is exactly

 D=M Y M^-1+M^-1 Y M-2Y
   =exp(ad_H)Y+exp(-ad_H)Y-2Y.

The norm-convergent commutator series contains only even iterates. It has
no automatic quadratic sign. In an abstract two-dimensional negative
control take M=diag(k,1), k>1, Y=(L/2)[[1,1],[1,1]], so 0<=Y<=LI. Then
D has diagonal zero and off-diagonal (L/2)(k+k^-1-2). Its eigenvalues are
the positive and negative of that number. Thus positivity of M and Y alone
does not supply the desired upper estimate. This is NOT the actual source
matrix or an RH counterexample. Source-specific cancellation remains needed.

A generic norm estimate gives only
||D||<=2L(||M|| ||M^-1||+1), which is not a subpolynomial source bound.
The old Sept4 weighted-Loewner double commutator has another M and another
geometry; its finite-rank algebra is not a supplied estimate for this polar M.

The literal outstanding target from answer1 is

 <f,D f> <= D_arch(f)+C_eta m^eta ||f||2^2, f in V_m.

It would imply lambda_min>=-cA-2log(m)-C_eta m^eta. Constants can absorb
logarithms, giving SP. By NEGATIVE_GROWTH_SYMBOL_PREFLIGHT, it is sufficient
to obtain these bounds on an unbounded subsequence for every eta>0. Neither
the all-tail nor subsequential bound is supplied by the identities above.

## Independent verification

The bounded causal_algebra_audit accepted (1)-(16),(28)-(35): exact finite
causal inverse, all prime powers, kernel positivity (not operator positivity),
6/20/240 constants, left-trace/range and zero-extension endpoint costs,
unsmoothed inverse, polar signs and restriction to the full complex carrier.
All inverse bounds are finite-L only; (36) remains OPEN.

growth_symbol_attempt independently accepted (17)-(27): top-mode partial
Fourier bound 16/sqrt(Omega), L2 loss, BV derivative bound and graph norm
<=10000 L/Omega for m>=3. At a jump S=log n, interpret r(S) in the IBP
boundary term as its left trace, or use sup|r|<=1; the constants are unchanged.
Thus carrier-wide subpolynomial inverse comparison for A is KILLED for
eta<1, even with D_arch in the comparison norm. This is NOT a bottom-vector
counterexample and does not refute the signed unsmoothed estimate.

The root checked the full saved algebra and matched the inherited source
form. Opaque Suzuki citation tokens were not used as an input. No Lean build.

## Alias return and next question

The bounded polar_commutator_alias pass found no supplier. Shelf search was
INCOMPLETE, not an absence result. Bhatia–Kittaneh–Li (1997), Thm2.1, is a
unitarily invariant norm inequality for Hermitian variables; it does not
map to the required signed carrier form. Root reread the rendered formula
and corrected the report's initial transcription from a sum to a product
with squared left side. The inapplicability conclusion is unchanged.
See docs/literature/polar_commutator_2026-10-06/README.md and stored PDF.

Answer1 is processed. The same phase continues with the actual unsmoothed
F double commutator, after the recorded failure of carrier-wide undressing.
Use the explicit arithmetic F and inverse; positivity of polar factors alone
fails in the abstract negative control above. The next question must supply
an actual source estimate of D (or a proved obstruction), not another
identity or a standalone condition-number target. A subsequence per eta
already suffices. The auxiliary finite-frequency reduction supplies no
estimate of D and is not a second active route.

## Exact question2

Sent 2026-10-06 about19:17 UTC in the same Proof of CCM Growth chat.
User item 2604508d-6836-4dc2-a078-1e417669cabd; exact text read back and
active response confirmed. Answer2 pending; do not resend.

Continuation 2/10, SAME negative-bottom-growth phase. Answer1 is fully processed by bounded independent checks. Work directly on the unsmoothed source operator, not another reformulation.

Accepted: causal identities (1)-(16),(28)-(35), constants6/20/240, all prime powers, finite-L inverse and polar identities; the actual top-mode estimate (17)-(27) proves carrier-wide subpolynomial undressing of A=R(I-R)Z fails even with the archimedean graph norm. At a jump S=log n in (20), use the left trace or sup|r|<=1; constants unchanged. This is NOT a bottom-vector obstruction. No uniform inverse bound was accepted; (36), SP and RH remain OPEN.

The next exact object is F=(I-R)Z=VM on L2(0,L), X multiplication by x, Y=V*XV, and
D=M^-1[M,[M,Y]]M^-1=MYM^-1+M^-1YM-2Y.
The original full form on V_m satisfies
W(f)>=D_arch(f)-(cA+2L)||f||²-<f,Df>.
We now seek the source-specific upper bound <f,Df><=D_arch(f)+C_eta m^eta||f||². Same actual complex V_m, m=N, L=log m, original schedule. Do not replace it by even vectors, arbitrary matrices, or the A-dressed carrier.

Useful quantifier relaxation, independently checked: the previously proved off-critical-zero alternative holds on EVERY late original cell. It therefore suffices that for every eta>0 there are arbitrarily large original m with the above upper bound for ALL f in V_m on that SAME cell. Equivalently at the terminal consumer, liminf_j log(1+(-lambda_min(K_mj))_+)/log m_j=0 suffices. No good subsequence is currently supplied; do not average entries or separate cells and infer a common matrix bound.

Our own attempt and alias return:
1. With H=log M, D=exp(ad_H)Y+exp(-ad_H)Y-2Y. It has no free sign: M=diag(k,1), Y=(L/2)[[1,1],[1,1]] gives D offdiagonal (L/2)(k+k^-1-2), diagonal0, eigenvalues of both signs. This abstract control is not the actual F; it kills only positivity-of-M,Y as a supplier.
2. Generic ||D||<=2L(||M||||M^-1||+1) just returns the missing conditioning and is not progress. The shelf's older weighted-Loewner double commutator involves different operators.
3. Actual causal F distribution is delta0+sum_(n>=2)n^-1/2 delta_log n-exp(-s/2)floor(exp s)ds. In Re z>1/2 its absolutely convergent Laplace transform is
Fhat(z)=(z-1/2)/(z+1/2) zeta(z+1/2),
and -Fhat'/Fhat=-zeta'/zeta(z+1/2)-1/(z-1/2)+1/(z+1/2).
This matches P-R_++R. It does not justify a bounded critical-line inverse or any sign. Mere analytic continuation would conceal the missing estimate.
4. Bounded alias check: Bhatia–Kittaneh–Li 1997 Thm2.1 bounds |||A-B|||² by the product |||AΓ-ΓB||| |||Γ^-1A-BΓ^-1||| for Γ>0,Hermitian A,B. It does not bound our signed form; A=B=Y makes its left side zero, while MYM^-1 is generally not Hermitian. No supplier found; shelf search was INCOMPLETE, not an absence certificate.

Task: derive a quantitative UPPER FORM estimate for this actual source-defined D against D_arch, retaining signed coupling and the full finite-window boundary action. Exploit the explicit integer/dilation F and Möbius inverse from (29), or an actually applicable primary theorem with all hypotheses mapped. An unbounded good subsequence for each eta is enough. If the target cannot be proved, test one concrete proposed source mechanism and give a proved obstruction with its exact quantifiers and the remaining source inequality. Do not claim a bound on standalone F^-1 or its condition number solves the signed estimate unless you prove the needed scale and carrier/domain map. No RH premise, zero-location assumption, free polar-factor positivity or graph-norm repair already killed. End with one next mathematical step justified by a new calculation; another exact wrapper is not a supplier.
