# Cofinal positive moment: budget test, not a new source bound

20.10.2026. Own bounded calculation while Proshka considers the actual-Mobius
joint question. Researcher supplied the moment comparison; root retains the
second short-return fee below. No status-changing proof claim or RH claim.

Keep N=m,L=log m, M=R=floor(m^epsilon), fixed 0<epsilon<1/32, the
original three-constraint P_m, and S_m=P_m A_prime,m P_m.
All prime powers and matrix entries remain. Let d_m=rank P_m<=2M+1.

## A sufficient cofinal input

For integer dyadic X, a bound

    (1/X) sum_{m=X}^{2X-1} Tr[(S_m)_+^4]
       <= C_epsilon X^{a(epsilon)} (log X)^B

would give at least one original m in each window with

    max(0,lambda_max(S_m))
       <= C_epsilon^(1/4) X^{a(epsilon)/4}(log X)^(B/4).

If a(epsilon)->0, choose fixed epsilon with a(epsilon)/4<delta.
The archimedean fee is O(log m); this contradicts the conditional
off-critical witness on EVERY sufficiently late original cell, including
the chosen subsequence. Constants and B may depend on fixed epsilon.
This is only a sufficient implication; the displayed arithmetic moment
bound is OPEN. Taking a positive part preserves the entire matrix before
spectral functional calculus; it is not deletion of mixed source terms.

## What the existing conditional Q10 actually pays

Q10-E states T_{>R}<=(4B_m+bsmall)P-2H_P, where
B_m=Ccl m^(3/8)L^2 log(3L), H_P>=0 and ||T_{<=R}||<=bsmall.
Thus S_m<= (4B_m+2bsmall)P-2H_P. The second bsmall must be returned.
For fixed epsilon<1/32 its power 3epsilon/2 is below 3/8. Consequently,
conditionally on Q10's stated ZF78 premise,

    Tr[(S_m)_+^4] <= d_m(4B_m+2bsmall)^4
       <<_epsilon m^(3/2+epsilon)L^8 log(3L)^4.

A dyadic average leaves that upper-budget exponent unchanged. It gives
only a cofinal top-eigenvalue budget 3/8+epsilon/4. This is a limitation
of this derived upper bound, not a lower bound or impossibility theorem
for the actual moment. New cancellation is still required.

## Why averaging a matrix is not enough

Even a uniform bound on the averaged quadratic form does not control
the average of the positive spectral part. As an abstract countercontrol,
alternate diag(H,-H) and diag(-H,H), H>0. Their matrix average is zero
for every fixed vector, while each has lambda_max=H and
Tr[(S)_+^4]=H^4. This is outside the arithmetic source; it only rejects
the inference. Moving P_m also requires its own exact treatment.

## What Q5 can and cannot supply

On ran P, S=P(Aarch-cA I-K)P <= cP+P K_- P, c=50log m+8.
Eigenvalue monotonicity, (x+y)^4<=8(x^4+y^4), and Schatten compression give

    Tr[(S)_+^4] <= 8[d_m c^4+Tr(K_-^4)].

There is no justified multiplication of the full trace by M/m.
Q5's paid m^(3/2) envelope is only part of its expansion: R-Ccredit
is unbounded. It cannot be substituted for Tr(K_-^4). A common finite
exponent for arbitrarily large fixed moments would be another sufficient
input, also unproved. Q6 rejects unsigned total variation, not the
signed moment or this cofinal variant.

## Decision

The cofinal variant is a documented backtrack candidate, not an improvement.
No second Proshka message is sent while the actual-Mobius question is pending.
First read and test that answer. A new question must identify a mechanism
for the missing signed saving, rather than simply request this inequality.

Sources: CCM_SPARSE_BAND_RECEIVER.md, CCM_MOMENT_Q10_CONCLUSION.md,
CCM_MOMENT_Q05_CONCLUSION.md, CCM_MOMENT_Q06_CONCLUSION.md, all in this directory.

## Parallel check of the pending dyadic correlation question

On H=L2(0,L), V_s f(t)=1_[s,L](t)f(t-s). For dyadic blocks of
d>R and k>=1, put A_D=sum mu(d)/sqrt(d) V_log(d) and
B_K=sum log(k)/sqrt(k) V_log(k). Then Z_DK=A_D B_K is exactly the
forward source block: dk>=m vanishes by physical support, including
the original zero endpoint dk=m. It is NOT A_D* B_K.

For an actual constrained physical vector f in ran E,

    <f,Z_DK f> = <A_D* f,B_K f>,
    ||A_D* f||^2
      = sum_{d1,d2} mu(d1)mu(d2)/sqrt(d1d2) Gamma_f(log d1,log d2),
    Gamma_f(a,b)
      = integral_0^{L-max(a,b)} conjugate(f(t+a)) f(t+b) dt.

Terms with a>=L or b>=L are zero. If a<=b<L and h=b-a, the integral
is from a to L-h of conjugate(f(u))f(u+h). Thus this is a
tail-truncated autocorrelation, not a function of h alone.

Gamma is a positive Gram matrix. Its positivity and the entry bound
|Gamma|<=||f||^2 only yield ||A_D* f||^2=O(D)||f||^2.
An abstract sign-aligned rank-one Gram saturates the corresponding
triangle bound; it is not asserted to arise from these physical shifts.
The other factor has ||B_K||=O(sqrt(K)log(2K)), so unrefined block
Cauchy gives O(sqrt(DK)log(2K)), hence only sqrt(m) times logarithms
after summing active blocks. The original signed pairing could still
be smaller; this is not its lower bound.

Any claimed improvement must estimate this source-specific kernel or
retain additional signed cancellation before Cauchy. In particular,
separate block norms may discard compensation between blocks and the
continuous term. No saving, no proof status change, and no extra
message to the running Proshka are inferred from this calculation.
