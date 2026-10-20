# Q04 waiting result: positive per-prime returns remain too large under operator balancing

2026-10-20. Independent bounded PAPER review ccm_q01_return_review: PASS for the abstract family, operator balance expansion, domain and source scope. Q04 is already running.
NOT sent as a second question. Original N=m,L=log m,M=floor(m^epsilon),P.

## Abstract family on the actual source

Write Q_n=P Q_M(log n)P on ran(P), a_n=Lambda(n)/sqrt(n)>=0,
D=P(A_arch-c_A I)P, ||D||<=50L+8. Suppose for each source n there are
positive semidefinite matrices G_n,H_n on ran(P) satisfying

    H_n = G_n-a_n Q_n.

Then H=sum H_n>=0, G=sum G_n>=0 and the EXACT full source has

    P K_m P = H-E,       E=G-D.

This includes independent prime-square constructions but imposes no scalar
or commuting restriction on G_n. Both positivities are hypotheses defining
this family, not asserted of an arbitrary positive realization of K.

Use the unit ORIGINAL vector c_m of CCM_Q03_ACTUAL_PRIME_BLOCK_OBSTRUCTION.md.
For I_m={n: exp(-1/2)m<n<=exp(-1/4)m}, that checked theorem proves

    sum_(n in I_m) a_n <c_m,Q_n c_m> >= c sqrt(m)/L^9

for every sufficiently large cell, with absolute c>0. Since H_n>=0,
<c_m,G_n c_m>>=a_n<c_m,Q_n c_m> for each n in this block.
Since G_n>=0, all remaining n contribute nonnegatively. Therefore

    <c_m,E c_m> >= c sqrt(m)/L^9 - 50L -8.             (1)

So E<=C_epsilon m^eta P is impossible in this entire family for fixed eta<1/2,
even on an unbounded original subsequence. No uniform choice of G_n can
change this conclusion. The witness belongs to the sparse band eventually
for every fixed epsilon>0. All prime powers and mixed modes remain.

## Positive operator balances are included

For each n let R_n be ANY bounded strictly positive invertible operator on
H=L2([0,L]); there is no uniform bound on R_n or its inverse across cells.
Let I synthesize original constrained Fourier vectors and V_n be causal shift.
Set

 G_n=a_n I*(R_n+V_n*R_n^(-1)V_n)I,
 H_n=a_n (R_n^(1/2)I-R_n^(-1/2)V_n I)*
          (R_n^(1/2)I-R_n^(-1/2)V_n I).

Both are positive; exact multiplication R_n^(1/2)R_n^(-1/2)=identity
keeps the two cross terms I*V_n I and its adjoint. Thus H_n=G_n-a_n Q_n
without assuming R_n commutes with V_n or with P. Formula(1) applies.
Finite-dimensional matrix balances are special cases. Unbounded balances
would require separate domain control and are not claimed covered.

## Decision and strict limits

Switching from scalar to operator weights within INDEPENDENT POSITIVE
PER-PRIME RETURNS does not repair the subpower cost. The logarithmic power9
is weaker than the scalar-specific9/2 obstruction but covers a larger family.
This is not a claim against every non-scalar or geometric construction.
A successful alternative can have signed return pieces that cancel across n,
or retain positive H jointly with E instead of discarding it. Formula(1)
is an obstruction on E, not on the full H-E and not on the target T_gtR.
The actual prime-block theorem, not an arbitrary-coefficient counterexample,
is what makes this exclusion apply to the source. No new full exponent.

Record for comparison with eventual Q04, no new Pro message or interruption.
