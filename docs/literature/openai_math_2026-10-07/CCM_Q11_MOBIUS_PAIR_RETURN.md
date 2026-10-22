# Post-Q10 replay audit: actual parity pairing, full cutoff return

2026-10-21. PAPER calculation independently checked by q11_mobius_pair_test. Actual
mu coefficients, original P,Q,N=m,L=log m and integer R>=2 retained.
This is a test of an arithmetic mechanism, not a new full exponent.

Write A(n)=P Q(log n)P, ||A(n)||<=2. The source is exactly

 T=sum_{d>R,dk<=m} mu(d)log(k)/sqrt(dk) A(dk).

For odd d, mu(2d)=-mu(d); multiples of4 have mu=0. Thus the COMPLETE
identity is T=C+U+B, where

 C=sum_{d>R,d odd} mu(d)/sqrt(d)
       sum_{k<=m/(2d)} log(k)/sqrt(k)
       [A(dk)-2^(-1/2)A(2dk)],
 U=sum_{d>R,d odd} mu(d)/sqrt(d)
       sum_{m/(2d)<k<=m/d} log(k)/sqrt(k) A(dk),
 B=-sum_{R/2<d<=R,d odd} mu(d)/sqrt(2d)
       sum_{k<=m/(2d)} log(k)/sqrt(k) A(2dk).              (1)

All inequalities have literal integer summation endpoints. k=1 has zero
logarithm, not a removed arithmetic atom. U is the original upper product
strip. B is the original divisor-threshold strip: an even divisor2d may
exceed R while d does not. Neither has been discarded or assigned a sign.
This identity reorganizes the actual coefficients, retaining all modes,
prime powers and mixed terms through the unchanged matrix A.

## What the pairing does, before pretending it gives a gain

On full-line physical functions, with U_b translation by b=log2,
A_parity=I-2^(-1/2)U_b has

 (1-2^(-1/2))||v|| <= ||A_parity v||
                        <=(1+2^(-1/2))||v||.            (2)

Reverse triangle and unitarity suffice. Its Fourier factor is
1-2^(-1/2)exp(-it log2), uniformly bounded away from zero. A single fixed
Euler factor therefore does not automatically supply m^(-delta) attenuation
of the unsymmetrized full-line source. This is a constant-scale comparison,
not a bound on the final signed arithmetic sum.

In particular (2) is NOT a lower bound for
Q(s)-2^(-1/2)Q(s+log2): the latter also takes the adjoint/real part and
compresses to a finite interval and the original P. Those operations may
create cancellation. No invertibility or Loewner lower bound is transported
through them. The finite-source formula actually used is (1), with both
strips paid explicitly below. Adaptive products of many primes are not ruled
out by this fixed-prime test.

## Honest complete budget from the available estimates

The direct paired-kernel norm is at most2+sqrt(2). For X>=1,
sum_{k<=X}log(k)/sqrt(k)<=2sqrt(X)log(X). Using |mu|<=1 only AFTER (1),
and sum_{d<=m}1/d<=1+L, yields

 ||C|| <=(2+2sqrt(2))sqrt(m)L(1+L),
 ||U|| <=4sqrt(m)L(1+L),
 ||B|| <=4sqrt(m)L.                                    (3)

For B use sum_{R/2<d<=R}1/d<=2; restricting to odd d only reduces this
positive majorant. Consequently ||T||<=13sqrt(m)L(1+L).
This is weaker than the existing elementary full-source budget. It pays the
complete original source but gives NO new power. The |mu| step has lost the
very interaction the pairing was intended to exploit; no stronger signed
estimate was derived here. Large separate strip prices in this budget are
not lower bounds for the actual strips or a no-go theorem for other returns.

## Verification and decision

ccm_mobius_pair_q11_checks.py checks (1) on3080 pairs (m,R),4<=m<=80,
2<=R<m, with exact formal logarithms of primes at each n. Thus equality is
checked BEFORE multiplying by the unchanged A(n)/sqrt(n), without floats.
Both planted omissions (U and B separately) are detected. Finite checks do
not prove a cofinal inequality; the identity proof is the parity partition.

The independent shelf audit found the broader general-q regrouping already
in CCM_FIXED_PRIME_COMPRESSION_TEST.md Q1-Q3 and the Q08 request.
This C/U/B presentation is a replay, not a new arithmetic mechanism. Existing CCM_LONG_MOBIUS_PRIMITIVE_TEST.md and
CCM_Q03_AFFINE_RETURN_TEST.md already exclude treating a scalar restatement
as a supplied arithmetic estimate. No old identity is renamed as progress.

Decision: one actual arithmetic regrouping tested, no full gain. Do not send
Pro merely 'use mu(2d)=-mu(d)'; a viable extension must control the signed
common sum AND U+B without a half-power return. This replay does NOT increment the substantive post-Q10 attempt counter. Goal ACTIVE. No Q11 send, no RH/CCM closure.
Independent bounded q11_mobius_pair_test PAPER PASS; reviewer reran3080
checks and verified constants and both strips. Existing direct bound4sqrt(m)L(1+L)
is stronger than13sqrt(m)L(1+L). Duplicate-mechanism finding incorporated
2026-10-22. Next genuine candidate: audited norm/coefficient transfer from
MangoldtDivisibilityEnergy.lean, an existing shelf lead with an unpaid lift.
