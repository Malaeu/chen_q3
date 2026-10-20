# Q04 own attempt 3: centered second primitive preserves the old power

2026-10-20. Independent bounded read-only check ccm_next_mechanism: PASS after the explicit common-G clarification below; no new prime estimate assumed proved.
Keep original A(t)=P Q_M(log t)P/sqrt(t), original finite band and constraints.
Let psi(x)=sum_(n<=x) Lambda(n), Delta1(x)=psi(x)-(x-1), and
Delta2(x)=integral_1^x Delta1(u)du. This is the actual all-prime-power source.
No truncated prime panel is substituted.

The full smooth term is already paid by the accepted full-window identity:
 integral_1^m A(t)dt=-P H_(1/2)P, ||H_(1/2)||<=4.
Define exact signed remainder
 B=sum_(2<=n<=m) Lambda(n)A(n)-integral_1^m A(t)dt.
Stieltjes integration by parts gives
 B=Delta1(m)A(m)-integral_1^m Delta1(t)A'(t)dt.
Q02 proves A(m)=A'(m)=0 under the ORIGINAL P; Delta1(1)=Delta2(1)=0.
A second integration by parts therefore yields EXACTLY

 B=integral_1^m Delta2(t)A''(t)dt.

There is no endpoint bill omitted. Discontinuities of psi are covered by
Stieltjes integration; Delta2 is absolutely continuous, so the second step
uses its almost-everywhere derivative. All Fourier cross terms remain in A''.
In the shift-square identity the SAME DISCRETE G cancels exactly:
J*J-E=D-A_prime=D+P H_(1/2)P-B. This is not an assertion that
the whole prime-weighted and continuous-weighted Dirichlet energies differ
only by B: comparing those separately also produces G_prime-G_continuous,
which must be retained. No such separate replacement is used here.

Test a supplier ONLY AS A HYPOTHESIS: |Delta1(t)|<=C t^theta(1+log t)^b,
where theta>1/2,b>=0. Then
 |Delta2(t)|<= C t^(theta+1)(1+log t)^b/(theta+1).
Q02 supplies, with Omega=2pi M/L,
 D1=2/L+4Omega, D2=4Omega/L+4Omega^2,
 ||A''(t)||<=(3/2+2D1+D2)t^(-5/2).
Hence

 ||B|| <= C(3/2+2D1+D2)(1+L)^b
          * (m^(theta-1/2)-1)/[(theta+1)(theta-1/2)].

The extra primitive gains one t power, exactly cancelling the derivative's
extra inverse power. With M=floor(m^epsilon) the displayed fee has power
(theta-1/2)+2epsilon up to logs. Even granting theta=7/8 would give
3/8+2epsilon, worse than Q03's conditional 3/8. No theta=7/8 estimate is
newly established here, and no source-zero-free result is silently imported.
Elementary bound |Delta1|<=O(t log t) gives only square-root power plus2epsilon.

This is a failure of this ABSOLUTE second-primitive budget, not a lower bound
on actual B or a no-go for signed integrated prime cancellation. It is distinct
from a claim that higher smoothness cannot ever help. To change the conclusion,
one needs a sharper actual Delta2 estimate or direct signed pairing with A'',
not only another integration by parts. The known continuous cancellation alone
has already been spent in the bounded term -P H P.

No new full exponent, Lean/Arb run or finite diagnostic. Compare Q03 before
sending the next question; do not count the identity itself as arithmetic gain.
