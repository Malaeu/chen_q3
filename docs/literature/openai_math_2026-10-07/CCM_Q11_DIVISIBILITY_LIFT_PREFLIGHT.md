# Post-Q10 attempt2: the counting-space divisibility cap needs a genuine lift

2026-10-22. Root calculation; independent q11_divisibility_lift bounded PAPER PASS.
Source: MangoldtDivisibilityEnergy.lean, definitions16-25 and
primeForm_le_log. This file inspects its statement, not a fresh Lean build.
The exact local lead was already recorded in CCM_COMPOSITE_SIGN_TARGET.md;
no new supplier is claimed merely because its theorem is formalized.

## Consumer and candidate

Keep original N=m,L=log m, Fourier band and three-constraint P. For f=Fc,
||f||_2=||c||, the desired full prime form is

 S[f]=2 Re sum_{2<=d<=m} Lambda(d)/sqrt(d)
         integral_0^(L-log d) conjugate(f(t)) f(t+log d)dt. (1)

All proper prime powers and mixed Fourier terms are retained. The graph
supplier instead bounds, for sequences c_n with counting norm,

 G_N[c]=2 Re sum_{nd<=N} Lambda(d)/sqrt(d) conjugate(c_n)c_(nd)
      <=[log N+log4+4] sum_{1<=n<=N}|c_n|^2.             (2)

Its proof is an exact square-energy expansion using sum_{d|j}Lambda(d)=log j.
No arithmetic hypothesis is missing INSIDE (2). The missing bridge is the
coefficient carrier and its norm.

## Test a natural family without hiding a Jacobian

Fix m and a real theta. Let integer X tend to infinity, N=floor(Xm), and set

 c_n=X^(-1/2)(n/X)^(-theta) f(log(n/X))
       for X<=n<=Xm, and zero otherwise.                 (3)

For the original finite Fourier polynomial f all Riemann limits below exist.
Endpoint f(0)=f(L)=0 is retained; isolated equality endpoints do not affect
these limits. In a nonzero graph edge both n and nd are in support, hence
d<=m; there are only finitely many d at this FIXED m. Thus

 lim_X sum |c_n|^2 = integral_0^L exp((1-2theta)t)|f(t)|^2dt, (4)
 lim_X G_N[c] =2 Re sum_{2<=d<=m} Lambda(d)d^(-1/2-theta)
   integral_0^(L-log d) exp((1-2theta)t)
                         conjugate(f(t))f(t+log d)dt.     (5)

Proof: c_n conjugate(c_nd) contributes X^-1 d^-theta
(n/X)^(-2theta), and the sum has mesh dx=1/X. Substitution x=exp(t)
contributes the additional exp(t). Conjugating in the opposite order gives
the same real form. No coefficient or endpoint has been suppressed.

At theta=1/2 the limiting norm is exactly the desired physical L2 norm, but the
coefficient is Lambda(d)/d, NOT Lambda(d)/sqrt(d). At theta=0 the coefficient
matches, but the physical weight and norm are exp(t)dt, NOT dt.
No fixed theta makes both literal matches. Multiplying (3) by a single
scalar changes both forms together and cannot fix a d-dependent discrepancy;
a phase does not change its absolute factor d^-theta.
This rules out direct identification in this specified sampling family,
not every possible map or a source-specific cancellation on P.

Also, (2)'s right side contains log(Xm). Taking X->infinity at fixed m
is not a finite logarithmic bound for the limiting operator. To take a
quantitative X=m^B instead requires a uniform quadrature return. Even a
perfectly paid quadrature would not repair the coefficient mismatch above.

## What happens if the graph weights are repaired instead

For theta=1/2 one could replace graph weights Lambda(d) by
w_d=Lambda(d)sqrt(d). Then (5)'s coefficient becomes the desired Lambda(d)/sqrt(d).
But the square-energy proof now has outgoing diagonal

 B_w(N/n)=sum_{d<=N/n} w_d/d=sum_{d<=N/n} Lambda(d)/sqrt(d),

and incoming diagonal sum_{d|j} w_d, not log j. For the full graph at
a prime j this incoming diagonal is sqrt(j)log(j), already incompatible
with reusing the old uniform logarithmic diagonal cap. This concerns the
modified graph majorant, not the actual CCM form. At n=X,N=Xm the outgoing
diagonal is the complete half-power weighted prime sum. The cheap logarithmic
cap of (2) therefore cannot be reused with the changed weights. The elementary O(sqrt(m)) estimate here applies ONLY to this outgoing
row, not to the complete modified diagonal; no subpower
bound is derived. This is a limitation of that diagonal-majorant transfer,
not a lower bound for the desired full compressed operator.

In particular do NOT multiply the theta=1/2 matrix upper bound by sqrt(m)
and call it a valid Loewner comparison: individual translation forms can
be negative, so a scalar coefficient comparison is insufficient.

## Decision

The known graph theorem is genuine, but the simplest counting-to-log sampling
bridge does not deliver (1). One must supply a different exact map with paid
norm/coefficient return, or use additional signed arithmetic. This is one
substantive post-Q10 mechanism test (attempt2 after the projected Mellin test).
The parity regrouping replay is NOT counted. No actual exponent improved;
CF22 parked, goal ACTIVE, RH OPEN. No Q11 message sent.
Independent readonly q11_divisibility_lift PAPER PASS after correcting the
weight-repair discussion to separate incoming and outgoing diagonals.
No Lean/build/numerical source runs. Read-only supplier_preflight returned
INCOMPLETE due to shelf freshness, not an absence result or exact fit.

Continuation: the root has no paid alternative carrier map for this concrete
supplier. The next same-chat Pro question may be triggered by that actual
bridge impasse, without manufacturing a third distinct attempt from the
parity replay. Ask for a quantitative source-preserving nonlocal use of the
divisibility energy, or a documented rollback; do not assume such a lift.
This does not assert that the requested bridge is impossible.
