# Q11 answer discriminator: local vector sampling and its norm cost

2026-10-22. Root PAPER derivation; independent q11_local_lift_audit bounded PAPER PASS.
The interval-domain continuity and d<m endpoint qualifications were checked.
This refines the specified sampling family of CCM_Q11_DIVISIBILITY_LIFT_PREFLIGHT.md.
It is not a new bound for the actual CCM and not a new Pro request.

## Exact scope

Fix m>2, L=log m. Let a:[0,L]->C^J be continuous, with finite J.
For integer X->infinity set c_n=X^(-1/2)a(log(n/X))f(log(n/X))
when X<=n<=Xm and zero otherwise. Apply the existing scalar graph theorem
componentwise and sum. Inner products conjugate the first factor.
This allows finite positive mixtures of local sampling maps by absorbing
square roots of the mixture weights into the components of a.
It does not cover arbitrary nonlocal maps or all forms of scale averaging.

For fixed m and every continuous scalar f, ordinary Riemann sums give

 lim sum_n ||c_n||^2 = integral_0^L e^t||a(t)||^2 |f(t)|^2 dt,

 lim G[c] = 2 Re sum_{2<=d<=m} Lambda(d)/sqrt(d)
   integral_0^(L-log d) H_d(t) conjugate(f(t)) f(t+log d) dt,

 H_d(t)=e^t <a(t),a(t+log d)>.

There are finitely many d at fixed m. Endpoint values are immaterial;
the d=m edge has zero limiting length. No prime powers or mixed terms
are omitted. The original source requires the multiplier H_d=1.
Here we test literal edge-by-edge recovery, not merely equality of the
summed compressed form on the original finite-dimensional P.

## Pointwise isometry obstruction

If the limiting norm equals ||f||_L2^2 for every continuous test f,
then e^t||a(t)||^2=1 everywhere by localization and continuity.
For h=log d, Cauchy-Schwarz therefore gives

 |H_d(t)| <= e^t ||a(t)|| ||a(t+h)|| = e^(-h/2)=d^(-1/2).

Thus H_d cannot equal 1 on a positive-length edge for d>1.
For theta=1/2 this recovers the old Lambda(d)/d coefficient. Adding
finitely many channels, phases, or positive local mixtures does not
remove the missing sqrt(d) while retaining this global physical isometry.

## Quantitative norm distortion

More generally suppose the limiting norm is at most K||f||_L2^2 for
EVERY continuous test f. Localization gives e^t||a(t)||^2<=K, so

 |H_d(t)| <= K/sqrt(d).

Literal H_d=1 on every active edge with d<m consequently requires
K>=sqrt(d). Choose the largest power of 2 strictly below m. It satisfies
m/2<=d<m and Lambda(d)=log2>0, hence

 K >= sqrt(m/2).

This is a necessary condition for that exact local edge-intertwining
construction. It is not an existence theorem for such a construction.
Paying the graph bound only through [log N+log4+4] times this global norm
cap cannot itself furnish a subpower certificate: its norm fee is already
at least half power. The additional log(Xm) / quadrature issue from the
preflight remains separate and unpaid.

## What this does NOT rule out

The original CCM needs a one-sided estimate only on ran P. A norm bound
restricted to that subspace does not imply the pointwise bound above.
A map may be nonlocal, may exploit the actual summed arithmetic, or may
supply one-sided domination without literal edge-by-edge identification.
Such mechanisms are not excluded by this discriminator. No Loewner
comparison follows by comparing individual coefficients in absolute value.
No lower bound for the actual S, T_{>R}, or K_m is asserted.
No numerical source evaluation, Lean run, or arithmetic exponent gain.

Use this only to audit a proposed local lift in the Q11 response. Do not
send it into the running/previously sent request or count it as a third
independent mechanism attempt: it is a refinement of attempt2.
