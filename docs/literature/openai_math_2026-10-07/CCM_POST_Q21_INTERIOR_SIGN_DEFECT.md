# After Q21 — interior sign reversal retains the corrected certificate price

2026-10-25. Root derivation, conditional on the inherited Q21 source/returns.
Fix Delta>0. Choose nonnegative nonzero symmetric smooth bump eta supported
inside (2Delta,5Delta/2), symmetric about its midpoint c. Set q=(-eta''+eta/4)
normalized in L2. It is symmetric, has both exponential contacts zero, and
is positive at the bump maximum c. Since its contact integral integral exp(-t/2)q(t)dt is
zero and q is nonzero, it has a negative value; symmetry supplies one to
the LEFT of c. Choose disjoint closed positive interval J+ about c and
negative interval J- left of it, with 0<v-u<Delta for all v in J+,u in J-.
Then f_L=(q(t)+q(L-t))/sqrt2, and its real normalized original sparse-P
return f_m, have positive values on J+ and L-J+, negative on L-J-.
The same uniform sup/L2/H1 return as Q21 applies (fixed profiles).

For x,v in J+, y=L-v, d=L-x-v, restrict routes so z=x+log n=L-u,
u in J-. Thus s=log n-d=v-u lies strictly inside (0,Delta), z is INSIDE
I and n<m (log n=L-x-u<L). All these original prime powers remain.
Fixed-relative-shell PNT gives a uniformly positive fraction of c_n/C_Delta(d)
on this subinterval, uniformly x,v in fixed J+. k(d)>=c_Delta sqrt(m).

For arbitrary positive rho,tau, f_m(x)>0, f_m(y)>0, f_m(z)<0 imply
A=u(z)-u(x)<0 and B=u(z)-u(y)<0. Hence
rho(x)rho(y)|tau A+B|²/tau >=4rho(x)rho(y)AB >=4f_m(x)f_m(y).
This uses real f_m; its sign intervals survive projection uniformly and
requires no comparison of rho-dependent operators through projection.
Therefore Xi_in[f_m]>=c sqrt(m), uniformly all allowed rho,tau.
Exactly as Q21, contacts cancel full PNT convolution main and Q[f_m]=o(sqrt(m)).
So (H-Xi_ext)-Eplus=Xi_in-Q>=c sqrt(m) eventually on this vector.
Upper is still <=H<=C sqrt(m) for rho_L,tau1. Thus corrected certificate,
for same routing/fixedDelta but deleting ALL exterior slack, still has
inf_rho,tau sup_unitP positive excess asymp sqrt(m).

Scope: this would exclude only discarding interior Young slack as well;
not all routing, variable Delta, pair-only bound or actual CCM. No actual
negative eigenvalue or new favorable exponent follows. Independent bounded audit completed below. The root has not sent this to Proshka.

For J-=[u0,u1], the routing fraction tends uniformly in x,v to
 p(v)=exp(v/2)*(exp(-u0/2)-exp(-u1/2))/(exp(Delta/2)-1)>0.
The interval choice ensures this is a subinterval of the full shell.
Fix p0=min_(v in J+)p(v)/2>0 for all late cells. This gives the uniform
positive mass without a shrinking interval PNT or omitted prime powers.
At negative fz, the gauge-independent AMGM step uses
 rho_x rho_y A B - fx fy
 =rho_x rho_y fz²/rho_z²-fz*(rho_y fx+rho_x fy)/rho_z >=0.
This replaces exterior-zero logic; it does not rely on exact compact
support after projection. The physical shape is not the actual zero pair,
so the result is only an all-vector certificate obstruction.

Independent q21_young_defect_audit bounded PAPER follow-up: PASS on the
new interior sign test, separately from the Q21 original audit. Checked
contact construction, uniform sign return, actual shell mass, internal
n<m geometry, gauge-independent inequality and matching upper. Upstream
source and sparse-P estimates inherited, not re-certified. No Lean/Arb
or spectral computation. One own failed completion after Q21; no Q22 sent.
AUTOPSY: dropped=CANCELLATION; note=Two positive Young leg costs lose cancellation even when every intermediate vertex stays inside the physical window.
