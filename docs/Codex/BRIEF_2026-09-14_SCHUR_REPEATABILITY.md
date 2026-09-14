# Source-pinned brief: repeatable exact compensation

STATUS: BOUNDED_EXPLORATORY_DISCOVERY; not canonical admission.
OWNER_REQUEST: repeat the positive-square / preserved-residual step for every finite family.
SOURCE_BASE: 8ec0ed1cfaf2de5e394ebd94679fe300c3e24015.
SOURCE: docs/Codex/REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md,
SHA256 51168fb802d7facfb74291d0a3fc0009b121f540711df2fe10ae01cd84c1d14f.

## Exact target and consumer

f=Phi/||Phi||_2 is the unchanged positive even full theta source.
I=(-log(2)/2,0). V(x,y)=integral_0^infinity (2t+x+y) f(t+x) f(t+y) dt.
For arbitrary finite nodes in I and arbitrary complex coefficients, the desired
consumer is sum conjugate(c_i) V(x_i,x_j) c_j >= 0.
Completing one square at a leaves S_a(x,y)=V(x,y)-V(x,a)V(a,y)/V(a,a).
Need an independently proved source property that supplies PSD of the full
residual and survives successive eliminations, including zero pivots.
The canonical theorem/consumer edge is unbound; exploration only,
INCOMPLETE_NO_CONSUMABLE_TARGET. No supplier dispatch or admission.

## Proven facts and explicit negative control

Pinned report R1--R7: strict concavity log f(sqrt(s)), all raw two-node
matrices positive definite at distinct real nodes. R15: S_a(x,x)>0 for x!=a.
R8: entrywise Gram domination is not a quadratic-form order.
R9--R13: f0(u)=exp(-u^2)-exp(-2u^2)/4 has the same strict concavity,
all two-node forms positive, but a negative four-node finite row in I.
The variant f_delta=f0 exp(-delta cosh(2u)) retains that failure for small
delta>0 with double-exponential tails. These are not theta counterexamples.
A proposed preservation criterion must therefore use more than these properties.

## Own search rewrites (UNVERIFIED until proved in the report)

A. Anchor removal / innovations / Christoffel transform:
S_a vanishes when either variable is a. Divide it by (x-a)(y-a) and
look for a positive-kernel representation of the divided residual.
A fresh positive-source V kernel cannot itself vanish at an anchor.

B. Logarithmic interactions / infinite divisibility / negative-type distances:
C(x,y)=partial_x partial_y log V(x,y),
H_a(x,y)=log[V(x,y)V(a,a)/(V(x,a)V(a,y))].
Look for a source-derived PSD representation of C or H_a that gives
S_a through exp(H_a)-1 and tensor squares. Do not assume V is PSD to start.
This may be strictly stronger than positivity of V and must be tested as such.

## Bounded work and evidence

Read existing shelf first; query three dictionaries: Schur innovations,
Christoffel divided kernel, Schoenberg infinitely divisible kernel.
Then fetch primary sources only for the unresolved precise mechanism.
Stop after a source-verified mechanism, exact application/preflight to V,
explicit negative-control discrimination, and a precisely stated remaining
source inequality or a scoped obstruction. Do not promise all-rank closure,
launch a size-by-size numerical campaign, or resend completed Proshka requests.
Owned output: this brief and REPORT_2026-09-14_SCHUR_REPEATABILITY.md in docs/Codex.
Ephemeral evidence: sibling schur-repeatability/ directory outside the worktree.
