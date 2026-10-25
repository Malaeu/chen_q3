# Joint energy path comparison: bounded preflight, no arithmetic bound

2026-10-25. Original full CCM, N=m,L=log m,M=floor(m^epsilon), same P.
Rollback after the translated-witness amplification test, to Q20 retained
energies. No claim of a newly proved comparison or global absence of one.

Q20(3.5),(3.12),(3.13) give, with u=f/varpi,

 Q[f]=E_arch[u]+E_prime,all[u]-E_pole[u].

The n>m prime energies are diagonal returns, not nonzero adjacency beyond
the physical window. They remain in E_prime,all. The two exponential
contacts set R[f]=0 but do not set E_pole to zero. All differences are
complex differences before squaring; no separate phase payment is made.

For a path x0,...,xk and positive edge numbers c_j, weighted Cauchy gives

 |u(xk)-u(x0)|² <= (sum_j c_j^(-1))
                       (sum_j c_j |u(x_(j+1))-u(x_j)|²).

To use this on the actual pole energy requires a distribution of paths
whose induced edge measure, including the resistance factor and every
multiplicity and Jacobian, is dominated by the ACTUAL arch/prime energy
measure. A finite list of prime identities does not supply that domination.
Prime-power jumps carry Lambda(n)/sqrt(n), and continuous jumps carry
 a(s)=exp(-s/2)/(1-exp(-2s)). Both also carry varpi(t)varpi(t+s).

The direct same-edge comparison already fails as a finite uniform
whole-line measure domination: the ratio of continuous pole density to
arch density is exactly

  2cosh(s/2)/a(s)=(exp(s)+1)(1-exp(-2s)).

It is unbounded as s grows. Even on interior separations of order L it
costs order m. The prime measure is atomic in s and cannot supply the
missing continuous density by pointwise domination almost everywhere.
This statement is about that measure domination only: it is NOT a lower
bound for an aggregate path comparison, the constrained quadratic form,
or any actual CCM eigenvalue. In particular the finite-support source has
outside pole edges; they cannot be deleted by restricting s to L.

An aggregate estimate E_pole<=C_m Eplus with Eplus=E_arch+E_prime,all
would imply Q>=-(C_m-1)Eplus. A bounded C_m>1 is not a small additive
defect: one must also pay Eplus in the original ||f||² normalization.
The exact remaining useful line is

 E_pole[u]-Eplus[u] <= b_(m,epsilon)||f||²

on the original three-contact sparse image, with the required subpower
exponent, or a proved sufficient actual-pair version. This line is unpaid.
Introducing it as an assumption or PSD feasibility constraint is not proof.

Next discriminating question: can the contact constraints be used before
positive path congestion is charged to construct such an additive-defect
comparison? No path distribution/congestion certificate has yet been found.
This bounded preflight supplies no new full exponent and no route no-go.
Local literal CCM path/resistance/Poincare search found no matching entry;
this is not a semantic/global literature absence claim. The broader radial
energy and positive-potential methods in Q12/Q20 remain already tested.

## Concrete forward-shell attempt

Bounded researcher joint_energy_path_budget tried h_n=log n in [d,d+Delta],
fixed Delta>0, c_n=Lambda(n)/sqrt(n), C_+(d)=sum c_n in this shell.
Exactly, u(x+d)-u(x)=(u(x+h_n)-u(x))-(u(x+h_n)-u(x+d)).
Weighted Young with parameter tau>0 preserves the difference before bounding:
|A-B|²<=(1+tau)|A|²+(1+1/tau)|B|². Ordinary PNT gives
 C_+(d)~2(exp(Delta/2)-1)exp(d/2) as d->infinity.
Ignoring ONLY FOR DIAGNOSTIC the source-weight ratios, repeated prime-edge
use across width Delta has leading coefficient
 Delta/[2(exp(Delta/2)-1)]<1, before the Young factor 1+tau.
This is not a completed inequality or arithmetic gain.

Root writes the actual prime-edge multiplier, before any supremum, as

 (1+tau) integral_(max(0,h_n-Delta))^h_n
   [K(d)/C_+(d)] [varpi(x+d)/varpi(x+h_n)] dd,
 K(d)=2cosh(d/2).

Where C_+(d)=0 the shell construction is unavailable and that region must
be paid separately. For large d PNT makes C_+ positive; small d is not
silently discarded. For the arch residual put y=x+d,s=h_n-d in [0,Delta].
Its multiplier against a(s)varpi(y)varpi(y+s)dy ds is

 (1+1/tau)/a(s) * sum_(n: h_n>=s)
  [c_n K(h_n-s)/C_+(h_n-s)]
  [varpi(y-h_n+s)/varpi(y+s)],

on the shells where the denominator is positive. All n, including n>m,
remain until the full outside-support return is paid. These formulas are
nonnegative comparison prices, not the actual signed CCM source.
No useful bound for their joint excess in the original norm has been
established. In particular the ratios cannot be set to 1, and C_+ PNT
alone does not control them. Taking pointwise suprema may be unnecessarily
expensive and is not compulsory; contact-aware integrated comparison is
precisely the remaining question. The residual Young cost also prevents
claiming the coefficient below one as a favorable full budget.

Scope: own bounded calculation plus researcher check, not independent
acceptance of an improved theorem. The scalar shell asymptotic and the
full-return obstruction to its naive use identify the Q21 question.
No source-specific aggregate path impossibility is asserted.
