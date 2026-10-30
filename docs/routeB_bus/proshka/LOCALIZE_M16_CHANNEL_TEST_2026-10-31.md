# LOCALIZE m16 source-channel test

Scope: one literal CCM even cell m=N=16, cached index0 ground input.
The interval calculation is conditional on the coordinate enclosure. Identifying
it with an exact ground eigenvector inherits the eigensolver-enclosure premise;
componentwise residual containment alone does not establish that premise.
No cofinal supplier, strict descent, NOESCAPE or RH is claimed.
Input: ../thetagrade_2026-10-28/noescape_m16_ground_eigenpair.json,
interval-normalized ground block. The older eigenpair cache is index1.

Choose fixed even chi=1 on |x|<=1/4 and chi=0 on |x|>=1/2.
On the transition put u=4|x|-1, theta(t)=exp(-1/t),
chi=theta(1-u)/(theta(1-u)+theta(u)). This extends smoothly by 1 and 0.
Set a0=log3>2R=1 and w=ceil(sqrt16)=4. Every prime power n>3 through16
belongs to F_far; the remaining atoms belong to the near term. All physical
window clipping points must be retained in integration.

## Edge contribution: certified absolute source bound

For kappa=chi², ||kappa'||_infinity<=64: the transition denominator is
at least exp(-2), each theta derivative is at most4exp(-2), hence a loose
quotient bound |chi'_u|<=8 and |chi'_x|<=32 suffice.
Let delta=||f_edge|| for even modes13,...,16, Omega=2pi*16/L,
r=(I-P)(kappa f_edge). Then

 ||r||<=delta,
 ||r'||_L2(I)<=(64+2Omega)delta,
 J(r)<=2sqrt(33/L)delta.

The last line uses zero endpoint values of kappa f_edge and the exact
carrier evaluation norm; it does not ignore the endpoint jumps of r.
LOCALIZE L2 gives

 |E|<=B_m(f) delta sqrt(10(64+2Omega)²+40*33/L+20+d_m),
 B_m(f)²<=10 sum_i omega_i² c_i²+10 J(f)²+20+d_m,
 J(f)=2|c0+sqrt2 sum_(i=1)^16 c_i|/sqrt(L).

The signed endpoint sum is evaluated before taking its absolute value.
All source components, including the scalar, full arch tail, prime powers
and both pole operator costs, are included in d_m and this majorant.
Direct Arb evaluation at100dps with the cached coordinate balls gives

 delta approximately2.10559410031508e-9,
 |E| < 0.00001185.

The stored symmetric enclosure is [-0.00001185,0.00001185]. This is an
absolute upper bound, NOT a measured value or a sign determination of E.
It uses neither stationarity nor recovery from the local-energy identity.
Script/data: ../thetagrade_2026-10-28/localize_m16_edge.{py,json}.
Independent bounded analytic review checked derivative, endpoint and majorant
factors and independently reconstructed the number at high precision; root
executed the directed-Arb bound and its strict rational-threshold assertion.

## Direct far contribution

Direct Arb interval integration with 262144 half-interval cells gives

 F_far in [-0.000036014, -0.000014079],
 E+F_far < -0.000002229.

These are outward rational bounds, asserted in the executable. The coarse
Arb display [+/−3.61e-5] loses the sign; use the detailed endpoint bounds.
All prime powers 4,5,7,8,9,11,13,16 are retained before support clipping.
Only 4 and 5 have positive-measure support on the chosen positive half-window;
the plus shift at n=4,x=0 is a measure-zero endpoint.
Monotonicity of chi gives an endpoint range on each cell; interval trigonometric
evaluation and exact cell widths enclose the integral. Dyadic breakpoint
slivers enclose both active and zero branches. For the continuum part,
with sigma=+1 or -1, an exact antiderivative is

 exp(a/2)[cos(omega(x+b+sigma a))/2
          +sigma omega sin(omega(x+b+sigma a))]/(1/4+omega²).

Root SymPy differentiation verified both signs exactly. Each integral ends
at the actual window cutoff b-sigma*x, and is zero if that cutoff is below
a0. Do not integrate a zero-extended trigonometric polynomial beyond its
window. No channel has been inferred by subtracting from an energy identity.
Near/off-edge and complete normalized-return budgets are not yet certified
as a joint channel test; LOCALIZE_SOURCE_CHANNELS_CERTIFIED is NOT claimed.

Script/data: ../thetagrade_2026-10-28/localize_m16_far.{py,json}.
Independent bounded source/code review PASS: phased basis, even factor, all
prime powers, clipping, primitive signs, interval ranges and rational comparisons.
The edge and far bounds use the same cutoff and normalized coordinate input.
Neither calculation uses exact minimality or the escape hypothesis. Thus this
finite negative sum is not yet a discriminator against escaping radical trials.
The first unpaid comparison is the near/off-edge contribution together with
the full projection-return numerator; its errors must fit the negative margin.
A cofinal source estimate specific to escaping exact bottoms remains OPEN.

For an exact unit bottom with eigenvalue lambda, write z=chi f,
e=(I-P)z, R_near=mathscr B-E-F_far. The full comparison is precisely

 N_lambda = E+F_far + R_near+I_chi
            -2 Re k(z,e)+k[e]+lambda ||e||².

The admissible even same-carrier candidate is g=Pz/||Pz||. Its denominator
is positive because <f,Pz>=integral chi|f|²>0 for nonzero analytic carrier f.
Exact minimality is used only in N_lambda>=0; a strict negative source upper
bound would contradict it. For the present finite bound, an upper bound on
R_near+I_chi-2 Re k(z,e)+k[e]+lambda||e||² by 0.000002229 would suffice,
conditional on the input being an exact bottom. Such an upper bound is NOT
proved and cannot hold for a genuine bottom if the preceding bounds are valid.
The research task is to derive a contradictory sign under complete escape,
not to expect an unconditional descending competitor for the m16 bottom.
For a trial with rho=k[f], the additional residual pairing is retained and
minimality yields only N_rho>=-(rho-lambda_min)||Pz||². Small residual does
not bound rho-lambda_min. This is the exact trial-control distinction.

## Full returned competitor: direct finite comparison

The full matrix calculation now independently evaluates v=P_16(chi f),
g=v/||v|| and k[g]-lambda using CCMArbBuilder(16,16).even_block().
All original source terms and prime powers are retained by that builder;
there is no inference of a source channel from the localization identity.
The 17 coefficient integrals are direct Arb interval Riemann sums, with the
same even phased basis, cutoff, coordinate input and exact factor two.
Both 8192 and32768 half-window cells separate the positive sign. At32768,
outward decimal bounds verified from the detailed Arb endpoints are

 ||v||² in [0.963892, 0.964126],
 k[v]-lambda||v||² in [0.006792, 0.007740],
 k[g]-lambda in [0.007005, 0.008070].

Both energy comparisons exceed the checked rational bound 1/1000.
This particular cutoff competitor INCREASES energy on the finite input.
Its positive denominator, evenness and original finite-carrier membership
are explicit. The eigenpair identification retains the conditional premise
above; the comparison itself uses direct coefficient and matrix enclosures.
The source/code review independently checked phase, factors, normalization,
full builder and hashes. The run took1.307s; root checked the three outward
bounds and matching script hash. Script/data:
../thetagrade_2026-10-28/localize_m16_cutoff_return.{py,json}.
No standalone near-term integral was computed. The finite full comparison
closes this candidate test without separating that remaining contribution.

The existing unsigned short-shift allowance is
K_log3=log(2)/sqrt(2)+log(3)/sqrt(3)+2(sqrt(3)-1)
=2.58851478746959216..., over a million times the proven 2.229e-6
negative partial margin. That allowance cannot certify descent here.
The full comparison proves that the aggregate remainder actually overwhelms
the partial gain, conditional on the same exact-bottom input; this is an
identity consequence, NOT an independent near-channel measurement.

The finite cutoff test is complete, but no cofinal cutoff mechanism is killed.
The requested escape-specific source inequality remains OPEN. Before choosing
another mechanism, the next semantic return tests the spectral-pollution
literature against NOESCAPE L4 strong-resolvent convergence to zero and the
fixed-negative-energy branch forced by an off-critical zero. Near-zero radical
trials must not be confused with that branch. No new supplier is assumed.
