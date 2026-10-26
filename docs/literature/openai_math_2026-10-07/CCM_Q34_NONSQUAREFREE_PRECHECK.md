# Q34 independent nonsquarefree-sector precheck

2026-10-26. Root derivation and one bounded independent read-only audit PASS,
conditional on accepted Q08/Q33 source identities and weighted-LCM derivative
and contact bounds. Prepared while Q34 is still responding; not an extraction
of its final answer, and no extra message sent. Full C5/CCM estimate remains OPEN.

Keep original N=m,L=log m,M=floor(m^epsilon), three-contact P, and auxiliary
Z=floor(m^(epsilon/4)). Let a_Z(n)=lambda_Z(n)^2/C_Z^2=sum_{d|n}g_d,
with actual signed divisor coefficients from CCM_WEIGHTED_LCM_RETURN_CONCLUSION.md.
They obey G=sum_d|g_d| <=(sum_{d<=Z}tau(d))² <=Z²(1+log Z)².
All divisor cross terms are included in g_d; no diagonal-only replacement.

For real x>=1 and every integer d>=1, exact square-divisor inclusion-exclusion is

 sum_{n<=x,d|n}mu(n)^2
   =sum_{a<=sqrt(x)}mu(a)floor(x/lcm(d,a²)).

Define h_d=sum_{a>=1}mu(a)/lcm(d,a²). Absolute convergence follows from
lcm(d,a²)>=a². Floors cost at most sqrt(x); the tail after floor(sqrt(x))
costs at most 2sqrt(x). The squarefree count differs from x h_d by <=3sqrt(x),
uniformly in d. Subtraction from floor(x/d) gives nonsquarefree error <=4sqrt(x).
Hence the actual nonnegative weighted nonsquarefree count satisfies

 A_ns(x)=sum_{n<=x,mu(n)=0}a_Z(n)=beta_Z x+E_ns(x),
 beta_Z=sum_d g_d(1/d-h_d), |E_ns(x)|<=4G sqrt(x).

The density exists for each fixed Z. Nonnegativity of the source counts and
of their squarefree complement, together with the inherited full mean 1/C_Z,
give 0<=beta_Z<=1/C_Z. No sign is assigned separately to g_d or h_d.
The error constants are uniform in Z, so the finite bound applies to Z=Z(m).

Set F(x)=log(x) P Q_M(log x)P/sqrt(x). The exact inherited source satisfies
F(1)=F(m)=0 and

 ||F'(x)|| <=[2+(1+D_M)log x]x^(-3/2), D_M=(2+8pi M)/L,
 ||integral_1^m F(x)dx||<=8.

Matrix-valued Stieltjes integration thus gives, with both times and all complex
mixed entries retained,

 sum_{n<=m,mu(n)=0} a_Z(n)F(n)
   = beta_Z integral_1^m F(x)dx - integral_1^m E_ns(x)F'(x)dx,
 norm <=8/C_Z+4G[2L+(1+D_M)L²/2].

The n=1 atom vanishes and Q_M(L)=0 pays the n=m atom exactly. Every
nonsquarefree n>1 is composite; proper prime powers remain included.
To restrict this to the actual C_comp range n>Z, subtract the complete short
block. The elementary norm price <=4Z^(5/2)log Z follows from a_Z<=Z²,
||P Q P||<=2 and sum_{n<=Z}1/sqrt(n)<=2sqrt(Z). It suffices here even though
stronger inherited short bounds exist. Therefore this full sector costs

 O_epsilon(m^(3epsilon/2)L³)+O(m^(5epsilon/8)L).

The original remaining squarefree-composite part is NOT discarded or signed.
A lower bound for it is still needed; this sector result gives no full exponent
gain. The rough semiprimes in H6 remain squarefree, so the prior norm-certificate
obstruction is consistent with the sector removal.

Validation: root ran192 exact integer count controls (six x through512,d1..32).
Independent q32_annulus_audit checked density, constants, original endpoints,
matrix Stieltjes transfer, mixed terms and exponent. Bounded PASS conditional
on inherited source inputs, not a new Lean/Arb or full-spectrum certification.
Compare with the eventual complete Q34 before deciding the next branch.
