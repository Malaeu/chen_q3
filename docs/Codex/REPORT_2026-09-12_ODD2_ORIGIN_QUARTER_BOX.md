# Full theta ODD2 on the whole quarter-unit origin square

Status: ACCEPTED_PAPER_LOCAL_ODD2_WHOLE_ORIGIN_QUARTER_BOX.
Author: parent mathematical task; no Lean or canonical admission.
Consumer: all 0<x,y<=1/4 and all complex two-node odd coefficients.
Independently reviewed theorem:

    Delta(x,y)>=x^2 y^2 (x^2-y^2)^2/(30000 A^4).            (T)

At x=y the determinant remains exactly zero. This is a whole-square
statement including the axis and diagonal limits, not a sampled grid.
Full ODD2 outside this square, higher odd/even sectors and RH remain open.
Base own-branch commit: b9f863ef7f5131fbb4edfc53cb3a17f9569bc189.

The source is exactly F=Phi, f=F/A, A=||Phi||_2, Kraw=A^2 K,
K(s,t)=V(s,t)-V(s,-t), and Delta=K(x,x)K(y,y)-K(x,y)^2.
The accepted full derivative formula, theta remainder and interval
arithmetic dependency are in
PROSHKA_RESPONSE_GOAL058_ODD2COMPACT_2026-09-12.md, SHA256
819511db9d46801e87b54e728faf7c55e7ce21e4e20e48d9d95d49a71b175e07.
Its reviewed interval implementation is imported byte-for-byte from
certificates/ODD2COMPACT_BOUNDARY_CERT_20260912.py, SHA256
27c072e2ae3ee548f52c9b01008c3161a968060dd133420fcaeb83892e33eebe.
The present certificate uses that arithmetic at precision100.

Reproduce the whole fixed square, without new node sampling, by

    python3 docs/Codex/certificates/ODD2_ORIGIN_BOX_20260912.py 512

The exact final code hash is 545f60cd85a38ee81c01fbfe498e5ab0b6709f5fa2b5f0564d456425510b9b7c below. Output numerical fields
must reproduce; elapsed seconds can differ. The scratch trial used the
same mathematics with its dependency at a scratch-relative path and
128 as the default resolution. Those two path/default settings alone
were changed for this portable final script; the explicit512 run is identical.

## 1. Exact origin derivatives from moments

For Vraw, differentiation of the complete integrand gives

    (partial_s+partial_t)Vraw(s,t)=-(s+t)F(s)F(t).

Both lower endpoint and full decay at infinity are included. Applying
partial_s-partial_t, and subtracting Vraw(s,-t), with evenness of F, gives

    Kraw_ss-Kraw_tt=2[sF(s)F'(t)-tF'(s)F(t)].               (1)

Write J_rq=(partial_s^r partial_t^q Kraw)(0,0), r,q odd, and
I_n=integral_0^infinity v F^(n)(v)^2 dv. The source derivative formula
gives J_rq=4 integral v F^(r)F^(q)+2r integral F^(r-1)F^(q)
+2q integral F^(r)F^(q-1). In particular,

    J_nn=4 I_n-2n F^(n-1)(0)^2                    (n odd),
    J_(n-1,n+1)=-4 I_n-2(n-1)F^(n-2)(0)F^(n)(0)   (n even). (2)

For the second formula, integral v F^(n-1)F^(n+1)=-I_n since
integral F^(n-1)F^n=0 (the odd endpoint vanishes). For the other
boundary term, integral F^(n-2)F^(n+1)=-F^(n-2)(0)F^(n)(0).

The differentiated PDE (1) is

    J_(r+2,q)-J_(r,q+2)
      =2[r F^(r-1)(0)F^(q+1)(0)-q F^(r+1)(0)F^(q-1)(0)]. (3)

Starting from (2), (3) and symmetry give all odd jets with r+q<=66.
The code steps toward r=1 by

    J_(r,q)=J_(r+2,q-2)-2r F^(r-1)(0)F^(q-1)(0)
                             +2(q-2)F^(r+1)(0)F^(q-3)(0).

Thus only I_1 through I_33 and even endpoint derivatives through64 are
needed for a total-degree32 polynomial in the squared coordinates.
This is an equality derived from the full kernel, not a sign premise.

## 2. Full interval moment certificate

The exact polynomial recursion P_(j+1)=(1/2-2z)P_j+2zP_j' gives
F^(j)(v)=e^(v/2) sum P_j(pi n^2 e^(2v))e^(-pi n^2 e^(2v)), v>=0.
For B_j=sum of absolute polynomial coefficients, nu_j=j+9/4,
D_j=(16/15) B_j nu_j^ceil(nu_j), the accepted all-order tail bound is

    |tail beyond n<=N|<=D_j exp[-pi(N+1)^2 e^(2v)/2].

The code uses20 modes and adds D_j exp[-441pi/2] to every derivative
enclosure, including each endpoint through order64. I_n on [0,3] is
integrated by Taylor8 on512 complete cells at precision100. At centers
derivatives through39 are needed; the whole-cell eighth derivative uses41.
For g_n(v)=v F^(n)(v)^2 its k-th derivative is

    v sum_(h=0)^k choose(k,h) F^(n+h)F^(n+k-h)
    +k sum_(h=0)^(k-1) choose(k-1,h) F^(n+h)F^(n+k-1-h).

The complete v>=3 tail is at most D_n^2 exp[-pi e^6]/(2pi),
using v<=e^(2v) and the substitution e^(2v). It is added separately.
The reviewed Decimal implementation is an explicit software dependency.

## 3. A complex bound paying the whole uncomputed Taylor tail

For a complex shift s with |s|<=1/2 and v>=0, put z=pi n^2 e^(2(v+s)).
Then |z|>n^2 e^(2v)>=1 and Re z>=|z|/2: pi>3, e<3, cos(1)>1/2.
The exact source summand e^((v+s)/2)(4z^2-6z)e^-z therefore has modulus
at most 10 |z|^(9/4)e^(-|z|/2). The maximum of u^(9/4)e^(-u/4) is
9^(9/4)e^(-9/4)<243/7<35. Thus each summand is bounded by
350 exp[-n^2 e^(2v)/4]. For t=e^(2v)>=1,

    sum_(n>=1) exp(-n^2 t/4)
       <=exp(-t/8) sum_(n>=1)exp(-n^2/8)
       <=sqrt(2pi) exp(-t/8)<3 exp(-t/8).

The Gaussian sum bound is its decreasing integral bound from0 to infinity.
Consequently |F(v+s)|<=1050 exp[-e^(2v)/8]. This pays holomorphy,
termwise differentiation and the complete V integral on this bidisk.
For |s|,|t|<=1/2, |s+-t+2v|<=1+2v. Since

    integral_0^infinity (1+2v)exp[-e^(2v)/4]dv
      =(1/2)integral_1^infinity (1+log z)e^(-z/4)/z dz<2,

we obtain |Kraw(s,t)|<=4*1050^2=:M=4410000 on the complex bidisk.
Oddness in both variables extends there by analytic continuation.
Cauchy's coefficient inequality then gives, for

    T(u,v)=Kraw(sqrt(u),sqrt(v))/sqrt(uv)=sum t_pq u^p v^q,
    |t_pq|<=4M*4^(p+q).                                  (4)

This proves the entire Taylor remainder, independently of computed jets.

## 4. Polynomial enclosure on the fixed whole square

Set P(xi,eta)=T(delta^2 xi,delta^2 eta) on [0,1]^2. The total-degree32
Taylor polynomial uses t_pq=J_(2p+1,2q+1)/[(2p+1)!(2q+1)!].
For N=32, k=N+1 and rho=4delta^2=1/4, (4) gives complete sup bounds
e0,e1,e2 for the polynomial errors in P, each first derivative, and P_xieta:

    e0=4M(k+1)rho^k/[1-rho(k+2)/(k+1)],
    e1=4M k(k+1)rho^k/[2(1-rho(k+2)/k)],
    e2=4M k(k+1)(k-1)rho^k/[6(1-rho(k+2)/(k-1))].          (5)

Indeed, at a fixed total degree k the sums of1, p, and pq are k+1,
k(k+1)/2 and k(k+1)(k-1)/6. Their successive ratios decrease, giving
the displayed geometric tail bounds. The same e1 covers either variable.

For the polynomial P0, compute N0=P0 P0_xieta-P0_xi P0_eta exactly at
the polynomial level before interval enclosure. The unordered pair of
monomials a_pq xi^p eta^q and a_rs xi^r eta^s contributes

    (p-r)(q-s) a_pq a_rs xi^(p+r-1)eta^(q+s-1).            (6)

Terms with a negative exponent have zero multiplier. This identity retains
the cancellations instead of separately multiplying coarse value intervals.
Convert monomial coefficients to a tensor Bernstein basis on [0,1]^2:
b_ij=sum_(p<=i,q<=j) a_pq choose(i,p)/choose(m,p)
                                      *choose(j,q)/choose(n,q).
The basis functions are nonnegative and sum to1; minimum/maximum interval
coefficient endpoints enclose the entire polynomial rectangle.

If a0,a1,a2,a12 bound the absolute polynomial derivatives P0,P0_xi,
P0_eta,P0_xieta (coefficient triangle sums suffice), the error in N is at most

    a0 e2+a12 e0+e0 e2+a1 e1+a2 e1+e1^2.                 (7)

Every computed coefficient uncertainty is already present in the Bernstein
interval; (7) additionally covers all omitted Taylor coefficients.

## 5. Consumer implication from the certified positive enclosures

The full enclosures below give 0<L<=P<=U and N=P P_xieta-P_xi P_eta>=h>0;
the exact log-kernel rectangle identity gives, for 0<x,y<=delta,

    Deltaraw(x,y)>=h (L/U)^2 x^2 y^2 (x^2-y^2)^2/delta^4.

At axes/diagonal this agrees with the exact structural zeros. Divide by
A^4 for the normalized determinant. Positive diagonal entries then imply
ODD2 for all complex coefficients and the usual four-node factor2.
The positive numerical certificate was independently reproduced; see section8.
A nonpositive Bernstein lower coefficient alone would be inconclusive,
not a negative theta witness.

## 6. Positive certificate and rational simplification

The complete512-cell run at precision100 gives outward enclosures
contained in

    0.0199966048244 < P < 0.0870584174677,
    0.00000363928424527 < N < 0.0000876583082810.

The full Cauchy contribution to the N error is less than8.13e-10;
it is already included. The polynomial alone is enclosed through all
3969 tensor Bernstein coefficients of bidegree(62,62). Its561 input
Taylor monomials generate2016 nonzero numerator coefficient positions.
These are proof basis coefficients, not locations of a theta grid.

In particular take L=19/1000, U=9/100 and h=3/10^6. Then

    h (L/U)^2/delta^4=361/10546875 >1/30000.

The parent's separate fractions.Fraction check confirms this inequality
and that the complete certificate endpoints imply all three rational
premises. Substituting into section5 proves (T) on its stated local domain.
For all complex c1,c2 and a=Kraw(x,x)>0, b=Kraw(x,y), exactly

    c* K_2 c=A^-2[a|c1+(b/a)c2|^2+(Deltaraw(x,y)/a)|c2|^2].

Together with (T) this gives the full two-node Hermitian sign, with
no common-phase or real-coefficient restriction. The full V form on
(x,y,-x,-y) with coefficients(c1,c2,-c1,-c2) is exactly twice this form.

## 7. Audit trail and limits

The target square1/4, degree32, mode20, precision100 and Taylor8 method
were registered before the first new source computation. The128-cell
attempt was inconclusive: its N Bernstein interval had lower endpoint
about-0.0011175 and positive upper endpoint. A diagnostic discarding
moment uncertainties, explicitly not a sign certificate, isolated the
loss from moment quadrature. The single preregistered refinement to512
cells retained the exact same whole square and all source parameters.
It produced the positive full enclosure in section6. No shrinking box,
pointwise theta sign list or omission of a tail was used.

The sole independent checker /root/sibling5_check read the complete
scratch derivation and code before any numerical acceptance and found
no analytic or implementation gap. It separately checked the PDE,
center jets and recurrence, orders through64/41, all moment tails,
complex bidisk/Cauchy bound, exact numerator identity, Bernstein basis,
error formula and delta^-4/A^-4 consumer scaling. Final portable code
and full512-cell reproduction were subsequently accepted; see section8.

This is a new usable size for the already proved origin sign family;
it replaces an extremely conservative tiny radius as a finite-coverage
input. The earlier tiny-corner bound with denominator720 stays valid
on its earlier scope. The present denominator30000 is for the larger
quarter-unit square. These different lower bounds are not interchanged.
No global IC, full ODD2, higher-rank PSD or RH follows from this square.

## 8. Final independent acceptance and exact parent readback

The sole reserved independent checker /root/sibling5_check reviewed the
complete final mathematical report (pre-receipt SHA256
321528705e1650f5a733441c7720af2962b3e040599c84e76b094b2ad5ef0420)
and portable script (SHA256
545f60cd85a38ee81c01fbfe498e5ab0b6709f5fa2b5f0564d456425510b9b7c).
It independently executed the final script at512 cells and returned ACCEPT
for the whole 0<x,y<=1/4 local all-complex certificate only. All analytic
identities, complete source/integration/Taylor tails, interval arithmetic,
Bernstein enclosure and normalization were reviewed without a found gap.

The independent output is preserved unchanged at
certificates/ODD2_ORIGIN_BOX_20260912.json, SHA256
6bd7ad33745defe18d111c731cc04c669db3c480d6b8c1282ef782e21f77cbb0.
The parent independently compared all31 top-level fields against its prior
512-cell result: every numerical field and nested interval matches exactly.
Only script_sha256 (the documented portable path/default change) and seconds
(the independently timed execution) differ. No repeat parent computation
was substituted for independent reproduction.

The parent also checked the rational premises against the exact decimal
endpoints, the exact constant361/10546875, and its strict excess
151/168750000 over1/30000 using fractions.Fraction. These are positive
rational inequalities, not rounded floating-point sign checks.

The raw output deliberately retains accepted:false and a CANDIDATE label:
execution does not grant its own acceptance. This separate reviewed receipt
records acceptance of the stated local mathematical theorem. It grants no
Lean, canonical node, full ODD2, global IC, higher-rank PSD or RH admission.
Post-review report edits only fix F^(n) notation, update status and add this
receipt; the reviewed mathematical argument and code are unchanged.
