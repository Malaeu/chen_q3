# Q05 own attempt2: short correlation windows and full-sum reconstruction

2026-10-20. Original CCM and Q01 full-k blocks retained. No Pro send.
Question: can we use only short shifts h<H, where correlation theorems might
be easier, and still return a subpower bound for the full T? This is a bounded
parameter test of the squared certificate, not a claim about all mechanisms.

For one original block (D,2D], X_i=mu(D+i)B_(m,D+i),1<=i<=D,
with zero continuation beyond m. Every X_i is Hermitian, supported on P.
Let1<=H<=D be integral, and define, for j=2-H,...,D,
 C_j=sum_(1<=i<=D, j<=i<=j+H-1) X_i,
 G_(D,H)=H^(-1) sum_j C_j² >=0.
The number of windows is D+H-1. Each i occurs in exactly H windows;
each ordered pair i,k occurs max(H-|i-k|,0) times. Therefore EXACTLY

 sum_j C_j=H T_D,
 G_(D,H)=sum_i X_i² +sum_(1<=h<H)(1-h/H)
                  sum_(1<=i<=D-h){X_i,X_(i+h)}.               (1)

Vector Cauchy, without commuting matrices or omitting cross terms, yields

 T_D² <= ((D+H-1)/H) G_(D,H).                                (2)

At H=D this is Q01. At H=1 this is exactly the ordinary Cauchy penalty D.
All k,k' couplings remain inside B_d B_e; no Fourier shift factorization.

Use b=40+16Omega and ||B_d||<=b/sqrt(d). The diagonal in (1) is bounded
by b² sum_(D<d<=2D)1/d P <=b²P. Now grant a HYPOTHETICAL stronger
source supplier, not a published result: uniformly for1<=h<H and every
W>=0, W=PWP,TrW=1,

 |sum_(D<d<=2D-h)mu(d)mu(d+h)ReTr(W B_d B_(d+h))|
       <= C b² rho(D,H).                                    (H)

Then G_(D,H)<=b²[1+2CH rho(D,H)]P. Since D+H-1<=2D,

 T_D² <= b²[2D/H+4CD rho(D,H)]P.                             (3)

The full return is T²<=J sum_D T_D²; J=O(log m). Original short/arch
returns are those of Q01/Q04 and are not replaced by a scalar model.

For H_D=min(D,ceil(D^theta)), fixed0<theta<=1, and a hypothetical
rho(D,H_D)<=C' D^(-kappa),0<kappa<=1, dyadic summation gives a full
power, allowing logarithmic factors,

 eta_T=epsilon+max(1-theta,1-kappa)/2.                        (4)

At endpoints theta=1 or kappa=1 the associated sum costs a logarithm,
not a positive power. A scalar K return also includes3epsilon/2. Constants
may depend on fixed epsilon,theta,kappa, never on growing m.

Thus, WITHIN THIS RECEIVER:
- To improve3/8 at fixed0<epsilon<1/32 using (3), both theta and kappa
  must exceed1/4+2epsilon, with strict margin for logarithms.
- To reach eta(epsilon)->0, both theta(epsilon) and kappa(epsilon)
  must tend to1. Short shifts with a fixed theta<1 do not give such a
  certified envelope by (3), even if their whole offdiagonal is nonpositive.
- For H polylogarithmic in D, the paid diagonal return D/H alone still
  has power1. Its square root keeps the half-power, before b_m.

These statements describe the exponent of the derived upper budget.
They are NOT lower bounds on actual T or claims that a stronger direct
one-sided use of the same source is impossible. In particular, a large
Cauchy allowance cannot establish that the actual sum is large.

Negative control of a forgotten reconstruction fee: take X_i=I for all i
in an abstract block. Then T_D²=D²I whereas G_(D,H)<=DH I; replacing
(D+H-1)/H by a uniform constant fails for H=o(D). This control is not
actual CCM or a substitution for mu. It only checks the algebraic transfer.

Decision: shortening the Fejer windows does not by itself make the
qualitative correlation import useful. A next source theorem must supply
joint signed cancellation with the (D/H) reconstruction fee accounted for,
or a direct one-sided method bypassing this squared certificate.
Own attempt2 after Q04, no full power gain. Independent read-only ccm_q01_return_review: bounded PAPER PASS for
window counts, noncommuting algebra, complete budget, endpoints and scope.
