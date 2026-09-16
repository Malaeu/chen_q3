# Theta reciprocity preserves the conditional mean, not the fluctuation norm

STATUS: INDEPENDENTLY_REVIEWED_PAPER_RECIPROCAL_LIFT_DIAGNOSTIC_ONLY.
Date: 2026-09-16. Source base: 345dfea4365498cfdff460e78620f4d717e49147.
Scope: one precise proposed lift of theta reciprocity; not the sign of V.

## 1. Exact object and consumer

Use the complete positive density h of sum E_n/(pi*n^2), r=h*h,
Phi(X)=exp(5X/2)r(exp(2X)), and the conditional density

    p_t(s)=t h(ts)h(t(1-s))/r(t), 0<s<1.

These are the accepted objects in BROWNIAN_DILATION_CONDITIONAL.
The source is even, so its exact reciprocal identity is

    r(t)=t^(-5/2)r(1/t).                                      (R1)

For a=exp(2x)>0 set

    g_a(t,s)=a^(9/4)h(ats)h(at(1-s))/[h(ts)h(t(1-s))],
    F_a(t)=E_t g_a=a^(5/4)r(at)/r(t),
    R_a(t,s)=g_a(t,s)/F_a(t).

Direct cancellation, with no inequality, gives

    R_a(t,s)=p_(at)(s)/p_t(s), E_t R_a=1.                     (R2)

Thus the centered normalized fields are likelihood-ratio fluctuations.
Their exact Gram kernel is

    C_t(a,b)=E_t[(R_a-1)(R_b-1)]
            =integral_0^1 p_(at)p_(bt)/p_t ds - 1.           (R3)

This is a covariance kernel, so its finite matrices are PSD wherever the
columns belong to L2(p_t). In particular C_t(a,a) is the chi-square
divergence of the probability density p_(at) from p_t. This identification
does not imply positivity after multiplication by log(t)+x+y.

From (R1), F_a(t)=F_(1/a)(1/t). A proposed mean-preserving isometric
lift of reciprocity would additionally require a linear isometry

    U_t:L2(p_t)->L2(p_(1/t)),
    U_t 1=1, U_t R_a(t)=R_(1/a)(1/t)                       (R4)

for all a in (1/2,1), or just on their linear span together with 1.
Such a lift would preserve the mixed fluctuation norms automatically.
We test this exact claim, not all possible reciprocal transports.

## 2. Large t: the normalized fluctuations vanish

The accepted full-source bounds in POINCARE_BUDGET_OBSTRUCTION, section 2,
give h(u)=2*pi*exp(-pi*u)*chi(u), with 0<chi<=1 increasing to 1.
Write

    B(t)=integral_0^t chi(u)chi(t-u) du,
    r(t)=4*pi^2 exp(-pi*t)B(t), B(t)/t ->1.

For any fixed 0<a<1, (R2) becomes

    R_a(t,s)=a B(t)/B(at)
       *chi(ats)chi(at(1-s))/[chi(ts)chi(t(1-s))].          (R5)

The product ratio is at most 1 by monotonicity. Hence 0<R_a<=K_a(t),
where K_a(t)=a B(t)/B(at)->1. Since E_t R_a=1, Jensen and (R5) give

    1 <= E_t R_a^2 <= K_a(t)E_t R_a=K_a(t).

In particular, without interchanging a varying measure and a limit,

    C_t(a,a)->0 as t->infinity.                            (R6)

For two fixed a,b in (0,1), covariance Cauchy--Schwarz implies C_t(a,b)->0.
All these fields are in L2(p_t) by the same bound.

## 3. Small t: an explicit nonzero limiting covariance

The full modular h-series in POINCARE_BUDGET_OBSTRUCTION gives

    h(u)=(pi/2)u^(-5/2)exp(-pi/(4u))(1+O(u)), u->0.

The O(u) is relative and uniform for 0<u<=epsilon, since the remaining
modular terms are exponentially small. The large-t asymptotic of r and
(R1) imply

    r(t)=4*pi^2 t^(-7/2)exp(-pi/t)(1+o(1)), t->0.

Consequently, putting w=s(1-s),

    p_t(s)= [w^(-5/2)/(16*sqrt(t))]
       *exp[-pi/(4*t)*(1/w-4)]*(1+epsilon_t(s)),            (R7)

with sup_(0<s<1)|epsilon_t(s)|->0. The error is uniform even at the
two endpoints: ts and t(1-s) are both at most t, and the relative
normalizing error from r(t) does not depend on s.

Fix a,b>0 such that lambda=1/a+1/b-1>0. Apply (R7) at the four scales
at,bt,t,t/lambda. All prefactors and exponential terms cancel exactly to
give, uniformly over 0<s<1,

    p_(at)(s)p_(bt)(s)/p_t(s)
       = [1/sqrt(a*b*lambda)] p_(t/lambda)(s)*(1+o(1)).     (R8)

The ratio of the four (1+epsilon) factors tends uniformly to 1 and is
positive for all sufficiently small t. Integrating against the actual
probability density p_(t/lambda) proves

    C_t(a,b)->1/sqrt(a+b-a*b)-1.                            (R9)

This also proves integrability for sufficiently small t. More generally,
for any fixed t the small-s h asymptotic gives an integrable factor
polynomial(s^(-1))*exp[-pi*lambda/(4*t*s)] at the left endpoint, and
the reflected bound at the right. Thus (R3) is finite under lambda>0
for every t>0. In particular every R_a with 0<a<2 belongs to L2(p_t).
There is no replacement of p_t by a Gaussian or truncation of the source.

## 4. The isometric reciprocal lift fails for the actual source

Choose any fixed a in (1/2,1). Formula (R6) gives C_t(a,a)->0.
For the reciprocal field, apply (R9) to both indices 1/a at time 1/t:

    C_(1/t)(1/a,1/a)->a/sqrt(2*a-1)-1 >0.                 (R10)

Strict positivity follows from a^2-(2*a-1)=(1-a)^2>0.
An isometry as in (R4) would preserve the squared norm of R_a-1 and
force equality of these two covariances. For all sufficiently large t
they are unequal, contradicting (R4).

The same norm comparison excludes a contraction in the direction
L2(p_t)->L2(p_(1/t)) with the stated exact images and U_t1=1. It does
NOT exclude a contraction in the opposite direction, a map with a
quantified defect, or a representation using additional channels.
The node 1/a is used only to test the explicitly proposed reciprocal
field; it is not presented as an original admissible negative shift.

## 5. Consequence for the signed comparison, and stopping boundary

The source reciprocity (R1) pays the equality of conditional means F.
It does not pay a norm-preserving identification of the conditional
fluctuations. The two ends have different chi-square kernels (R6),(R9).
This gives an exact discriminator for any proposed reciprocal lift:
it must explain this change of covariance, not silently suppress it.

For the physical target, the conditional mixed contribution is

    Cov_t(g_x,g_y)=F_a(t)F_b(t) C_t(a,b).

Multiplying by log(t)+x+y and integrating in the original physical
measure is still a signed operation. PSD of C_t or an ordinary Markov
contraction does not, by itself, establish its full signed comparison
with the microscopic part. We claim no positivity of V or L_pi, no
negative V witness, and no impossibility of other source-specific lifts.
No prime-specific sign theorem is used. The exact theta reciprocity and
full small/large source estimates are used at their stated places.

The result identifies the exact normalized statistical object and excludes
only the cost-free isometric/contraction transfer in (R4). It does not
count as a new complete attempt to prove the sign of V.
