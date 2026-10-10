# Q7 entrance test: logarithmic completion filter and its full return

2026-10-10. Independent read-only q07_log_inverse_check bounded PASS on exact identity, all-scale correction, full outer return and coefficientwise uniqueness. Same Q6 SG13–19 source and original SG27/QL49 consumer. RH/SP/MB34 OPEN. No new Pro question sent.

## Exact coefficient test
Fix the actual s,h,R and common compact V. Write A=A_(h,s), including every zero mask and baralpha³ (equivalently A_h(b) with the explicit SG18 coprimality mask), and D_x,T_x exactly as Q6 SG17. For x>0 put ell(x)=log(2+x) and

    E_x = sum_(b sf, q_b³<=beta_W x) mu(b) A(b)/q_b
                      [1−3 log(q_b)/ell(x)] T_(x/q_b³).

This is a candidate modified inverse, not an equality to the original column. Expanding the source completion and regrouping f=bc admits all b|f at every nonzero supported term, including primes shared with the squarefree inner index. The coefficient identities are

    sum_(b|f) mu(b)=1_(f=1),
    sum_(b|f) mu(b) log q_b=−Lambda_F(f).

Here Lambda_F(p^j)=log q_p for every j>=1. Thus, exactly,

    E_x=D_x+Delta_x,
    Delta_x=3/ell(x) sum_(f, q_f³<=beta_W x)
                      Lambda_F(f) A(f)/q_f D_(x/q_f³).

All prime powers and original masks remain. No Euler factor is divided by zero; no new coprimality(n,f) is imposed. ell(x) avoids an artificial singularity at x=1. It does not add a large denominator when x is small.
This coefficient algebra is the usual Mobius/logarithm identity, already related to the all-prime-power convolution in PROSHKA_VERDICT_MIXED_PRIME_CORRECTOR_Q06.md MP4–7. The new test is its application to the current cubic completion and a full SG13 return, not a novelty claim for the identity.

## Uniform elementary correction bound
Actual squarefree Gauss coefficients have magnitude at most1 and all twists/masks at most1. Ideal counting gives |D_x(V)|<=C_V sqrt(x) for all x>0; for beta_W x<1 the sum is empty. Therefore

    |Delta_x| <= C_V sqrt(x)/ell(x)
                 sum_f Lambda_F(f) q_f^(-5/2)
               <= C_V' sqrt(x)/ell(x).

The last sum converges absolutely using Lambda_F(f)<=log q_f and O(T) ideal counting. No prime number theorem, moving-Hecke uniformity or unproved moment is used. E_x itself is O_V(sqrt(x)). For two different common profiles V,V′,

    E_x(V) conjugate(E_x(V′))−D_x(V) conjugate(D_x(V′))
      = Delta_x(V) conjugate(D_x(V′))
        +D_x(V) conjugate(Delta_x(V′))
        +Delta_x(V) conjugate(Delta_x(V′)).

The full difference, including both cross terms, is O_(V,V′)(x/ell(x)). This is not a relative estimate to a possibly vanishing D_x.

## Entire high-poor return
Define H_E from Q6 SG14–16 by replacing both D columns by these E columns, with original s/h/outer weights unchanged. Its difference from H05 retains the exact cross above. Q6 common Fourier profile obeys polynomial-height integrability and (1+q_h/J)^(-N), J=X0²/Y. On the original late band X0=L/q_g is large uniformly.

    sum_(q_s<=beta_W X0) q_s^(-2)/log(2+X0/q_s)
         <= C/log(2+X0).

Proof: for q_s<=sqrt(X0), the denominator is at least a fixed multiple of log(2+X0), and sum q_s^-2 converges. Above sqrt(X0), log(2+X0/q_s)>=log2 while the tail of sum q_s^-2 is O(X0^-1/2). Squarefree/coprime restrictions only reduce this positive bound.
Hence the full signed s-pair difference is bounded by C X0/log(2+X0), with all common profile seminorms. Summing h after Fourier decay costs O(J), since J>=c U^(6/5), even when we enlarge the high/poor/cap domain positively. The original Y/L prefactor gives

    (Y/L) * J * X0/log(2+X0)
       = L²/[q_g³ log(2+X0)].

Since q_g<U^(1/100) and log_U(L)>=111/100, log(2+X0) is uniformly comparable to log(2+L). Sum over all d<=C U^(1/6), e|g, all g and all a0<=P gives

    |H_E−H05| <= C P U^(1/6)L²/log(2+L)

with fixed finite common-profile norms (and polynomial external profile-height factors if included). This is a complete elementary correction estimate, not a bound for H_E. Its exponent excess over H U^-eta is at least24217/18750 before logarithmic division, so this bound does not pay the return. A logarithmic improvement of the old direct envelope is not a power saving over CF22. No lower bound on the actual correction is inferred.

## What an exactly preserving diagonal filter can do
On a divisor-closed finite live set, suppose w(1)=1 and sum_(b|f)mu(b)w(b)=1_(f=1) for every supported f. Mobius inversion, or induction over squarefree f, forces w(b)=1 at every squarefree live b. Weights at nonsquarefree b are irrelevant because mu(b)=0; forbidden masked ideals impose no constraint. This excludes only nontrivial coefficientwise-preserving diagonal reweighting of the inverse on that set. It does not exclude aggregate cancellations for actual D, row-dependent identities, a non-diagonal operator or a new joint covariance estimate.

## Decision and diagnostic scope
The filter trades exact inversion for an explicit prime-power correction. The full cross is still required and its elementary return is too expensive. Do not send a proposal that treats E as D or assumes its prime-power correction is small from support alone. A next attempt must estimate H_E together with this exact correction on the original consumer budget, or bypass this filter.
Root finite diagnostic:256 exponent-tuples (four formal primes, exponents0..3) satisfy both identities exactly in the formal log-prime basis. This checks algebra only; it is not a full moment certificate.
