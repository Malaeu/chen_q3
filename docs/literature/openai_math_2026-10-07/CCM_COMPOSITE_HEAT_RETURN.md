# Positive heat smoothing: paid return on the original finite band

2026-10-08. Root own attempt after Q8; Independent read-only sparse_band_receiver PAPER audit PASS for H1–H5; no correction found. C5/full-SP/RH OPEN. This tests a smoothing entrance for the actual signed comparison, not a new source family.

## Objects

Keep m>=4,1<=M<=m,2<=R<m, L=log m, original isometry F and original projection P onto the b,v_plus,v_minus constraints within |j|<=M. Write Omega=2pi M/L. For unit c in ran P, f=Fc extended by zero outside[0,L] is in H1(R), because its endpoint traces vanish by b*c=0. Its weak derivative is the original trigonometric derivative on (0,L), so ||f'||_2<=Omega. No second-order endpoint condition is assumed.

Define the full-line compressed translation matrix

    Qtilde(s)=P F*(T_s+T_{-s})F P, s real.

It agrees with P Q_M(s)P for 0<=s<=L, is even in s and zero for |s|>=L (including endpoints). For n=m the exact original value is zero. Let w_n=b_R(n)/sqrt(n) for ALL composite R<n<=m, including proper powers and small-factor composites. Then C=sum_n w_n Qtilde(log n) is exactly C_comp.

For h>0 let gamma_h(z)=(2pi h²)^(-1/2)exp(-z²/(2h²)) and define

    C_h = sum_n w_n integral_R gamma_h(z) Qtilde(log n+z) dz.    (H1)

No cutoff is imposed on z and no lower/upper n block is removed. Even the n=m atom is retained: its new nonzero smoothed contribution is charged in the return below. Gaussian tails crossing 0 and L are retained using the zero-extended physical translation, not the raw formula Q_M outside its domain.

## Second-order return using only the original endpoint constraint

For unit f=Fc, put q_f(s)=2Re<f,T_s f>. Since f in H1, its autocorrelation is C²: Fourier inversion applies to xi²|fhat(xi)|² in L1. Equivalently

    q_f''(s)=-2Re<f',T_s f'>,  |q_f''(s)|<=2Omega².             (H2)

This is valid across s=0 and s=±L; it does not assert that the zero-extended f belongs to H2. Taylor's integral remainder gives

    |q_f(s+z)-q_f(s)-z q_f'(s)|<=Omega² z².

The Gaussian first moment is zero and second moment h². Sum the actual nonnegative weights, then take the supremum over unit c in ran P. Hermiticity gives

    ||C_h-C|| <= h² Omega² W_m,R,
    W_m,R=sum_(R<n<=m,composite) b_R(n)/sqrt(n).                 (H3)

The accepted Q8(11) bound b_R(n)<=log(n)tau_9(n) and the nine-factor summation used in Q8(12), now through m, give

    W_m,R<=2sqrt(m)L(1+L)^8,
    ||C_h-C||<=2h²Omega²sqrt(m)L(1+L)^8.                        (H4)

Constants are uniform in R; no prime-distribution theorem enters. In particular for any fixed kappa>0, choose

    h=Omega^(-1)m^(-1/4-kappa).

Then the entire operator return is <=2m^(-2kappa)L(1+L)^8=o(1). For M=floor(m^alpha), this uses logarithmic smoothing width h=L/(2pi M)*m^(-1/4-kappa). Parameters alpha,kappa are fixed once. The rate is a smoothing return, not a spectral lower bound.

## Does positive smoothing supply the missing sign?

No automatic whole-line positivity follows. With Fourier convention fhat(xi)=integral f(t)e^(-itxi)dt, the exact multiplier of H1 before finite compression is

    a_h(xi)=exp(-h²xi²/2) a(xi),
    a(xi)=2sum_n w_n cos(xi log n).                            (H5)

For any nonempty finite atom family with positive weights, a has both signs. Its long-interval mean is zero; its squared mean is 2sum_n w_n²>0 because distinct positive log n give distinct cosine frequencies. If a>=0 everywhere, then 0<=a²<=A a with A=2sum_n w_n, contradicting those two means. Also a(0)>0. The Gaussian factor is strictly positive at every finite xi; hence a_h has both signs for every h>0. This elementary argument does not use Q8's unaudited quantitative whole-line falsifier or independence of primes.

Thus heat smoothing never makes this nonempty whole-line multiplier PSD. It MAY still permit a small negative floor after the original P compression: no such floor follows from H3-H5. The exact remaining task is C_h>=-C_epsilon m^(c epsilon)P for the actual original band (e.g. M=R=floor(m^epsilon)); H4 would return that bound to C_comp with o(1) loss. The actual positive and negative compressed parts must still be compared jointly. No replacement of P by a whole-line pointwise estimate is allowed.

## Decision

This supplies a full quantitative smoothing return, with all original weights, endpoints and Gaussian tails. It excludes automatic positivity from positive heat smoothing; it does not exclude a quantitative source-specific signed bound for C_h. Combined with CCM_COMPOSITE_REFLECTION_TEST.md, the own attempt shows exactly what the next arithmetic calculation must retain: the actual finite-band constraint and compensation between positive and negative contributions. Q9 has not been sent.

AUTOPSY: dropped=THEOREM_SHAPE; note=Gaussian smoothing preserves every finite-frequency multiplier sign; its paid finite-band return supplies no arithmetic lower bound by itself.
