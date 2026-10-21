# Post-Q07 own attempt: exact annihilator coordinates before averaging

2026-10-21. Source: original sparse CCM, N=m, L=log m, fixed epsilon,
M=floor(m^epsilon), original three constraints. Independent read-only q08_annihilator_audit returned bounded PAPER PASS
for the complete source/filter calculation, including the same-band update.
No full exponent improvement claimed.

## Exact coordinates, no new test space

Let f(t)=sum_(|j|<=M)c_j exp(2pi i j t/L)/sqrt(L) on[0,L],
zero outside, with c in the original ran(P). Then f(0)=f(L)=0 and
integral exp(±t/2)f(t)dt=0. Let a=1/2, B=D²-a² and

    h(t)=-integral_R exp(-|t-u|/2) f(u)du.

Distributionally B[-exp(-|t|/2)]=delta_0, so Bh=f. The two original
exponential contacts imply h=0 on both exterior half-lines EXACTLY.
Thus h,h' vanish at both endpoints. Also h''=f+h/4 has zero endpoint
values. No derivative jump is silently dropped. Globally h is H³ for
this zero-extended continuous piecewise-smooth f. In particular h is H²,
and the identities below are valid by distributional derivatives or IBP.

In fact h has the SAME Fourier band on[0,L]. Write omega_j=2pi*j/L and

    d_j=-c_j/(omega_j²+1/4), h(t)=sum d_j exp(i omega_j t)/sqrt(L).

The two contacts on f, using the exact exponential Fourier integrals, imply
sum d_j=0 and sum omega_j*d_j=0. Thus this periodic particular solution has
h(0)=h'(0)=0, extends without boundary deltas, and equals the whole-line inverse
by uniqueness. The original sum c_j=0 additionally gives sum omega_j²*d_j=0.
Consequently the coordinate image is EXACTLY the same-band functions with

    h(0)=h'(0)=h''(0)=0,                                    (0)

and periodic matching at L. Conversely (0) implies f=Bh has all three original
constraints. This is an invertible diagonal change, not a smaller test space.
For z=exp(2pi*i*t/L), h=L^(-1/2) z^(-M)H(z); the polynomial H of degree<=2M
has a triple root at1. Thus H=(z-1)^3 G, degree(G)<=2M-3. No conditioning or
spectral improvement follows from this factorization alone.
Whole-line convolution has L1 norm4, so ||h||_2<=4||f||_2. Exact IBP gives

    ||f||_2²=||h''||_2² + (1/2)||h'||_2² + (1/16)||h||_2².       (1)

There is no inverse exponential cost. Conversely an arbitrary compact h must NOT
be admitted; the band and endpoint conditions (0) remain mandatory.

## Full signed source and exact continuous return

Set r_h(s)=integral conjugate(h(t)) h(t+s)dt, and similarly r_f.
Then r_f=B_s² r_h (the reflected second derivative has the same sign).
Define the even source measures, interpreted against compact support,

    sigma_m=sum_(2<=n<=m) Lambda(n)/sqrt(n) [delta_logn+delta_-logn],
    nu_m=sigma_m-exp(|s|/2)ds.

Every prime power and mixed term is retained. With S=P Aprime P and c the
original coefficient vector, the real pairing is exactly

    c*Sc = <sigma_m,r_f>
          = <B² nu_m,r_h> - ||h'||_2² - (1/4)||h||_2².        (2)

Indeed B exp(|s|/2)=delta_0, hence B² exp(|s|/2)=delta_0''-delta_0/4.
Also r_h(0)=||h||² and r_h''(0)=-||h'||². These delta terms at zero are
part of the full return, not an omitted boundary. Endpoint prime n=m has
r_f(±L)=0. Extending the continuous measure to the whole line is legitimate
because the correlation and its relevant derivatives have compact support.
Formula(2) is the old negative continuous kernel in new coordinates.

To close the desired supplier, one needs a function eta(epsilon)->0 as
epsilon decreases to0 such that for each sufficiently small FIXED epsilon>0
there exist C_epsilon and m_0(epsilon) making the following true for ALL
m>=m_0 and ALL the original image functions h (no epsilon(m) tuning):

    <B² nu_m,r_h> <= ||h'||² + (1/4)||h||²
                     + C_epsilon m^eta ||Bh||², eta->0.      (3 OPEN)

No estimate of (3) is provided by the coordinate identity. Requiring it on
all compact h would strengthen, not solve, the current task. Actual mu is
retained through Lambda=mu*log; no independent phases or signs introduced.

## Cheapest discriminator: what the filter actually annihilates

For a fixed complex z and s away from zero,

    B² exp(z s)=(z²-1/4)² exp(z s).                          (4)

The filter kills z=±1/2, but otherwise changes the amplitude, not the exponent.
For z=1/2+i*tau, tau nonzero, the coefficient is nonzero; Q07's auxiliary
sqrt(m) example therefore survives. On real Fourier frequencies xi the
multiplier is (xi²+1/4)², bounded below by1/16, not a small factor.
This is a filter calculation, NOT an expansion of actual prime discrepancy
into such modes and NOT an actual-source impossibility theorem.

Thus exact source annihilation alone supplies no sign for B²nu_m. It cannot
turn a previously insufficient PNT error bound into a new power merely by
applying B twice. A valid arithmetic argument for (3) could still exploit
nu_m jointly; none has been proved here. Q03's sign-changing primitive kernel
already excludes replacing this gap by a general scalar upper primitive.

Decision after bounded independent check: retain (0)–(2) as exact bookkeeping if
useful; reject the inference that this coordinate change itself pays (3).
No new eta, cofinal result, SP or RH. CF22/PySR remain parked.

Bounded shelf check: q08_annihilator_shelf identifies the prior forward filter
in CCM_RESTRICTED_PRIME_RECEIVER.md and the same unpaid arithmetic in
CCM_Q04_CENTERED_SECOND_PRIMITIVE.md. Registered ask.sh returned INCOMPLETE
(index freshness), not absence. No novelty is claimed for forward filtering.

Full consumer return is unchanged: a bound for S gives T_{>R} after paying
the existing short fee O(m^(3epsilon/2) times logarithms); direct K uses
the archimedean fee50L+8 without paying that short term again. This note
proves neither bound. Asymptotic polynomial factorization assumes M>=2.
