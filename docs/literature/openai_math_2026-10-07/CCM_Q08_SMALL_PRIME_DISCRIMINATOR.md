# Waiting Q08 discriminator: exact small-prime inclusion–exclusion

2026-10-21. Q08 is LIVE, not interrupted or supplemented. Interim author
message names simultaneous small-prime inclusion–exclusion. This independent
preflight is an answer discriminator, not an accepted Q08 result or a new
full arithmetic gain. Keep full source N=m,L=log m,M=floor(m^epsilon), fixed epsilon>0, and original P.

Let y>=2, q_y=product_(p<=y)p. Define, on ALL integers n>=2,

    a_y(n)=sum_(d|n, d|q_y) mu(d) log(n/d).

Writing J={p<=y:p|n}, finite inclusion–exclusion gives exactly

    a_y(n)=log n                      if |J|=0,
            log p                     if J={p},
            0                         if |J|>=2.             (1)

Proof: log(n/d)=log n-sum_(p|d)log p. The log n coefficient is
(1-1)^|J|, and the coefficient of log p is
-sum_(d|product J,p|d)mu(d)=(1-1)^(|J|-1).
Prime exponents are NOT discarded: J records distinct small factors,
while log n retains all exponents.

Consequently w_y(n)=a_y(n)-Lambda(n)>=0 for EVERY n. More explicitly:
- for n=p^k with p<=y, w=0;
- for n=p^k with p>y, w=(k-1)log p;
- for composite n not a prime power and J empty, w=log n;
- for composite n with exactly one distinct small prime p, w=log p;
- if |J|>=2, w=0.
In particular all primes have w=0, but proper powers of large primes do not.

Define full projected matrices with the SAME shifts:

    A_y=sum_(2<=n<=m) a_y(n)/sqrt(n) P Q(log n)P,
    W_y=sum_(2<=n<=m) w_y(n)/sqrt(n) P Q(log n)P.

Here S=P Aprime P is the projected Mangoldt operator (which is SUBTRACTED
in K_m). Then S=A_y-W_y EXACTLY. The smooth-divisor formula for A_y is
sum_(d|q_y,d<=m) mu(d)/sqrt(d) sum_(k<=m/d) log k/sqrt(k) P Q(log(dk))P.
Terms beyond cutoff are zero, k=1 is zero, n=m is retained with Q(L)=0.
All mixed matrix entries remain. No magnitude estimate is asserted here.

The sign w_y>=0 does NOT imply W_y>=0: the shift Q(s)=V_s+V_s* is not a
positive operator. A sufficient transfer is W_y>=-r_m P plus an upper bound
A_y<=a_m P, giving S<=(a_m+r_m)P. The missing input is this JOINT lower
composite-shift bound, with proper powers and one-small-prime mixed factors.
Dropping those mixed factors or calling w_y>=0 a PSD certificate is invalid.
This resembles the earlier C5 composite-sign debt and must be compared with
CCM_C5_SIGNED_SUBLEMMA_ATTEMPT.md before claiming a new mechanism.
The exact coefficients differ from prior Ramanujan weights; equivalence of
the unpaid inequalities is not asserted without a quantitative bridge.

Status: root derivation, independent q08_small_prime_check bounded PAPER PASS
on the full coefficient identity and appended Q01 norm return.
No new prime-spectral computation, Lean/Arb run, source exponent or RH result.

## Accepted Q01 bound pays the smooth part, not the sign debt

Q01§4 Lemma A, retained in CCM_ACTUAL_MOBIUS_Q01_CONCLUSION.md, gives
||B_(m,d)||<=(40+16Omega)/sqrt(d) for EVERY d<=m on original P.
Therefore, retaining all k before the norm,

    ||A_y|| <= (40+16Omega) product_(p<=y)(1+p^(-1/2))
            <= (40+16Omega) exp(2sqrt(y)).                    (2)

The last inequality uses log(1+u)<=u and the sum over primes is bounded
by sum_(2<=j<=y)j^(-1/2)<=2sqrt(y); no prime asymptotic is needed.
Take y=L=log m for large m. Then (2) is m^(epsilon+o(1)); for each FIXED
epsilon it is eventually <=C_epsilon m^(2epsilon). This is a bound for the
ENTIRE projected A_y, not a bare scalar coefficient estimate or a raw bound.

Since S=A_y-W_y, subpower-in-epsilon upper families for S and lower families
for W_y are equivalent after adding this 2epsilon fee, in BOTH directions.
This is not an equivalence to the different prior weighted C5 object without
a further bridge. It proves that merely isolating W_y has not supplied an
independent sign theorem. Full scalar T and K returns remain unchanged.
