# Q9 long-Mobius primitive: exact prime-discrepancy return

2026-10-09. Root own attempt; independent read-only sparse_band_receiver PAPER audit PASS for L1-L2, both RH-equivalence implications and DLMF source mapping; no defect found. RH is not proved. This tests Q09(34)-(35), not the weaker one-sided matrix estimate(32).

## Obstruction, source and negative control

The proposed centered long-divisor scalar bound is stronger than the signed matrix estimate. Before treating it as a simpler supplier, unfold its exact arithmetic and retain the short-divisor quadrature error. The goal is to detect whether changing to long Mobius coefficients has actually removed any of the classical prime-discrepancy obligation.

Source: PROSHKA_VERDICT_FULL_CCM_HEAT_SIGN_Q09.md(34)-(35). Fix integer m>=4, 2<=R<m, real 1<=y<=m, omega real, s=1/2+i omega. Let

    rho_R(t)=sum_{d<=min(R,t)} mu(d)/d * log(t/d),
    H_R(omega;y)=sum_{d>R,dk<=y} mu(d)log(k)/(dk)^s
                 -integral_1^y [1-rho_R(t)]t^(-s)dt,
    D(omega;y)=sum_{n<=y} Lambda(n)n^(-s)-integral_1^y t^(-s)dt.

All powers, integer products and endpoints are literal. Q9's H_mu asserts: one finite absolute a>=1, every sufficiently small fixed epsilon>0, eventually in integer m, R=floor(m^epsilon), sup over y<=m and |omega|<=2pi R/log m of |H_R| <=K_epsilon m^(a epsilon).

Negative control outside the arithmetic class: a synthetic cumulative error E(x)=x^sigma-1, 1/2<sigma<1, produces D(0;x)=sigma/(sigma-1/2)*(x^(sigma-1/2)-1). A change of names or subtracting a genuinely smaller short-divisor error cannot give a subpolynomial bound for this source. This is not a counterexample for actual primes or RH.

Search dictionaries: finite Mobius convolution; Mellin-Stieltjes primitive of the centered prime-power measure; Chebyshev/von Koch error criterion. Three ask.sh queries were run; the semantic shelf reports INCOMPLETE (freshness), not absence. The candidate exact identities below were UNVERIFIED search hints before the calculation.

## L1. Exact return with a uniform elementary price

For d<=min(R,y), set F_d(t)=log(t/d)t^(-s), d<=t<=y, and

    E_d(omega;y)=sum_{k<=y/d}log(k)(dk)^(-s)-(1/d)integral_d^y F_d(t)dt,
    E_R(omega;y)=sum_{d<=min(R,y)}mu(d) E_d(omega;y).

For d>y set E_d=0. With B_d(t)=floor(t/d)-t/d, Stieltjes summation gives E_d=B_d(y)F_d(y)-integral_d^y B_d(t)F_d'(t)dt. F_d(d)=0, but F_d(y) is NOT deleted. This also holds when y/d is an integer (B_d(y)=0).

Since |B_d|<=1, |F_d(y)|<=2/(e sqrt(d)) and |F_d'|<=t^(-3/2)[1+|s|log(t/d)],

    |E_d| <= [2/e+2+4|s|]/sqrt(d) <= [5+4|omega|]/sqrt(d),
    |E_R(omega;y)| <= (10+8|omega|)sqrt(R).                 (L1)

This is uniform over every prefix y, with no averaging or cancellation assumption. Finite interchange gives sum mu(d)/d integral_d^y F_d=integral_1^y rho_R(t)t^(-s)dt. The exact identity Lambda=mu*log therefore yields

    H_R(omega;y)=D(omega;y)-E_R(omega;y).                  (L2)

The coefficient of the original prime discrepancy is exactly one. L1-L2 do not rely on Q9's unaudited matrix short-divisor calculation.

## L2. H_mu is equivalent to classical RH, not an easier scalar premise

Forward: at omega=0 and integer y=m, L1-L2 imply |D(0;m)|<=K_epsilon m^(a epsilon)+10m^(epsilon/2). For each eta>0 choose one fixed small epsilon with a epsilon<eta and epsilon/2<eta. Hence D(0;m)=O_eta(m^eta). For real x between m and m+1, there is no new integer atom and the integral changes by at most 1/sqrt(m), so the same bound holds on the real half-line. Put E(x)=psi(x)-(x-1), so E(1)=0. Exact reverse partial summation gives

    E(x)=sqrt(x)D(0;x)-(1/2)integral_1^x D(0;t)/sqrt(t)dt.

Consequently psi(x)=x+O_eta(x^(1/2+eta)) for every eta>0, which is the classical RH criterion in DLMF25.16.4. Already the zero-frequency terminal-prefix slice of H_mu suffices; no growing frequency or all-prefix hypothesis is needed for this implication.

Reverse (conditional on RH): DLMF25.16.4 gives |E(t)|<=C_eta t^(1/2+eta) for each eta>0, extending the constant to t>=1. Direct Stieltjes integration gives

    D(omega;y)=y^(-s)E(y)+s integral_1^y E(t)t^(-s-1)dt,
    |D(omega;y)|<=C_eta[1+|s|/eta] y^eta.

Fix epsilon, take eta=epsilon/2, |omega|<=2pi m^epsilon/log(m) and y<=m. L1-L2 then give sup|H_R|=O_epsilon(m^(3epsilon/2)), hence H_mu holds with the single absolute choice a=2 for all fixed sufficiently small epsilon. Constants and onset may depend on epsilon, as in Q9. No epsilon(m) or growing moment is introduced. Thus H_mu iff RH, as a PAPER equivalence using the cited classical criterion; this is no proof of either statement.

## Source mapping and decision

NIST DLMF https://dlmf.nist.gov/25.16#E4, section25.16(i), equation25.16.4 and its trailing quantifier. Verbatim quote: “The Riemann hypothesis is equivalent to the statement”; the equation is psi(x)=x+O(x^(1/2+epsilon)), followed by “for every epsilon>0” (math glyph normalized here). Definition25.16.1 includes every prime power, exactly matching sum Lambda(n). This is an exact classical criterion for the scalar error, not an independently supplied bound. Local fetched HTML sources/dlmf_25_16_2026-10-09.html SHA2564e491a57060b14f06b521c6819cfaca7c097f83f886c22e92f9d555d59bab04b. Independent reviewer must check mapping and both implications, not accept a method name as a supplier.

Decision: H_mu remains OPEN and the change of scalar representation alone is STALLED. Equivalence to RH is not an impossibility theorem or a reason to reject every attempt to prove H_mu; the missing evidence is a new estimate rather than the equivalence itself. L1-L2 pay the proposed change of scalar representation but do not improve its exponent. Keep the weaker source-specific one-sided matrix pairing as the actual unresolved target; joint frequency compensation remains possible. No change of production N=m, no full-SP/complement return, no Hecke uniformity, no Linux Comparator rerun, no RH claim. Own test is independently checked; Q10 has not been sent.

AUTOPSY: dropped=THEOREM_SHAPE; note=all-prefix absolute long-Mobius primitive retains classical prime discrepancy with coefficient one and a paid short-divisor error; its quantified bound is RH-equivalent rather than a new supplier.
