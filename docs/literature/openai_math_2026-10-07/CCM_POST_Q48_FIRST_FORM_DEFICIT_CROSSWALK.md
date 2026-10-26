# Post-Q48 first-form upper deficits return the recorded jump energy

Status: BOUNDED_SOURCE_CROSSWALK; no new arithmetic estimate or no-go.
Inputs: Q48(4.1)-(4.4) and CCM_POST_Q28_EULER_POSITIVITY_PREFLIGHT.md.
Original H(s),P,physical zero-extension and both shift orientations retained.
This note distinguishes Q48's positive upper deficit from its quadratic E_p.

Let W>=0 on ran P,TrW=1, the SAME W for all p. Let
 G_p=u_p I-A_p>=0, u_p=2logp/(sqrtp-1),
 B_d=sum_(n<=m) Lambda(n)/sqrt(n),
 E_d=sum_(n<=m) Lambda(n)/sqrt(n)[2I-H(log n)].
Thus A=2B_d I-E_d exactly, with the n=m atom retained in E_d.
For finite m define the actual scalar tail
 tau_m=2 sum_(p<=m) logp sum_(k>=1,p^k>m) p^(-k/2).
No prime p>m enters. Since p<=m, every omitted k is at least2.
Geometric summation therefore gives
 sum_(p<=m)u_p=2B_d+tau_m,
 sum_(p<=m)G_p=E_d+tau_m I.
Consequently Tr(WA)=sum u_p-sum Tr(WG_p)=2B_d-Tr(WE_d).
This identity keeps the same W, all mode cross terms, every proper power,
and both times. Infinite per-prime geometric tails contribute only their
scalar identity part after zero-support compression; no infinite prime sum.

The entire tail is paid without a distribution theorem:
 0<=tau_m<=2/(1-1/sqrt2) sum_(p<=m) logp/p
          <=2/(1-1/sqrt2) L(1+L).
Here all k>=2 were enlarged geometrically and primes enlarged to integers.
This deliberately loose bound is sufficient to distinguish polylogarithmic
tail from the half-power main mass. Tau cancels EXACTLY in the joint return;
there is no reason to add it again to the final fallback.

Dropping positive G_p independently gives A<=sum u_p I, only
2B_d+O(L²), hence no improved exponent. Returning the complete equality
instead gives the already-recorded Q28 jump-energy obligation, with no new
lower bound on Tr(WE_d). Q48 quadratic E_p>=0 is a different object and
cannot be silently substituted for G_p or used to assert that lower bound.

Full C=A+H_d and T_>R=A-T_<=R are unchanged. Keep the inherited direct
s_keep<=6sqrt(m)+6m^(1/4), its single short fee for T and single arch fee
for K. This is an exact duplicate preflight for an upper-deficit summation,
not three new failed attempts and not a no-go for other joint arithmetic.
Do not send Q49 on the basis of this identity alone. Goal OPEN.

## Supplier threshold for the bounded energy search

This is a search-strength filter, not a new theorem or failed attempt.
For m>=2, Bd>0. Write K=A/(2Bd), so Ed/(2Bd)=I-K exactly
on the SAME original sparse image. An independent bound
 Ed >= 2Bd(1-r_m) I
returns A<=2Bd r_m I, C<= (2Bd r_m+4)I and
T_>R <= (2Bd r_m+b_div)P. Direct K_m return charges arch once.
Thus a fixed r_m=0.01 still retains half power in this certificate.
Using the inherited ordinary PNT Bd~2sqrt(m), the sufficient threshold
for exponent eta is r_m=O_epsilon(m^(eta-1/2)). For illustration ONLY,
choosing eta=2epsilon at epsilon=1/64 or1/128 asks for r_m of order
m^(-15/32) or m^(-31/64), respectively. No such estimate is supplied.
A lower energy constant greater than1 is allowed and gives a stronger
upper bound; closeness to1 from both sides is NOT required.
A generic fixed spectral gap, positive jump measure, or sampling lower
bound therefore does not pass merely by being positive. The original
contacts and actual Lambda weights must supply the stated one-sided scale.

Bounded read-only supplier screen: researcher post_q48_energy_supplier
reported three local ask dictionaries (jump-energy coercivity, translate
frame lower bounds, prime-weighted correlation), all INCOMPLETE due to
semantic-index freshness validation and one local-shelves failure. Hits
were not exact source suppliers. This is NOT evidence of literature
absence. The Q28 compound-Poisson lead was recognized as already mapped;
no repeated external lookup or new mathematical attempt was counted.
Next admissible lead must provide the near-1 lower-energy threshold above
on the actual source image, or a strictly weaker sufficient signed input.
No new Proshka question was sent; arithmetic exponent unchanged.

Exact local queries (all with --defer-external; HEAD8770b1c8):
- jump energy Dirichlet coercivity spectral gap
- translate frame lower bound synthesis range sparse contacts
- Mangoldt prime weighted correlation logarithmic shifts mixed terms
The normalized eigenvalue requirement is an UPPER bound, not an absolute
O-bound: lambda_max(A/(2Bd)) <= C_epsilon m^(eta-1/2). No lower bound
on lambda_max or two-sided closeness to zero is needed or inferred.

## Q49 finite factorization preflight

Read-only researcher q49_hb_preflight checked the request's finite
Heath-Brown identity with k5,z=ceil(m^(1/5)). If X=mu_z*1 then
mu*X=mu_z and delta-X=(mu-mu_z)*1 has support n>z. The binomial
convolution polynomial is mu*[delta-(delta-X)^{*5}]; multiplying by
ell gives Lambda with a remainder supported strictly above z^5>=m.
Inclusive n=m is preserved. Every j contribution has absolute coefficient
<=log(n)d_(2j)(n); full matrix norm payment with ||h(n)||<=2/sqrt(n)
costs O(sqrt(m)log^10(2m)). This is no new source estimate. Q49 asks
whether jointly retained factor lengths and signs supply an independent
central comparison, not to prove the binomial identity again.
