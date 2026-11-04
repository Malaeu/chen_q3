# Independent bounded audit of inherited density-tail port

Status: PAPER / DIAGNOSTIC. The inherited implication from the stated uniform Ingham premise to an even nuclear tail `O_c(L^7/h²)` and an `o(N)` score loss checks out. No counterexample found in the audited port. No new zero census, spectral computation, state change, or export.

Inputs: `/workspace/second_moment/output/INPUT_VERDICT.md`, exact supplied `07a242c1` verdict, §§1–4; target `/workspace/ccm_phi/output/INPUT_VERDICT.md` (5.2). Here L=log m, h=1+log L, Omega=2pi m/L, T=(1+ch/L)Omega, fixed 0<c<1, and sigma asymp L. This audit checks the deductions from the external density premise, not a new proof of Ingham or the inherited rank–trace inequality.

## External premise and counting

The external premise is the stated unconditional *uniform* estimate

`N(1/2+a,U) <= C_I U^[3(1/2-a)/(3/2-a)] (log U)^5`,

for 0<=a<=1/2 and all sufficiently large U, with constants independent of a, plus the ordinary bound N(U)<=C_N U log U. Classical Ingham remains an imported theorem statement here; its proof and the precise endpoint/uniformity provenance were not independently re-proved in this audit. Uniformity is necessary for the integration in a; pointwise-in-a bounds with uncontrolled constants would not suffice. The claimed deduction is conditional on this precise imported version.

N(U) counts all upper-half-plane zeros with multiplicity. Reflection beta ->1-beta preserves gamma and multiplicity. An off-line reflected pair contributes two to N, whereas its lower conjugates are not counted there. This is consistent with the factor2 for the two height signs in the operator tail.

## Evaluation and even nuclear norm, inherited (2.1)–(2.2)

For z=gamma+i eta, a=|eta|, gamma>=T>Omega, the physical even column is

`F_j(z)=2 d_j z sin(zL/2)/(sqrt(L)(z²-omega_j²))`.

The estimates used are valid:

- `|sin(zL/2)|² <= exp(aL)`;
- `|z²-omega²|²=(gamma²-omega²)²+2eta²(gamma²+omega²)+eta^4 >= (gamma²-omega²)²`;
- `|z|²<=gamma²+1/4` and `sum_j d_j²=2m+1`.

Consequently `||e_E(z)||² <= K_m(T) m^a/gamma²`, with precisely the inherited `K_m(T)=4(2m+1)/L * (1+1/(4T²))/(1-Omega²/T²)²`. Its dependence on T can be pulled outside the sum since gamma>=T. A single zero term is rank one with trace norm the product of its two evaluation norms. Real carrier functions and parity give equal norms at the reflected arguments, even though the rank-one summand need not be Hermitian or PSD. Summing by the triangle inequality and paying both height signs gives `||R_T^E||_1<=2K_m(T)W_m(T)`. No positivity of the tail is assumed. For a quartet the upper count contains two zeros and this rule pays all four zero terms exactly once before any slack. Zeros at gamma=T are included via the lower Stieltjes value A(T-).

The optional odd assertion is also consistent: replacing z in the numerator by omega_j only decreases the crude upper bound because omega_j<gamma. The target (5.2) needs only the even block; no full-carrier trace asymptotic is imported accidentally.

## Weighted density, inherited (3.1)–(3.5)

For each zero, `m^a=1+L integral_0^a m^u du`. Reflection doubles the right-of-line count for almost every positive layer. Thus

`A_m(U)=N(U)+2L integral_0^(1/2) m^a N(1/2+a,U) da`

is correct. Possible equality choices at layer boundaries have measure zero; on-line zeros contribute only the baseline1. There is no sign assigned to left zeros.

For f(a)=3(1/2-a)/(3/2-a),

`f(a)=1-2a/(3/2-a) <=1-4a/3`,

and `(f(a)+a)'=1-3/(3/2-a)²<=-1/3` on the entire layer interval. The exponent of the integrand is at most `-[4log(U)/3-L]a`. For U>=T and d_T=4log(T)/3-L>0, its integral is at most1/d_T. This proves (3.3) with the stated constants.

Integration by parts against the weighted zero measure gives

`W_m(T)=-A_m(T-)/T²+2 integral_T^infinity A_m(U)/U³ du`.

The infinity term vanishes by (3.3); the lower term is nonpositive, so dropping it is an upper bound. Direct integration gives

`integral_T^infinity (log U)^5/U² du=P_5(log T)/T`,

with the displayed coefficients 1,5,20,60,120,120, and the logarithmic term gives `(log T+1)/T`. Hence (3.4) and, after multiplication by2K, the coefficient8 in (3.5) are correct. This controls the whole infinite tail, not just one dyadic band.

For the cofinal cutoff, `log T=L-log L+log(2pi kappa)`. Eventually d_T>=L/6; `1-kappa^-2` is comparable to ch/L for fixed positive c; `(2m+1)/(LT)=O(1)`; and the bracket in (3.5) is O(L^5). Thus E_den=O_c(L^7/h²). Constants/onset are not numerically supplied. This is an upper bound, not an equivalent, and does not extend to c=0 or a claimed uniform c->0 limit.

## Source norm and score payment, inherited (4.1)–(4.3)

The rough source Frobenius bound can be obtained without the target's sharper section3 result. Circle nodes log n/L have pairwise circular separation at least1/(mL): adjacent logarithms have gap>=1/m before division by L, and the wrap gap is at least log2/L. Packing by that separation bounds each absolute Dirichlet-kernel row sum by a constant times mL(1+L). Schur's test applied at each physical x to the two shifted Fourier sums, followed by integration and compression, therefore gives `||B||F²=O(mL² sum c_n²)`. The crude `sum c_n²<=L²(1+L)` gives O(mL^5). The displayed factor4 from separating two shift directions is consistent and not needed sharply here.

For Gamma, the zero-extension difference estimate has an interior `Omega²u²` contribution and an endpoint-strip contribution bounded by `4(2m+1)u/L`. Combining with the universal bound4 and integrating the arch kernel split at u~1/Omega and1 gives operator norm O(L), and hence Frobenius norm O(sqrt(m)L). The pole has rank one and norm O(sqrt(m)+L). Therefore `||A||F=O(sqrt(m)L^(5/2))` follows.

The even leading trace `tr A=mL(1+o(1))` is consistent with the independent exact Gamma check in `AUDIT_ASYMPTOTICS.md`: it yields the stronger arch trace `m(L-1-log L)+O(L²)`; the inherited prime and pole trace bounds are o(mL). No zero-sign input is needed for that trace statement. The current tail-error calculation itself only needs the rough Frobenius bound, not the trace asymptotic.

For sigma asymp L and E=E_den, the explicit conservative score is

`F_safe=4tr(A)/sigma-4E/sigma-(||A||F+E)²/sigma²`.

Thus the loss from `Phi(A/sigma)` is exactly

`4E/sigma+2||A||F E/sigma²+E²/sigma²`.

Using the preceding bounds gives the inherited powers

`O_c(L^6/h² + sqrt(m)L^(15/2)/h² + L^12/h^4)=o(m)=o(N(T))`.

Both the exponents and signs check. This can alternatively be derived directly from `head=A-R`, `|tr R|<=||R||_1`, `||R||F<=||R||_1`, and `||head||F<=||A||F+E`; it never turns the tail into a positive operator. No finite onset for the o(N) statement follows.

## Consequence and remaining interface

The inherited cofinal density-tail port supplies the `o(N)` loss needed by target (5.2), conditional on the stated uniform Ingham import and the exact literal source-to-zero identity. Combining it with independently valid t->1, v->4/3 gives normalized safe score8/3-o(1). The final fractions still use the inherited rank–trace consumer, which this file does not re-prove. The sampling normalization must be sigma=L+O(1) for the substitution4t->4; sigma2L cannot use that substitution. No finite claim is obtained by dropping these asymptotic errors.

No `CCM_PHI_AUDIT_COUNTEREXAMPLE` found in this port. Review scope: analytic deductions and source norm estimates; external Ingham proof, exact rank–trace consumer, and finite interval backend remain separately identified dependencies.
