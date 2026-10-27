# Post-Q53: arbitrary finite weighted carrier, absolute-return price

2026-10-27. Bounded PAPER derivation, independent audit passed; see receipt below. Original source
and P unchanged; Q53 graph theorem and elementary theta bounds inherited.

Let a=(a_n) have arbitrary complex coefficients, finite support n<=N_aux,
sum |a_n|²=1. Define lift (La f)_n(t)=a_n f(t+log n) on the whole real t line.
This is an exact isometry of the ORIGINAL zero-extended f=I c, c=P c.
For every positive integer d set alpha_d=sum_n conjugate(a_n) a_(nd),
with missing entries zero. The sum of all graph edges with ratio d, integrated over t, has exactly
alpha_d times the original correlation I_d=integral conjugate(f(t))f(t+log d)dt.
Thus A_a[f]=2 Re sum_(p^k<=m) (log p)/p^(k/2) alpha_(p^k) I_(p^k).
Virtual d>=m overlaps vanish by support, but their graph cost stays paid.
All prime powers, complex phases and mixed terms are retained in the exact
remainder A[f]-A_a[f]=2 Re sum weight (1-alpha_d) I_d.
Q53(7.4), integrated after this isometry, gives A_a<= (log N_aux+3)||f||².
The explicit pointwise-absolute return certificate is
 E_a(m)=2 sum_(p^k<=m) (log p)/p^(k/2) |1-alpha_(p^k)|,
 S_a(m)=log N_aux+3+E_a(m), A<=S_a(m) P.
This is a sufficient certificate, not a necessary price of the source.

## Uniform obstruction for exactly that certificate

For each prime p, Cauchy gives
 |alpha_p|² <= (sum_n |a_n|²)(sum_n |a_(np)|²)
             = sum_(p|n) |a_n|².
Consequently for ANY finite prime set J,
 sum_(p in J) log p |alpha_p|²
 <= sum_n |a_n|² sum_(p in J,p|n) log p
 <= sum_n |a_n|² log n <= log N_aux.
No multiplicity or sign information from source is discarded in this statement:
it constrains only the auxiliary carrier coefficients.
Also |alpha_p|<=1 and |alpha_p|²>=1-2|1-alpha_p|.
Using J={p<=m} and log p <= sqrt(m) log p/sqrt(p), obtain
 log N_aux >= theta(m)-2 sum_(p<=m)log p |1-alpha_p|
       >= theta(m)-sqrt(m) E_a(m).
Q53 proves theta(m)>=m/8 eventually without RH or PNT. Hence
 log N_aux + sqrt(m) E_a(m) >= m/8.
For m>=1, log N_aux>=0 and E_a>=0 imply
 sqrt(m)(log N_aux+E_a) >= log N_aux+sqrt(m) E_a >= m/8,
so S_a(m)>=sqrt(m)/8+3 eventually, UNIFORMLY over all finite complex
carriers, including m-dependent supports, N_aux and weights.
This rejects subpower optimization of this graph-plus-absolute-return
certificate even after abandoning the rectangular equal-weight box.
It does NOT imply any positive lower for A, T_>R or full CCM; it does not
exclude signed remainder payment or a sharper graph comparison on the image.

## Full budget and next boundary

Trial T_>R <= (S_a+bdiv)P, PK_mP>=-(S_a+50L+8)P.
Small-divisor return occurs only in T, arch once in K. No contour fees added.
Retain the inherited half-power fallback s_keep<=6sqrt(m)+6m^(1/4);
no exponent improvement is obtained. No numerical dominance over every
individual carrier certificate is asserted.
No new full exponent. This is one substantive own post-Q53 attempt.
Rollback BEFORE replacing the complete defect by E_a; tuning carrier weights
alone cannot improve this certificate. Need actual signed defect inequality
or a different source supplier, not another optimized full graph norm.
AUTOPSY: dropped=NO_DERIVATION; note=Auxiliary divisibility mass forces half-power total certificate price uniformly over finite complex carrier weights.

## Verification receipt

weighted_carrier_audit qualified PAPER PASS, no material findings, on
SHA256407379ddbb71164c85fca9004d70113e9ab8daa2419212c350b99221791429f5.
Three wording clarifications incorporated: aggregate edges, N_aux distinct
from production N=m, and no universal numerical comparison to old fallback.
Root checked48 exact Gaussian-rational carrier/prime cases at supports
1,2,8,32 and primes2,3,5,7, using Q53 exact arithmetic. These check finite
Cauchy/conjugation algebra only, not actual source or cofinal certification.
No new production spectrum, Lean or Arb.
