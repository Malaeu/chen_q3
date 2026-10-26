# Post-Q41: can the cheap constrained inverse be iterated?

2026-10-26. Own bounded preflight; independent q32_annulus_audit qualified PASS.
Audit checks hyperbola/Stieltjes, actual original-P return and scope;
inherited contact Gram estimate is used, not independently rebuilt.
Consumer unchanged: original-P one-sided T_gtR upper, eta(epsilon)->0.
This checks reuse of Q04 inside Q41, not a new bound for CCM.

Q04 proves ||Z f||<=3||f||+6||f'|| on original contact inputs, where
Z=sum_{n<=m}n^(-1/2)V_log(n), V causal zero-extended shift on [0,L].
Q41 contains powers Z. The input hypotheses must be re-established before
iterating the cheap bound; no intermediate compression is legitimate.

## A second application has a surviving moment

Choose fixed a>0 and nonzero nonnegative chi in C_c^infinity(0,a).
Let f=(chi''-chi/4)/||chi''-chi/4||_2, fixed as L grows above a.
It is unit, has zero endpoint values and both exponential moments zero.
Use the minus-sign Laplace convention F(z)=int exp(-zt)f(t)dt.
Then F(z)=(z^2-1/4)Chi(z)/||chi''-chi/4||_2.
Thus J=int u exp(-u/2) f(u)du=-F'(1/2)
=-int exp(-u/2)chi(u)du/||chi''-chi/4||_2<0.
This explicit convention differs from the plus-sign notation of Q40.

Exactly Z^2=sum_{n<=m}d(n)n^(-1/2)V_log(n), including all ordered divisor
pairs; terms with product>=m vanish physically, not by coefficient deletion.
The elementary Dirichlet hyperbola formula gives
 D(x)=sum_{n<=x}d(n)=x log x+(2gamma-1)x+O(sqrt(x)), x>=1.
This follows from D(x)=2sum_{r<=floor(sqrt x)}floor(x/r)-floor(sqrt x)^2
and H_k=log k+gamma+1/(2k)+O(k^-2). No prime or RH hypothesis is used.
For t>=a, Stieltjes integration against x^-1/2 f(t-log x) gives
 (Z^2 f)(t)=exp(t/2)int_0^a exp(-u/2)(t-u+2gamma)f(u)du+O_f(1)
           =-J exp(t/2)+O_f(1).
All boundary terms vanish because f and all derivatives vanish at 0,a.
The O(sqrt x) error integrates to at most
 C int_0^a (|f'(u)|+|f(u)|/2)du,
uniform in t,L. Consequently ||Z^2 f||>=c_f sqrt(m) eventually, using
only t in [L-1,L] and L>a+1. This is a norm of Z^2, not a CCM sign.

## Return to the original sparse band

Use the accepted fixed-compact-profile Fourier/contact correction of Q40
§5.2, now with one packet instead of two. Derivative norms remain fixed,
all three original contacts are exact, and the normalized contact Gram
has the same eventual lower bound. It yields unit f_m=F_M c_m, c_m=P c_m,
 delta_m=||f_m-f||<=C_q L^(q-1/2)M^(1/2-q).
No compact support is asserted after this correction.
By the exact ordered convolution,
 ||Z^2||<=sum_{ab<=m}(ab)^(-1/2)
         <=2sqrt(m)sum_{a<=m}1/a<=2sqrt(m)(1+L).
Thus ||Z^2(f_m-f)||<=2sqrt(m)(1+L)delta_m=o(1)
for a fixed q>2/epsilon+2. Therefore ||Z^2 f_m||>=c'_f sqrt(m).
All terms are kept; the estimate transfers a single norm discriminator,
not a lower bound for the alternating Q41 source or for its signed spectrum.

## Decision and unchanged consumer budget

Do not iterate the Q04 constrained norm lemma through uncompressed Z powers.
The second power already has a half-power norm on an actual original-P
family. This says nothing adverse about joint cancellation with the short
Mobius factors and alternating binomial channels. Those must remain joint.
No full-source exponent improved; no new norm certificate is optimized.
Retain A<=s_keep P, s_keep<=6sqrt(m)+6m^(1/4),
T_gtR<=(s_keep+b_div)P, PK_mP>=-(s_keep+50L+8)P.
One bounded reuse preflight, not three failures; no Q42 sent.

## Bounded shelf return

post_q41_supplier_screen found no qualifying supplier in the inspected shelf.
Three focused ask.sh --defer-external queries returned INCOMPLETE because
q3_docs semantic-index freshness validation failed; no global absence claim.
Q09 uncentered scalar cap and centered PNT fallback are already tested.
The positive heat-RKHS Carleson cap lacks a signed-source comparison; integer
quadrature leaves the actual Lambda-1 term. These repeats count as zero new
attempts. Q04 remains useful only within its original input hypotheses.
No external theorem newly imported, numerical spectrum, Lean or Arb run.

## Rejected follow-up phrasing: finite-rank subtraction alone

Root and post_q41_supplier_screen compared Q04,Q26,Q27,Q41. Merely writing
Z^j=F_j+R_j and recombining Q41 before norms supplies no new inequality.
Q27 already pays growing-continuum subtraction and the entire original-P
analytic return; its whole signed residue lower bound is equivalent up to
m^{2epsilon} fees to the target. This equivalence by itself does NOT make
every new method a duplicate. The rejected phrasing is specifically missing
an additional actual-short-mu cancellation and a bound for its full return.
No Q42 is dispatched under that phrasing. The explicit second-power result
remains one bounded own test; duplicate screening adds no failed-attempt count.
The selected-pole return of Q26 is adverse, not favorable evidence.
