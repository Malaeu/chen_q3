# Q16 own attempt: retain negative endpoint credit, pay its complete remainder

2026-10-25. Original N=m,L=log m,M=R=floor(m^epsilon),fixed0<epsilon<1/32.
P is the orthogonal projection in the |j|<=M band onto the original
three constraints b,v_+,v_-, padded by zero in the original |j|<=m carrier.
A(n)=P Q_M(log n)P,S=sum Lambda(n)A(n)/sqrt(n). No new hypothesis.
This tests a one-sided inequality for the original LINEAR form, not II^2.
All prime powers, Fourier mixed entries and both temporal directions remain.

## Source and choice

Q15 rules out only weighted Cauchy followed by independent scalar row caps.
CCM_Q03_ENDPOINT_SIGN_TEST.md already proves endpoint A(m exp(-h)) is
indefinite: negative cubic alone cannot be dropped as if it were the whole
operator. Here the negative cubic is retained to absorb its actual cross
terms. No novelty claim for the Taylor identity. Q05 Fourier/sup-variation
and old absolute Abel/PNT are already stalled and are not new attempts.

Let c=Pc, f(t)=L^(-1/2)sum_(|j|<=M)c_j exp(2pi i jt/L), periodically
continued for Taylor calculation only; the source overlap uses zero extension.
f(0)=f(L)=0, both exponential contacts remain, ||f||_[0,L]=||c||,
||f''||_[0,L]<=Omega^2||c||, Omega=2pi M/L.
For 0<h<=L the exact source form is
 q_c(L-h)=2 Re integral_0^h conjugate(f(t)) f(t-h) dt.
Here f(t-h)=f(L+t-h) by periodicity, not a replacement of the zero extension.
Write a=f'(0),f(t)=at+e_+(t), f(t-h)=a(t-h)+e_-(t-h).
Taylor's integral formula and Cauchy ONLY for the derivative remainder give
 |e_+(t)|<=t^(3/2)Omega^2||c||/sqrt(3),
 |e_-(t-h)|<=(h-t)^(3/2)Omega^2||c||/sqrt(3).
These bounds use [0,t] and [L+t-h,L] inside the original window.

## One-sided bound before any operator square

Put B=Omega^2||c||. Exact leading contribution is -|a|^2 h^3/3.
All mixed terms between a and e_±, and e_+ and e_-, give the upper
 q_c(L-h)<=-|a|^2h^3/3
   +16/(35sqrt(3)) |a| B h^(7/2) + (pi/64) B^2 h^4.
Indeed integral_0^h (h-t)t^(3/2)dt=4h^(7/2)/35 and
integral_0^h t^(3/2)(h-t)^(3/2)dt=3pi h^4/128.
Optimizing this scalar concave quadratic in |a| gives
 q_c(L-h)<=(64/1225+pi/64)Omega^4 h^4||c||^2
             <=Omega^4 h^4||c||^2.                         (1)
Thus A(m exp(-h))<=Omega^4 h^4 P, including all mixed modes.
This is a genuine directed improvement over the trivial2P near the endpoint;
it does not assert A<=0. The negative term paid the cross products.
No independent choices of vectors or weights have been introduced.

## Complete budget and optimization obstruction for THIS bound

Choose 0<h0<=L. Split the full source at x0=m exp(-h0), keeping equality
in the first block and every endpoint atom in the second. A(m)=0.
For n<=x0 use ||A(n)||<=2; for n>x0 use(1), since log(m/n)<h0.
The inherited elementary W(x)=sum_(n<=x)Lambda(n)/sqrt(n)<=6sqrt(x)
then gives, with no missing boundary strip,
 S <= B_end(m,h0)P,
 B_end=12sqrt(m)exp(-h0/2)+6sqrt(m)Omega^4 h0^4.            (2)
For h0=0 take the old12sqrt(m) bound. Also retain that old bound as fallback.
This positive sum is the completed certificate, not actual lambda_max(S).
For fixed epsilon>0, Omega>=1 eventually. For every h0 in(0,L]:
 if h0<=1, first term>=12exp(-1/2)sqrt(m)>6sqrt(m);
 if h0>1, second term>=6sqrt(m).
Consequently inf_h0 min(12sqrt(m),B_end)>=6sqrt(m).       (3)
Optimizing this completed budget cannot supply any power<1/2. This lower
bound is on the DISPLAYED certificate only, not CCM nor every possible
use of the sharper Taylor coefficient/local prime mass/retained a term.

Full original restricted floor:
 PK_mP >=-[min(12sqrt(m),B_end)+50log(m)+8]P.              (4)
For T_>R only, add (56+32Omega)sqrt(R)+12(1+log R)^2 once.
No Vaughan short-sector fee is charged: all factors were recombined to S.
The pq packet is exactly zero before(1)-(2); p^k retains log p. No mixed
Vaughan products are omitted because the original equality is linear.

## Concrete impasse and question

The negative endpoint geometry pays a short terminal slice, but making the
remaining early mass sub-half-power requires h0 comparable to log m, where
this remainder price is already too large. Improving the constant in(1)
or selecting h0 numerically does not repair(2). This is NOT an arithmetic
no-go. The unfunded step is a joint one-sided comparison for the central
prime-minus-continuous operator using both exponential contacts, before the
early-block norm in(2); neither PNT absolute error nor a renamed target pays it.
Ask Proshka to test a concrete joint continuation of this negative credit
(or justify a different earlier rollback), and require its entire budget.
Independent read-only q16_endpoint_audit: bounded PAPER PASS, all constants,
complex mixed terms, periodic/zero-extension distinction and full budget checked.
Inherited W/archimedean/receiver inputs not re-proved. No Lean/Arb or full spectra run.

## Shelf correction before escalation

Bounded q16_shelf readback located CCM_Q06_ONE_SIDED_EDGE_BUDGET.md:
it ALREADY proves q(L-h)<=3||f''||_infinity^2 h^5/80 and pays a narrow
shell o(1). Thus endpoint credit and paid remainder are NOT a new mechanism.
The present L2 second-derivative bound is only a different quantitative return,
not uniformly sharper (the old h^5 bound is better for sufficiently small h).
Its complete split is explicitly stalled. Do not submit it as an arithmetic
breakthrough or ask Pro to repeat Q06. Escalation must report the failed
continuation and request a different joint bulk mechanism or substantive
rollback, with the Q06 source included in full.

Root arithmetic check:64/1225+pi/64=0.10133228317152419<1;
12exp(-1/2)=7.278367916551601>6. No finite spectral proof inferred.
