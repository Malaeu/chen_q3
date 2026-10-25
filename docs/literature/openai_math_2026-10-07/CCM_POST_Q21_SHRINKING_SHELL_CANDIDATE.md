# Q21 shrinking-shell return: bounded certificate obstruction

25 October 2026. Original P, M=floor(m^epsilon), L=log(m),
0<beta<epsilon<1/32 fixed, Delta=m^(-beta). Same Q21 forward-shell routing.
This is a lower-price test of that Young certificate, NOT actual CCM spectrum.

Take a fixed smooth nonnegative bump eta supported in (1/16,1/8),
eta_D(t)=eta(t/Delta), q_D=(-eta_D''+eta_D/4)/N_D with its exact L2 norm.
N_D=Delta^(-3/2)||-eta''+Delta^2 eta/4||_2. Hence
q_D(Delta s)=Delta^(-1/2)(-eta''(s)+Delta^2 eta(s)/4)/||-eta''+Delta^2 eta/4||_2.
Both exponential contacts vanish exactly, ||q_D||=1. A fixed rescaled
positive interval has length c Delta and height >=c Delta^(-1/2).
For each fixed integer k, ||q_D^(k)||_1=O_k(Delta^(1/2-k)).

With f_L=(q_D(t)+q_D(L-t))/sqrt(2), Q21's linear Fourier/contact correction,
if its stated Gram estimate is used with these explicit derivative norms,
gives r=O_k(L^(k-1/2) M^(1/2-k) Delta^(1/2-k)).
Thus r/Delta=o(1) when k(epsilon-beta)>(epsilon+beta)/2.
Sup error is O_k(L^(k-1)M^(1-k)Delta^(1/2-k)), negligible relative to
Delta^(-1/2) when k>1 and M Delta/L -> infinity.
H1 error is bounded by (M/L)r plus normalization cost O(r/Delta).
Choose k larger if needed to make H1 error o(Delta^-1).
The returned real unit f_m has the original three contacts; no small support
is assumed after P. All-prime return is <=12 sqrt(m) r (||f_m||+||f_L||)
=o(sqrt(m) Delta). This includes all mixed terms activated by projection.

Verified arithmetic supplier (statement checked, original proof not re-proved):
uniform short-interval PNT for intervals of length comparable to
m Delta=m^(1-beta), with relative error o(1), retaining Lambda/prime powers.
Given this premise, Q21 exterior routes carry probability ->1/2 uniformly;
positive endpoint product is >=c/Delta over area c Delta^2, kernel >=c sqrt(m).
Consequently Xi>=c Delta sqrt(m), uniformly positive gauges and balances.

Full signed source: the long mixed term is the complete sum of
Lambda(n)/sqrt(n) times F_D(L-log(n)), F_D=q_D*q_D.
F_D has bounded amplitude and total variation O(1), support width O(Delta).
Short-interval PNT plus partial summation therefore gives error
 o(Delta sqrt(m)); its continuous main vanishes exactly because
integral exp(-v/2)F_D(v)dv=(integral exp(-t/2)q_D(t)dt)^2=0.
Same-lobe prime correlations vanish eventually (width<log 2).
Arch return O(Delta^-2)=o(Delta sqrt(m)) since 3beta<1/2.
Hence Q[f_m]=o(Delta sqrt(m)), using that unconditional arithmetic supplier.

Bounded consequence: the same certificate costs at least
c m^(1/2-beta). Since beta<epsilon, this cannot supply eta(epsilon)->0.
No matching upper for shrinking shells is asserted. No assertion for
beta>=epsilon, other routing, exact exterior-slack subtraction, or pair-only
source. In particular this does NOT automatically extend the separate
fixed-gauge shell-mean test, whose negative margin also shrinks.

Routing completion: use d_*(m)=4 beta L+C, C fixed sufficiently large.
For x=exp(d), d>=d_*, x Delta>=x^(3/4); thus the entire routed shell has
positive mass eventually. Keep all smaller/empty shells EXACT, not discarded.
The witness d=L-O(Delta) lies in the routed range since 4beta<1.
This is the stated m-dependent-threshold extension, not the literal fixed
threshold Q21 formula when a denominator is zero.

For partial summation, use cumulative residuals from a support endpoint.
Intervals >=m^(3/4) have relative error o(1) uniformly; shorter ones have
trivial error O(m^(3/4)log m)=o(m Delta). Thus cumulative residual is
uniformly o(m Delta); multiplying by x^-1/2 F_D(log(m/x)), whose total
variation is O(m^-1/2), gives o(sqrt(m)Delta). No absolute-value replacement
of the signed F_D occurs in its main term.

Supplier: Kaisa Matomaki, The Mobius function in all short intervals,
Oberwolfach Report 50/2019, printed p3177, equation (1), explicitly states
sum_(x<n<=x+H) Lambda(n)=(1+o(1))H for H>=x^(7/12+sigma), fixed sigma>0.
https://ems.press/content/serial-article-files/46829 (PDF page37).
Root checked the displayed statement; use sigma=1/6, hence threshold3/4.
Original attribution: M.N.Huxley, Invent.Math.15(1972),164-170,
https://doi.org/10.1007/BF01418933; original proof not independently audited.
Researcher additionally checked Lou-Yao https://hrj.episciences.org/127/pdf.

Root derivation plus shrinking_shell_budget bounded independent check PASS,
conditional only on inherited Q21 source/Gram identities, which were not
re-certified here. All prime powers, mixed returns and contact corrections
retained. This is no favorable CCM estimate and no numerical spectral test.
Exact sample epsilon=1/64,beta=1/128,k=8: r/Delta exponent -13/256,
relative sup -7/128, relative H1 -13/256, arch/price -61/128,
lower certificate price63/128.

This closes a parameter loophole of the original Young certificate only.
It is not a third independent mechanism and does not supersede the interior
or shell-mean tests. The exterior obstruction is removable as in Q21;
shrinking width after that exact removal remains outside this result.
AUTOPSY: dropped=CANCELLATION; note=Resolved-width shrinking does not rescue the uncorrected forward-shell Young certificate.
No Q22 sent; full CCM and source-specific signed comparison remain open.
