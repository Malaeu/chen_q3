# Post-Q44 signed auxiliary cutoff screen

2026-10-26. Bounded analytic screen, not a new arithmetic gain or a closed
consumer node. Sources: Q17 verdict exact signed object and its actual C
bounds; Q44 conclusion; CCM_POST_Q44_AUXILIARY_CUTOFF_SMOOTHING.md.
Original all-P objective unchanged. No Q45 sent.

Fix the same actual g,k, h=L/2-log L, P and m. Let J_s use auxiliary
cutoff n<=m exp(s), s>=0, with both C(2h-log n) and C(2h+log n).
For a finite signed or complex measure nu_m of mass 1, set V_m=||nu_m||TV.
The actual C tail and Chebyshev mass give, uniformly in s>=0,

 |J_s-J_0| <= E_m := C_w sqrt(m)(1+L) exp(-c_w L^2).

One direct proof partitions n>m into log intervals [L+j,L+j+1]. Their
Lambda/sqrt(n) masses are O(sqrt(m) exp((j+1)/2)); both C arguments have
absolute size at least 2log L+j. Sum the resulting double-exponential
majorant. Constants may be weakened to obtain the displayed E_m.
All prime powers are included. The extra (1+L) is harmless and conservative.

Therefore, BEFORE any forcing-seam absolute completion,

 J_nu-J_0 = integral (J_s-J_0) dnu_m(s),
 |J_nu-J_0| <= V_m E_m.                                      (S1)

This also justifies the integral for finite variation with unbounded cutoff
support: the already formed scalar J_s is uniformly bounded by |J_0|+E_m.
It does not justify interchanging the infinite prime forcing and its inverse.
Every original n<=m retains coefficient exactly 1. In particular the two-cut
combination (1+a_m)J_0-a_m J_B differs by at most |a_m| E_m.

With X=m^delta L^(-2delta), any V_m=exp(o(L^2)) gives V_m E_m=o(X), indeed
o(1). More generally V_m<=exp(alpha L^2), fixed alpha<c_w, also gives o(1).
Conversely, an actual change |J_nu-J_0|>=theta X, theta>0 fixed, necessarily
requires

 V_m >= theta X/E_m
     = (theta/C_w) exp(c_w L^2+(delta-1/2)L)
                           L^(-2delta)/(1+L).               (S2)

This is only a NECESSARY amplification threshold; no existence of such a
filter or useful effect at that size is asserted. An upper bound E_m alone
cannot imply an actual error or lower expense of every possible verifier.

Return the scalar J_nu to J_0 first. Then apply the inherited original-m
whole-pair projection/cutoff/contact return rho_C:=rho_K+rho_S=o(1) ONCE. Self terms and
H_d are unchanged. The additional mixed-term error is <=2V_m E_m; the
archimedean price is O_w(L) once. No enlarged-cutoff operator is applied to
Fourier leakage. For V_m E_m=o(1), the inherited endpoint full fallback stays
O_w(sqrt(m)/L+L)+o(1), with no improved exponent.

Decision: do not search bounded/polynomial signed cutoff weights merely to
make the actual pair's value smaller. The entire retained original portion
is exactly unchanged and the added tail is too small. This does NOT exclude
using a signed representation to PROVE a stronger bound on that same value.
That approach still needs an independent estimate on the joint forcing before
absolute values. Nor is this a no-go for cutoffs below m: those remove original
prime terms and must pay a different, currently unbounded return.

This is an extension/preflight of attempt1, not a fabricated second independent
mechanism or evidence of a new CCM spectral bound. No numerical tests needed
for (S1)-(S2); no Lean/Arb run. Independent bounded audit by q44_cutoff_average_check passed S1, S2 and
the original-P ordering; its notation correction rho_C=rho_K+rho_S is applied.
Inherited source bounds are not independently recertified here.
AUTOPSY: dropped=NONE; note=Normalized signed enlargement leaves original coefficients intact; small actual tail limits value alteration, not the power of a new joint proof.
