# While Q45 runs: Möbius/theta collapse and its required inverse return

2026-10-26. Root derivation; bounded independent read-only check PASS
(q45_primitive_screen) for M1–M3, finite tail and receiver boundary. Not a new
CCM bound. Sources: Q18 exact phi_j scaling; Q17 actual normalized g,k and
source moments; same source convention as the two quadrature notes.

Write U_mu f(t)=sum_(d>=1)mu(d)/sqrt(d) f(t+log d), initially pointwise.
The exact Q18 identity d^(-1/2)phi_j(t+log d)=phi_(dj)(t) gives

 U_mu Phi(t)=phi_1(t).                                      (M1)

At fixed real t the double series is absolutely convergent by Gaussian
index decay and the elementary divisor bound; likewise locally uniformly
for each fixed derivative. Thus (M1) and U_mu F0=F1 are legal, where
 F0=-4(partial²-1/4)Phi, F1=-4(partial²-1/4)phi_1.
This is genuine coefficient cancellation, but the finite cutoff is different:
 U_(mu,D)Phi=sum_(j>=1) a_D(j)phi_j,
 a_D(j)=sum_(d|j,d<=D)mu(d).
For 1<j<=D this is zero; for j>D it is not generally zero. The omitted
infinite tail has coefficients -a_D(j), j>D. Its full return cannot be
replaced by the statement that the infinite divisor sum is zero.

## Actual inverse does not preserve the source class after collapse

Direct substitution u=pi exp(2t) gives, for Re z>-5/2,
 M_phi1(z)=pi^(-z/2-1/4)(z-1/2)Gamma(z/2+5/4).
Hence M_F1(w)=-4(w²-1/4)M_phi1(w) !=0 for the fixed hypothetical
w=delta+i gamma, 0<delta<1/2. The true F0 has a zero of order r at w;
F1 has lost that zero. All separate constants c_w remain unchanged.

The pointwise sum H_g=U_mu g and its fixed derivatives converge locally
normally, and H_g decays doubly exponentially at +infinity. Commuting the
finite-order differential operator through this convergent series gives
 (partial+w)^r H_g=F1/c_w.
The +infinity tail uniquely selects
 H_g(t)=(-1)^r exp(-wt)/[c_w(r-1)!]
              int_t^infinity (s-t)^(r-1)exp(ws)F1(s)ds.       (M2)
The integral converges at both ends when its lower limit tends to -infinity:
F1(s)=O(exp(5s/2)) there, and is doubly exponential at +infinity.
Its leading asymptotic is therefore
 H_g(t)=(-1)^r M_F1(w)/[c_w(r-1)!]
                  (-t)^(r-1)exp(-wt)(1+o(1)), t->-infinity. (M3)
For r=1 the polynomial has degree0; lower-degree terms for r>1 are included
in the relative o(1). The leading coefficient is nonzero. Thus H_g is NOT L2.
Uniqueness uses the fact that a nonzero homogeneous exp(-wt) polynomial
cannot decay doubly exponentially at +infinity.

Each finite H_(g,D)=U_(mu,D)g is a finite sum of the original L2 profiles
and has two-sided double-exponential tails (constants may depend on D).
The exact pointwise remainder H_g-H_(g,D) inherits (M3) and is also not L2.
The non-L2 growth cancels only when these two infinite objects are recombined
to recover the finite original source. Their separate L2 norms cannot pay a
finite return. This is a scope statement about this attempted splitting,
not an impossibility theorem for a signed correlation with fast-decaying k.
Such correlations can converge and all their mixed terms must remain.

## Decision and complete consumer accounting

M1 must not be used to replace the actual normalized pair by a single-Gaussian
source with the old interpolation and receiver unchanged: the selected zero
moment has been removed, as explicitly witnessed by M_F1(w)!=0. Either keep
the exact finite tail before inversion, or prove a new joint bound for the
paired non-L2 pieces with their boundary cancellation. No such bound is
provided by M1–M3. No infinity/finite interchange inside the original inverse
or an independent favorable sign is asserted.

Keep the independently checked finite pair reduction d<=m/log^6m=o(1),
with its exact complementary k<log^6m long-mu sum. Its original-P mixed return
is still o(1); full self terms O_w(1) and arch O_w(L) are paid once. This
collapse screen does not improve the surviving long sum or the inherited
endpoint O_w(sqrt(m)/L+L). It supplies no all-P T_>R exponent, no source
spectral lower bound and no RH claim. No additional message sent during Q45.
AUTOPSY: dropped=BOUNDARY; note=Infinite Möbius collapse removes the selected zero moment; the exact inverse tail must return before using the original pair receiver.

Shelf reconciliation: Q18_THETA_FILTER_TRANSFER already retains a finite
theta-index edge, and Q17 verdict around line680 warns against an unpaid
improper inverse. The explicit nonzero F1 moment diagnoses that same boundary;
this is not counted as a new independent arithmetic saving or a new no-go.
