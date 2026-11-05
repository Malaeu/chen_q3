# No nonzero positive raw-response square can be a minorant of full V

STATUS: ACCEPTED_LIMITED_PAPER; ACCEPT_FIXED_POSITIVE_RAW_RESPONSE_MINORANT_OBSTRUCTION_ONLY.
Base: a9f89af4dea01430be79ed3d2499afaac94e2b71.
Original full V and RH: OPEN. No negative original-V witness is claimed.

## F0. Return point and exact decision effect

The old SOURCE_ENERGY_PREFLIGHT excludes a bounded reservoir with specified
unitary dynamics. NULLFIELD excludes a positive fraction of a specified lifted
field energy. POINCARECOMP excludes an absolute derivative comparison. None
may be generalized just by dropping its hypotheses. Here a direct corollary
of the accepted source-tail estimate and analytic positivity propagation
excludes an entire precisely stated class of minorants of ORIGINAL V.

The class consists of a fixed nonnegative weighted square of the raw scalar
response P_c(t)=sum_i c_i f(t+x_i). This includes ordinary L2 energy, bounded
nonnegative weights and individual point observations. It does not cover a
different transformed response, a source-dependent moving observation, or a
weight that changes with the tested family. The mathematical mechanism is
inherited tail comparison plus all-rank propagation, not a new source identity
or a new positivity mechanism. No literature-novelty claim is made.

Pinned inputs: ANALYTIC_POSITIVITY_PROPAGATION A1--A2; FULL_SIGN_TRANSFER_AUDIT
for the unchanged source/target; SOURCE_ENERGY_PREFLIGHT E7 for the full-source
tail estimate; NULLFIELD_INTAKE_AND_COUPLING I2--I3 for prior-scope comparison;
LAYER_GRAM_TEST L2--L5 for the positive quartic comparison below.

## F1. Fixed target, observation measures and theorem

Let f=Phi/||Phi||_2 be the complete positive even theta source and

    V(x,y)=int_0^infinity (2t+x+y) f(t+x)f(t+y)dt.

Let mu be a nonzero, positive, locally finite Borel measure on [0,infinity)
such that, for every a>0,

    int_[0,infinity) exp(-a exp(2t)) dmu(t)<infinity.       (F1)

Finite measures, Lebesgue measure and measures with polynomially growing
densities satisfy F1. In particular atoms, including an atom at zero, are
allowed. Define the raw-response Gram kernel

    G_mu(x,y)=int_[0,infinity) f(t+x)f(t+y) dmu(t),
    G_mu[c]=int |P_c(t)|^2 dmu(t)>=0.                     (F2)

Claim: for EVERY such mu, every kappa>0 and every nonempty open real interval J,
there is a finite complex row with nodes in J for which

    V[c] < kappa G_mu[c], with G_mu[c]>0.                 (F3)

In particular J can be the original I=(-log(2)/2,0). Equivalently, no positive
constant multiple of this fixed nonzero raw-response Gram kernel is a PSD
minorant of V on the entire required finite-family class. This is a statement
about a lower-bound strategy, not about the sign of V itself.

## F2. The full kernels have one common holomorphic domain

The accepted full-series bound on S={z:|Im z|<pi/4} says that, for z in a
fixed compact subset and t>=0,

    |f(z+t)| <= C exp(9t/2) exp(-c exp(2t)), c>0.          (F4)

For a pair of compacts the product is bounded by C' exp(-c' exp(2t)),
absorbing exp(9t) into part of the exponential. F1 therefore provides an
integrable majorant for G_mu on every compact of S x S. The integrals over
bounded t intervals are holomorphic, and their tails converge uniformly on
compacts. Thus G_mu is jointly holomorphic on S x S. V has exactly that
extension by accepted A2. K_kappa=V-kappa G_mu is consequently holomorphic
there and real symmetric on real nodes. No continuation of mu itself is used.

## F3. A distant negative diagonal of the COMPARISON kernel

Full-source E7 proves, for u>=1,

    f'(u)<=-pi exp(2u) f(u).

For R>=1 put L_R=pi exp(2R). Integrating the differential inequality gives
f(R+s)<=f(R) exp(-L_R s) for s>=0. Exact evenness, then this bound, gives

    V(-R,-R)=2 int_R^infinity u f(u)^2 du
      <= f(R)^2 [R/L_R+1/(2 L_R^2)].                     (F5)

Since mu is nonzero and locally finite, some finite B>=0 has
m=mu([0,B]) in (0,infinity). If R>B+1, evenness and the decreasing positive
tail imply f(t-R)=f(R-t)>=f(R) for 0<=t<=B. Hence

    G_mu(-R,-R)>=m f(R)^2.                              (F6)

This includes mu concentrated at t=0. The quotient in F5--F6 tends to zero:

    0<V(-R,-R)/G_mu(-R,-R)
       <=[R/L_R+1/(2 L_R^2)]/m ->0.                     (F7)

For each fixed kappa, sufficiently large R therefore gives
K_kappa(-R,-R)<0. Both diagonal values themselves are positive; the negative
quantity here is V-kappa G_mu, not V. No divergent endpoint test is used.

## F4. Localization to the ORIGINAL allowed interval and normalization

If K_kappa were PSD on every finite complex row in J, the accepted analytic
propagation lemma A1 would make it PSD on all of R. Its hypotheses are
verified in F2, and the mixed old/new matrices in that lemma are essential.
This contradicts F7. Thus some finite row c in J has K_kappa[c]<0.

To ensure G_mu[c]>0 without an unstated injectivity assumption, handle the
possible case G_mu[c]=0 explicitly. Choose a node a in J and let e be its
one-node row. Because f is strictly positive and mu nonzero, G_mu[e]>0.
The Gram identity gives P_c=0 mu-almost everywhere, so
G_mu[c+epsilon e]=epsilon^2 G_mu[e]>0 for real epsilon!=0.
The finite quadratic expression K_kappa[c+epsilon e] remains negative for
sufficiently small epsilon by continuity. Adjoin a to the row if needed.
This proves F3, including atomic measures and possible null Gram rows.

Rescale such a row to G_mu[c]=1. Consequently, on any J,

    inf_{finite rows, G_mu[c]>0} V[c]/G_mu[c] <= 0.        (F8)

IF the still-open V>=0 is true, this infimum is exactly zero. Without that
hypothesis we assert only the upper bound, not equality or a negative V.
The proof gives no rank, coefficient-size or conditioning bound for the
localized rows. Positive fixed-rank tests are not contradicted.

## F5. Consequence for exact energy realizations

Any representation V= kappa G_mu + R with R a PSD kernel on all rows is
excluded by F3. In particular, if an exact Hilbert Gram family Psi_x for V
were constructed, its raw scalar readout cannot be bounded: there cannot
be a bounded linear operator B into L2(mu) with

    (B Psi_x)(t)=f(t+x), for every x in J.                (F9)

Indeed G_mu[c]<=||B||^2 V[c] would contradict F3 with kappa=1/||B||^2.
B cannot have norm zero because every individual readout is nonzero.
For mu=delta_T, this rules out a bounded vector readout of f(T+x), T>=0,
without assuming any particular generator, evolution or reservoir dynamics.
Unbounded observations, other transformed fields, and exact cancellations
are outside this implication. Their existence or positivity is not supplied.

This does NOT prohibit all positive Gram representations. The accepted
quartic source f_q(u)=C exp(-a u^4-bu^2), a>0, has an explicit positive
Gram representation for V_q (LAYER_GRAM_TEST L2--L5), yet its decreasing
tail satisfies -f_q'/f_q=4au^3+2bu and V_q(-R,-R)/f_q(R)^2->0.
The same comparison argument applies to it for mu=delta_0; we do not
import the entire F1 measure class for the quartic source. Thus ordinary
positivity and absence of a raw point-readout floor are compatible. Conversely, the
Gaussian f_g(u)=C exp(-bu^2), b>0, has exactly
V_g(x,y)=f_g(x)f_g(y)/(2b), allowing a delta_0 floor. Its slope grows only
linearly; the crucial ratio R/L_R does not tend to zero there.

Decision: do not propose another fixed nonnegative weighted raw-response
square as an independently positive part of V, even with an arbitrarily
small constant. A useful remaining construction must respect F9's
observation obstruction and still prove its exact identity with full V.
This is a broader filter from old analytic tools, not an RH proof, an
original-source negative witness, a canonical admission or a counter reset.

AUTOPSY: dropped=OBJECT_IDENTITY; note=Every fixed nonzero admissible positive measure of raw-response squares has more diagonal mass than original V can pay after translation; analytic all-rank propagation excludes a positive floor already on the original interval.

## Independent acceptance

Candidate SHA256: 8a5a91813d3b8b7a6c8e21c439c7436358b1e1989818db2405fb414992ce4260.
Complete independent review SHA256: 1353f3af063d7b20844fc9d537b72612fb7861f55c51ded3b8dbdd2c0ef67d36.
Parent check SHA256: cfae75a109007435b6172f9c1660f31ab18e887350d1bd2ac8e4a06df1524714.
Reviewer: /root/pairzero_geometry_review. The full independent review and pinned source formulas were read. The quartic comparison was explicitly restricted to the point measure delta_0 before final review. Only the raw-response-square floor and conditional bounded-readout obstruction is accepted. No Lean verification, canonical admission, original-V negative witness or source-sign progress is asserted.
