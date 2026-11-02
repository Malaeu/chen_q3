# Independent certificate implementation review

2026-11-02. **PASS for the stated fixed finite Rayleigh enclosures.** No substantive normalization, integration or sign error found. This review does not certify the numerical envelope inputs, the first onset, or any cofinal statement.

Reviewed actual `certify.py`, both exact-dyadic witness files, completed `rayleigh_m51.json` and `rayleigh_m55.json`, plus `envelope.py`, CSV and `ENVELOPE.md`. Verifier SHA256 at review: `8e229d747574af5e0d982d660ff76c58c7f416894869f73754ab13648c424532`. The saved result files' witness and verifier hashes were independently checked. No reviewed producer files were edited and no duplicate eigensolve was performed.

## Normalization and source algebra

The witness integers divided by2^320 define an exact vector in the stated physical orthonormal basis. The certificate does not assume that the rounded vector is unit: N=Σc_n² is enclosed positively; Q(0)=2N; the arch tail is multiplied by2N; the scalar term is −c_D N; the complete form is divided byN. Numerical eigenvectors and matrices select candidates only and are absent from verification.

The scalar correlation synthesis is the contraction of the literal phased `q_even`: cosine coefficients2c_n²(1−s/L); diagonal sine coefficient−c_n²/(πn); each i<j pair contributes2c_i c_j d_i d_j[j sin(ω_j s)−i sin(ω_i s)]/[π(i²−j²)]. Thus its signs agree with the physical phi_n=d_n(−1)^n cos(2πnx/L)/sqrt(L). No missing endpoint factor or Fourier2π factor occurs.

The DH parameter is algebraic and enclosed with Arb square roots. The recurrence computes the coefficients of−D'/D at **all** integers, using b(n)=a(n)log n−Σ_{1<d<n,d|n}b(d)a(n/d). It does not filter to prime powers. The sum omits n=m legitimately because the exact physical Q(L)=0. The positive c_D=γ+log(8π/5)−π/2 is subtracted, giving the required signed constant log(5/π)+psi(3/4). No pole matrix is added.

## Rigorous integral and the removable origin

The code replaces a near-zero numerical subtraction by an exact analytic identity. Its `z` is

    z(s)=(2N−Q(s))/s,

continued through s=0 using

    (1−cos(ωs))/s=ω sin(ωs/2)sinc(ωs/2),
    sin(ωs)/s=ω sinc(ωs).

The identity s*j_D(s)=exp(−s/2)/[2sinc(i s)] then makes the callback exactly j_D(s)(2N−Q(s)). Here sinc(z)=sin(z)/z, not the π-normalized sinc. This regularization means **no omitted epsilon interval or independent near-zero remainder bound is required**. The s=0 singularity is removable in the actual callback. Other denominator zeros are genuine meromorphic poles away from the real integration interval.

Installed python-flint0.9.0 `acb.integral` documentation was inspected directly: ignoring its analytic flag is explicitly valid for meromorphic callbacks whose pole evaluations become nonfinite balls. This callback uses only entire sin/sinc/exp operations and a reciprocal; it has no branch-cut operation depending on the complex integration variable. The real algebraic constants were enclosed before callback evaluation. Thus the analytic contract is satisfied. The verifier requires finite panel enclosures and imaginary balls containing0; real projection encloses the exact real integral.

The tail is exact: ∫_L^∞j_D(s)ds=atanh(exp(−L/2))−atan(exp(−L/2)), multiplied by2N. Tolerance parameters are requested accuracy goals; the returned Arb balls, finite checks and strict upper endpoint establish the result, rather than the tolerance alone. `arb.str(radius=True)` includes decimal conversion error. Its documentation was checked; printed interval parsing may enlarge the ball, which is safe.

## Results independently read back

|m|saved outward Rayleigh ball|conclusion|
|---:|---|---|
|51|[−1.32685772638906062688395e−47 ±3.62e−71]|upper<0|
|55|[−0.663920646081049791677195486330354903436092995093398739402280 ±4.73e−61]|upper<0|

Both serialized intervals were independently parsed by Arb and again had strictly negative upper bounds. The parsed m51 width is below7.25e−71, satisfying the predeclared1e−49 width criterion by a wide margin. The larger printed radius relative to the internal radius reflects decimal rendering, not an under-enclosure. Witness norms were checked positive from the saved outward values.

These are certificates for existence of negative directions in the respective finite literal DH carriers. They are not certified values of the exact minimum or proofs that51 is the first negative m. They certify neither interpolation membership nor a negative projected-complement witness by themselves.

## Projection-envelope scope

`envelope.py` correctly extracts R from the saved **full** spectrum, checks numerical0≤δ<R, and evaluates−R+δ²/(R−δ). It uses the positive c_D and strict C<R−δ²/(R−δ)−c_D for the claimed conditional budget violation. The text explicitly requires an isometric true quiet-space synthesis Q and a genuine bound||AQ||≤δ; the supplied R, Q, zero census and δ remain numerical inputs.

Consequently the fixed-vector Arb certificates must not be used to upgrade the displayed envelope or its C thresholds to interval-certified complement statements. `ENVELOPE.md` makes that separation correctly. No cofinal conclusion or RH promotion follows from this finite implementation review.
