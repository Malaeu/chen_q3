# PEN 3.3 — G04 canonical object dictionary

Date: 2026-07-10

Gate: `G3_0_CanonicalObjectDictionary`

Verdict: `GREEN — OBJECT_DICTIONARY_LOCKED`

Exact H2 branch: `H2-POLE/CORRECTION`

Scope: supply-side Route B only; `NOT_RH`, `NOT_GATE6`, no detector theorem.

The next mathematical target is `ProjectedProlateDefectEquation`, with the
commutator and boundary source retained.  A homogeneous prolate ODE must not be
asserted for an already projected defect.

## 1. Authoritative conventions

Let \(\lambda>1\).  Use the Fourier transform

\[
  \mathcal Ff(y):=\int_{\mathbb R} f(x)e^{2\pi ixy}\,dx
\]

and the prolate operator

\[
  \operatorname{PW}_{\lambda}
  :=-\partial_x\!\left((\lambda^2-x^2)\partial_x\right)
    +(2\pi\lambda x)^2.
\]

The dimensionless prolate bandwidth is, exactly,

\[
  \boxed{C_\lambda=2\pi\lambda^2}.
\]

For \(n\ge 0\), start from

\[
  \widetilde h_{n,\lambda}(x)
  :=\operatorname{PS}_{n,0}\!\left(C_\lambda,\frac{x}{\lambda}\right),
  \qquad |x|<\lambda,
\]

extend it by zero outside \([-\lambda,\lambda]\), and let
\(h_{n,\lambda}\) be its \(L^2([-\lambda,\lambda],dx)\)-normalization.
For \(n=0,4\), fix the remaining real sign by

\[
  I_{n,\lambda}:=\int_{-\lambda}^{\lambda}h_{n,\lambda}(x)\,dx>0.
\]

This is the phase used by the high-precision Legendre constructor: its
constant Legendre coefficient, hence its integral, is positive.

The restricted Fourier eigenrelation is

\[
  \mathcal F(h_{2m,\lambda})(y)
  =\chi_m(\lambda)h_{2m,\lambda}(y),
  \qquad |y|\le\lambda,
\]

where \(\chi_m^2=\nu_m\) and \(\operatorname{sign}(\chi_m)=(-1)^m\).
Therefore the exact index dictionary is

\[
  \boxed{h_{0,\lambda}\longleftrightarrow\chi_0(\lambda)},
  \qquad
  \boxed{h_{4,\lambda}\longleftrightarrow\chi_2(\lambda)}.
\]

In particular, an \(h_4\leftrightarrow\chi_4\) label is an index error.
These conventions and the two indices are explicit in
[Connes, §§6.3–6.4](https://arxiv.org/html/2602.04022v1#S6.SS3).

## 2. Canonical time-side packet \(h_\lambda\)

Write

\[
  I_{0,\lambda}:=\int h_{0,\lambda},\qquad
  I_{4,\lambda}:=\int h_{4,\lambda},\qquad
  D_\lambda:=\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2}.
\]

The canonical two-mode packet is

\[
  \boxed{
  h_\lambda
  :=\frac{I_{4,\lambda}h_{0,\lambda}
           -I_{0,\lambda}h_{4,\lambda}}{D_\lambda}.}
\]

Since \(h_{0,\lambda}\) and \(h_{4,\lambda}\) are orthonormal,

\[
  \|h_\lambda\|_2=1,
  \qquad
  \int_{-\lambda}^{\lambda}h_\lambda(x)\,dx=0
\]

exactly.  The request-local constructors call this time-side object `g04`;
that implementation label must not be confused with the multiplicative-space
object \(g_\lambda\) defined below.  The coefficient row is implemented by
`normalize_real_combo([I4, -I0])` in
[`true_precision_packet_gate_v1.py`](../ACTIVE/requests/routeB_twolevel_spectral_ladder/true_precision_packet_gate_v1.py).

## 3. Midpoint extension and multiplicative packet \(g_\lambda\)

The zero extension has jumps at \(\pm\lambda\).  Its canonical point values
are the averages of the two one-sided limits:

\[
  h_\lambda^*(x):=
  \begin{cases}
    h_\lambda(x), & |x|<\lambda,\\
    \tfrac12h_\lambda(\lambda^-), & x=\lambda,\\
    \tfrac12h_\lambda(-\lambda^+), & x=-\lambda,\\
    0, & |x|>\lambda.
  \end{cases}
\]

Define the starred summation map and its restriction to the Weil window by

\[
  \mathcal E_*(f)(u):=u^{1/2}\sum_{m\ge1}f^*(mu),
  \qquad
  \boxed{g_\lambda:=\mathcal E_*(h_\lambda)
    \big|_{[\lambda^{-1},\lambda]}}.
\]

Connes' equation (20) calls this same unnormalized window function
\(k_\lambda\).  This dictionary reserves \(g_\lambda\) for the unnormalized
object and \(k_{1,\lambda}=s_\lambda g_\lambda\) for the normalized trial
vector, matching the request-local `k1` implementation name.

Only finitely many terms are nonzero at each \(u\) in this window.  If
\(M=\lambda^2\in\mathbb N\), the left edge is therefore

\[
  \boxed{
  g_\lambda(\lambda^{-1})
  =\lambda^{-1/2}
    \left(
      \sum_{m=1}^{M-1}h_\lambda(m/\lambda)
      +\frac12h_\lambda(\lambda^-)
    \right).}
\]

The same half-weight applies at every comb tooth \(u=\lambda/m\), not only
at the left edge.  A comb/boundary split must put the endpoint atom in exactly
one component and must not count it a second time.

Changing these finitely many point values does not change the
\(L^2(du/u)\) element, its Fourier coefficients, or its Weil quadratic-form
value.  It does change pointwise Poisson and boundary identities.  In
particular, the existing direct sums in
[`leakage_falsifier_v1.py`](../ACTIVE/requests/routeB_twolevel_spectral_ladder/leakage_falsifier_v1.py)
lines 337–345 and
[`split_identity_check_v1.py`](../ACTIVE/requests/routeB_twolevel_spectral_ladder/split_identity_check_v1.py)
lines 101–113 include the \(m=M\) endpoint with full weight.  Their pointwise
left-edge values are diagnostics under a noncanonical endpoint convention and
cannot certify the starred identity without a midpoint rerun.

## 4. Exact normalization and trial value

Let

\[
  \mathcal H_\lambda
  :=L^2([\lambda^{-1},\lambda],du/u),
  \qquad
  s_\lambda:=\|g_\lambda\|_{\mathcal H_\lambda}^{-1},
  \qquad
  k_{1,\lambda}:=s_\lambda g_\lambda.
\]

For the restriction \(QW_\lambda\) of the Weil quadratic form, define the
analytic trial value

\[
  \boxed{
  a_1(\lambda)
  :=QW_\lambda(k_{1,\lambda},k_{1,\lambda})
  =s_\lambda^2QW_\lambda(g_\lambda,g_\lambda).}
\]

This is a Rayleigh trial value.  The dictionary does not identify it with the
bottom of the spectrum.

The finite computation has an indispensable second parameter.  Put

\[
  L_\lambda:=2\log\lambda,
  \qquad
  V_{n,\lambda}(u)
  :=L_\lambda^{-1/2}
    \exp\!\left(\frac{2\pi i n\log(\lambda u)}{L_\lambda}\right),
\]

let \(P_{\lambda,N}\) be the orthogonal projection onto
\(\operatorname{span}\{V_{n,\lambda}:|n|\le N\}\), and define

\[
  \begin{aligned}
  g_{\lambda,N}&:=P_{\lambda,N}g_\lambda,\\
  s_{\lambda,N}&:=\|g_{\lambda,N}\|^{-1},\\
  k_{1,\lambda,N}&:=s_{\lambda,N}g_{\lambda,N},\\
  a_{1,\lambda,N}&:=s_{\lambda,N}^2
    QW_\lambda(g_{\lambda,N},g_{\lambda,N}).
  \end{aligned}
\]

Equivalently, if \(T_{\lambda,N}\) is the Weil matrix in this basis, then

\[
  a_{1,\lambda,N}
  =\langle k_{1,\lambda,N},T_{\lambda,N}k_{1,\lambda,N}\rangle.
\]

The basis and finite restriction are the objects in
[the local primary-source extract, §§3.1 and 5.1](../literature/zotero/H8ULBMAL/fulltext.md).
The lambda-only notation is permitted only after \(N\) has been fixed; the
current anchor is \(N=120\).

In `packet_truth_pull_v1.json`, the field `T0_T2_main.a1_raw` is this
normalized, pre-parity-projection value \(a_{1,\lambda,N}\).  The word `raw`
there does **not** mean the unnormalized value
\(QW_\lambda(g_{\lambda,N},g_{\lambda,N})\).

## 5. Exact H2 fork

At \(y=0\), the Fourier eigenrelations give

\[
  I_{0,\lambda}=\chi_0h_{0,\lambda}(0),
  \qquad
  I_{4,\lambda}=\chi_2h_{4,\lambda}(0).
\]

Consequently

\[
  \widehat h_\lambda(0)=\int h_\lambda=0,
\]

but

\[
  \boxed{
  h_\lambda(0)
  =\frac{(\chi_2-\chi_0)
          h_{0,\lambda}(0)h_{4,\lambda}(0)}{D_\lambda}.}
\]

The centers of the nonzero even prolate eigenfunctions cannot vanish: evenness
gives zero first derivative at the origin, and simultaneous zero value and
derivative would force the ODE solution to vanish identically.  Moreover
\(\nu_0>\nu_2>0\), while both relevant Fourier signs are positive.  Hence
\(\chi_0>\chi_2>0\).  With the phase convention above,

\[
  \boxed{h_\lambda(0)<0,\quad\text{in particular }h_\lambda(0)\ne0.}
\]

Thus the canonical two-mode object has the exact classification

```text
H2-INTEGRAL-ZERO:       PASS
H2-ZERO:                FAIL
H2-POLE/CORRECTION:     SELECTED
```

The corresponding Mellin-side correction recorded by the current left-edge
contract is

\[
  -\frac{h_\lambda(0)}{2}
   \frac{\lambda^{1/2-i\gamma}-\lambda^{-1/2+i\gamma}}
        {1/2-i\gamma}.
\]

It must be retained pole by pole with matched Fourier sign, midpoint weight,
and Mellin normalization.  The alternative is to replace the two-mode packet
by a new constructor satisfying one additional exact linear constraint; that
would be a different object dictionary.

The numeric `H2_HOLDS` in `leakage_falsifier_v1.json` used only the threshold
\(|h_\lambda(0)|\le10^{-8}\|g_\lambda\|\).  Its tiny nonzero result is
consistent with \(\chi_0-\chi_2\) being exponentially small, but it is not an
exact zero and is superseded by the algebraic classification above.

## 6. Fixed-cell no-fit check: \(\lambda^2=13\), \(N=120\)

This check uses the fixed cell, the fixed true-precision constructor, and the
fixed Weil matrix.  No constant is fitted and no asymptotic model is used.

Input artifacts:

| Artifact | SHA-256 |
| --- | --- |
| `out/portable_k_coeffs_lambda_sq_13_N_120.json` | `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88` |
| `out/packet_truth_pull_v1.json` | `19996fde610772145da7722d33fdf088f9d9b5cc0c485daabb8de49a5cfda304` |
| `out/lambda_sq_13_N_120.json` | `3c18c63faf3eff8ce0665acddb5a9f80d0e0bcd0bd8e38f60a55767a266c70c7` |
| `out/leakage_falsifier_v1.json` | `69fe0bf62bfab2172dd47cdffd6572acdd8fbd4a792a0237b5d1871097e4719e` |
| `out/split_identity_check_v1.json` | `1d8efd6ce740b6f958908e094c0a0355477e2af7c24e4e449393200947b08eaa` |

The persisted projection norm and its reciprocal are

\[
  \begin{aligned}
  \|g_{\lambda,120}\|
    &=0.4693475223537305706103998033443504037082982794475510777028854977\ldots,\\
  s_{\lambda,120}
    &=2.1306174047432927315374340328125784178801879489345264081923817691\ldots,\\
  s_{\lambda,120}^2
    &=4.5395305253950440767131973403811532757526718479627703218336031928\ldots.
  \end{aligned}
\]

The saved summary field `coeff_norm_after_normalization` is `1.0`.
Reconstructing the vector from its decimal coefficient serialization gives a
norm differing from one by about \(5.13\times10^{-91}\); this serialization
floor explains why the independent matrix comparison below certifies about 63
relative decimal places rather than all 191 working digits.  The 96/192
quadrature coefficient discrepancy is

\[
  3.7124408753414596\ldots\times10^{-36}.
\]

For the independent check, let \(c\) be the persisted normalized coefficient
vector and put \(d:=\|g_{\lambda,120}\|c\).  Rebuild
\(T_{\sqrt{13},120}\) from the fixed matrix formulas at `dps=191`, then compute
the unnormalized contraction directly, before applying \(s^2\):

```text
QW(g_{sqrt(13),120}) = d^* T d
  = 1.18359237929663490917992197824248294199739453696313339088818703595248e-59

s_{sqrt(13),120}^2 QW(g_{sqrt(13),120})
  = 5.37295373544202335868687414196622456333894394054268905623759843902656e-59

packet_truth_pull_v1.json:T0_T2_main.a1_raw
  = 5.37295373544202335868687414196622456333894394054268905623759844092845e-59

absolute difference = 1.90188862954e-122
relative difference = 3.53974503260e-64
verdict             = NO_FIT_NORMALIZATION_PASS
```

The rebuilt contraction does not derive its first line by multiplying the
saved `a1_raw` by the norm; it performs a fresh matrix-vector contraction.
The discrepancy is consistent with the persisted decimal coefficient precision.

The high-precision endpoint cache gives

\[
  h_\lambda(\lambda^-)
  =-8.9446729900892226424357567094911\ldots\times10^{-30}.
\]

A fresh `dps=110` constructor evaluation gives the full-endpoint left-edge sum
\(-1.63792282855308998\ldots\times10^{-29}\).  Its endpoint contribution is
\(-4.71062605267346158\ldots\times10^{-30}\), so the canonical midpoint value is

\[
  \boxed{
  g_\lambda(\lambda^{-1})
  =-1.40239152591941690\ldots\times10^{-29}.}
\]

This midpoint correction leaves the \(L^2\) normalization calculation
unchanged, but it invalidates promotion of the old full-endpoint pointwise
diagnostics to a starred Poisson certificate.

The older `out/lambda_sq_13_N_120.json:a1`
(`5.9933906766531484...e-28`) came from the early double-precision packet path
and is quarantined for this normalization check.  The true-precision
pre-parity value is

\[
  a_{1,\sqrt{13},120}
  =5.3729537354420233586868741419662\ldots\times10^{-59}.
\]

## 7. Gate closeout

```text
G3_0_CanonicalObjectDictionary:  GREEN
C_LAMBDA:                        2*pi*lambda^2
INDEX_LOCK:                      h0 <-> chi0; h4 <-> chi2
TIME_PACKET:                     exact normalized zero-integral h_lambda
MULTIPLICATIVE_PACKET:           g_lambda = E_*(h_lambda)|window
RAYLEIGH_NORMALIZATION:          a1 = s_lambda^2 QW_lambda(g_lambda,g_lambda)
FINITE_PARAMETER_DISCIPLINE:     lambda,N both explicit
H2_BRANCH:                       H2-POLE/CORRECTION
ENDPOINT_CONVENTION:             midpoint / half-weight
RH_STATUS:                       NOT_RH
NEXT:                            ProjectedProlateDefectEquation
```

Local semantic search was run for the object dictionary, index map,
normalization, H2 fork, and left-edge convention.  The new Route B terminology
was not recovered by the index with useful confidence; the lock above therefore
uses the primary Connes formulas, the local quadratic-form source, and the
request-local high-precision constructor rather than a reconstructed audit.
