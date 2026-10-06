# Odd secular sign for the prescribed two-column trial

Status: UNRESOLVED. No production review admission, eventual sign, negative
certificate, G1 closure, or RH claim. PX_RH_CLAIM: NOT_MADE.
Owner: current Codex chat on AC-WKS-067, branch rh_clean.
Source: 5ce1377cd5ad5b006dfa0cd67426ade38c6dfb57.
Request: REQ-2026-10-06-ODD-SECULAR-SOURCE-SIGN, user attachment
`/home/chirurgie/.codex/attachments/7bd3eeea-cfd5-4855-89b5-5673b48cb1f6/Eingefügter Text.txt`.
The byte-exact request is retained beside this note as
`ODD_SECULAR_REQUEST_2026-10-06.txt`.

## Binding and domain

Use exactly the request's U, from the window coefficients of the full G and
G'', not the selected Ferrers row or the true even ground state. The source
matrix is the general finite wrapper with N=m and L=log(m). The existing
`Goal058CurvatureBorderedSecular.lean:17-51` supplies the pole factorization.
Restriction to `(e_n-e_-n)/sqrt(2)` gives exactly the request's s and
Kminus=Aminus-2ss*. No prime or archimedean contribution is removed.

[SOURCE + elementary deduction; not independently reviewed here]
The domain is nonempty for every m>=2. For t>=0 and r>=1, x=r exp(t)>=1,
so 24*pi*x^2-16*pi^2*x^4<0. Hence G(t)<0. Source evenness gives G(t)<0
also for t<0. Thus c(G)_0<0. Both columns are even; U is well-defined on
their actual nonzero range. Eventual rank two follows from the projection
convergence and independence used in the pinned floor audit. No Gram
inverse is required to define U in a possible early rank-one cell.

## Exploratory observations

Native source-binding check `/root/locate_odd_packet` found all four request
blob IDs identical to the pinned Git tree. Root independently checked them
with `git ls-tree`. The request-copy SHA-256 is
`714cc4f765885b7aade851a371d927933c0fa68cc38d362eaa3ab14f2f057628`.
The initial `ask.sh` lookup returned INCOMPLETE (semantic-index freshness
failure); no claim of exhaustive absence is based on it.

These runs began before the actual attachment, including its prediction
requirement, arrived. They are exploratory, not retrospectively registered
predictions. They use the existing `full_center_probe.matrix_K` and
`gaussian_plane` at the pinned source. The latter approximates the infinite
theta sum and uses integration by parts for G'' coefficients. The plane
projector's two leading eigenvectors supply an orthonormal trial basis.

| m | decimal precision | U | min(Kminus)-U | min(M) | Psi |
|---|---:|---:|---:|---:|---:|
| 2 | 60 | 3.432564509e-3 | 1.222083603e-1 | 1.319517211e-1 | 9.253445597e-1 |
| 4 | 60 | 3.285021745e-8 | 2.705505369e-7 | 4.495392705e-4 | 9.128721474e-6 |
| 8 | 60 and 90 | 6.022171426e-15 | -5.988781607e-15 | 3.603836036e-13 | -1.491546899e-13 |
| 12 | 90 | 4.946679218e-21 | -4.946637753e-21 | -3.343593260e-21 | -8.923298473e-21 |
| 16 | 100 | 4.403979434e-25 | -4.403979433e-25 | -4.403902910e-25 | -4.732776564e-24 |

At m=8, the two precisions agree in the 20 displayed significant digits
of the original output. This checks numerical stability, not integration
or truncation error. At m=12 and 16, M is numerically indefinite, so the
positive-M interpretation of Psi cannot be used there.
The alternative odd trial plane diag(n)*range(V), corresponding up to a
common scalar to G',G''', has its minimum ABOVE U at m=8,12,16. It does not
explain the observed negative odd margin by itself.

Reproduction (existing environment, no file outputs by default):

```
.venv/bin/python docs/routeB_bus/source_observability_2026-09-28/odd_trial_probe.py --m 8 --dps 90
```

Saved BEFORE running the extracted script: prediction for its m=8,dps=90
replay is U in (6.02217e-15,6.02218e-15), min(M)>0 and Psi<0, with
Psi in (-1.49155e-13,-1.49154e-13). This is a replication prediction only,
not a blind source-sign forecast or a registered production review plan.

Replay outcome: the extracted script reproduced U=6.0221714258731687174e-15,
min(M)=3.6038360356286524502e-13 and Psi=-1.4915468990385281584e-13.
Projector residual was 1.33e-91 and endpoint parity residual 1.71e-90.
These are internal residuals, not quadrature error bounds. The three exact
rational scalar controls returned 3/4, 0 and -3; the diag(0,1) and
diag(-1,-1) strictness/determinant controls also passed. No source-sign
certificate follows from those abstract controls.

## What the observations do not establish

No interval error enclosure was computed. A negative floating-point value
is not the requested proved negative upper enclosure. A finite negative
certificate, even if obtained, would not refute existence of a later J(P).
None of these cells is asserted to be on the selected port's admitted tail.
The infinity of original cells has not been replaced by this table.

The requested eventual inequalities remain open. In particular, merely
knowing U tends to zero supplies no comparison with the odd bottom. A
successful proof must also explain why the observed unfavorable finite
ordering reverses eventually. No replacement of U was made.

## Two remaining representations and their discriminators

1. Full odd quadratic form: prove a source-dependent lower bound
   lambda_min(Kminus_m)>U_m on every sufficiently late original cell.
   Alternatively, a normalized odd y_m with certified
   y_m*(Kminus_m-U_m I)y_m<=0 on an unbounded subsequence would refute
   the requested eventual strictness. This representation avoids an
   ill-conditioned inverse, but needs uniform control of all odd directions
   for a positive result. A finite-cell enclosure tests the numerics only.
2. Pole-removed resolvent: first prove mu_m=lambda_min(Aminus_m-U_m I)>0;
   then bound the full scalar 2s*(Aminus_m-U_m I)^(-1)s strictly below 1.
   Cost is two signed estimates, including all source terms. A certified
   nonpositive mu_m or Psi_m at unbounded m is a negative discriminator;
   an interval meeting zero is inconclusive. On cells with M positive,
   solve Mx=s with a certified residual to bound the scalar error using
   |s*(M^-1 s-x)| <= ||s|| ||s-Mx|| / mu_m. A small residual without a
   certified positive mu_m does not establish the sign.

Neither representation currently has the required cofinal estimate.

## Additional exact candidate, not a signed estimate

The bounded read-only mathematical worker `/root/odd_sign_analysis` supplied
the following source-level deduction, checked algebraically by root against
the pinned audit. With omega_n=2*pi*n/L, integration by parts gives
c(G')_n=i*omega_n*c(G)_n and c(G''')_n=i*omega_n*c(G'')_n; the endpoint
terms cancel by evenness of G and G''. This explains exactly the odd trial
plane tested above.

Let H=G'''-G'/4. Its transform is
Hhat(z)=-i*z*(z^2+1/4)*Ghat(z). It vanishes at every zeta zero used in
the explicit formula and at both pole points +/-i/2. The same rapid-decay
extension as in the pinned audit therefore gives W(H,f)=0 and W02(H,f)=0,
hence (-WR-Prime)(H,f)=0 for finite-window tests f. This is a continuous
form radical, not an exact null vector of a finite section. It explains a
possible source of small pole-removed odd energies, but supplies no signed
comparison of the projected H energy with U. The two-column derivative
test above in fact fails to give a negative witness on the sampled cells.

Next mathematical step: find a cofinal odd witness or a signed source
asymptotic that reverses this finite ordering; another determinant identity
does not supply it. No Lean work, external dispatch, or route promotion.
