# Odd secular sign for the prescribed two-column trial

Status: EVENTUAL SIGN UNRESOLVED. A strict finite m=8 counterexample to
separation by this trial is certified below. No eventual counterexample, G1
closure, or RH claim. PX_RH_CLAIM: NOT_MADE.
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

The exploratory table alone has no interval error enclosure. The later m=8
certificate below supplies one finite strict comparison. It does not refute
existence of a later J(P).
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

## Continuation: exact coefficient decomposition

The owner requested continued work with Proshka. The previous paragraph's
no-dispatch statement describes the first checkpoint only; the continuation
question and answer are to be retained together after the answer arrives.

For b=L/2 and omega_n=2*pi*n/L, repeated integration by parts gives

```
c_n(G^(2k)) = (-omega_n^2)^k c_n(G)
  + (2/sqrt(L)) sum_{ell=1}^k (-omega_n^2)^(k-ell) G^(2ell-1)(b),
c_n(G^(2k+1)) = i*omega_n*c_n(G^(2k)).
```

The first boundary term vanishes for even derivatives and contributes
2G^(2k-1)(b)/sqrt(L) for the next even derivative. This retains the original
Fourier phase and both endpoints; no derivative of a merely C0 limit is used.

For each FIXED r, differentiating the explicit theta series gives
G^(r)(b)=O_r(m^(r+9/4) exp(-pi*m)) and
integral_b^infinity |G^(r)(t)|dt=O_r(m^(r+5/4) exp(-pi*m)).
Indeed each summand is exp(t/2) times a polynomial of degree r+2 in
z=pi*l^2*exp(2t), times exp(-z); on t>=b, the l=1 term dominates a
uniformly convergent Gaussian tail. Substitution z=pi*l^2*exp(2t) in the
integral removes one power of m. A further integration by parts in the
exterior Fourier integral gives

```
sum_{|n|>m} |L^(-1/2) integral_{|t|>b} G^(r)(t)e^(-i omega_n t)dt|^2
  = O_r(L*m^(2r+7/2)*exp(-2*pi*m)).
```

The whole-line coefficient is exactly
(-1)^n/sqrt(L)*(i*omega_n)^r*(-4*xi(1/2-i*omega_n)).
Stirling and a polynomial vertical-line bound for zeta give its squared
omitted-coefficient tail an upper bound of the form
poly_r(m/log(m))*exp(-pi^2*m/log(m)). Constants depend on the fixed order;
this is not uniform for an order growing with m.

These are upper envelopes, NOT a comparison of actual energies. An upper
envelope larger than the endpoint bound does not prove actual Mellin-tail
dominance. To get the requested sign one still needs a lower bound for the
optimized samples (a-b*omega_n^2)*xi(1/2-i*omega_n) and a signed transfer
from those samples to the full Weil quadratic form. Neither is supplied.
The bounded native worker `/root/odd_sign_analysis` returned this decomposition;
root checked the boundary recurrence and exponents. No node status changed.

## Strength of the eventual target: a conditional density consequence

This paragraph is a local deduction, not an RH equivalence claim. The NEW
trial U tends to zero: use (S) of the pinned floor-kill attachment,
sup_{unit w in range(V_m)} ||K_m w|| <= epsilon_m -> 0. Cauchy-Schwarz
then bounds every Rayleigh value in this same plane in absolute value by
epsilon_m, including its minimum U_m. This argument does not identify U_m
with the different quantity called U in the old complement-floor statement.

For a fixed real odd f in C_c^infinity, eventually its support is strictly
inside I_L. Let p_m be its projection onto the actual modes |n|<=m, extended
by zero. Its coefficients are (-1)^n*fhat(2*pi*n/L)/sqrt(L), and they are
odd. Write e_m=f-p_m and Omega_m=2*pi*m/L. Schwartz decay and Fourier
Parseval give, for arbitrarily large fixed q,

```
||e_m||_2 = O_q(Omega_m^(1/2-q)),
||e_m'||_{L2(I_L)} = O_q(Omega_m^(3/2-q)),
||e_m||_{infinity,I_L} = O_q(Omega_m^(1-q)).
```

For 0<h<=1, zero extension at the two edges gives
||e_m(.+h)-e_m||_2 <= h||e_m'||_2+C*sqrt(h)||e_m||_infinity.
Thus e_m tends to zero in X=A+D, where A(f)=||exp(|t|)f||_2 and
D(f)=sup_{0<h<=1}h^(-1/4)||f(.+h)-f||_2: indeed
A(e_m)<=sqrt(m)||e_m||_2 ->0 after choosing q large enough.
The complete-form continuity estimate (11) in
`../proshka/PROSHKA_VERDICT_GOAL058_FIRST_OMITTED_COMPRESSION_2026-09-26.md`
then gives W(p_m,p_m)->W(f,f), with every pole, prime-power and archimedean
term retained. The original matrix crosswalk gives
W(p_m,p_m)=x_m* Kminus_m x_m, and ||x_m||_2->||f||_2.

Consequently, IF the requested Kminus_m>U_m I holds on the original
cofinal tail, THEN W(f,f)>=0 for every such compact smooth odd f. Strictness
is lost in the limit. The same statement for complex odd tests follows by
splitting into real and imaginary parts of the real symmetric form.
Conversely, a negative compact odd test would refute the requested eventual
inequality by this projection argument. No such test is constructed here.

## Strict finite certificate: m=N=8

`odd_m8_certificate.py` uses the existing python-flint/Arb environment and
unchanged `../fokas_k_sign_2026-09-25/arb_m2_certificate.py` integration
implementation. It retains the full archimedean term, all prime powers,
pole term, infinite theta-tail enclosures, phase, and prescribed trial plane.
`odd_m8_certificate.json` contains the exact rational odd witness and all
intervals. Its approximate eigenvector is used only to select a rational
vector; the final inequality is evaluated with that exact rational vector.

Certified enclosures (rounded outward here):

```
6.02217142587316871739e-15 < U_8 < 6.02217142587316871741e-15,
3.33898190666647286812e-17 < R_odd < 3.33898190666647286813e-17,
U_8 - R_odd > 5.9887816068065039887e-15 > 0.
```

Thus the requested strict comparison fails at m=8. No assertion is made
that m=8 lies in a port's admitted tail. Neither eventual positivity nor
its cofinal negation follows. This certificate does not separately certify
M_8 positive or Psi_8 negative; its exact odd witness suffices to disprove
their conjunction at this single cell.

The 2-by-2 generalized minimum uses the stable smaller-root formula
2 det(H)/(T+sqrt(T^2-4 det(B) det(H))), where B is the column Gram matrix
and T=H00 B11+H11 B00-2 H01 B01. Required positivity and rank conditions
are enclosed. The theta majorants follow from y^k exp(-y)<=k!:
48*1!+64*2!=176<304 and 120*1!+480*2!+256*3!=2616<8952.

Root independently reran `certify()` successfully. Native independent
review `/root/odd_m8_review` also reran it and obtained byte-identical JSON
before the label-only correction. One on-target pass found no substantive
findings: only WORDING, two Gram keys named Gprime actually meant Gsecond.
Those keys and the endpoint derivative-tail label were clarified without
changing arithmetic or interval values. Reviewed pre-label SHA-256:
py `2fd602ddb0b7337da60453eae2d10296fcb5c2d68edba66faf85b7c2e19dcc24`;
json `4125d24e7c921c71a60d43a82c115a511f1a7173ca011e76f45a6d6a980eda76`.

Reproduce: `.venv/bin/python docs/routeB_bus/source_observability_2026-09-28/odd_m8_certificate.py`.

## Odd radical tower: small singular scales, not the required sign

[PAPER deduction; no node promotion.] The initial Luna sign attempt lacked
lower bounds and was escalated to `/root/odd_tail_escalation`. Its first
claim that even projection estimates extend verbatim to odd functions was
rejected by root: odd functions have opposite endpoint values. The corrected
argument below retains the boundary term. Root checked it against the full
mixed-form table and exterior bound in
`../proshka/PROSHKA_ATTACHMENT_GOAL058_INDEPENDENT_COMPLEMENT_FLOOR_2026-09-25.md`,
sections 4.2--4.3 (lines 219--288), not just an energy estimate.

Set H_r=D^(2r)(G'''-G'/4), for fixed r>=0. Its Fourier multiplier is a
nonzero polynomial times xi, vanishes at every zero and both pole points.
Thus W(H_r,f)=W02(H_r,f)=0 by the same rapid-cutoff extension as the source
audit. This extends the audited argument to fixed odd derivatives: weighted
smooth cutoff errors retain Gaussian decay and the extra fixed polynomial
Fourier multiplier is absorbed by the rapid decay in the zero sum. For
real h=H_r (and also h=h_m below), with z_rho=i*(rho-1/2),
conj(hhat(z_rho))=hhat(-conj(z_rho))=hhat(z_conj(rho))=0, since the
zeta zero set is closed under conjugation. The factor z^2+1/4 kills
both pole values. Thus the conjugated first slot retains its zero factor.
These functions are linearly independent: a polynomial relation would multiply
the nonidentically-zero entire function Ghat by a zero polynomial. No RH
hypothesis is used.

For any fixed derivative g, write b=L/2, p=Pi_m(g|I_L), e=p-g|I_L,
Delta_k=g^(k)(b)-g^(k)(-b). Repeated integration by parts gives, for n!=0,

```
|c_n(g)| <= sum_{k=0}^{q-1} |Delta_k|/(sqrt(L)*|omega_n|^(k+1))
             + ||g^(q)||_1/(sqrt(L)*|omega_n|^q).
c_n(g') = i*omega_n*c_n(g) + Delta_0/sqrt(L).
e' = -(I-Pi_m)g' - (Delta_0/sqrt(L))*sum_{|n|<=m} psi_n.
```

Every fixed Delta_k is polynomial(m)*exp(-pi*m); every fixed derivative
is integrable. In particular, the odd 1/n coefficient tail is retained,
and the derivative has a Dirichlet-kernel correction of norm
|Delta_0|*sqrt((2m+1)/L). For odd g, p(+/-b)=0 exactly, so the sum of
endpoint errors D_e is 2|g(b)|. For even g, the first boundary term vanishes;
absolute summation of the remaining coefficient tails bounds D_e. Choosing
q sufficiently large proves, for each fixed R,

```
||e||_2 + ||e'||_{L2(I_L)} + D_e = O_{g,R}(m^(-R)).
```

This statement concerns the interior derivative, not a global H1 derivative
of the zero extension. Constants are not uniform in growing derivative order.
The source's full mixed-form estimate, valid for every unit finite test f,
is explicitly

```
|W(e-t,f)| <= (2+4L)*sqrt(m)*||e||_2 + 26*||e'||_2
              +26*D_e*sqrt(3m/L) + tau_g(m),
t=g*1_{I_L^c},
tau_g=2*m^(1/4)*A_g +2*sqrt(m)*S_Lambda*T_g
       +26*||g'*1_{I_L^c}||_2
       +26*(|g(-b)|+|g(b)|)*sqrt(3m/L).
```

Here A_g, T_g and S_Lambda are precisely those of source (T); tau_g is
polynomial(m)*exp(-pi*m) for each fixed g. The polynomial Fourier remainder
contributes at most C_q*(1+L)*L^(q-1/2)*m^(1-q) to the odd interior norm
bound, with harmless additional polynomial factors for even endpoint values.
All fixed powers can be absorbed by choosing q larger. Taking the supremum
over unit f proves operator residuals, not only small Rayleigh values.
The W02-only error is bounded by 2*sqrt(m)*||e||_2+2*m^(1/4)*A_g.
Using both continuous radical identities therefore gives

```
||Aminus_m c(H_r)||_2 = O_{r,R}(m^(-R)),
||K_m c(G)||_2 + ||K_m c(G'')||_2 = O_R(m^(-R)).
```

The odd coefficient vector in this display is expressed in the normalized
odd basis (an isometry). The Gram matrices of any fixed finite independent
set converge to their positive continuous Gram matrices. Hence
|U_m|=O_R(m^(-R)), and for each fixed d and R the first d projected H_r span
a d-dimensional odd subspace S_m with ||M_m y||<=C_{d,R}m^(-R)||y||.
Consequently at least d eigenvalues of M_m lie in
[-C_{d,R}m^(-R),C_{d,R}m^(-R)]. Otherwise S_m intersects the orthogonal
complement of that spectral interval, where the norm of M_m on every
nonzero vector exceeds this bound, a contradiction. No positivity is assumed.

If M_m is eventually positive definite, its inverse norm therefore grows
faster than every fixed power of m. A polynomial upper bound on the full
inverse cannot supply the proposed proof. This does not decide the sign,
does not control the inverse specifically along s_m, and does not exclude
an accurate source-aligned estimate for s_m* M_m^(-1) s_m. The exact missing
step remains a signed comparison at a scale below all fixed powers.

## Proshka continuation question (exact sent text)

Sent in the existing `Missing T7 Lemma` chat, mathematical question 2/10,
2026-10-06 approximately 09:29 UTC. UI confirmed both attachments and a
running response after the send click timed out; no resend was performed.
Chat: https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6aba5f5a-f804-83ed-a667-68147ee00f59
Attachments: byte-exact `ODD_SECULAR_REQUEST_2026-10-06.txt` and this note's
committed c256c651 version (before the continuation sections above).

```text
Continue the mathematical work on G1, not the explanation of the conditional Schur criterion. The owner has explicitly authorized Codex and Proshka to work together on this exact target. In docs/Codex/NEXT.md, owner plain-mode rules dated 2026-09-28 make a Proshka question a working message without review-plan/intent/dispatch bureaucracy. This is not a claim of formal production admission.

The first attachment is your byte-exact proposed request REQ-2026-10-06-ODD-SECULAR-SOURCE-SIGN, SHA256 714cc4f765885b7aade851a371d927933c0fa68cc38d362eaa3ab14f2f057628. All four source blobs were checked and match 5ce1377cd5ad5b006dfa0cd67426ade38c6dfb57. The second attachment is Codex's actual attempt and limitations, now committed at c256c6510e10a218dc65b68a7e373f246893ff55 in Malaeu/chen_q3 branch rh_clean. No request has been sent twice.

We must retain exactly U_m=min Rayleigh on span{c_m(G),c_m(G'')}, L=log m, N=m, and the original cofinal schedule. Domain is nonzero and even. Root used full_center_probe.matrix_K and gaussian_plane, retaining all source terms. Observations (floating-point only, NOT certified intervals):
m=8, at 60 and 90 decimal digits: U=6.0221714258731687174e-15; lambda_min(Kminus)-U=-5.9887816068065039887e-15; lambda_min(M)=3.6038360356286524502e-13; Psi=-1.4915468990385281584e-13.
m=12,90 digits: U=4.946679218227e-21; odd-minus-U=-4.946637753088e-21; min(M)=-3.343593260352e-21.
m=16,100 digits: U=4.403979433730e-25; odd-minus-U=-4.403979433045e-25; min(M)=-4.403902910300e-25.
Thus the candidate is unfavorable on these finite cells. This does not refute eventual positivity. The scalar controls including zero passed. We did NOT replace U with the actual even ground level.

Own analytical attempt: c(G')=i diag(2pi n/L)c(G), c(G''')=i diag(2pi n/L)c(G'') exactly by parity and integration by parts. The derivative odd plane has minimum ABOVE U on these cells, so it is not the observed low witness. H=G'''-G'/4 has Hhat=-iz(z^2+1/4)Ghat, vanishes at the zero points and both pole points; the audit's rapidly decreasing cutoff argument suggests A(H,f)=0 in the full continuous form. This gives no signed bound for its finite projection relative to U.

Please attack the actual asymptotic discriminator now. Either prove both M_m positive definite and Psi(U_m)>0 eventually on the original tail, OR prove a cofinal negative/nonpositive witness for this precise two-column trial candidate. A useful direction is compare the leakage of this fixed even plane with odd directions from the higher derivative radical tower. Determine which dominates: window endpoint leakage or omitted Fourier modes at omega~2pi m/log m; preserve prime powers and archimedean terms. Can a fixed finite odd derivative combination, or an explicit growing-dimensional construction, yield a certified asymptotic Rayleigh upper bound smaller than a certified lower bound for U_m?

If the claim remains unresolved, return the first concrete new source estimate you can actually prove and the exact remaining inequality, not another determinant identity or a finite-table extrapolation. A proved failure of this U will change our next candidate; it does not kill parity ordering or RH. No G3 promotion, no RH claim. Answer with a self-contained derivation that Codex can check. Do not modify the repo; we will integrate the answer with our calculations after checking it.
```

## Proshka answer and root mathematical check

The answer completed after 32m09s and was observed complete on 2026-10-06.
Exact inline text was saved through `read_thread` as
`PROSHKA_ODD_LEAKAGE_INLINE_2026-10-06.md` (16,369 characters).
The additional attachment was read in the browser preview, including its
TeX annotations; its extra constants and unsimplified error budgets are
transcribed in `PROSHKA_ODD_LEAKAGE_BUDGETS_2026-10-06.md`. Download events
timed out, so the transcription is not represented as byte-exact attachment
capture. Source chat turn: `90a8c340-648a-4f57-a3f5-e6dbaf9429c7`.
The prior attachment's PREPARED_NOT_REGISTERED metadata was not rewritten.

Proshka's new construction is h_m=H*eta_m, where eta_m is the r-fold
convolution of the uniform probability density on [-delta/r,delta/r],
delta=(log L)/4 and r=floor(delta*Omega/e), Omega=2*pi*m/L. Its support
is [-delta,delta], but variance delta^2/(3r) tends to zero. Thus h_m tends
to nonzero H in L2, remains odd, and retains every radical zero. Its
Fourier multiplier sinc(delta*omega/r)^r is bounded by exp(-r) for
|omega|>=Omega. No uncontrolled growing derivative constants are used.

Root checked the following steps directly:
- Substitution u=q*exp(t) in the full theta sum gives the shifted-line
  L1 bound 48*cos(2b)^(-5/2). The contour shift b=pi/4-1/|omega| yields
  |Ghat(omega)|<=48*e*(pi/4)^(5/2)*|omega|^(5/2)*exp(-pi|omega|/4).
- The finite polynomial recurrence for fixed physical derivatives and
  the maximum of v^(ell+1/4)*exp(-v/2) give the stated D[R] envelope.
- Exterior integration by parts gives the 1/omega remainder for odd h,
  and 1/omega^2 for even h'. The derivative's retained-mode contribution
  is exactly 4(2m+1)|h(a)|^2/L. All its terms are present in P_1.
- Odd projection vanishes at both endpoints. Thus the WHOLE-LINE error
  f_m-h_m is in H1. This differs from the interior zero-extended error in
  the earlier mixed-form argument; no boundary jump is silently removed.
- The grouped archimedean constant is gamma+log(8*pi)+pi/2, since
  2 integral_0^infinity (exp(x/2)-1)/(exp(x)-exp(-x)) dx=log2+pi/2.
  The complete prime-power contribution is bounded using weighted
  Cauchy-Schwarz, and the two pole moments each have squared norm 4/3.
- The frequency-cell sum, weighted exterior integral, positive eventual
  normalization d_m, and exponents in B_m retain the original lattice.
- The full matrix's coarse polynomial norm and the positive limiting
  two-column Gram matrix give the stated window comparison Gamma_m.
  This comparison does not replace the prescribed U_m.

The resulting auxiliary PAPER bound is

```
max(|y_m* Kminus_m y_m|, |y_m* Aminus_m y_m|) <= B_m,
B_m <= C_H [m*Omega^11*exp(-pi*Omega/2-2r)
                       +L*exp(-pi*m/sqrt(L))],
exp(C*m/L)*B_m -> 0 for every fixed C>0.
```

This applies to every sufficiently large integer m and hence to the
original schedule. It is an absolute Rayleigh upper envelope, not an
operator residual, not positivity, and not a negative shifted witness yet.

### Attempt on the remaining lower comparison

The exact cancellation W(g,f)=0 for g in span{G,G''} rewrites its projected
energy as W(e,e), where e is the whole-line projection error. For real even
g, e is real even and the pole term is 2*(integral e(t)exp(t/2)dt)^2>=0.
Grouping the full archimedean term therefore gives the valid lower bound

```
W(e,e) >= D(e) - c_ar*||e||_2^2
                    -2*sum_{n>=2} Lambda(n)/sqrt(n)*|C_e(log n)|,
C_e(x)=integral e(t)e(t+x)dt.
```

The weighted absolute estimate pays the last term by 10*||exp(|t|)e||_2^2.
It does not supply a strictly positive lower bound: no inequality showing
D(e) dominates this complete budget uniformly over the two coefficient
parameters has been established. The physical window also means that the
error is not a whole-line high-pass function; a lower spectral multiplier
bound at |omega|>=Omega cannot simply be applied to it. This is the first
failed lower step in this attempt. A lower L2 bound on omitted samples
would not repair that signed-form gap by itself.

Thus no constants c,C_0>0 with U_m>=c*exp(-C_0*m/L) on an unbounded original
sequence have been proved. Nor has the weaker direct U_m>B_m been proved.
If either were proved, the explicit y_m would refute this U_m already at
M_m>0. Conversely success of the requested eventual comparison would force
(U_m)_+<=B_m eventually. Both are conditional statements. G1 and the
requested eventual pair remain OPEN; no RH claim is made.


### Independent analytical review and final checkpoint

Native read-only review `/root/odd_m8_review`, pass 2, checked the odd radical
tower and Proshka convolution construction against the source. No CRITICAL,
HIGH or MEDIUM findings. One LOW finding requested the explicit conjugation
identity for the first sesquilinear slot; the identity above was added and
checked by root using -conj(z_rho)=z_conj(rho). This is a local exposition
repair with no change to the estimates. The reviewer explicitly confirmed
the complex mixed-form supremum, discrete Fourier tail, endpoint correction,
complete prime-power budget and B_m rate. The finite pass 1 WORDING finding
was also fixed; reversing only the label replacements reproduces both
reviewed SHA-256 values exactly. Python syntax and JSON parsing passed.
Root's exact rational polynomial recurrence independently reproduced
H's polynomial 128v^5-1440v^4+4224v^3-3240v^2+360v.

All local workers and the Proshka response are complete. No ongoing job or
monitor remains for this question. Current mathematical result: finite m=8
failure certified; auxiliary cofinal odd upper bound checked; the signed
lower comparison and the originally requested eventual positive pair remain
OPEN. No Lean build was run or needed for these PAPER and Arb checks.
The two unrelated preexisting untracked files were left unchanged.

## Bounded alias-hunt: Gårding does not supply the unshifted sign

Researcher `/root/signed_source_hunt` fetched the primary paper
L. Gårding, "Dirichlet's problem for linear elliptic partial differential
equations" (1953), DOI https://doi.org/10.7146/math.scand.a-10364.
Local source: `docs/literature/garding_dirichlet_elliptic_forms_1953.pdf`;
SHA-256 `16ff729b8584ed629b62dcbcb0e561e6329a03cf114a072094480d0e72731975`.
Root independently checked this hash and rendered/read printed pp. 60-61.

Theorem 2.1 (p. 61): "If p(f,f) is any Dirichlet integral belonging to p
then" `inf_{f in H} p(f,f)/(f,f) > -infinity`.
Section 2 (p. 60) assumes a real homogeneous principal polynomial of degree
2m, smooth uniformly continuous coefficients, and a uniformly positive
lower bound on the unit sphere. The domain H consists of smooth compactly
supported tests in S (p. 56). This is semiboundedness, not positivity of the
unshifted form. The theorem itself permits a negative lower bound.

Mapping attempted: its test f would be our full projection error e;
its p(f,f) would have to be the complete W(e,e), including prime translates.
These hypotheses are not supplied: W is nonlocal, the window grows, and e
retains a nonzero exterior source tail. Window Fourier orthogonality does
not make e a whole-line high-pass test. Thus the original theorem is an
EXCLUDED DIRECT BRIDGE, not a refutation of the desired U bound and not
an exclusion of every modern Gårding variant.

Negative control for the broader shortcut "positive principal symbol
implies positive energy": on (0,1),
`Q(u)=integral(|u'|^2-2*pi^2*|u|^2)` has positive principal symbol, while
smooth compactly supported approximations to sin(pi*x) have negative Q.
This is not a counterexample to the quoted semiboundedness theorem.

The first unpaid source estimate is still the joint archimedean/finite-prime
comparison, uniformly in both trial coefficients. The earlier
`PROSHKA_VERDICT_GOAL058_LOG_SYMBOL_TRANSFER_2026-09-26.md`, (17)-(22),
already isolates the derivative diagonal and gives its exact divisor
collapse; it does not supply this two-column signed lower bound.

## Signed-lower continuation question (3/10)

Exact text of the existing chat message `1eb8f937-da28-4fda-aa72-03c10bd981a0`,
sent on 2026-10-06. The message is present in the chat; no duplicate was sent.
The earlier browser showed an interrupted connection; on continuation the
connector returned the completed final answer. Its verbatim inline text is
saved in PROSHKA_SIGNED_EVEN_TAIL_INLINE_2026-10-06.md. Independent checks
of the new periodization, mass and exterior-error claims are in progress.
The signed prime comparison is explicitly left open in the answer.

```text
Continue G1 on the exact source and unchanged two-column U_m. The owner has now set an explicit continuing goal to close RH together, using all project work, alias-hunt and verified literature. This does not authorize assuming RH or promoting partial estimates. Your previous answer has been checked and integrated at fc0b25a887feea95a4c7ee2191661184be0a53c7 in Malaeu/chen_q3, branch rh_clean. Root and native independent review accepted the auxiliary convolution envelope, with explicit conjugation of the first slot added: conjugate(hhat(z_rho))=hhat(-conjugate(z_rho))=hhat(z_conjugate(rho))=0. We also rigorously certified finite m=8 using Arb: U8=6.02217142587316871739809e-15, exact rational odd Rayleigh=3.33898190666647286812302e-17. This is not eventual evidence.

Please now attack the remaining actual SIGNED lower comparison in your equations (31)-(33), not rederive your odd construction. Preserve N=m,L=log m, the full K and original schedule; U_m remains min Rayleigh span{c_m(G),c_m(G'')}. Your explicit odd envelope B_m satisfies exp(Cm/log m)B_m ->0 for every fixed C; |U_m-U_tilde_m|<=Gamma_m=C_G m^(3/2)sqrt(log m) exp(-pi m/2).

Our bounded own attempt: for real even g=aG+bG'', whole-line projection error e=Pi_m(g|I)-g, radical cancellation gives W(Pi g,Pi g)=W(e,e). The even pole contribution is nonnegative. Grouping the full archimedean term yields W(e,e)>=D(e)-c_ar||e||²-2 sum_{n>=2}Lambda(n)/sqrt(n)*|C_e(log n)|. Paying the last sum by 10||exp(|t|)e||² fails: there is no established domination by D(e). Also e is NOT a whole-line high-pass function, so a high-frequency multiplier lower bound cannot simply be applied. This is the exact obstruction; lower Fourier L2 mass alone is not signed energy. The generalized Gram metric must be retained uniformly in (a,b).

Find a source-specific cancellation/oscillation estimate for this two-column error family proving U_tilde_m>B_m+Gamma_m on an unbounded original sequence, or a different genuinely signed estimate settling the prescribed candidate. Test alternate representations such as the explicit zero sum (retaining off-line paired terms), arithmetic-translation correlations, boundary layer of the analytic Fourier tail, or a valid Garding/oscillation theorem with its hypotheses proved for this source. We are running alias-hunt in parallel. Do not infer sign from residual smallness, finite numerics, generic displacement rank, or a positive model with unpaid correction. If the lower route is genuinely false, give a source counterargument; if it remains open, derive a new concrete paid reduction and identify its first missing inequality. No repository writes. Plain-mode working question, not another request-registration cycle.
```


## Answer 3/10: independent check of auxiliary even-tail estimates

The completed inline response and downloaded supplemental Markdown are saved
as `PROSHKA_SIGNED_EVEN_TAIL_INLINE_2026-10-06.md` and
`PROSHKA_G1_SIGNED_EVEN_TAIL_REDUCTION_2026-10-06.md` in this directory.
The supplement SHA-256 is
`e4f7b1542f11a75136597e20fba8e5ab97d38ccaa4d060120ce2da1ba2b91177`.
It explicitly leaves its signed inequalities (6.1)/(6.2) open.

Native read-only check `/root/even_tail_identity_check` independently derived
the even periodization identity, archimedean constant, exterior budget and
boundary-prime identity. It found no mathematical defect in these estimates,
conditional on the previously checked source envelopes/radical crosswalk.
One exposition clarification: throughout use
`C_vw(s)=integral conjugate(v(t))*w(t+s) dt`; evenness makes C_vv real.
The author text is preserved unchanged.

Root independently reread CCM (3.5)-(3.11) in
`../litreview/pdfs/survey_2026-09-03_sources/ccm.txt:245-308`:
`W=W_02-W_R-Prime`, `W_R=-W_infinity`, and
`theta'(omega)=(a(omega)-c_ar)/2`. Thus the archimedean contribution is
exactly `D-c_ar*||v||²`, with `c_ar=gamma+log(8*pi)+pi/2`.
The image correction is positive for even functions and negative for odd
ones; it is not transferred to the atomic prime kernel.

Root also checked the Gram determinant `34/45`, trace `36/5` and lower
constant `17/162` by exact rational arithmetic. Differentiating
`2*omega²/[beta*(beta²+omega²)]` proves monotonic decrease in beta;
integration over beta>=1/2 with lattice spacing 2 gives
`a(omega)>=log(1+4*omega²)/2`. Direct 40-digit quadrature for cosine/sine
on [-pi,pi], beta=1/2,5/2, agrees with the image formula within 1e-40
(diagnostic algebra check, not a source-family certificate). The reflected
cosine prime control is exactly `-L/4=-log(2)/2` at L=log(4).

The exterior estimate retains both jumps and all prime powers. Short
translations are bounded by the piecewise derivative plus two boundary
strips, long translations by the norm. Since r and o have disjoint support,
the ordinary norm cross term vanishes; D's cross term is paid by Cauchy,
and weighted prime/pole bounds pay the remaining terms. The resulting
`R_m=O_G(m exp(-pi*m/2))` is negligible relative to the proposed mass
scale. None of this supplies the remaining signed prime comparison.


### A sharper necessary arithmetic condition for the prescribed candidate

Keep the supplement's E,P,A,H,G,mu,R,kappa and the accepted odd envelope B,
on the same original cofinal sequence. On the eventual rank-two family,
define `lambda_m=lambda_max(E_m^(-1/2) P_m E_m^(-1/2))` and
`d_m=kappa_m-lambda_m`. These are arithmetic-tail quantities, not the
previous convolution normalization also called d_m in the predecessor.
Here `E>=mu I`, `G<=C0 I`, `A>=kappa E`, and
`H>=A-P-R I>=d_m E-R I`.

If d_m>0 and d_m*mu_m>R_m, it follows that
`U_m >= (d_m*mu_m-R_m)/C0`.
Consequently `d_m*mu_m>R_m+C0*B_m` supplies an odd witness below U_m.
This keeps the generalized Gram metric and does not require the arbitrary
constant margin 1 in the author's stronger inequality (33).

Conversely the requested `M_m=A_m^- -U_m I>0` implies `U_m<B_m` by testing
its normalized odd envelope vector. Choose a generalized U-minimizer z.
If d_m>0, then
`d_m*mu_m*||z||² <= z*H_m*z+R_m||z||²
 < (B_m*C0+R_m)||z||²`.
This uses U<B and B>=0, not an assumption U>=0. If d_m<=0 the same upper
bound on d_m is automatic. Thus eventual M>0 requires

`d_m <= (C0*B_m+R_m)/mu_m -> 0`,

and in particular `limsup d_m<=0` along the original sequence.
A strictly positive limsup d_m would refute the prescribed candidate,
not RH or every possible even trial. No sign or limsup for d_m has been
proved here; dropping positive image/pole terms can make this discriminator
inconclusive. Native independent checker `/root/even_tail_identity_check`
verified this deduction, its minimizer direction, and the same-sequence
quantifiers. No source-node status changes.


### Primary-source and sampling check

Native researcher `/root/hardy_sampling_check` checked the unconditional
Hardy moments, weighted two-column reduction, gamma factor and actual
window error. Primary source: Bui--Hall, *On the derivatives of Hardy's
function Z(t)*, arXiv:2304.05178v1, equation (1), p.1.
URL: https://arxiv.org/pdf/2304.05178v1 . Saved source:
`docs/literature/bui_hall_hardy_derivatives_2304.05178v1.pdf`, SHA-256
`1dc6faff2be07aa4a9f55f0666679df7087c3b8d874972032b7bbdad0c3a7b14`.
Root independently read p.1 and verified the saved hash. The displayed
formula is `integral_0^T Z^(k) Z^(ell) = (-1)^d T Q_(2s+1)(log(T/(2pi)))/
[4^s(2s+1)] + O(T^(3/4)(log T)^(2s+1/2))`, when k+ell=2s,
|k-ell|=2d. Exact accompanying text: "where Q2s+1(x) is a monic polynomial
of degree 2s + 1. This follows from [11; Theorem 3] by integration by parts."
The equal-order specializations 0,1 give leading constants 1,1/12 and the
weaker errors used in the answer; no RH assumption enters these moments.

The researcher checked DLMF 5.11.9, https://dlmf.nist.gov/5.11#E9:
`|Gamma(x+iy)| ~ sqrt(2*pi)|y|^(x-1/2)exp(-pi|y|/2)`.
With x=1/4,y=t/2 this gives the required eventual lower envelope;
no differentiated asymptotic is used. `ClassicalXiInterface.lean:45-62`
and the already checked Ghat=-4xi identity give the factor A_G exactly.
Production modes on [0,L] gain (-1)^n after centering; this phase is
retained in both coefficients and reconstruction.

Stieltjes integration against weights 1,x²,x⁴ gives the uniform matrix
moment estimates, using the positive 2x2 Gram bound. On each grid cell,
linear interpolation plus endpoint-zero Poincare bounds the error by
(h/pi)||F'||. The resulting ratio tends to 1/sqrt(3)<2/3 on the actual
h=2pi/log(m) grid. The source exterior integral supplies the actual
coefficient error, with constant 8A0/pi² in (16). T=o(m) makes that
error negligible uniformly in the two coefficients, including a
coefficient combination cancelling near the first omitted node.
This establishes only the auxiliary mass bound, not the sign of W.


### Actual-window two-column diagnostic, m=8 only

`signed_tail_probe.py` computes E and the entire prime-power matrix P from
physical window residuals. Both mixed entries and q=m cancellation are
retained. The initial adaptive implementation omitted (-1)^n from synthesis;
root caught this before any result was accepted. That attempt was interrupted
and discarded. The corrected implementation uses the same phase in coefficients
and basis, and directly checks residual projections onto modes 0,1,m.

Corrected runs: 60 decimal digits / Gauss-Legendre orders 24 and 32, and
90 digits / order 32. Root independently replayed 70 digits / order 28:
`python3 docs/routeB_bus/source_observability_2026-09-28/signed_tail_probe.py
 --m 8 --settings 70:28 --output /tmp/q3_signed_tail_root_70_28.json`.
The root run took 8.24 seconds and agrees in all 48 reported eigenvalue digits:

`lambda_min(P,E)=0.0978422989510242752311253973694408296845597090355`,
`lambda_max(P,E)=1.20670223127215800865134417176946544741828070036`,
`kappa_8=1.34727084352394087904488545064433240250059491527`.

Thus the stronger fixed-unit-margin test (33) fails numerically at this
cell, but `d_8=kappa_8-lambda_max=0.140568612251782870393541278874866955...`
is positive. This does not settle the actual budget with mu,R,B at m=8,
nor any eventual sign. The previous independent Arb certificate already
settled the original finite m=8 candidate comparison; this diagnostic
investigates the new arithmetic mechanism, not a new tail claim.

Root's mixed q=2 direct-overlap versus periodic-minus-reflected discrepancy
is 1.19e-75 or less. These computations share quadrature and part of the
integrand; they check the decomposition, not an independent certified
integration method. Changing precision and quadrature order demonstrates
numerical stability only. No Arb enclosure of these new matrices is claimed.
The data, including root replay, are saved in `signed_tail_probe.json`.
