# RESOLVENTGRAM — exact map obstruction and an early diagonal filter

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; NAMED_MAP_AND_STATIONARY_TAIL_FILTER_ONLY.
SCOPE: the named normalized Mellin/Cauchy map, plus the separately reviewed
stationary positive tail-Gram identity filter; no full-V sign conclusion.

## 1. Exact received object

Request: `REQ-2026-09-16-RESOLVENTGRAM`, boundary
`GOAL058_FULL_SOURCE_RESOLVENT_GRAM_TO_WEIL_KERNEL`.
Request commit: `5fb0c0693427a870409446cf24416790f06e69f2`.
Request SHA256: `f8014d60f15d8ab17d8ae2bc7a2fa4e25d680e94d20988fb5ce7d8a2867ef514`.

Raw response, retained unchanged:
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_RESOLVENTGRAM_2026-09-16.md`
at commit `9051998df0dc748d2f9e647d012350661d068d5e`.
SHA256: `d3fc01e09bde88074d657f031c9701bdbf1e6d985c8d50e7ba3a3fc1381ccfb9`;
44665 bytes, 481 LF, final LF; blob
`412d8e273c4e1d43f30f1134708c48b3a96e4d4b`.

The parent read the full response and reproduced the source normalization,
conjugate-first Fourier transport, full-mode bounds, diagonal defect, and
finite-frequency-row passage. An independent reviewer accepted the raw
response as `ACCEPT_NORMALIZED_MELLIN_CAUCHY_MAP_OBSTRUCTION_ONLY`.
Raw-review SHA256:
`79517b65b7af3bc1bdd8b3f700b52b10af5acd6b9527172c09fd4daed121c586`.

Source pins at that commit:

- `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, SHA256
  `1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282`.
- `docs/Codex/REPORT_2026-09-16_RESOLVENTGRAM_MELLIN_PREFLIGHT.md`, SHA256
  `ded92e32d79596b0292c6dac13c3ffb8dc26972f8cda81ecf88613867703deba`.
- `docs/Codex/REPORT_2026-09-16_RESOLVENTGRAM_RECIPROCAL_GAMMA.md`, SHA256
  `26013672622466181a73cc5e567befd702b5264e61f65510194a9b7d60e9dd27`.

## 2. What the proposed positive object actually represents

Keep the full source r, its Laplace transform L, lambda_n=pi*n^2,
A=||Phi||_2, and original f=Phi/A. The consumer is exactly

  K_2(u,v)=[conj(R_2(u))+R_2(v)]/[4+i(u-v)],
  R_2(u)=xi'(5/2-iu)/xi(5/2-iu).

With q_u=3/4-iu/2, reciprocity gives the convergent Mellin identity

  B(q)=integral_0^infinity v^(q-1)L(v)dv
      =2 Gamma(q) xi(1+2q),
  F_2(u)=B(q_u)/(2 A Gamma(q_u)),
  R_2(u)=1/2 [B'(q_u)/B(q_u)-psi(q_u)].             (I1)

The actual Gram uses

  b_n(u)=[integral_0^infinity v^(q_u-1)L(v)/(lambda_n+v)dv]/B(q_u),
  G(u,v)=2 sum_n conj(b_n(u))b_n(v)/[4+i(u-v)].       (I2)

It is PSD on every finite complex frequency row: its explicit features are
sqrt(2)*b_n(u)*exp(-2 tau+i u tau), tau>=0. Complex normalized Mellin weights
are not called positive measures. The Gamma correction in I1 is retained,
as are all terms of the signed defect Delta_eta=K_2-eta G (raw RG10).

Its exact physical image is

  v_n(t)=integral_0^t r(t-y)exp(-lambda_n*y)dy,
  phi_n(x)=A^(-1)exp(-5x/2)v_n(exp(-2x)),
  V_G(x,y)=2 sum_n integral_0^infinity phi_n(x+X)phi_n(y+X)dX. (I3)

The matched Fourier identity is

  conj(F_2(u)) Delta_eta(u,v) F_2(v)
    =integral_R^2 exp(2(x+y)) [V(x,y)-eta V_G(x,y)]
                    exp(i u x-i v y) dx dy.          (I4)

The source estimate r(t)<=4*pi^2*t*exp(-pi*t), its reciprocal counterpart,
and the summable lambda_n^(-2) budget justify the full sums and integrals.
The factor 4 comes from the complete product over n>=2, not a truncation.
The parent checked the factors 2 and A and both Fourier phases in I1-I4.

## 3. Exact obstruction: positive energy survives where V cancels it

For R>0, evenness of the full source gives

  V(-R,-R)=2 integral_R^infinity y f(y)^2dy -> 0+,    (I5)

whereas the positive image accumulates a nonzero full norm:

  V_G(-R,-R) -> 2 sum_n ||phi_n||_2^2 > 0.           (I6)

This is not a negative V witness: the V in I5 is strictly positive.
The raw proof strengthens the mismatch to an explicit strict bound. With

  d_*=2 integral_0^1 exp(-5y)v_1(exp(-2y))^2dy > 0,
  C_V=8*pi^3*(9/(2*pi*e))^(9/2),

any R>=1 satisfying C_V*exp(-pi*exp(2R))<=eta*d_*/2 gives

  V(-R,-R)-eta V_G(-R,-R)<=-eta*d_*/(2*A^2)<0.      (I7)

For every fixed eta>0 such an R exists. No numerical evaluation is needed.
The continuous integrable kernel in I4 then has a negative compact smooth
bump test. Fourier inversion, Schwartz-tail control and finite Riemann
approximation produce a finite frequency row beta with a strict negative
quadratic value. Setting a_j=F_2(u_j) beta_j returns precisely

  sum_ij conj(a_i)[K_2(u_i,u_j)-eta G(u_i,u_j)]a_j<0. (I8)

Every F_2(u_j) is nonzero by Euler in Re s=5/2 and Gamma nonvanishing;
no bounded inverse multiplier on a whole function space is assumed.
The frequency row is proved to exist analytically; its rank, nodes and
numerical coefficients are not claimed to have been computed.

Conclusion: no fixed eta>0 and no PSD kernel B, of any rank, can give
K_2=eta G+B for this named map. This includes a PSD boundary repair.
It does not exclude a different map or prove negativity of K_2 itself.

## 4. Parent addition: reject stationary positive tail identities locally

This smaller necessary test already works on the original negative interval
I=(-log(2)/2,0), without taking a node outside I.

Let Psi:R->H be strongly measurable into a Hilbert space, with finite tails
on an open negative interval, and define

  T_Psi(x,y)=integral_0^infinity <Psi(x+t),Psi(y+t)>dt.

For x1<x2 in I, with the first argument conjugate-linear,

  T_Psi(x1,x1)-T_Psi(x2,x2)
      =integral_x1^x2 ||Psi(u)||^2du >= 0.           (I9)

Every such stationary positive tail Gram has a nonincreasing diagonal.
No differentiability of Psi is used. For the original continuous positive
even f, however,

  D(x)=V(x,x)=2 integral_|x|^infinity u f(u)^2du,
  D'(x)=-2x f(x)^2>0 for x<0.                       (I10)

Thus T_Psi cannot equal V on any open negative interval. Constant positive
multiples and Hilbert direct sums remain in the excluded class.

This DOES NOT exclude arbitrary Gram representations <Psi_x,Psi_y>,
nonstationary fields Psi(x,t), node-dependent weights, signed interference,
or T_Psi plus an independent PSD boundary kernel on bounded I. In particular,
I9-I10 alone do not prove the stronger arbitrary-positive-addition result
I8. That result needs the named map and its exact global Fourier transport.
No alternative listed here is asserted to work.

The candidate for this section was separately independently accepted as
`ACCEPT_STATIONARY_POSITIVE_TAIL_GRAM_EXACT_IDENTITY_FILTER_ONLY`.
Candidate SHA256:
`f3bddf93615da4eb36596f1d6211fbf7045c898b8cc41b35d227048a9f8368cd`.
Review SHA256:
`1021ca7ae23bce94d7d29d26acfb906d73c4785a07f813f4d7176e969f165792`.

## 5. Decision and remaining obligation

The request is answered. The tested positive source-to-consumer map is
rejected analytically, including its constant rescalings and PSD additions.
The early filter I9-I10 prevents repeating stationary positive half-line
lifts that cannot even preserve the target diagonal. Reopening this exact
map requires an error in the identities or the strict defect proof, not a
new positive coefficient.

The next construction must account for the original reciprocal cancellation
before claiming an exact positive representation. Matching the diagonal
is a cheap necessary condition, not a sufficient sign theorem. Matching
all mixed entries and every finite complex row remains mandatory.
The existing exact signed identities are retained; their total sign is
still unpaid. No automatic new Proshka proof request is issued by this intake.

Full-V sign progress: NONE. Negative original-V witness: NONE.
RH proved or refuted: NO. Joint additive TN and reciprocity refuted: NO.
Other Gram maps excluded: NO. Lean runs: 0. Canonical admission: NO.
PX_RH_CLAIM: NOT_MADE. This is independently reviewed analytic research,
not formal kernel certification or canonical proof-node closure.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The named positive tail image retains a nonzero norm while the exact reciprocal V diagonal cancels to zero; a PSD correction cannot repair that map, and full V sign remains open.

## Independent intake acceptance

Reviewer `/root/sibling5_check` checked the full raw response, the separate
stationary-tail filter, and this complete intake. Intake verdict: CLEAN_INTAKE.
Candidate SHA256: `4f0c4d754de200bb0bcb4a5f29f1bffd6e84cddc83a2c9d14bed713e0e8210c5`.
Intake review SHA256: `7434c47a1327115a06233fafdd984cfbadefd27a0f3cffe6c5f0db192721a083`.
Only the status line and this receipt were added after intake review.
The companion certificate preserves all three full independent reviews.
No source-sign counter was reset and no canonical node was closed.
