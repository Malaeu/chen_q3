# ГОЛ 030 — COUPLED FULL-SUM RESPONSE CERTIFICATE (контракт Прошки дословно)

От: Mythos, из proshka/PROSHKA_030_DIRECTIVE.md (representation shift после
029 INCONCLUSIVE; маршрут (a) в усиленной связной форме; старый split
P_core ± r·ε ЗАПРЕЩЁН как decisive representation навсегда).
Статус: CHALLENGER / NOT_RH. BUS_010_VOID. Ниже — контракт судьи дословно.

```
# GOAL 030 — COUPLED FULL-SUM RESPONSE CERTIFICATE

STATUS:
CHALLENGER / NOT_RH
FINITE CELL m=257 ONLY
No cofinal-family claim.
No sign grid.

PRIMARY TARGET:
030_CoupledFullSumResponseCertificate

PURPOSE:
Decide the exact sign of the canonical sampled sum on the two priority
bands without splitting it into

  finite core ± r * independent sup-tail.

This is the mandatory representation shift after 029.

====================================================
SOURCE LOCKS
====================================================

Consume:

- 026 certified Theta intervals;
- 026 live continued-fraction recessive tails;
- 026 finite-plus-tail normalization;
- 027 canonical source convention;
- 028R semantic retraction;
- 029 independently rederived J and epsilon machinery;
- exact midpoint/star convention.

Keep:

  m = 257
  degree pair = {0,4}
  canonical phase = '+'
  raw Legendre gauge a0 = 1 for both modes
  J0_raw = J4_raw = 2.

Do not use stored J or epsilon as primitive values.
Re-derive them as in 029 STEP 0.

====================================================
EXACT COMPUTING OBJECT
====================================================

Let the exact signed Legendre expansions be

  phi_j(t) = SUM_{q>=0} b_(j,q) P_(2q)(t),
  j in {0,4},

with all source phases already included.

Define the canonical combined row

  delta_q = (b_(4,q) - b_(0,q)) / 2.

Mandatory algebraic lock:

  delta_0 = 0

exactly, before interval arithmetic.

Do not represent the two P0 terms as independent balls.

For an open tooth-band

  I_r = (1/(r+1), 1/r),

define the exact response polynomial

  A_(r,q)(z) = SUM_{n=1}^r P_(2q)(n z).

Then the exact full canonical sum is

  S_r(z) = SUM_{q>=0} delta_q A_(r,q)(z).

At tooth z=1/r define

  A*_(r,q)
    = SUM_{n=1}^{r-1} P_(2q)(n/r)
      + (1/2) P_(2q)(1),

  S*_r = SUM_{q>=0} delta_q A*_(r,q).

These are the theorem-facing objects.
Do not reconstruct S through pointwise mode sup-bounds.

====================================================
TAIL BACKEND
====================================================

Build a COUPLED RESPONSE-WEIGHTED tail.

Forbidden old estimate:

  |tail| <= r * (epsilon0/J0 + epsilon4/J4).

Required object:

  T_(r,K)(z)
    = SUM_{q>K} delta_q A_(r,q)(z),

and similarly T*_(r,K) at teeth.

Use:

- the live continued-fraction ratio intervals;
- no terminal rho = 0;
- exact rational Legendre response polynomials;
- outward-rounded coefficient balls;
- response-weighted backward recurrence, interval Clenshaw,
  or an equivalent exact infinite-series enclosure.

A finite internal summation depth is permitted only to meet the
pre-registered remainder budget:

  tau_response = 2^-512.

The depth must be selected from contraction/remainder bounds before
examining the sign.

No sign-driven third K escalation is permitted.

The final residual beyond the internal response depth must be
proved <= tau_response after applying the sampling response.
It must not be a raw mode sup-tail multiplied by r.

====================================================
MANDATORY DOMAINS
====================================================

Open-band analytic continuations:

  r=256:
    z in [1/257, 1/256]

  r=255:
    z in [1/256, 1/255]

Using the interior-band response polynomial on the closed rational
interval is allowed as a stronger certificate for the open band.

Star teeth, separately:

  r=257: z=1/257
  r=256: z=1/256
  r=255: z=1/255

Also check the old 028 witness interval:

  [65281/16711680, 32641/8355840].

No boundary tooth may be omitted.

====================================================
PROOF BACKEND
====================================================

Bands:

- construct one outward-rounded enclosure of the WHOLE S_r;
- use exact rational Bernstein subdivision or validated Taylor models;
- subdivision must be rational and coverage-complete;
- do not interval-evaluate each n-term independently and add radii.

Teeth:

- A*_(r,q) must be exact rational;
- form one coupled infinite-series ball for S*_r.

Required outputs for every domain:

  lower_full_sum
  upper_full_sum
  coupled_tail_radius
  final response remainder
  exact coverage record.

====================================================
K1 PLANTS
====================================================

P1 - P0 cancellation:
Do not cancel delta_0.
The resulting response must change by the exact constant-mode amount.
The certificate must reject it.

P2 - independent-tail regression:
Replace the coupled tail temporarily by the old
  r * epsilon_Psi
bound.
It must reproduce an inconclusive 029-style enclosure.
This result is diagnostic only and must not enter the verdict.

P3 - terminal-ratio plant:
Set the terminal continued-fraction ratio to zero.
The full-sum enclosure must change materially.

P4 - mode-4 sign:
Flip the mode-4 source phase.
The result must change materially.

P5 - midpoint plant:
Replace the primal endpoint weight 1/2 by 1 at each tooth.
The tooth functional must change by exactly
  (1/2) Psi(1).

P6 - zero-mass-is-not-tooth-zero:
Run the symbolic control
  Psi(t)=t^2-1/3.
Verify
  integral_0^1 Psi = 0
but
  S*_r = (r+1)/(6r) != 0.
This prevents a false edge-zero inference.

====================================================
DECISIVE VERDICTS
====================================================

Return EXACTLY ONE:

COUPLED_FULL_SUM_NONNEGATIVE_PRIORITY_PROVED

iff:
- lower_full_sum >= 0 on both complete priority bands;
- lower tooth value >= 0 for r=257,256,255;
- all response remainders and coefficient uncertainties are consumed.

COUPLED_FULL_SUM_NEGATIVE_CELL_PROVED

iff:
- upper_full_sum < 0 on a strict rational subinterval
  or at an exact tooth.

This is the only finite-cell kill of DualThetaDominance.

COUPLED_FULL_SUM_RESPONSE_INCONCLUSIVE

iff:
- the certified whole-sum enclosure still contains zero after
  tau_response = 2^-512;
- no further depth or precision escalation is permitted.

COUPLED_TAIL_RESPONSE_BACKEND_GAP

iff:
- the live continued-fraction tail cannot be propagated through
  the sampling response without reverting to r*epsilon_Psi.

====================================================
SECONDARY FLAGS
====================================================

EXACT_TOOTH_ZERO_IDENTITY

may be emitted only if an exact symbolic recurrence/Poisson identity
proves S*_r = 0.

A ball containing zero is not this flag.

EDGE_FACTOR_REQUIRED

may accompany COUPLED_FULL_SUM_RESPONSE_INCONCLUSIVE only if:
- one or more teeth remain zero-compatible;
- adjacent interior cells have certified nonnegative lower bounds;
- the remaining problem is exact multiplicity/contact at the tooth.

====================================================
FORBIDDEN
====================================================

- no point grid as proof;
- no new decimal ladder;
- no third ordinary K-escalation;
- no r*epsilon_Psi as the final tail;
- no assumption S*(1/256)=0;
- no one-sided tail assumption;
- no mu := 1;
- no coefficient centers as exact;
- no terminal rho := 0;
- no cofinal or RH claim;
- do not modify lemma A / result 027.

====================================================
ARTIFACTS
====================================================

030_coupled_full_sum_response.answer.md
COUPLED_FULL_SUM_RESPONSE_CERT.json
coupled_full_sum_response_certificate.py
check_coupled_full_sum_response_certificate.py

Independent checker must:

- import neither generator nor Arb;
- verify all source hashes;
- rederive delta_0=0;
- rebuild all exact response polynomials;
- verify the rational band cover;
- verify the live-tail enclosure and tau_response;
- recompute all decisive lower/upper bounds;
- replay all six plants.
```

Отчёт и артефакты — по списку ARTIFACTS выше. STATE не трогать.
Зеркало по правилу 014 после закрытия.
