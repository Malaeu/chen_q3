# H2A.4.1B.3C.1.1 — fixed-mode C1/H1 source acquisition (READ-ONLY)

```yaml
PRIMARY: H2A_4_1B_3C_1_1_FIXED_MODE_C1_SOURCE_ACQUISITION
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict 8e0f2693 — CODEX DIRECTIVE (REQ-2026-08-22-V, NEXT)
MODE: READ_ONLY
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: 8e0f2693d3aa9945940b33d263402065517ee26d

OUTCOME_CODE: ONLY_C0_RATE_SOURCE_NEW_ANALYSIS_REQUIRED

SOURCE_READ:
  BOOK: /mnt/hdd01/Paper_to_read/978-3-662-00941-3.pdf (Meixner–Schäfke 1954)
  PAGE_MAP: printed N = PDF N+12 (confirmed again this session)
  SECTIONS_READ_AS_IMAGES:
    - "§2.33 intro + §2.331 Satz 3–7: printed 134–139 (PDF 146–151)"
    - "§2.332 Satz 8 (Mathieu branch-point statement): printed 139–140"
    - "§2.333 COMPLETE: printed 140–145 (PDF 152–157) — Satz 9 (L2), Fourier coefficients (3)/(3'), integral relations (4)/(5), Satz 10 (uniform), asymptotic series (6)/(7)"
    - "§3.251 COMPLETE: printed 240–244 (PDF 252–256) — operator F_gamma, quotient bound (*), Satz 7, eta_p estimate, alpha normalization, Satz 8 (mean square), Satz 9 (eigenvalue series + uniform first approximation), citation line to MEIXNER [3] and SIPS [1]"
    - "§3.252 (gamma^2 -> -infty, Laguerre side): printed 244–246 — read to confirm no derivative estimates hide in the mirrored treatment"
  ALSO_READ:
    - docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md (426 lines)
    - Q3/Proofs/RouteB/G6N1Satz9SourcePackageInterface.lean (162 lines)
    - Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean (407 lines)
    - docs/routeB_bus/H2A_4_1B_3C_1_0_..._PREFLIGHT_2026-08-23.md (own preflight)

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## TEST 1 — DERIVATIVE PROVENANCE

**Result: NO derivative or weighted-H1 remainder estimate exists in the
inspected sections.**  Every error statement in the relevant chain controls
function values only.  The complete inventory of error-carrying statements:

| statement | page (printed) | norm | remainder |
|---|---|---|---|
| §2.333 Satz 9 (Mathieu) | 141 | L2 over [0, pi] | O(h^-2) on the squared integral |
| §2.333 coefficients (3), (3') | 141, 143 | pointwise on Fourier coefficients | 1 + O(h^-1) factors |
| §2.333 Satz 10 (Mathieu) | 144 | UNIFORM on 0 <= z <= pi | O(h^-3/4) |
| §2.333 series (6)/(7) | 145 | asymptotic "~" only | no quantified remainder, no derivative |
| §3.251 quotient bound (*) | 241 | ratio of L2 norms of residual F_gamma y_p + Lambda_p y_p | O(1) |
| §3.251 eta_p estimate | 242 | L2 | factor O(gamma^-1) |
| §3.251 Satz 8 (spheroidal) | 243 | quadratic mean over [-1, 1] | O(gamma^-1) |
| §3.251 Satz 9 (spheroidal) | 243 | UNIFORM on [-1, 1] | O(gamma^-3/4) |

The uniform statements are C0 statements about the functions themselves; the
symbols `ps'` or `ce'` never appear inside any remainder estimate.  The only
derivatives on these pages are (a) derivatives of the parabolic cylinder
functions `D_p` inside exact residual identities (e.g. the §3.251 residual
`f_p(z) = (1−z^2)^{m/2} {−x^2 D_p''(x) − 2(m+1) x D_p'(x)}`, an identity, not
an approximation), and (b) sign values `D_p'(0)` used for normalization.

**Delegation audit.**  The spheroidal uniform statement is not even proved in
§3.251: the page states the uniform approximation can be proved analogously to
§2.333 (one German clause, quoted for provenance: "Ferner kann man analog zu
den Überlegungen in 2.333. die gleichmäßige Approximation ... beweisen").
§2.333 itself derives uniformity from the mean-square statement via two exact
integral relations — (4): a cosine-kernel integral reproducing
`D_{2n}(zeta)/D_{2n}(0)`, and (5): a cosine-kernel integral reproducing
`ce_{2n}(z)/ce_{2n}(pi/2)` — substituting the L2 asymptotic under the integral
and using ONLY the boundedness of the cosine kernel.  No differentiation is
performed anywhere in that argument.

The MEIXNER [3] / SIPS [1] citation line on printed 244 concerns solely the
five-term recursion system for the series coefficients `alpha_r` and the
formal gamma^-1 power series for lambda — coefficient bookkeeping, not error
control, and not derivative control.  There is no delegated derivative
theorem to chase further in this book; §3.252 (the Laguerre mirror) repeats
the same L2 + uniform pattern (Satz 11, quadratic mean, O(gamma*^-1)) with no
derivative statement either.

**Conclusion of Test 1:** the strongest directly quotable results are exactly
the ratified C0 ones (Satz 8 mean-square O(gamma^-1); Satz 9 uniform raw
O(gamma^-3/4), i.e. normalized O(gamma^-1), physical O(lambda^-2)).  A C1 or
weighted-H1 rate would have to be PROVED, not cited.  This matches the judge's
P_H2A41B3C1_1_2 = 0.70 branch.

## TEST 2 — SCALING AUDIT

Exact chain, read off the source pages and the ratified cards:

```text
dimensionless variable:   z in [-1, 1]                     (§3.21, Satz 1, Satz 8/9)
substitution:             x = (2*gamma)^(1/2) * z          (§3.251, printed 240)
parameter conversion:     gamma_MS = fuchs a^2 = 2*pi*lambda^2   (RATIFIED, REQ-I 082421cf)
project schedule:         gamma_k = 2*pi*(k+2), lambda_k = selectedFerrersPaperLambda k
physical window:          [-lambda, lambda], z = x_phys/lambda
derivative scalings:      d/dz = (2*gamma)^(1/2) * d/dx    (cylinder argument)
                          d/dx_phys = lambda^(-1) * d/dz   (window rescale)
```

Consequence for any FUTURE derivative estimate: a dimensionless uniform bound
`sup_z |R'(z)| <= C * gamma^(-a)` converts on the physical window to
`sup |d/dx_phys R| <= C * lambda^(-1) * gamma^(-a)`, and in the log coordinate
`t = log u` one more chain factor `u` enters (`d/dt = u * d/du`).  None of
these factors are present in the book because no such bound is stated there.
The value-level chain (raw O(gamma^-3/4) → normalized O(gamma^-1) → physical
O(lambda^-2)) remains exactly as carded and is consumed by
`selectedFerrers_directCylinderRate_of_explicitSatz9RawRates`
(G6N1SelectedFerrersDirectCylinderRate.lean:273) as a typed C0 input
(`‖scale·p − D_n‖ <= rawC / gamma` pointwise on the closed physical window) —
the Lean consumer likewise has no derivative field.

## TEST 3 — ENDPOINT AUDIT

Satz 9's uniformity is on the CLOSED interval [-1, 1]; endpoint values are
covered by the C0 statement.  But the production modes are indicator zero
extensions (`logWindowZeroExtendedMode`; the H_m window construction), so:

- the distributional derivative of the zero-extended mode carries jump terms
  at the window endpoints of size |mode value at the endpoint|;
- interior C1 control (even if it existed) says nothing about these jumps;
- for the fixed modes n = 0, 4 at m = 0 the endpoint value scale involves
  `D_n((2*gamma)^(1/2))`, which is Gaussian-small (`~ e^{-gamma/2} *
  (2*gamma)^{n/2}` up to normalization), so the SOURCE-mode endpoint jumps are
  exponentially negligible — but the TARGET/trial side and the E-star
  dilation stitching create their own O(polynomial) jump ledger that the book
  cannot see.  Satz9SourceData (G6N1Satz9SourcePackageInterface.lean:84)
  carries `hasDeriv` only on the OPEN interval Ioo(-lambda, lambda), which is
  the correct honest interface: nothing in the package claims a distributional
  derivative of the extension.

## TEST 4 — E-STAR AUDIT

The E-star construction sums dilations with seams at the points u = lambda/n.
Each seam contributes a finite jump to the piecewise log-derivative of the
assembled row; the number of seams on a window is finite (bounded by the
dilation count), so the jump ledger is finite and explicit IN PRINCIPLE — but
it is a project object.  The book's statements are about a single mode on a
single dimensionless interval; they survive the dilation sum only as C0
statements (values compose through the sum), while any derivative version
must add the seam-jump budget by hand.  No source result addresses this; the
required object is exactly the judge's
`SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_AND_JUMP_BUDGET`.

## TEST 5 — RATE AUDIT

Required threshold (ratified ledger): `GammaEnergy_k = o(sqrt(m_k)/L_k^2)`;
for the selected-row budget the same ledger applies through the preflight's
R1 reduction (`GammaEnergy = (L/2pi)^2 * ||d/dt synthesis(r)||^2`).

Since NO derivative rate exists in the source, there is nothing to convert;
the rate audit is answerable only conditionally.  For the record, IF a future
derivative analysis yields a normalized uniform first-derivative remainder
`O(gamma^(-b))` in the dimensionless variable for the fixed modes, then the
physical piecewise log-derivative error of one dressed mode scales as
`O(lambda^(-1) * u * gamma^(-b))`-type on the window; whether the assembled
selected-row mode-weighted budget lands below `sqrt(m)/L^2` then depends on
(i) the E-star seam ledger (Test 4), (ii) the zero-mass combination and
center normalization transport, and (iii) the finite projection — the exact
transport chain the verdict's STRONGEST ATTACK enumerates.  No shortcut from
a fixed-mode C1 bound to the Gamma threshold exists without those steps.

## FORBIDDEN CHECK

```yaml
differentiate_O_term_without_derivative_theorem: not done (explicitly refused; the
  book's O(gamma^-3/4) was never formally differentiated)
interior_C1_identified_with_zero_extension_H1: not done (Test 3 separates them)
endpoint_or_dilation_jumps_omitted: not omitted (Tests 3–4 carry them)
gamma_rate_inferred_from_source_mode_rate: not done (Test 5 is conditional only)
lean_written_or_aristotle_submitted: no
```

## POSITIVE FINDING (for the next directive, not a claim)

The §2.333 uniformization mechanism is DERIVATIVE-CAPABLE even though the book
never differentiates it.  The integral relations (4)/(5) represent the mode
through a smooth cosine kernel; differentiating the IDENTITY (5) with respect
to `z` (not the O-term) moves the derivative onto the explicit kernel
`cos(2h*cos z*cos t)` and onto `D_m'`, both explicitly controllable, at the
price of one factor of `h^(1/2)`-scale from the kernel argument.  A
theorem-sized new analysis along this line would produce a uniform
first-derivative remainder for the fixed modes with an explicit exponent —
this is a legitimate derivative theorem route, not a formal differentiation of
a big-O.  It is NEW analysis (nothing citable), it lives before the E-star
seam ledger, and its Mathieu prototype would still need the spheroidal
transposition that the book itself only sketches by analogy.

Cost estimate for that route: comparable to one 3C.0-scale floor (the kernel
identities (4)/(5) have clean spheroidal analogues via §3.32–3.33 integral
relations, unverified here), PLUS the seam-ledger theorem, PLUS the transport
chain.  This is consistent with the verdict's plan: the next analytic object
is `SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_AND_JUMP_BUDGET`, not a broad
`sum n^2 |q_n|^2` contract.

## PREDICTION CHECK (registered by the judge)

```text
P_H2A41B3C1_1_1 = 0.30 (source contains usable C1/H1 rate): REFUTED — no
  derivative estimate exists in §2.333, §3.251, or §3.252.
P_H2A41B3C1_1_2 = 0.70 (C0 is the strongest quoted result, new analysis
  required): CONFIRMED.
P_H2A41B3C1_1_3 = 0.90 (endpoint/dilation jump accounting stays load-bearing):
  CONFIRMED — the book's interval statements cannot see the E-star seams;
  the jump ledger is irreducibly a project object.
LIKELIEST_FAILURE (source controls values, not derivatives of the remainder):
  OBSERVED EXACTLY.
```

SUCCESS_CODE_RETURNED: ONLY_C0_RATE_SOURCE_NEW_ANALYSIS_REQUIRED
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
