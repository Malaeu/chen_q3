# STATUS: SOURCE_ONLY_FIRST_ORDER_FAIL — SATZ 9 REMAINS THE ONLY STATED UNIFORM MODE THEOREM; R2_OUTER_FORBIDDEN_REGION_AGMON SELECTED; EXACT PAPER TARGET RETURNED

```yaml
ARTIFACT_CLASS: LINUX_EDGE_TOP_SOURCE_PREFLIGHT
GOAL: GOAL_058
DIRECTIVE: GOAL058_EDGE_TOP_DIRECT_OUTER_ASYMPTOTIC_PREFLIGHT (verdict 95e9584f, REQ-2026-08-26-C)
MODE_HONORED: PAPER_AND_SOURCE_READ_ONLY — no Lean written, no numerical probe run
REPORT_STATUS: SOURCE_ONLY_FIRST_ORDER_FAIL
SELECTED_REREPRESENTATION: R2_OUTER_FORBIDDEN_REGION_AGMON
AUTHOR_BODY: LINUX_CLAUDE (LINUX_STANDING_GRANT_2026-08-25)
RH_CLAIM: false
```

## PHASE 0 — exact rate map (paper)

Claim: an outer-half C0 defect rate `sup_{y in [lam/2, lam]} |delta(y)| <= A*lam^{-p}`
feeds the committed flux ledger into the top budget as follows.

1. Flux representation (committed B-chain): `F(y) = (lam^2-y^2)*delta'(y)`,
   `F(lam-) = 0`, `F' = -r` with
   `r = c*(4pi^2 lam^2 t^2 - theta)*S + 2t*Wd - (lam^2-t^2)*Wdd`.
2. On the outer half, `|c*S| <= |delta| + |W| <= A*lam^{-p} + Gaussian`, the
   cylinder terms are explicit Gaussians, and `|4pi^2 lam^2 t^2 - theta| <= 4pi^2 lam^4`,
   so `sup_{[y_top, lam]} |r| <= 4pi^2 A lam^{4-p} + Gaussian-junk`.
3. KEY CANCELLATION (no averaging needed): `|F(y_top)| <= (lam - y_top) * sup|r|`
   and `lam^2 - y_top^2 >= (lam - y_top)*lam`, so the `(lam-y_top)` factor divides
   out EXACTLY:  `|delta'(y_top)| <= 4pi^2 A lam^{3-p}`.
   (The arithmetic `y_top > lam/2` — u > lam/2 forces y_top = u; u <= lam/2 forces
   y_top > lam - u >= lam/2 — places y_top in the outer half. PAPER_PASS.)
4. Budget: `T_k <= INT_0^L sqrt(u)*lam*(4pi^2 A lam^{3-p}) dx`,
   `INT_0^L sqrt(u) dx = 2(sqrt(lam) - 1/sqrt(lam)) <= 2 sqrt(lam)`, hence
   `T_k <= 8 pi^2 A lam^{4.5-p}`.
5. Consumer: `T_k^2 / bandwidth <= 64 pi^4 A^2 lam^{9-2p} / (pi lam) -> 0  iff  p > 4`.

MINIMAL SUFFICIENT: any `p > 4` (integer minimal p = 5).
CONSERVATIVE: `p_safe = 6` — CONFIRMED as adequate, not assumed: it leaves the
margin `lam^{-3}` in the ratio and absorbs the anchor-scalar and theta-window
constants without bookkeeping.

## PHASE 1 — source audit (pages read as images, not OCR)

Read: printed pp. 243–247 (PDF 255–259) of Meixner–Schäfke 1954
(`/mnt/hdd01/Paper_to_read/978-3-662-00941-3.pdf`, mapping printed N = PDF N+12).

FINDINGS, page-locked:

1. Printed p. 243, between Satz 8 and Satz 9, the method paragraph states the
   HIGHER-ORDER MACHINERY: linear combination
   `y_p(z) = SUM_{r=-k}^{k} alpha_r D_{p+2r}((2 gamma)^{1/2} z)` with a
   truncated eigenvalue series
   `Lambda_p = -gamma^2 + (2p+1)gamma + beta_0 + beta_1 gamma^{-1} + ...`,
   coefficients chosen so `||F_gamma y_p + Lambda_p y_p||*||y_p||^{-1}`
   vanishes "von möglichst hoher Ordnung in gamma^{-1}"; uniformity is said
   provable "analog zu den Überlegungen in 2.333."; the recursion system is
   delegated: "Wir verweisen dazu auf MEIXNER [3] und SIPS [1]" (printed p. 244).
2. The STATED THEOREM (Satz 9, printed p. 243) gives the eigenvalue to
   `O(gamma^{-6})` but the MODE only "in erster Näherung — gleichmäßig in
   [-1,1]" with remainder `O(gamma^{-3/4})`.  NO theorem with a higher-order
   uniform fixed-mode remainder is stated on pp. 243–247.  Section 3.252
   (printed 244–247) is the gamma^2 -> -infinity (Laguerre) branch — Satz 10–12
   mirror the same structure there: high-order eigenvalue series, first-order
   uniform mode statement (`O(gamma*^{-1/2})`), method-only higher order.
3. Per the directive's own rule ("the long eigenvalue expansion alone is not
   evidence for a mode remainder") the discriminator
   SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE FAILS: the source provides the
   method and delegates the coefficients to MEIXNER [3] / SIPS [1] (not on the
   shelf), with no proved uniform remainder of order >= p_safe stated.
4. Optional acquisition (decision yours, not pursued): MEIXNER [3] and
   SIPS [1] might contain the recursion with remainders; both are external
   references and likely Mathieu-first.  Not treated as evidence here.

## R2 SELECTION — exact paper theorem target

```text
TARGET: SELECTED_ANCHORED_OUTER_POLYNOMIAL_DECAY (Agmon route)

STATEMENT (paper, to become the single Lean supplier after your gate):
  There is C >= 0 such that eventually, for BOTH selected anchored modes
  phi in {centerAnchorScalarZero(k)*h0_k, centerAnchorScalarFour(k)*h4_k}:
      sup_{y in [lambda_k/2, lambda_k]} |phi(y)| <= C * lambda_k^{-6}.

  (The Agmon mechanism actually yields e^{-c*lambda^2}; the target is CAPPED
  at the consumer-sufficient polynomial p_safe = 6 to keep the Lean port in
  the polynomial class.  C04 honored: the statement is about the literal
  anchored modes, not a raw S_phys.)

INPUTS (all committed or already-typed):
  - exact physical prolate ODE (committed, B1);
  - eigenvalue window theta <= C_theta * lambda^2 (F72.3 scale, typed input);
  - unit L2 normalization of the modes (committed normalized field);
  - anchor scalars bounded above eventually (companion of the committed
    |scale^{-1}| <= 8 chain; to be typed as a hypothesis if not yet public);
  - NO derivative sup-norm, NO delta'', NO new source theorem.

PROOF ROUTE (paper):
  On [lambda/4, lambda] the potential dominates:
  Q(y) = (2 pi lambda y)^2 - theta >= (pi^2/4) lambda^4 - C_theta lambda^2
       >= lambda^4 eventually.  Two steps:
  (i)  ENERGY/AGMON STEP: test the ODE against eta^2 * phi with a cutoff eta
       supported in [lambda/4, lambda], eta = 1 on [lambda/3, lambda]; the
       committed weighted-energy identity machinery (node-1 toolset) gives
           INT_{lambda/3}^{lambda} [ (lambda^2-y^2)|phi'|^2 + Q(y)|phi|^2 ]
             <= C * lambda^2 * INT_{supp eta'} |phi|^2  <=  C * lambda^2,
       hence INT_{[lambda/3, lambda]} |phi|^2 <= C * lambda^{-2}.  Iterating
       the same test once more (cutoff [lambda/3, lambda] -> [2lambda/5, ...])
       upgrades each pass by lambda^{-2}: three passes reach
       INT_{[lambda/2-eps, lambda]} |phi|^2 <= C * lambda^{-14} —
       FAR beyond need (each iteration costs one cutoff, no new input).
  (ii) POINTWISE RECOVERY: for y in [lambda/2, lambda], the mean-value +
       fundamental-theorem step on a unit cell inside [0.45 lambda, lambda]
       with the weighted energy of (i) converts L2 smallness into sup
       smallness at polynomial cost lambda^{C_small}: with the (i)-iterate
       chosen deep enough, sup <= C*lambda^{-6} follows with margin.
  The flux consumer (PHASE 0) then closes
  W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE with p = 6 > 4.

KILL CONDITION (honest): if the anchor upper bound fails eventually, the
target is restated for the unanchored unit-L2 modes and the anchor enters
the consumer as the typed factor it already is downstream.
```

CLOSES: SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE (FAIL, page-locked)
OPENS:  SELECTED_ANCHORED_OUTER_POLYNOMIAL_DECAY (paper target, awaiting gate)
CARRIES_OPEN: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
