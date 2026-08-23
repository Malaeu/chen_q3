# H2A.4.1B.3C.1.6 — selected Ferrers global-radical window/projection defect preflight (READ-ONLY MATH+SOURCE)

```yaml
PRIMARY: H2A_4_1B_3C_1_6_SELECTED_FERRERS_GLOBAL_RADICAL_WINDOW_PROJECTION_DEFECT_PREFLIGHT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict 6a98cfea — CODEX DIRECTIVE (REQ-2026-08-22-V)
MODE: READ_ONLY_MATH_AND_SOURCE
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: 6a98cfeaf7b4703a94e4b993bc31dc036b83c36c   # live git rev-parse HEAD (receipt repair honored)

OUTCOME_CODE: LIMIT_TARGET_RADICAL_ONLY_SELECTED_TRIAL_DOMAIN_OPEN

PRIMARY_SOURCE_READ:
  PDF: docs/routeB_bus/litreview/pdfs/2602.04022.pdf (Connes, Feb 2026)
  PAGES_READ_AS_IMAGES: 26-30 (sections 6.1-6.6 complete, 7.0-7.1 opening)
  USAGE_CARDS: docs/routeB_bus/litreview/CONNES_RH2026_USAGE_CARDS.md (re-read)

DISK_LOCKS_VERIFIED:
  - "sourceModeCorrelation_add_neg_eq_zero_of_window_lt: PRIVATE, D0PstarSourceModeCosineCCMQKernel.lean:536 (consumed at :1010)"
  - "sourcePrimeModePairing_eq_ccmPrimeEntryN1 (public, 49-line file)"
  - "E_star (D0KTrialStage2.lean:24) = literal summation map"
  - "explicitCCMLimitH (D0PstarExplicitCCMLimitFourier.lean:29)"

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## TEST 1 — GLOBAL RADICAL SOURCE LOCK

Located, read from the rendered page (p. 29, §6.4), the exact statement:

> "The range of the map E is contained in the radical of the global Weil
> quadratic form (see (18))" — Connes 2026, §6.4, p. 29.

**Exact domain and mechanism, read from the same page.**  The mechanism is
equation (18): the Poisson formula, "using the conditions f(0) = f-hat(0) = 0
to define the codimension 2 subspace S_0 of the Schwartz space", gives

```text
E(f-hat)(x) = E(f)(x^{-1})   for all f in S_0^{ev}.          (18)
```

So the domain of the radical statement is exactly:

```text
D_rad = S_0^{ev} = { f Schwartz, even, f(0) = 0, f-hat(0) = 0 }   (codim 2).
```

Polarization convention: the global Weil quadratic form on test functions
(§4.1 of the paper); the statement is about its RADICAL (nullspace of the
polarized form), quantified over all f in S_0^{ev}.  K7-tag for our ledger:
PAPER_PROVED at survey level, with the mechanism displayed (Poisson + the
two point conditions), detailed proof delegated to the cited companion works.

**The obstruction sentence is on the same page and is decisive for Test 2:**

> "The obstruction to obtain an element E(f) of the radical of QW_lambda is
> the equality P_lambda \cap P-hat_lambda = {0}" — p. 29,

followed by: after taking care of the two conditions `f(0) = f-hat(0) = 0`,
the restriction of `E(f)` to `[lambda^{-1}, lambda]` gives `k_lambda` "on
which QW_lambda takes non-zero, but extremely small values" — i.e. the
paper itself states the selected-type trial is NEAR-radical, not radical.

## TEST 2 — PROJECT OBJECT MATCH

```text
project E_star = paper E:               EXACT.
  E_star(h)(u) = sqrt(u) * sum'_{n>=1} h(n*u)  (D0KTrialStage2.lean:24)
  vs paper (12): E(f)(u) = u^{1/2} sum_1^inf f(nu).  Same formula, same
  normalization.  DEFINITIONAL MATCH.

factor-four limit target in D_rad:      YES — ALL THREE CONDITIONS EXACT.
  h(u) = (pi/2) u^2 (2 pi u^2 - 3) e^{-pi u^2}  (paper (13)) =
  explicitCCMLimitH (disk :29).  (i) Schwartz: polynomial times Gaussian —
  yes.  (ii) h(0) = 0: the u^2 factor — exact.  (iii) h-hat(0) = integral
  of h = 0: Fact 6.2 (h is the zero-integral combination of h_0, h_4) —
  exact.  A nonzero scalar (factor four; L73.5 Mellin normalization to
  centeredXi) does not change radical membership.
  => G = E_star(4*explicitCCMLimitH) IS in the global radical: PAPER_PROVED
  after this domain check.  No new analysis needed for the LIMIT target.

selected hTrial_m in D_rad:             NO — TWO EXACT VIOLATIONS.
  hTrial = prolateCombination: the zero-integral combination of the
  TRUNCATED prolates h_{0,lambda}, h_{4,lambda} (supported in
  [-lambda, lambda], zero-extended).
  (V1) NOT Schwartz: PSWFs have nonzero endpoint values; the zero
       extension is discontinuous at ±lambda.  S_0^{ev} membership fails
       at the regularity level, not just decay.
  (V2) f(0) != 0: the construction imposes ONE linear condition (vanishing
       integral = f-hat(0) = 0) in the two-dimensional span {h_0, h_4};
       the second domain condition f(0) = 0 is NOT imposed.  It holds only
       in the limit (h(0) = 0 exactly), so h_{lambda}(0) -> 0
       exponentially but is nonzero at finite lambda.
  Both violations are exponentially small IN SIZE (prolate-to-Hermite
  convergence), which is exactly why the paper calls k_lambda near-radical
  — but membership is a yes/no question and the answer is NO.

midpoint convention: the production hTrial carries the midpoint
  representative at the jump (D0KTrialStage2 docstring) — an a.e./value
  convention that matters for pointwise seam values, not for L2 classes;
  it does not repair (V1).
```

Conclusion: the R1 hope ("the selected trial itself is globally radical,
no error/target split needed") DIES at the domain, and dies in the primary
source's own words — the obstruction `P_lambda ∩ P-hat_lambda = {0}` is
structural (a nonzero function cannot be simultaneously time- and
band-limited), not a technical endpoint gap.  What survives is the judge's
P_RADICAL_DEFECT_1 direction in REPAIRED form: not "hTrial admits the
theorem after extension", but "hTrial is near-radical with an explicit
exponentially small budget" — a NEW quantitative theorem (extension of the
Poisson mechanism to the truncated class with both point-condition defects
carried as explicit terms).  Named:

```text
NEAR_RADICAL_BUDGET_FOR_TRUNCATED_PROLATE_ESTAR_TRIAL
  QW_global-pairing of E_star(hTrial_lambda) against window test vectors
  = O(exponentially small in lambda), with the two domain defects (V1),
  (V2) as the only sources.
```

## TEST 3 — GLOBAL/WINDOW FORM CROSSWALK

Four objects, kept strictly apart:

```text
QW_global      : Weil quadratic form on (Schwartz) test functions — paper §4.1;
QW_lambda      : its restriction to support in [lambda^{-1}, lambda] — paper §6.4,
                 with canonical selfadjoint A_lambda, QW_lambda(f,f) = <A_lambda f | f> (16);
sourceWeil i   : the project window form on H_m (W02 - arch - prime pieces);
finite matrix  : ccmWeilMatFinite via the synthesis crosswalk (3C.1.5, admitted).
```

**Prime cutoff status.**  On the finite mode span the cutoff is EXACT by
support: `sourceModeCorrelation_add_neg_eq_zero_of_window_lt`
(D0PstarSourceModeCosineCCMQKernel.lean:536, private, consumed at :1010)
kills every prime `k` with `log k > L_m` on zero-extended log-window modes,
and `sourcePrimeModePairing_eq_ccmPrimeEntryN1` locks the finite sum to the
CCM entry.  PROVED on basis vectors, hence on the finite span by
(sesqui)linearity — no continuity argument needed there.  [FINITE_CELL][LEAN]

On the FULL H_m domain: the same support argument applies pointwise to any
window element (the correlation of two functions supported in a log-window
of length L vanishes when the shift log k exceeds L), so the all-prime
global sum restricted to window functions is a FINITE sum term-by-term;
but the theorem identifying `sourceWeilSesquilinearForm i` with the
restriction of QW_global on ALL of H_m (not just the finite span) is NOT
on disk.  It is theorem-sized (continuity of both forms + density, or the
direct support argument), and it is the exact crosswalk the verdict marks
OPEN.  Status: GLOBAL_TO_WINDOW_RESTRICTION — OPEN, with a clear route.
[COFINAL_FAMILY][CONDITIONAL]

## TEST 4 — EXACT SELECTED DEFECT IDENTITY (schematic, with every term named)

Objects: `G_k = E_star(hTrial_k)` (global, support in (0, lambda_k] by the
paper's support lemma), `y_k = P_{m,N}(restrict G_k)`, `q_k = t_k y_k /
(via s_k q_k = t_k(eE_k + gE_k) chain)`, `delta_k = G_k - zeroExtend(y_k)`.

Under (A) the Test-3 crosswalk on the needed domain and (B) the Test-2
near-radical budget, the polarized Rayleigh-centered chain reads:

```text
<v, Gamma_k>  = (dual identity, 3C.1.5, ADMITTED)
  = W_i(S(D_k v), S(q_k)) - a_k <D_k v, q_k>
  = [crosswalk (A)]  QW_global(iota S(D_k v), zeroExtend(S(q_k))) - a_k <...>
  = (t_k/s_k) * [ QW_global(iota S(D_k v), G_k)          <- near-radical term, budget (B)
                 - QW_global(iota S(D_k v), delta_k)      <- window/projection defect term
                 - a_k <D_k v, eE_k + gE_k> ].            <- Rayleigh-centering term
```

Exact signs and casts as in 3C.1.5 (star-first, s in the linear slot);
nothing here is proved — this is the target identity whose two supplier
walls are exactly (A) and (B), plus the defect rate of Test 5/6.

## TEST 5 — DEFECT SPLIT

With `supp G_k ⊂ (0, lambda_k]` (paper p. 29: supp E(f) ⊂ (0, lambda]
when supp f ⊂ [-lambda, lambda]):

```text
delta_k = G_k * 1_{(0, lambda^{-1})}                  (below-window tail; NO
                                                       above-window tail exists)
        + [G_k * 1_{[lambda^{-1}, lambda]} - zeroExtend(P_{m,N}(restrict G_k))]
                                                      (inside-window finite-
                                                       projection tail)
        + endpoint atoms at u = lambda^{-1}, lambda   (zero-extension seams;
                                                       the E-star carrier cuts
                                                       at u = lambda/r from
                                                       3C.1.2 live INSIDE the
                                                       window and belong to the
                                                       function itself, not to
                                                       delta).
```

Below-window tail structure: for `u < lambda^{-1}` the E-star sum has
`~lambda/u` terms; the vanishing-integral condition kills the leading
Riemann-sum term, leaving Poisson-type remainders — this is the same
mechanism that makes the paper's `k_lambda` near-radical from below.  No
component W02/WR/Prime split is used anywhere in this ledger (firewall
respected); each of the three pieces needs a FULL-form pairing bound.

## TEST 6 — RATE LEDGER

Target (3C.1.5, admitted): `dual_sup = o(m^{1/4}/L^{3/2})`.  Required
estimates, named exactly, one per term of Test 4:

```text
(B) near-radical term:  |QW_global(iota S(D_k v), G_k)| <= C(v) * eps(lambda),
    eps exponentially small — plausible at the paper's own accuracy scale
    (Fig. 1: eps(lambda) tracks 1 - chi_2, doubly exponential); FAR below
    threshold IF the near-radical budget theorem (Test 2) is proved.
(delta, below-window): full-form pairing of the below-window tail —
    Poisson-remainder scale, plausibly exponentially small by the same
    mechanism; needs the actual theorem.
(delta, projection): full-form pairing of the inside-window projection
    tail — THIS is the piece that inherits the old rate question: the
    finite-Fourier tail of G_k on the window at mode cutoff N = m.  The
    target is smooth away from seams, so a polynomial-log budget is
    plausible; the mode-weighted version of exactly this object was N3 in
    the earlier ledgers.  Required: full-form (not component) bound at
    o(m^{1/4}/L^{3/2}).
(a_k term): scalar ledger from 3C.1.4/3C.1.5 carries over unchanged (open:
    |a_k| bound).
```

No `eta_k` appears (enters only in the final ratified consumer);
no component norm sum replaces any full-form pairing.

## MANDATORY PLANTS

1. **Mellin label does not imply radicality** (generic firewall, retained
   from 3C.1.5): `G = e_0`, identity form, any transform label: `B(G,G) =
   1 != 0`.  It attacks the generic inference only — NOT the
   source-specific §6.4 theorem, which has its own Poisson mechanism
   (repair from verdict 6a98cfea honored).
2. **Global radicality is not preserved by projection** (retained):
   `B = diag(0,1)`, `G = e_0` radical; project onto `span(e_0+e_1)`:
   `B(e_0+e_1, PG) = 1/2 != 0`.  This is why Test 4's delta-term is
   load-bearing even though the limit target is exactly radical.
3. **A finite prime cutoff can be exact by support and must not be
   relabeled a tail**: for two functions supported in a log-window of
   length `L`, the shift-correlation at `log k` vanishes identically once
   `log k > L` — a support fact, not an approximation; disk instance:
   `sourceModeCorrelation_add_neg_eq_zero_of_window_lt`.  Calling the
   `k <= m` sum a "truncation error" would invent a nonexistent tail term.
4. **Component norm sum is not the full signed consumer** (retained):
   4.1A cancellation plant + the 3C.1.4 corrected-vs-raw falsifier.

## FORBIDDEN CHECK

```yaml
radical_from_mellin_or_evenness: not inferred (plant 1; the source theorem
  is cited with its own mechanism and domain)
projected_radical_inferred: no (plant 2; Test 4 keeps delta explicit)
ambient_operator_or_compression: not used
full_pairing_replaced_by_component_norms: no
new_hypotheses_added: none (every unproved input is named OPEN)
selected_row_schedule_target_scale_rayleigh_altered: no
lean_numerics_aristotle: none
receipt: BASE_HEAD from live git rev-parse (6a98cfea...)
```

## PREDICTION CHECK

```text
P_RADICAL_DEFECT_1 = 0.82 (hTrial admits the theorem after endpoint/domain
  extension): PARTIALLY — the literal membership FAILS structurally (the
  paper's own obstruction: no nonzero simultaneously time- and band-limited
  function), but the REPAIRED form (near-radical with exponentially small
  budget, both defects (V1)/(V2) explicit) is exactly what the paper's
  near-radical language licenses.  The extension theorem is the right
  target; plain membership is not.
P_RADICAL_DEFECT_2 = 0.95 (primes above m vanish exactly): CONFIRMED on
  the finite span (disk lemma); on the full window domain the same support
  argument works pointwise, crosswalk theorem-sized (Test 3).
P_RADICAL_DEFECT_3 = 0.88 (selected row = normalized finite projection of
  one global E-star trial): CONFIRMED definitionally (gTrial chain,
  D0KTrialStage2).
P_RADICAL_DEFECT_4 = 0.68 (remaining wall is a window/projection defect
  norm, not a separate prime oscillation): SUPPORTED by this preflight's
  structure — IF (A) crosswalk and (B) near-radical budget land, the prime
  content is absorbed into full-form pairings of explicit defect terms;
  not yet proved.
LIKELIEST_FAILURE (SELECTED_PROLATE_ENDPOINT_DOMAIN_OR_GLOBAL_TO_WINDOW_
  FORM_CROSSWALK_GAP): OBSERVED — both named walls are exactly the two
  suppliers (A) and (B).
```

## RANKED OPEN SUPPLIERS AFTER THIS PREFLIGHT

```text
S1 (A): GLOBAL_WEIL_FORM_TO_PROJECT_WINDOW_FORM_EXACT_RESTRICTION —
        theorem-sized: support argument for primes + arch/W02 normalization
        match on the full H_m domain.
S2 (B): NEAR_RADICAL_BUDGET_FOR_TRUNCATED_PROLATE_ESTAR_TRIAL — new
        quantitative Poisson-mechanism theorem with (V1),(V2) as explicit
        exponentially small terms.
S3: WINDOW_PROJECTION_DEFECT_RATE — full-form pairing bounds for the three
        delta-pieces at o(m^{1/4}/L^{3/2}).
S4: |a_k| scalar bound (carried over).
```

The limit-target half of the old gap is CLOSED at paper level; the route
now runs entirely through S1-S3 without any component split and without a
separate prime-oscillation estimate — which, if it survives the next
adjudication, is the first representation in the whole 3C.1 chain where
the prime wall is not a standalone input.

SUCCESS_CODE_RETURNED: LIMIT_TARGET_RADICAL_ONLY_SELECTED_TRIAL_DOMAIN_OPEN
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
