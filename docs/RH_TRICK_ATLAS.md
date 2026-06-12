# RH Trick Atlas

Date: 2026-06-12

Purpose: collect reusable mathematical proof tricks that may replace brute-force
Lean or interval computation in RH/Q3 work.

Working motto: computation finds the wall; mathematics changes the room; Lean
verifies that the new wall is gone.

This is strategy documentation only.  It does not claim a proof of RH, does not
mutate the active route, does not edit Lean files, and does not touch `Q3.Main`.
Every idea below must still become either a checked Lean theorem, a hole-free
Aristotle output integrated through Lean, or a mathematically verified external
argument before it can affect the mainline.

## Scan Rule

The atlas is scanned by task signature, not by mathematical field.  Each card
therefore has:

- `Status`: `applied`, `hot candidate`, `candidate`, `parked`, or
  `awaiting-research`.
- `Applicability signature`: the shape of a Q3 blocker that makes the trick
  relevant.
- `Dropped structure / danger`: the K3 check.  This field must name a concrete
  lost structure, counterexample pattern, or repo-local risk.  "Be careful" is
  not enough.

Use a trick only when it compresses proof work while preserving the exact object
that the route needs.  A successful trick should turn a large family of scalar
checks into one of:

- a structural identity;
- a finite jet or interpolation theorem;
- a margin-accounting certificate;
- a positivity-cone or dual witness;
- a Fourier-side or explicit-formula rewrite with checked normalization.

## Source Anchors

External anchors checked on 2026-06-12 for cards 1-3:

- Viazovska, "The sphere packing problem in dimension 8",
  Annals of Mathematics 185 (2017), 991-1015,
  https://doi.org/10.4007/annals.2017.185.3.7; arXiv:
  https://arxiv.org/abs/1603.04246.
- Cohn, Kumar, Miller, Radchenko, Viazovska, "Universal optimality of the
  E8 and Leech lattices and interpolation formulas", Annals of Mathematics
  196 (2022), 983-1082,
  https://arxiv.org/abs/1902.05438.
- Guth and Maynard, "New large value estimates for Dirichlet polynomials",
  Annals of Mathematics 203 (2026), no. 2,
  https://doi.org/10.4007/annals.2026.203.2.6; arXiv:
  https://arxiv.org/abs/2405.20552.

Local anchors found by exact repo search:

- `q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md`
- `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_margin_ledger.md`
- `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/STRATEGIC_CONTEXT.md`
- `q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`
- `q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md`
- `q3.lean.aristotle/docs/INSIGHTS.md`
- `q3.lean.aristotle/docs/insights/h1_po3_square_2d3_stable_adaptive_shifts_reconciled_2026_04_27.md`
- `q3.lean.aristotle/docs/insights/connes_zeta_spectral_triples_2026_01_29.md`
- `q3.lean.aristotle/docs/insights/q3_psdpd_step25_certificate_family_manifest_2026_05_03.md`
- `q3.lean.aristotle/docs/insights/q3_psdpd_step26_finitecert_ledger_2026_05_03.md`
- `q3.lean.aristotle/docs/insights/q3_psdpd_step32f_coeff_payload_import_plan_2026_05_24.md`

Expected local docs not found by exact filename search on 2026-06-12:
`analytic_plan_L3`, `c_sat_origin`, `uncertainty_map`.  When those files are
added or renamed into discoverable paths, update cards 4-7 to point to them
directly.

## 1. Viazovska Magic Auxiliary Function

- Status:
  hot candidate.

- Trick name:
  Magic auxiliary function / saturating linear-programming witness.

- Applicability signature:
  Infinite-class optimization appears equivalent to the existence of one
  extremal function satisfying sign constraints on both sides of Fourier
  transform.

- Original theorem/problem:
  The sphere packing problem in dimension `8`: prove the `E8` lattice packing
  is optimal.  Cohn-Elkies linear programming reduces the packing bound to a
  dual auxiliary function; Viazovska constructed the magic function from
  modular forms.

- Transformed object:
  "Prove optimality for every packing" becomes "construct one function `f`
  whose physical-side and Fourier-side signs, zeros, and equality cases
  saturate the linear-programming bound."

- Preserved structure:
  Poisson summation, Fourier transform symmetry, radial Schwartz class, the
  equality shell data, and dual cone positivity.

- Dropped structure / danger:
  K3 check: the `E8` proof has exact shell multiplicities and modular-form
  identities.  In Q3, a numerical extremizer for a test function `h` may have no
  closed form and may satisfy the right sign pattern only on the sampled grid.
  That would be only a prior for `h*`, not a proof object.

- RH/Q3 analogue:
  Weil positivity also has two sides: the `u`/test-function side with support,
  kernel, and boundary restrictions, and the zero/gamma/prime side controlled
  through the explicit formula.  The `E5'`-type question should be phrased as:
  is there a magic test function `h*` whose prime-side or edge defect collapses
  by identity, not by accumulated interval estimates?

- Step33 or L3 use-case:
  For Step33A.1-A, search for a local magic majorant for the worst raw-Omega
  Taylor cell so that `hRawCenterCoeffAbs` and the residual-derivative norm
  bound come from one structural witness.  For L3, search for a prime-comb test
  function whose prime-side defect cancels by transform-side structure before
  scalar hbox generation.

- Concrete next experiment:
  CC-style numerical optimization on a small `K`: optimize a candidate test
  function `h` under two-sided sign/support constraints, inspect the extremizer,
  and record whether its shape suggests a closed-form kernel, modular object,
  prolate/Sonin object, or only a numerical ansatz.

- Failure mode:
  The experiment produces an attractive extremizer but no exact identity.  Then
  the card degrades into "shape prior for `h*`"; it must not be reported as
  Step33, L3, or RH progress.

## 2. Cohn-Kumar-Miller-Radchenko-Viazovska Interpolation

- Status:
  parked candidate.

- Trick name:
  Fourier interpolation / sample-and-derivative reconstruction.

- Applicability signature:
  Two-sided data on a discrete set appear to determine, or sharply constrain, a
  whole admissible function.

- Original theorem/problem:
  Universal optimality of `E8` and the Leech lattice.  CKMRV prove an
  interpolation theorem reconstructing radial Schwartz functions from values
  and radial derivatives of `f` and `fhat` at special radii.

- Transformed object:
  A continuous radial Schwartz function is replaced by finite/discrete nodal
  data plus an interpolation basis.

- Preserved structure:
  Fourier duality, radial Schwartz class, equality-shell nodes, derivative
  data, and the sharp linear-programming framework.

- Dropped structure / danger:
  K3 check: CKMRV nodes are special radii tied to dimensions `8` and `24`.
  Zeta zeros are not automatically an interpolation set for the Q3 test class.
  A collocation formula at zeros could reconstruct only a diagnostic surrogate
  or require unproved completeness of the zero-data basis.

- RH/Q3 analogue:
  Ask whether admissible Q3 test functions can be reconstructed or controlled
  from values at zeta zeros plus edge/boundary data.  If yes, positivity could
  be reduced to node inequalities, with a rhyme to finite-prime extremization
  in Connes/Consani-style notes.

- Step33 or L3 use-case:
  Step33's active direct derivative surface asks for endpoint/center data and
  derivative bounds on a cell.  A local interpolation receiver could certify an
  entire refined subchunk from a small jet package rather than replaying scalar
  expressions.  For L3, the analogue is replacing dense prime-shift sampling by
  certified values at structural nodes.

- Concrete next experiment:
  Research sub-agent task: literature check for "Fourier interpolation zeta
  zeros", Radchenko-Viazovska follow-ups, and any zero-set interpolation
  theorem compatible with Weil test functions.  Keep it parked until a theorem
  shape exists.

- Failure mode:
  The interpolation theorem exists only for a different function class, loses
  the exact support/boundary structure, or requires assumptions equivalent to
  the target positivity.

## 3. Guth-Maynard Dirichlet Polynomial Large Values

- Status:
  candidate / adjacent.

- Trick name:
  Large-value stratification by structure versus randomness.

- Applicability signature:
  A proof is stuck on many "bad" large values or tight cells, and the bad set
  may have additive, difference-set, row/chunk, or phase structure.

- Original theorem/problem:
  Guth and Maynard prove new bounds for how often Dirichlet polynomials can take
  large values, especially near the critical size `N^(3/4)`, with consequences
  for zero-density estimates and primes in short intervals.

- Transformed object:
  Pointwise large-value control becomes a structural analysis of the large-value
  set via spacing, additive energy, difference sets, incidence/moment bounds,
  and a split between structured and unstructured cases.

- Preserved structure:
  Dirichlet polynomial coefficients, frequency data, spacing of large-value
  points, and the zeta/prime estimate interface.

- Dropped structure / danger:
  K3 check: the Guth-Maynard transfer is blocked for our current use by their
  coefficient/range hypotheses, especially the `l_infty`-type bounded
  coefficient regime.  Q3 needs an `l2` or finite-certificate version before it
  can become more than adjacent technology.  This is the `GM-adjacent, not
  exactly our hole` warning (`D17/K7`).

- RH/Q3 analogue:
  Treat the margin-ledger bad cells as a structured set.  If tight cells share
  row, chunk, shift, phase, or derivative signatures, close them by a family
  identity.  If they are dispersed, try an aggregate energy or moment bound
  that reduces the number of local certificates.

- Step33 or L3 use-case:
  Step33 has `2392` missing Taylor/model cells in the active ledger.  Before
  payload replay, cluster by residual-derivative shape and row/chunk geometry.
  For L3 prime shifts, group live shifts by logarithmic spacing and
  additive/difference energy before hbox generation.

- Concrete next experiment:
  Build a diagnostic "bad-cell energy" report from
  `a_margin_ledger.{json,md}`: threshold by remaining slack, compute clustering
  in `(row, parentChunk, subchunk)` and prime/log-shift coordinates, and record
  whether the worst cells form a small structured family.

- Failure mode:
  The energy decomposition only relabels the same scalar obligations, or the
  aggregate estimate cannot feed the exact Step33 receiver fields.  If no `l2`
  version appears, keep the card adjacent.

## 4. Ratchet / Self-Improvement

- Status:
  applied; plan B for `E5'`.

- Trick name:
  Ratchet inequality / bootstrap self-improvement.

- Applicability signature:
  A weak estimate either improves itself under iteration or forces a rigid
  structure in every counterexample.

- Original theorem/problem:
  Self-improvement patterns in incidence geometry and additive combinatorics
  include the Wang-Zahl style loop: failure of an estimate forces structured
  offenders, and a separate lemma kills that structure.

- Transformed object:
  One sharp estimate becomes a loop:
  weak bound -> bad structure if improvement fails -> structure-kill lemma ->
  improved bound.

- Preserved structure:
  Monotonicity, scale parameters, noncircular use of previous bounds, and a
  stopping criterion that is independent of numerical wishful thinking.

- Dropped structure / danger:
  K3 check: the loop is circular if the "bad structure" lemma uses the
  improved estimate it is meant to prove.  Repo-local version: using
  `C_k ||epsilon_k|| -> 0` before proving the shifted row-error estimate would
  fake the PO3 stable-projection closure.

- RH/Q3 analogue:
  When `E5'` or an L3 obstruction does not close directly, prove that any
  failure has rigid shape, then kill that shape.  This matches the parked H1
  route's stable-projection logic: row error plus conditioning either captures
  the packet or records a route kill.

- Step33 or L3 use-case:
  In Step33A.1-A, close easiest margin tiers first, recompute budgets, and see
  whether hard cells become structurally forced.  In L3, use closed
  prime-shift hboxes to tighten the next live support filter.

- Concrete next experiment:
  Write a small offline ratchet schedule: sort Step33 ledger cells by slack,
  simulate closure of easiest tiers, recompute row/local budgets, and list the
  remaining offender structures.  Do not change any theorem statement.

- Failure mode:
  The ratchet terminates only numerically, depends on unproved generated
  payloads, or shrinks the domain at each iteration until the original theorem
  is gone.

- Related local references:
  `ACTIVE/PHASE_MONITOR.md`,
  `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md`,
  `docs/insights/h1_po3_square_2d3_stable_adaptive_shifts_reconciled_2026_04_27.md`.
  Expected local reference to wire when present: `analytic_plan_L3` /
  `L3_clean` DAG.

## 5. Margin Ledger

- Status:
  applied.

- Trick name:
  Margin Ledger / proof-budget accounting.

- Applicability signature:
  A numerical or interval proof has many local error terms, and it is unclear
  which ones are proof blockers versus diagnostics.

- Original theorem/problem:
  Certified numerical proofs succeed only when every local error contribution
  is assigned to an explicit available slack budget.

- Transformed object:
  A large family of inequalities becomes a budget law:
  `certified_error_budget <= available_cert_slack`, with provenance and active
  blocker status for every term.

- Preserved structure:
  Inequality direction, local versus global slack, error provenance, active
  theorem fields, and the distinction between proof data and diagnostics.

- Dropped structure / danger:
  K3 check: a ledger is not a proof.  Positive slack is useful only if every
  ledger field maps to a checked theorem field or generated certificate.  In
  the older `mu`-book / anti-circular accounting language (`K5/D13`), the
  ledger dies if `epsilon_n` is not polynomially controlled; the sufficient
  survival threshold is of the form `epsilon_K <= C * K^(-c)`.

- RH/Q3 analogue:
  Keep proof-budget visibility before payload generation.  The ledger must say
  exactly which analytic fields remain open and which artifacts are merely
  informational.

- Step33 or L3 use-case:
  Step33A.1-A already uses
  `ACTIVE/requests/step33_bootstrap/a_margin_ledger.{json,md}`.  It records
  `worstRemainingSlack`, active blockers, readiness, and proof-input coverage.
  The same shape should be used for L3 hboxes: separate live-support slack,
  transform-side slack, hbox radius budget, and global PSD aggregation.

- Concrete next experiment:
  Add, conceptually first, a `trick_source` column to the ledger:
  `direct_taylor`, `interpolation`, `fourier_rewrite`, `dual_witness`,
  `ratchet`, or `unknown`.  This makes the intended closure mechanism visible
  without mutating the route.

- Failure mode:
  The team reports ledger positivity as Step33 closure, or generated diagnostic
  margins are treated as trusted Lean facts.

- Related local references:
  `ACTIVE/requests/step33_bootstrap/a_margin_ledger.md`,
  `ACTIVE/requests/step33_bootstrap/a_margin_ledger.json`,
  `q3.lean.aristotle/scripts/q3_psdpd_step33_a_margin_ledger.py`,
  `docs/insights/q3_psdpd_step26_finitecert_ledger_2026_05_03.md`.
  Expected local references to wire when present: `uncertainty_map`,
  `c_sat_origin`.

## 6. Fourier-Side Rewrite / Explicit Formula

- Status:
  applied.

- Trick name:
  Fourier-side rewrite / explicit-formula transfer.

- Applicability signature:
  A heavy object is diagonal, sparse, or sign-visible on the other side of the
  transform mirror.

- Original theorem/problem:
  Explicit formulas relate zeros, primes, archimedean terms, and Fourier
  transforms of test functions.  Weil-style positivity criteria use this
  transfer to move a question to the side where sign or support is visible.

- Transformed object:
  A difficult zero-side, physical-side, or raw integral inequality is rewritten
  as a prime-side or Fourier-side expression plus controlled archimedean and
  boundary terms.

- Preserved structure:
  Transform duality, test-function admissibility, support/decay, gamma or
  archimedean terms, boundary/cap terms, and exact normalization of signs.

- Dropped structure / danger:
  K3 check: normalization mistakes are fatal.  Repo-local counterexample
  pattern: `a_star` versus `P_A` and raw-Omega versus centered `A` can make a
  true-looking proof certify the wrong object.  Another concrete risk is the
  trig-Gram identity: `spec(F^T F) = spec(F F^T)` preserves nonzero spectrum,
  but not arbitrary coordinate-level fields expected by a receiver.

- RH/Q3 analogue:
  Use the explicit formula or Fourier mirror when interval arithmetic is
  working too hard on the wrong side.  The rewrite is admissible only if it
  returns to the exact active Q3 object with all normalization terms named.

- Step33 or L3 use-case:
  Step33A.1-A should audit which raw-Omega analytic tails have closed-form
  mirror-side identities.  This is a direct candidate to replace weeks of
  interval arithmetic, but only if it lands back in the raw-Omega direct
  chunk-integral receiver.  For L3, preserve exact log-shift and prime-weight
  normalizations.

- Concrete next experiment:
  For the first tight Step33 raw-Omega cell, produce a side-by-side diagnostic:
  direct Taylor bound versus Fourier/explicit-formula-derived bound, with every
  gamma, boundary, cap, scale, and sign term named.  Accept the rewrite only if
  it lowers the margin budget and maps to existing receiver fields.

- Failure mode:
  The rewrite proves a cleaner inequality for a nearby transformed model but
  does not reconstruct the active raw-Omega A hbox.  Losing a gamma, boundary,
  or cap term turns cancellation into an untracked assumption.

- Related local references:
  `TRICKS_LIBRARY.md`,
  `ACTIVE/requests/step33_bootstrap/STRATEGIC_CONTEXT.md`,
  `docs/insights/connes_zeta_spectral_triples_2026_01_29.md`,
  `docs/insights/heat_localization_kills_primes_2026_01_16.md`.
  Expected local references to wire when present: `analytic_plan_L3`,
  `uncertainty_map`.

## 7. Dual Certificate / Positivity Cone

- Status:
  applied pattern / hot candidate for stronger certificates.

- Trick name:
  Dual certificate / positivity cone.

- Applicability signature:
  A positivity claim over many primal objects may be checked by one finite
  object in the dual cone.

- Original theorem/problem:
  Linear-programming, SOS/Lasserre, MSS-style barriers, and Cohn-Elkies sphere
  packing bounds prove primal positivity or optimality by a dual witness in a
  positivity cone.

- Transformed object:
  A universal inequality over many primal objects becomes one explicit dual
  certificate with cone membership, complementary slackness, and exact model
  alignment.

- Preserved structure:
  Convex duality, positivity cone membership, equality cases, basis/Gram
  conventions, boundary conditions, and exact rational or symbolic certificate
  data.

- Dropped structure / danger:
  K3 check: a numerical PSD table is not a dual proof.  The cone must match the
  exact finite model, including Gram correction and boundary null conditions.
  A dual witness for raw coordinates is misleading when the route requires the
  Gram-corrected centered coefficient model.

- RH/Q3 analogue:
  Prove positivity by certificate objects in the same cone as the active
  Weil/Q3 finite model.  This is the shared skeleton behind Viazovska,
  SOS/Lasserre, and finite PSD certificate checks.

- Step33 or L3 use-case:
  Step33 already wants `ActiveCenteredCoeffEntryHboxCert`, finite analytic
  positivity, and singleton `DirectedCertFamily` handoff.  Keep those
  certificate objects central, not the scalar tables.  For an L0/L3 diagnostic
  slice, an SOS decomposition of `Q_W|_{V_n}` would let Lean verify positivity
  by matrix multiplication rather than interval replay.

- Concrete next experiment:
  CC/SOS experiment: factor the already computed `K=2` matrix as an SOS or
  rational Cholesky-like dual certificate, then check whether the factorization
  certifies the same inequality and coordinate model that the current hbox path
  targets.

- Failure mode:
  The certificate is feasible only numerically, ignores boundary leakage, or
  proves positivity in the wrong cone.

- Related local references:
  `Q3_OBSTRUCTION_ATLAS.md`,
  `docs/insights/q3_psdpd_step25_certificate_family_manifest_2026_05_03.md`,
  `docs/insights/q3_psdpd_step32f_coeff_payload_import_plan_2026_05_24.md`.
  Expected local references to wire when present: `c_sat_origin`,
  `analytic_plan_L3`.

## 8. MSS Interlacing

- Status:
  awaiting-research.

- Trick name:
  Marcus-Spielman-Srivastava interlacing families / barrier method.

- Applicability signature:
  Need to prove that some choice among many finite signed or weighted objects
  has a good spectral floor, without enumerating all choices.

- Original theorem/problem:
  MSS use interlacing families and barrier methods to prove existence of
  partitions/operators with controlled spectra, famously resolving Kadison-
  Singer-related problems.

- Transformed object:
  A combinatorial search over many finite objects becomes a polynomial or
  barrier argument proving that one choice has controlled eigenvalues.

- Preserved structure:
  Finite-dimensional spectrum, characteristic polynomials, interlacing, and
  positivity of the relevant operator family.

- Dropped structure / danger:
  K3 check: MSS gives existence in a very specific random/finite operator
  setup.  It does not automatically supply a constructive Lean certificate for
  the active Q3 basis, nor does it preserve boundary/null conditions unless the
  family is built with them.

- RH/Q3 analogue:
  Candidate for finite certificate selection when many hbox/packet choices
  exist and direct enumeration is a scalar swamp.

- Step33 or L3 use-case:
  Possible future use for selecting a good finite packet or split schedule
  before hbox generation.

- Concrete next experiment:
  Research note only: identify whether any current Step33/L3 finite selection
  problem has an interlacing-family formulation.

- Failure mode:
  The family is not closed under the required Gram-corrected model, or the
  theorem is purely existential and gives no certifiable witness.

## 9. Selberg Extremal Functions

- Status:
  awaiting-research.

- Trick name:
  Selberg/Vaaler extremal majorants and minorants.

- Applicability signature:
  Need to replace sharp cutoff, interval indicator, or support condition by a
  bandlimited majorant/minorant with controlled Fourier support.

- Original theorem/problem:
  Selberg extremal functions solve sharp approximation problems for indicators
  by entire/bandlimited majorants and minorants, widely used in analytic number
  theory.

- Transformed object:
  A hard discontinuous cutoff becomes a smooth or bandlimited extremal function
  with exact integral and support control.

- Preserved structure:
  Fourier support, one-sided inequality, integral error, and compatibility with
  explicit formula inputs.

- Dropped structure / danger:
  K3 check: one-sided majorants can destroy sign-sensitive cancellation.  In
  Q3, a Selberg majorant that widens support may violate the exact support or
  boundary-null hypotheses of the active test class.

- RH/Q3 analogue:
  Useful when a cutoff creates interval arithmetic blow-up but a bandlimited
  replacement keeps the explicit formula clean.

- Step33 or L3 use-case:
  Candidate for L3 support filters and for replacing hard windows in prime-side
  hbox generation.

- Concrete next experiment:
  Research note only: compare one L3 support window against a Selberg-style
  bandlimited majorant and measure the margin ledger effect.

- Failure mode:
  The majorant buys smoothness but pays too much support/error budget, or it no
  longer maps to the active receiver.

## 10. Log-Gas Large Deviations

- Status:
  awaiting-research.

- Trick name:
  Log-gas large deviations / Coulomb energy rate function.

- Applicability signature:
  A zero/particle configuration looks governed by a global energy functional,
  and the desired estimate is a rare-event exclusion rather than a pointwise
  bound.

- Original theorem/problem:
  Log-gas and random-matrix large-deviation principles control atypical
  configurations through an energy/rate functional.

- Transformed object:
  A combinatorial or pointwise configuration problem becomes an energy barrier
  problem.

- Preserved structure:
  Repulsion, global energy, scaling regime, and rate-function normalization.

- Dropped structure / danger:
  K3 check: random-matrix/log-gas analogies do not prove deterministic zeta
  statements.  Repo-local danger: averaged or probabilistic control can miss a
  deterministic microcluster obstruction, exactly the kind of route-kill issue
  tracked in `ROUTE_KILL_REGISTRY.md`.

- RH/Q3 analogue:
  Possible heuristic or research guide for identifying impossible zero
  clusters, not a proof input unless a deterministic theorem is supplied.

- Step33 or L3 use-case:
  Parked.  Could help prioritize bad-cell or bad-zero cluster diagnostics, but
  does not feed Step33 hboxes directly.

- Concrete next experiment:
  Research note only: map current bad-cell clustering metrics to an energy-like
  statistic and check whether it predicts the same worst cells as the margin
  ledger.

- Failure mode:
  The statistic is predictive but not certifying, or it replaces deterministic
  route-kill criteria with probabilistic language.

## Practical Priority

For the active Step33/L3 environment, the most robust order is:

1. Keep the Margin Ledger as the control surface.
2. Use Fourier-side rewrites when normalization back to raw-Omega is explicit.
3. Try Viazovska-style magic-function search on the smallest tight diagnostic
   slice.
4. Try CKMRV-style local interpolation only after a theorem-shaped receiver is
   visible.
5. Use Guth-Maynard-style stratification to decide whether cells should be
   closed by family identities or local payloads.
6. Use ratchet/self-improvement only with a separately named structure-kill
   lemma.
7. Reserve dual/SOS certificates for slices where the exact cone and basis are
   already pinned.

None of these steps closes Step33 or RH by itself.  They are ways to choose
smaller, more structural proof experiments.

## Experiment Cards

Experiment cards are route-local tests of atlas tricks.  They are not proof
status changes until the named Lean receiver compiles without holes and the
active monitor/report records the validation.

- `EC-001`: A-side interpolation replacement probe.
  Path:
  `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_side_interpolation_replacement_probe.md`.
  Atlas anchors: card 2 `Cohn-Kumar-Miller-Radchenko-Viazovska
  Interpolation` and card 5 `Margin Ledger`.  Target: first raw-Omega
  Step33A.1-A worst cell, replacing scalar Taylor/interval replay by a finite
  rational interpolation or jet certificate for `hRawCenterCoeffAbs` and
  `hResidualDerivBoundOnCell`.
