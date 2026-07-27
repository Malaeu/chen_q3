# SOFT_3 — PRO VERDICT (Proshka V1, round 3: tails, target, mesh) — 2026-07-13

Status: `EXTERNAL_VERDICT_TRANSCRIPT_CONDENSED_FAITHFUL / AUTHORITY_FOR_SOFT_3_DAG / NOT_RH`
Channel: V1 (Proshka, breaker, kill+repair). Round 3.
Provenance: owner-pasted; materialized by Mythos (V2). Condensation note: the
mathematical statements, quantifiers, theorems, plants, and stop codes below
are verbatim-faithful; prose is compressed. Read together with Codex
`SOFT_1_..._2026-07-13.md` (type obstruction, code
SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC), which BLOCKS the prime/Gamma
decomposition assumed by Attack A until a linearity crosswalk exists (SOFT_2).

## TOP-LEVEL

```text
STATUS: REFUTED AS AUTOMATIC IMPLICATION
  (exact finite pairing formula =/=> pairing convergence)
Frozen accepted inputs: CONSTRUCTION_GAUGE vs LIMIT_UNIT split;
  gamma_0 = e^(a+ibz); distributional S2; anchor z=i/4; zeta(1/4)!=0; NOT_RH.
Route score 4/5. Progress class: FALSIFICATION_PROGRESS.
```

Soft roof re-confirmed VALID with anchor i/4: local boundedness + anchor +
pairing convergence for every phi in C_c^inf(I) + fixed zero-free gamma_0
=> cluster point = c*Xi*gamma_0 on I => (identity theorem) on S => (real-zero
roof + Hurwitz) RH. Distributional S2 genuinely replaces quantitative H3/H4 —
but only AFTER a true pairing-convergence theorem.

## ATTACK A — prime tails and the joint limit: KILL as currently imagined

Decompose <Fhat_i,phi> = G_i(phi) + P_i(phi) + C_i(phi) (Gamma/archimedean +
finite prime sum + exact corrections), i=(m,N). The identity alone says
nothing about i -> infinity. Four failure points:
 1. Joint index undefined: need an explicit object
    AdmissibleSoftSequence(m_j,N_j); since S2 needs only ONE subsequential
    limit, the weakest legal form is ONE explicitly chosen cofinal sequence,
    not a uniform theorem over the whole index product.
 2. Moving-tail defect: every fixed head converges while mass migrates
    through shells R_j < log n < R_j+1. Root cause: Lambda(n)/sqrt(n) is not
    summable by itself; smallness must come from the transform/kernel factor
    with decay constants UNIFORM along the chosen sequence. Q3 already has
    the lawful structure: a fixed heat scale gives log-Gaussian decay, after
    which the prime tail is estimated independently of the finite cutoff.
 3. LIMIT_UNIT must be one fixed (a,b), not (a_j,b_j): a moving unit can
    grow, oscillate, destroy pairing convergence, move mass between test
    frequencies.
 4. Prime and Gamma converge only JOINTLY: forbidden to bound P^{>R} and
    G^{>R} separately if the formula converges only after cancellation; the
    correct object is T_i^{>R} = P_i^{>R} + G_i^{>R} + C_i^{>R}
    (same lesson as the Poisson-ledger audit: componentwise triangle bounds
    can destroy real cancellation).

### Weakest repaired theorem — SOFT_3B_UniformRenormalizedPrimeGammaTail
There exists ONE admissible sequence i_j=(m_j,N_j) such that for every fixed
phi in C_c^inf(I) and every eps>0 there exist R and j0 with:
  for all j>=j0: |T_{i_j}^{>R}(phi)| < eps,  and  |T_infty^{>R}(phi)| < eps;
and for every fixed R: T_{i_j}^{<=R}(phi) -> T_infty^{<=R}(phi).
Then the eps/3 argument gives <Fhat_{i_j},phi> -> T_infty(phi).
CRITICAL QUANTIFIER ORDER: forall phi, forall eps, exists R, exists j0,
forall j>=j0.  (forall j exists R_j = SOFT_JOINT_LIMIT_QUANTIFIER_MISSING.)

## ATTACK B — target pairing and hidden RH import: default REFUTED

Distinguish three objects: Xi, Xi'/Xi, sum_rho delta_rho. Explicit formula
naturally produces zero-counting distributions, log-derivatives, Weil
functionals — not Xi itself. The identity "prime/Gamma side =
c<Xi*gamma_0,phi>" must be proved as a SOURCE-TARGET IDENTITY, never declared
by notation similarity. Fatal substitutions:
 1. Critical line embedded in the zero sum: 2*sum_{gamma>0} H(gamma) as the
    full zero side ALREADY assumes rho = 1/2 + i*gamma. Unconditional forms:
    sum over ALL nontrivial rho in the plane, or no zero side at all.
    Verified low zeros are finite calibration only, never a universal
    identity.
 2. Formula actually yields -Xi'/Xi: integrating a logarithmic derivative
    needs branch choice, constant control, a path avoiding zeros, and
    knowledge of the divisor — on a strip with potential off-axis zeros this
    can be exactly the RH content. The i/4 anchor fixes the multiplicative
    constant only AFTER lawful integration is proved; it does not remove the
    branch/divisor wall. Stop: SOFT_TARGET_IS_LOG_DERIVATIVE.
 3. gamma_0 := F/(c*Xi) post hoc — RH repackaged (known).

Lawful routes: B1 theta/Mellin (cleanest: Xi identified via its unconditional
theta/Mellin representation; the prime/Gamma finite formula is then proved
equal to that same distribution without zero-location input); B2 direct
prime/Gamma identity whose target is honestly phi -> int_I Xi*gamma_0*phi
(exact normalization + transform convention required); B3 full-zero formula
over the complete multiset sum_rho without Re rho = 1/2, followed by a
separate proof that the result equals the Xi-pairing, not a zero-counting
distribution.

### Weakest repaired theorem — SOFT_3C_UnconditionalTargetPairing
For every phi in C_c^inf(I) prove unconditionally
  T_infty(phi) = c * int_I Xi(x) gamma_0(x) phi(x) dx,
with c!=0 fixed by the i/4 anchor; gamma_0 fixed before the theorem; no RH;
no critical-line-only zero sum; no BFM/modulus-square input; target exactly
Xi*gamma_0, not Xi'/Xi and not a zero measure.
Stops: SOFT_CRITICAL_LINE_ZERO_SUM_SMUGGLED / SOFT_TARGET_DISTRIBUTION_MISMATCH /
SOFT_TARGET_IS_LOG_DERIVATIVE / SOFT_GAMMA0_POSTHOC_QUOTIENT /
SOFT_PAIRING_RH_CONDITIONAL_IMPORT.

## ATTACK C — condensing grid: KILL without a regularity theorem

mesh -> 0 alone is insufficient. Counterexample: f_j(x) = sin(pi(x-a)/h_j)
vanishes at every grid point yet has sup norm 1. Dense sample agreement does
not imply function agreement; a uniform modulus of continuity is required.

### Minimal mesh theorem — D06_CompactMeshPairingLift (proof included)
Let I=[a,b], U_eta a fixed complex eta-neighborhood of I; F_j, H holomorphic
on U_eta with sup_j sup_{U_eta} |F_j| <= M_F, sup_{U_eta} |H| <= M_H; grids
Gamma_j subset I with fill distance h_j -> 0; sample error
eps_j := max_{y in Gamma_j} |F_j(y)-H(y)| -> 0. Cauchy estimates give
sup_I |F_j'| <= 2 M_F/eta and sup_I |H'| <= 2 M_H/eta, hence
  ||F_j - H||_{L^inf(I)} <= eps_j + (2(M_F+M_H)/eta) h_j -> 0,
and for every phi in L^1(I):
  |<F_j - H, phi>| <= ||phi||_1 (eps_j + (2(M_F+M_H)/eta) h_j) -> 0.
Responsibility split (no DAG cycle): D0.6 proves ONLY the generic
mesh/Cauchy lemma; SOFT-S1 supplies M_F on U_eta; the target supplies M_H;
grid construction supplies h_j -> 0; pairing computation supplies eps_j -> 0.
Stops: D06_MESH_FILL_DISTANCE_MISSING / D06_UNIFORM_COMPLEX_NEIGHBORHOOD_MISSING /
D06_MESH_DERIVATIVE_BOUND_MISSING / D06_GRID_ALIASING_FATAL /
D06_LATE_S1_IMPORT_CYCLE.

## REGISTERED PLANTS (validator obligations)

Plant A moving prime shell -> must fire SOFT_JOINT_LIMIT_QUANTIFIER_MISSING.
Plant B critical-line replacement 2*sum_{gamma>0} -> must fire
  SOFT_CRITICAL_LINE_ZERO_SUM_SMUGGLED.
Plant C grid aliasing (zero on all nodes, sup 1) -> must fire
  D06_GRID_ALIASING_FATAL.

## THEOREM DAG (round-3 canonical)

SOFT-3.0 ExactFinitePairingIdentity  ->  SOFT-3.1 AdmissibleJointSequence
 -> SOFT-3.2 UniformRenormalizedPrimeGammaTail
 -> SOFT-3.3 UnconditionalTargetPairing
 -> SOFT-3.4 PairingConvergence on C_c^inf(I)
 -> (with S1 NormalFamily and anchor i/4)
 -> SOFT-S2 cluster point = c*Xi*gamma_0
 -> (with H2a-cofinal + Hurwitz roof) -> RH.
Backup branch: grid values + D06_CompactMeshPairingLift -> SOFT-3.4 (does not
replace the prime-tail theorem if grid values come from truncated sums).

STRONGEST ATTACK: "Your finite pairing formula is true for every (m,N), but
its new prime terms live ever deeper in the tail. You proved convergence of
every fixed head, not convergence of the full distribution."

META: "prove S2" compressed to TWO walls — uniform combined prime/Gamma tail
AND unconditional target distribution identity. Smallest gap:
SOFT_3B_UniformRenormalizedPrimeGammaTail (contingent on SOFT_2 linearity).

NOT_RH.
