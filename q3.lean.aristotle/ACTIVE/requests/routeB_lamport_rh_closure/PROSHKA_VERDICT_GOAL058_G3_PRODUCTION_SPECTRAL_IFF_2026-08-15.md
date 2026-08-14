# Proshka verdict — Goal 058 G3 production spectral iff

Date: 2026-08-15
Conversation: `6a7afc0e-2aec-83eb-a9ca-469b44c84f83`
Evidence HEAD: `2755daff538c1b1da905ff360d1cc0d5bc39cce1`
Request commit: `7e04518b5e10f109550f8bbb0a91dd934b97df30`
Request SHA-256: `f8b095440ae647a9d3ab56bd095bfe60f0d3829e23a035c1a77a6afc95e56419`

## Transport receipt

The immutable GitHub blob and raw endpoints returned `CACHE_MISS`.  Proshka
stopped fail-closed with `NOT_ADJUDICATED`.  The same transaction was then
repaired by pasting the exact 7,279-byte UTF-8 request into the living chat.
The first transport stop reported `4m04s`; the substantive repaired judgment
reported `8m17s`.  `Answer now` was shown and was never clicked.

## Decision

`B — PRODUCTION_ROOT_TO_CARRIER_ONE_DIRECTION_FIRST`

The full production biconditional is not ready.  The honest first direction is
square-summable normalized DLMF left row to one indexed finite-limit carrier.

## Exact first Lean head selected by Proshka

```lean
namespace Q3.RouteB

theorem
    mode4DLMF3035EvenLeftCoefficient_sqSummable_imp_exists_finiteLimitSpectrum
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ < 20)
    (hL2 :
      Summable
        (fun q : ℕ =>
          ‖mode4DLMF3035EvenLeftCoefficient
              (mode4JacobiG mProject) Λ q‖ ^ 2)) :
    ∃ j : ℕ,
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) j = Λ
```

The strict endpoint hypothesis `Λ < 20` is load-bearing: the current backend
does not supply the two-sided endpoint argument at `Λ = 20`.

## Proof chain selected

1. `hL2` gives the literal DLMF characteristic equation through
   `mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable`.
2. The exact split adapter at `2 * (K - 1)` gives
   `mode4RootFunction mProject K Λ = 0`, hence the literal Schur matrix is
   singular.
3. The one-dimensional kernel and quadratic crossing permit nonsingular
   endpoints `Λminus < Λ < Λplus < 20` with a strict negative-count jump.
4. At both endpoints,
   `mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix`
   transports the literal counts to the finite truncations.
5. The full finite DLMF spectrum crosswalk rewrites those counts as finite
   ordered eigenvalue counts.
6. If `r` is the lower endpoint count, then eventually
   `Λminus ≤ mode4DLMFEvenFiniteEigenvalue G d r < Λplus`.
7. Fixed-index convergence sends that finite value to
   `mode4ClassicalEvenEigenvalue G r`.
8. Shrinking the isolating interval gives
   `mode4ClassicalEvenEigenvalue G r = Λ`.

This direction needs neither global carrier growth nor a carrier-tail binder.
It forces any independently supplied degree-four square-summable DLMF row onto
the internal finite-limit carrier.  It does not prove that every carrier value
produces a root.

## Exact reverse wall

```lean
theorem
    mode4ClassicalEvenEigenvalue_eq_imp_literalSchur_det_eq_zero_of_lt_twenty
    (mProject K j : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ < 20)
    (hcarrier :
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) j = Λ) :
    (mode4HermitianSchurMatrix mProject Λ K).det = 0
```

At `Λ = carrier j`, the separated carrier-count theorem is unusable.  The
missing proof is a singular-endpoint contradiction: assume `det ≠ 0`, obtain
local constancy of the literal negative count, transport the same count to
two nearby finite sections, and contradict convergence of the `j`-th finite
eigenvalue through that interval.  This is not yet a public theorem.

## K1–K5 dispositions

- K1 — killed. `mode4TailSeparationThreshold` is invented.  Use the literal
  `hsep` binder.
- K2 — killed. `∀ j, carrier j ≠ Λ → True` is vacuous.  The selected direction
  takes no carrier-separation binder.
- K3 — killed as duplicate.  The proposed `GrowthDichotomy` supplies no new
  source fact; the proved l2 crosswalk already excludes the nonmatching
  dominant branch and proves uniqueness against the recessive tail.
- K4 — repaired for the selected direction.  The local literal count jump pins
  one finite eigenvalue index without a global carrier tail.  K4 remains a
  wall for global finite-head counts.
- K5 — open, and exactly the reverse-direction wall described above.

## Cheapest falsifier

For the free half-line Jacobi matrix with Dirichlet finite sections, every
fixed finite index tends to the essential-spectrum edge `-2`, while `-2` has
no nonzero l2 eigenvector.  Therefore a fixed-index finite limit does not imply
an l2 solution without compactness, a literal-root theorem, or the K5
local-count contradiction.  This kills the reverse implication from the
finite-limit facts alone.

## Aristotle boundary

`NOT_READY`.

The proposed `GrowthDichotomy` task is a duplicate.  The genuine first work is
Codex-local assembly of the one-direction production theorem against exact
current declaration names.  No Aristotle owned file or target is authorized.

## Stop and status

`G3_ROOT_TO_FINITE_LIMIT_CARRIER_DIRECTION_READY_CARRIER_TO_LITERAL_ROOT_SINGULAR_ENDPOINT_BRIDGE_MISSING`

G1 `OPEN`; G3 `OPEN`; Route B `CHALLENGER_NOT_RH`; no route promotion; no RH
claim.
