# Goal 058 G3 — exact finite even-Legendre quadratic-form closeout

Date: 2026-08-15
Branch: `rh_clean`
Pinned HEAD at entry: `d55a82458656`
Route state: `CHALLENGER_NOT_RH`

## External ruling lock

- Proshka request packet:
  `.playwright-mcp/GOAL058_G3_POST_GRAM_FINITE_FORM_PROSHKA_REQUEST_2026-08-15.txt`
- request SHA-256:
  `7b8ab29dbe27f2c742c44101a50a9c725ed0d54fcca13408a6bf9f08c6d05be8`
- captured verdict JSON SHA-256:
  `a4a54083f929e2b0a67e67ce1230780c490b1370bd1060be701f14dff87218f7`
- decoded verdict text SHA-256:
  `e384042a5821046fadccfc7f6ee0c100024112f923577af5850b30b500d99fcd`
- natural Proshka reasoning time: `8m37s`
- exact primary: `A_FINITE_FORM_BOTH_HEADS`
- Aristotle authorization:
  `G3_MODE4_FINITE_EVEN_LEGENDRE_QUADRATIC_FORM` only
- P0/minmax authorization: false
- commit authorization: false
- push authorization: false

No forced-answer or stop control was used. The pre-existing composer draft
`wer ist da` was restored byte-for-byte and was not sent.

## Production artifact

- file:
  `Q3/Proofs/RouteB/D0Mode4FiniteEvenLegendreQuadraticForm.lean`
- SHA-256:
  `118c8f81ed263e5a722ea4e56820fd92c211b0f5fc8fd115fdd596e4a0329266`
- bytes / lines / final LF: `30944 / 790 / yes`
- exact direct imports:
  - `Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreGram`
  - `Q3.Proofs.RouteB.D0Mode4LegendreHermitianCoordinateScale`
- knowledge preflight:
  `./orchestrator/kb.py ask "mode4 finite even Legendre polynomial exact quadratic form L2 energy Gram Hermitian matrix"`
- preflight result: exit `0`, `no hits`

The public synthesis is exactly

```lean
noncomputable def mode4FiniteEvenLegendrePolynomial
    (G : ℝ) {d : ℕ} (b : Fin d → ℝ) : ℝ[X] :=
  ∑ q : Fin d,
    C (((-1 : ℝ) ^ q.val) *
        mode4DLMFEvenSimilarityScale G q.val * b q) *
      mode4OrdinaryLegendrePolynomial (2 * q.val)
```

Both approved public heads are proved exactly:

```lean
theorem mode4FiniteEvenLegendrePolynomial_l2
    (G : ℝ) {d : ℕ} (b : Fin d → ℝ) (hG : 0 < G) :
    (∫ x in (-1 : ℝ)..1,
      (mode4FiniteEvenLegendrePolynomial G b).eval x ^ 2) =
      2 * (b ⬝ᵥ b)

theorem mode4FiniteEvenLegendrePolynomial_energy
    (G Λ : ℝ) {d : ℕ} (b : Fin d → ℝ) (hG : 0 < G) :
    (∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) *
          ((mode4FiniteEvenLegendrePolynomial G b).derivative.eval x) ^ 2 +
        G * x ^ 2 *
          ((mode4FiniteEvenLegendrePolynomial G b).eval x) ^ 2 -
        (Λ + G) *
          ((mode4FiniteEvenLegendrePolynomial G b).eval x) ^ 2) =
      2 *
        (b ⬝ᵥ
          ((mode4ForwardHermitianFiniteMatrix G Λ d) *ᵥ b))
```

Proof architecture:

1. The exact even Legendre Gram theorem collapses the L2 double sum. The
   source scale identity `D_q^2 = 4q+1` cancels its weight and leaves the
   literal factor `2`.
2. Exact `x^2 P_(2q)` zero/successor actions provide the potential couplings,
   including the endpoint branches.
3. The derivative Gram supplies the diagonal differential energy. Exact
   diagonal similarity balance converts source upper/lower coefficients to
   the forward Hermitian off-diagonal entries.
4. The alternating phase `(-1)^q` supplies their negative sign. The first
   omitted `P_(2d)` term vanishes against every retained basis vector by the
   exact Gram theorem, so no finite-cutoff boundary term is assumed.
5. The final equality is assembled pointwise and then integrated; neither
   target identity is an input hypothesis.

No P0 zero-free statement, global minimizer, form-core density, regular
solution selection, characteristic count, endpoint count, or nodal theorem is
used.

## Kernel and plant validation

- strict startup before the production write: PASS, `P9_STRICT_PASS`
- direct `lake env lean`: PASS
- named target build: PASS, `7761 jobs`
- full `lake build`: PASS, `7817 jobs`
- `q3_check`: PASS
- `git diff --check`: PASS
- forbidden scan (`sorry`, `admit`, `exact?`, custom `axiom`, `unsafe`,
  `native_decide`): no hits
- trailing-whitespace scan: no hits
- final LF: present
- public axioms for both heads: exactly
  `[propext, Classical.choice, Quot.sound]`

Scratch plant file:

- `/tmp/Goal058FiniteEvenLegendreFormPlants.lean`
- SHA-256:
  `3c734f33c412e51fad11829a57e043601fd8cee0ad7cb4ce9df4899eb8b47e9e`
- bytes / lines: `3305 / 82`
- direct Lean: PASS
- every plant axioms: exactly the standard triple

Fail-closed controls:

1. `MODE4_FINITE_FORM_FACTOR_TWO`: the `d=1`, `b_0=1` mass is exactly `2`.
2. `MODE4_FINITE_FORM_SCALE_DELETION_REJECTED`: `D_1^2=5`, while raw `P_2`
   has norm square `2/5`, so deleting the similarity scale is detected.
3. `MODE4_FINITE_FORM_PHASE_DELETION_REJECTED`: for the exact two-coordinate
   plant, removing the alternating phase changes the Hermitian energy; the
   off-diagonal coefficient is proved strictly positive before rejection.
4. `MODE4_FINITE_FORM_POTENTIAL_SIGN_REJECTED`: flipping `+Gx^2` changes the
   `q=0`, `G=1` Hermitian diagonal by `-2/3` and is rejected.
5. `MODE4_FINITE_FORM_LAST_ROW_ORTHOGONAL`: the omitted `P_4` term is exactly
   orthogonal to the last retained `P_2` mode at cutoff `d=2`.
6. `MODE4_FINITE_FORM_INTERVAL_ORIENTATION_REJECTED`: reversing `-1..1` to
   `1..-1` changes the normalized mass from `2` to `-2`.

## Aristotle transport record

- request file:
  `aristotle_input/goal058_g3_mode4_finite_even_legendre_quadratic_form_2026_08_15.md`
- request SHA-256:
  `aef33ee5ac30cd61148e1a8e9b83b6bb95e9aba588a439c2ec844763410c262b`
- project:
  `1653edc4-9853-46db-bd37-73595b48bfc8`
- task:
  `77a491fb-180d-46da-8c84-7867c7b67355`
- status at local closeout: `RUNNING`
- supplier status: `NOT_USED_AS_SUPPLIER`; the local kernel proof completed
  independently

The separate earlier Gram project
`036bf9ec-0307-48a8-8143-fc2fbfb357a2` also remained `RUNNING` at this
closeout and was not used as a supplier.

## Honest boundary

- `G1_STATUS: OPEN`
- `G3_STATUS: OPEN`
- `NO_P0_ZERO_FREE`
- `NO_GLOBAL_MINIMIZER`
- `NO_FORM_CORE_DENSITY`
- `NO_REGULAR_SOLUTION_MINMAX_IDENTIFICATION`
- `NO_NODAL_COUNT`
- `NO_G3_CLOSURE`
- `NO_G1_CLOSURE`
- `NO_ROUTE_PROMOTION`
- `NO_RH_CLAIM`

The exact finite theorem authorized for a separately reviewed next step is
`mode4FiniteEvenLegendrePolynomial_energy_nonneg_at_finite_bottom`. Even if
proved, that is only a finite variational statement and does not identify the
singular-endpoint regular solution.

Current source wall after this closeout:

`EVEN_LEGENDRE_FORM_CORE_AND_REGULAR_SOLUTION_MINMAX_IDENTIFICATION_NOT_YET_PROVED`

No commit or push was made. The ready production file and this closeout require
a separate Proshka review before the next theorem is authorized.
