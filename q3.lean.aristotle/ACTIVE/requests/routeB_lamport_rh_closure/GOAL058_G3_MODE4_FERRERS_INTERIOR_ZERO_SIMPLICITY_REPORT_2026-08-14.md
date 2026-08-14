# Goal 058 G3 — mode-four Ferrers interior-zero simplicity

Date: 2026-08-14

Status: PROVED — ACCEPT

## Pin and preflight

- Repository: `/Users/emalam/GitHub/rh_lean_01_2026`
- Branch: `rh_clean`
- Execution base: `e0ab4fa0ae11dce49b02564042eb8243c61986d6`
- Base equals `origin/rh_clean`: yes
- Worktree before work: clean
- Strict startup: `P9_STRICT_PASS`
- Route B: `CHECK: OK`
- Knowledge query:
  `Goal 058 mode4 Ferrers interior zero simplicity ODE uniqueness HasDerivAt`
- Knowledge result: exit 0, `no hits`.

## Exact public theorem

```lean
theorem Mode4FerrersRegularEvenProlateSolution.interior_zero_simple
    {mProject K : ℕ} {Λ x : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hz : mode4FerrersSeries S.coefficients x = 0) :
    deriv (mode4FerrersSeries S.coefficients) x ≠ 0
```

The clean `(S, hx, hz)` head authorized by the interface-repair verdict is
preserved literally.  No constructor guard is reopened.

## Proof architecture

Let

```text
Y(t) = (f(t), f'(t))
```

where the second component is the accepted first-derivative series.  The
stored prolate ODE is solved for the second derivative on `(-1,1)` and becomes
the exact first-order linear system

```text
Y'(t) = (Y₂,
  ((G t² - (Λ + G)) Y₁ + 2 t Y₂) / (1 - t²)).
```

The vector field is a continuous family of continuous linear maps.  At every
point its operator norm is locally bounded, so Mathlib's
`ODE_solution_unique_of_eventually` supplies local uniqueness against the
zero solution.

The zero-state set inside the subtype `(-1,1)` is:

- closed, by continuity of the solution state;
- open, by local ODE uniqueness;
- nonempty if both `f(x)` and `f'(x)` vanish.

Since the interval subtype is preconnected, the zero-state set would be the
whole interval.  Continuity extends `f = 0` to `[-1,1]`, so its interval
integral is zero.  The already accepted coefficient-extraction identity says
the same integral is `2 * S.coefficients 0`, contradicting
`S.coefficient_zero_pos`.

## Falsifier gates

1. A zero of `f` alone does not trigger propagation; zero derivative is
   assumed only inside the contradiction.
2. Division by `1 - t²` is used only with an explicit proof that it is positive
   on the open source interval.
3. Local uniqueness is not silently promoted to global uniqueness; the
   open-and-closed argument explicitly uses interval preconnectedness.
4. Global nontriviality is not assumed to imply interior nontriviality; the
   coefficient integral supplies the contradiction on the closed source
   interval.

## Validation

- Scratch kernel check: PASS.
- Owned Lean SHA256:
  `587c655a13cfd149124d4b1547053dd5995bd0838de6ad00f7a94f4f9fbdad77`.
- Direct Lean elaboration: PASS.
- Target build: PASS, 7772 jobs.
- Full build: PASS, 7817 jobs.
- `scripts/q3_check.sh`: PASS (`q3_check ok`).
- Axiom gate: `[propext, Classical.choice, Quot.sound]`.
- `sorry` / `axiom` / `admit` scan: clean.
- `git diff --check`: PASS.

## Nonclaims

- `NO_ZERO_COUNT`
- `NO_EXACTLY_FOUR_INTERIOR_ZEROS`
- `NO_ORDERED_PSI4_IDENTIFICATION`
- `NO_MATCHING_ROOT_EXISTENCE`
- `NO_PHYSICAL_SCALE`
- `NO_MODE_ZERO`
- `NO_FINITE_FOURIER_EIGENRELATION`
- `NO_ACTUAL_PROLATEPAIR`
- `NO_LEMMA_7_2`
- `NO_G3`
- `NO_G1`
- `NO_ROUTE_B_PROMOTION`
- `NO_RH`

## Proshka code verdict

Natural review time: 8m29s.

- `PRIMARY: ACCEPT`
- exact source SHA256 verified: true
- first-order ODE rewrite: accepted
- local Lipschitz / local uniqueness boundary: accepted
- clopen propagation on `(-1,1)`: accepted
- endpoint use only through continuity after ODE uniqueness: accepted
- coefficient-integral contradiction: accepted
- hidden assumptions: none found
- isolated two-file commit: authorized
- push to `origin/rh_clean`: authorized

The next cheapest G3 leaf is:

```lean
theorem Mode4FerrersRegularEvenProlateSolution.center_value_ne_zero
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    mode4FerrersSeries S.coefficients 0 ≠ 0
```

Its route is `evenness → f'(0)=0`, contradicting
`interior_zero_simple` if `f(0)=0`.  It still does not count roots or identify
the ordered degree-four PSWF.
