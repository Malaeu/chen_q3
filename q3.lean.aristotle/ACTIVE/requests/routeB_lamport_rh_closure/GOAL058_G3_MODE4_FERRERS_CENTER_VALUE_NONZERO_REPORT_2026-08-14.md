# Goal 058 G3 — mode-four Ferrers center value nonzero

Date: 2026-08-14

Status: PROVED — ACCEPT

## Pin and preflight

- Repository: `/Users/emalam/GitHub/rh_lean_01_2026`
- Branch: `rh_clean`
- Execution base: `259fa73877eaacb6c05c9648dcdb2deeb4877f9e`
- Base equals `origin/rh_clean`: yes
- Worktree before work: clean
- Strict startup: `P9_STRICT_PASS`
- Route B: `CHECK: OK`
- Knowledge query:
  `Goal 058 mode4 Ferrers center value nonzero even derivative zero simple interior zero`
- Knowledge result: exit 0, `no hits`.

## Exact public theorem

```lean
theorem Mode4FerrersRegularEvenProlateSolution.center_value_ne_zero
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    mode4FerrersSeries S.coefficients 0 ≠ 0
```

## Proof

The stored evenness identity says `f(-t)=f(t)`.  The accepted derivative
interface supplies `HasDerivAt f d 0`.  Differentiating the same function after
composition with negation supplies derivative `-d` at zero.  Uniqueness of the
derivative gives `d=0`.

If `f(0)=0`, the accepted theorem
`Mode4FerrersRegularEvenProlateSolution.interior_zero_simple` would instead
force `deriv f 0 ≠ 0`.  This contradicts the evenness derivative calculation.

## Falsifier gates

1. Evenness is used together with an actual `HasDerivAt` witness; no informal
   symmetry-to-derivative rewrite is assumed.
2. Interior-zero simplicity is invoked at the explicit point `0 ∈ (-1,1)`.
3. The conclusion is only a nonzero center value; it is not a sign claim or a
   root-count theorem.

## Validation

- Scratch kernel check: PASS.
- Owned Lean SHA256:
  `139244a622d5ccec8b5bac275fa5b2e0be8bedd5b4c71bc447281b52e0bb4960`.
- Direct Lean elaboration: PASS.
- Target build: PASS, 7773 jobs.
- Full build: PASS, 7817 jobs.
- `scripts/q3_check.sh`: PASS (`q3_check ok`).
- Axiom gate: `[propext, Classical.choice, Quot.sound]`.
- `sorry` / `axiom` / `admit` scan: clean.
- `git diff --check`: PASS.

## Proshka code review

- Natural reasoning time: 4m49s; no early-answer control was used.
- Verdict: `PRIMARY: ACCEPT`.
- Exact public head: ACCEPTED.
- Exact owned Lean SHA256 verified:
  `139244a622d5ccec8b5bac275fa5b2e0be8bedd5b4c71bc447281b52e0bb4960`.
- The derivative interface and evenness are used correctly.
- `interior_zero_simple` is used non-circularly.
- No hidden sign, zero-count, or ordered-mode claim was found.
- Authorized scope: exactly this Lean file and this report, then push to
  `origin/rh_clean`.

## Next exact blocker

Proshka placed further executable wrappers on HOLD.  Pairing nonzero roots as
`±x` is immediate from evenness but would not advance the source wall.  The
next load-bearing target is
`G3_MODE4_FOUR_INTERIOR_ZEROS_AND_THIRD_EVEN_SELECTION`: prove exactly four
interior zeros, identify mode index 4, and select the third even regular
eigenmode `ψ₄`.  This requires a source-locked singular Sturm–Liouville
oscillation/index theorem or an equivalent exact eigenvalue-ordering theorem;
the current fields do not imply a zero count.

## Nonclaims

- `NO_CENTER_SIGN`
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
