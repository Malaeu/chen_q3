# TASK 2026-08-22 — spheroidal high-mode Jacobi witness

```yaml
task_id: 2026-08-22-spheroidal-high-mode-jacobi-witness
authorized_by: PROSHKA_VERDICT_REQ_2026_08_22_S_ARISTOTLE_PARTIAL_HARVEST_AND_INFINITY_GAP_2026-08-22.md
verdict_commit: cab2b8c79b3a2ed0158f6b1ee7cd19bca23bea6b
verdict_blob: a97a5b96f9234e70ccbfe5143067d25e25756dd0
written_by: LINUX_CLAUDE
authorization_scope: READ_ONLY_PLUS_SOURCE_PURE_LOCAL_PROOF_SEARCH
```

## Authorization boundary — read before touching anything

```
production Q3 source write:      FORBIDDEN
import Q3 into this proof:       FORBIDDEN
second paid Aristotle run:       FORBIDDEN (prior grant covered one deep run;
                                  it is spent — C09)
edit BookRegularEvenSpectrum:    FORBIDDEN
```

This is a **local proof search inside the quarantined harvest tree**, not a
Q3 node. Nothing here closes anything until a later, separately authorized
transaction ports it.

## Where to work

```
q3.lean.aristotle/aristotle_input/req_r_ms_satz1_m0_even_spectrum_2026_08_22_harvest/
```

This is a **standalone Lake project** with its own `lakefile.toml` and its own
Mathlib pin (`v4.28.0`), separate from the main repo's Mathlib. Do not invent a
repository-relative `lake` command against the main tree's `.lake` — it will
not resolve. `cd` into that directory and run `lake build` there; that is the
exact environment that produced the reported 8030-job green build after the
five mechanical repairs already applied (see `HARVEST.md` in that directory
for what those repairs were, so you don't re-diagnose them).

Live files: `RequestProject/Defs.lean`, `RequestProject/Legendre.lean`,
`RequestProject/Spectrum.lean`, `RequestProject/Main.lean`.

## The one target

```lean
theorem spheroidal_highMode_eigenvalue_near_specD (G : Real) :
    exists N : Nat, exists C : Real, 0 <= C and
      forall n : Nat, N <= n ->
        exists Lambda : Real,
          RegularEvenSpheroidalEigenvalue G Lambda and
          abs (Lambda - specD G n) <= C
```

`C` is fixed once, outside the `forall n`. A statement that lets `C` depend on
`n` is nearly vacuous and will be rejected.

## Why this and not the sorry already sitting there

The gap in `Main.lean` is stated as abstract infinitude:

```lean
theorem spheroidal_spectrum_infinite (G : ℝ) :
    {Λ : ℝ | RegularEvenSpheroidalEigenvalue G Λ}.Infinite := by
  sorry
```

The judge killed the shortcut of getting this for free from what is already
proved. `{0, 6} ⊂ ℝ` is separated and locally finite on every bounded set, and
it is finite, not infinite — separation plus local finiteness does not imply
infinitude, even with both `G = 0` plants already landed. Min–max / Courant
could give infinitude, but only after building an infinite-dimensional
self-adjoint object and proving compact-resolvent, which is not a consequence
of the lemmas already in hand — it is a separate, more expensive proof of the
same wall (cost 9/10 against this route's 6/10).

The uniform high-mode witness above is stronger than bare infinitude and
reuses machinery already sitting in `Spectrum.lean`, which is why it is the
selected route (`R1_HIGH_MODE_WEIGHTED_JACOBI_FIXED_POINT`, kill power 10/10,
cost 6/10) over the runner-up self-adjoint route and the quarantined book-port
route.

## Work loop

1. Reuse `Defs.lean`, `Legendre.lean`, `Spectrum.lean` as they stand.
2. Keep the moving-centre weight `rho^(-abs(k-n))`.
3. Derive the exact row map and the scalar `n`-th row equation for `Lambda`.
4. Prove one uniform contraction / diagonal-dominance estimate valid for all
   `n >= N`.
5. Feed the resulting row into the existing `specF` / `specF1` / `specF2`
   regularity and ODE lemmas — do not re-derive what `Spectrum.lean` already
   proves.
6. Prove nonzero from the normalized centre coefficient `c n = 1`.
7. Return either a compiled theorem or the first exact missing lemma, named
   precisely.

## Forbidden shortcuts

```
assuming compact resolvent
using finite matrices as the universal proof
trimming the endpoints
choosing the constant C after inspecting finitely many n
```

Any of these is the surrogate the review deck exists to catch, not a repair.

## Success

```
no sorry / admit / new axiom
C sits outside forall n
exact degenerate endpoints retained
axiom profile is exactly [propext, Classical.choice, Quot.sound]
```

## Failure

```
FAILURE CODE: REQ_S_HIGH_MODE_UNIFORM_CONTRACTION_GAP
```

If you hit a wall you cannot pass, obtain, or kill locally: write
`docs/routeB_bus/CODEX_REQ_2026-08-22_<slug>.md` with a non-empty `TRIED`
field and push it. Do not address the judge directly — the browser lives on
the Linux body.

## Ledger

```
CLOSES: []
OPENS:  []
```

Nothing closes here. This is preflight inside a quarantined tree; porting the
result into `BookRegularEvenSpectrum` is a later, separately authorized
transaction, and the verdict's own integration order is: close this witness →
build the even-only source spectrum package → prove the DLMF forward / project
reverse crosswalk → instantiate the project interface. Do not skip ahead.
