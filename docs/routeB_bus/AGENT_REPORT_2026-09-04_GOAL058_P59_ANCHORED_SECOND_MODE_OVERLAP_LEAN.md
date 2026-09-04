# Claude-agent report — Goal 058: P59 anchored second-mode overlap, finite identities (Lean)

Date: 2026-09-04
Judge source: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SECOND_MODE_OVERLAP_OF_THE_XI_ROW_2026-09-04.md`
(`REQ-2026-09-04-OVERLAP`; `## CODEX DIRECTIVE`, `TASK_ID: GOAL058_P59_SECOND_MODE_OVERLAP_FINITE_IDENTITIES`;
statements read verbatim from §Q1, §Q2 and §5 "Lean-ready bookkeeping")
Convention: `docs/routeB_bus/CONVENTION_CARD_GOAL058.md` — rows are **FULL** mode coefficients
`c_k`, `k ∈ [−N, N]`; the even orthonormal translation `v₀ = c₀`, `vₙ = √2 cₙ` is itself proved
(`proposition59_even_coords_pairing`), not assumed
Executor: Linux-Claude agent (Opus), owner-authorized bounded transaction; branch `rh_clean`,
main checkout, **no commit, no push**
File: `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59AnchoredSecondModeOverlap.lean` (653 lines)

```yaml
TASK_ID: GOAL058_P59_SECOND_MODE_OVERLAP_FINITE_IDENTITIES
RESULT: P59_SECOND_MODE_OVERLAP_FINITE_IDENTITIES_KERNEL_GREEN
ITEMS_KERNEL_GREEN: [1, 2, 3, 4, 5]
ITEMS_BLOCKED: []
AXIOMS: [propext, Classical.choice, Quot.sound]
LEAN_EDIT_PERFORMED: true      # one new file only; no existing .lean file touched
NUMERICAL_RUN_PERFORMED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
COFINAL_CLAIMS: none
```

No existing `.lean` file was edited; nothing outside the new file and this report was written.
`docs/cartographer/TOOLS.yaml` untouched. `git status --porcelain` shows exactly one entry:
the new `.lean` file.

## Validation — commands and exit codes

| where | command | exit |
|---|---|---|
| `q3.lean.aristotle` | `lake env lean Q3/Proofs/RouteB/Proposition59AnchoredSecondModeOverlap.lean` | `0` |
| `q3.lean.aristotle` | `lake build Q3.Proofs.RouteB.Proposition59AnchoredSecondModeOverlap` | `0` (`Build completed successfully (7776 jobs)`, module built in 22 s) |
| repo root | `scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59AnchoredSecondModeOverlap.lean` | `0` (`q3_check ok`) |

Exit codes taken from `${PIPESTATUS[0]}` (all three commands were piped).
`rg -n 'sorry|admit|axiom |exact\?|native_decide'` over the file: **no match** (rg exit `1`).
`lake env lean` emits **no warnings** — the whole output is the 20 `#print axioms` lines.
Toolchain `leanprover/lean4:v4.26.0`, Mathlib `v4.26.0`.

## `#print axioms` — all 20 printed declarations

```
'Q3.RouteB.proposition59_even_coords_pairing'                   [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59RealTransform_at_realPole'              [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59RealTransform_at_zero'                  [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_real_even_lattice_pairing'             [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59RawTransform_of_sum'                    [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59RealTransform_of_sum'                   [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59Anchor_of_sum'                          [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_anchor_residual_term_zero'             [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_anchoredDefect_of_sum'                 [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_anchored_eigenbasis_decomposition'     [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_anchored_two_mode_form'                [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59XiSampleRow_at_zero'                    [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59RealTransform_xiSampleRow_at_realPole'  [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_second_mode_overlap_lattice'           [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59JetRemainder_at_zero'                   [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59JetRemainder_secondJet_zero'            [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_curvature_transfer_split'              [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_ground_second_mode_trace_orthogonality'[propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_second_mode_curvature_transfer'        [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_second_jet_two_mode_ledger'            [propext, Classical.choice, Quot.sound]
```

Expected set exactly; `lake build` reprints the same list at module level.

## Objects introduced

All of them are named in the project's own terms and every one is tied back to the source
object `proposition59RawTransform` by a proved lemma; nothing is redefined.

```lean
def proposition59FullPairing (N : ℕ) (v w : ℤ → ℝ) : ℝ :=            -- ⟨v,w⟩, FULL window
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), v k * w k

def proposition59EvenCoord (c : ℤ → ℝ) (n : ℕ) : ℝ :=                -- card: v₀=c₀, vₙ=√2 cₙ
  if n = 0 then c 0 else Real.sqrt 2 * c (n : ℤ)

def proposition59RealTransform (L : ℝ) (N : ℕ) (v : ℤ → ℝ) (x : ℝ) : ℝ :=   -- F_v on ℝ
  (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k => (v k : ℂ)) ((x : ℝ) : ℂ)).re

def proposition59Anchor (L : ℝ) (v : ℤ → ℝ) : ℝ := Real.sqrt L * v 0        -- ℓ(v) = F_v(0)

def proposition59LatticeTrace (L : ℝ) (N : ℕ) (f : ℝ → ℝ) : ℝ :=            -- Tr_m
  2 * Real.pi / L * (f 0 + 2 * ∑ n ∈ Finset.Icc 1 N, f (proposition59RealPole L n))

def proposition59AnchoredDefect (L : ℝ) (N : ℕ) (v : ℤ → ℝ) (X : ℝ → ℝ) : ℝ → ℝ :=  -- ψ_j and e
  fun x => proposition59RealTransform L N v x - proposition59Anchor L v * X x

def proposition59XiSampleRow (L : ℝ) (u₁ : ℤ → ℝ) (X : ℝ → ℝ) (k : ℤ) : ℝ :=        -- y
  (-1 : ℝ) ^ k.natAbs * u₁ 0 * X (proposition59RealPole L k.natAbs)

def proposition59JetRemainder (G X : ℝ → ℝ) (α : ℝ) : ℝ → ℝ :=      -- B = G − X + α z² X
  fun x => G x - X x + α * x ^ 2 * X x

def proposition59Kappa (f : ℝ → ℝ) : ℝ := -(iteratedDeriv 2 f 0) / 2        -- κ(f) = −f''(0)/2
```

`proposition59RealPole L n = 2πn/L` is the existing object of
`Proposition59AlternatingLatticeCurvature.lean`; `proposition59RealPole_zero` records
`x₀ = 0`, so `Tr_m`'s centre term really is the anchor node.

Bridge lemmas to the source (both proved, both used everywhere below):

```lean
theorem proposition59RealTransform_at_realPole                   -- F_v(x_n) = √L (−1)ⁿ vₙ
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) {n : ℕ} (hn : n ≤ N) :
    proposition59RealTransform L N v (proposition59RealPole L n) =
      Real.sqrt L * (-1 : ℝ) ^ n * v (n : ℤ)

theorem proposition59RealTransform_at_zero                       -- F_v(0) = √L v₀
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) :
    proposition59RealTransform L N v 0 = proposition59Anchor L v
```

The first is `proposition59RawTransform_at_lattice` (bridge file) composed with
`proposition59RealPole_ofReal`; the second matches
`proposition59RawTransform_at_zero_eq_sqrt` (entire-transform file), which is the
verdict's §1 normalization repair `ℓ_m(v) = √L v₀`, **not** `1`.

## Per-item status

| item | judge's name | status | main declaration |
|---|---|---|---|
| 1 | `P59_REAL_EVEN_LATTICE_PAIRING` (C) | KERNEL GREEN | `proposition59_real_even_lattice_pairing` |
| 2 | `P59_ANCHORED_EIGENBASIS_DECOMPOSITION` (A), (B) | KERNEL GREEN | `proposition59_anchored_eigenbasis_decomposition`, `proposition59_anchored_two_mode_form` |
| 3 | `P59_SECOND_MODE_OVERLAP_LATTICE_IDENTITY` (D) | KERNEL GREEN | `proposition59_second_mode_overlap_lattice` |
| 4 | `P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY` (F) | KERNEL GREEN | `proposition59_second_mode_curvature_transfer` |
| 5 | `P59_SECOND_JET_TWO_MODE_LEDGER` (G) | KERNEL GREEN | `proposition59_second_jet_two_mode_ledger` |

### Item 0 (convention card, not requested but load-bearing) — even/full coordinate conversion

```lean
theorem proposition59_even_coords_pairing (N : ℕ) (c e : ℤ → ℝ)
    (hc : ∀ k : ℤ, c (-k) = c k) (he : ∀ k : ℤ, e (-k) = e k) :
    ∑ n ∈ Finset.Icc 0 N, proposition59EvenCoord c n * proposition59EvenCoord e n =
      proposition59FullPairing N c e
```

This is the card's line "FULL Euclidean over `[−N,N]` = `c₀d₀ + 2Σ_{n≥1} c_n d_n` for equal
parity = EVEN/ODD coordinate Euclidean", proved rather than asserted. It is the only place
the `√2` appears, and it is why `⟨v,w⟩` in the verdict and `proposition59FullPairing` here are
the same number. Every other theorem uses the FULL pairing.

### Item 1 — identity (C)

```lean
theorem proposition59_real_even_lattice_pairing
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v w : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hw : ∀ k : ℤ, w (-k) = w k) :
    proposition59LatticeTrace L N
        (fun x => proposition59RealTransform L N v x * proposition59RealTransform L N w x) =
      2 * Real.pi * proposition59FullPairing N v w
```

Pure algebra from the exact removable sampling formula, exactly as the verdict says: the
`√L·√L` of the two samples cancels the `2π/L` of the trapezoid, `(−1)ⁿ(−1)ⁿ = 1` kills the
signs, and the mirror halves of the FULL pairing are recombined by the local
`sum_Icc_symm_split` (the additive twin of the bridge file's `prod_erase_zero_Icc_symm`,
which is `CommMonoid`-only and does not additivize). Both signs of `n` are covered — that is
what evenness of `v` and `w` is for, and it is the only use of those hypotheses.

### Item 2 — identities (A) and (B)

Three linearity facts first, each a theorem, none assumed:

```lean
theorem proposition59RawTransform_of_sum      -- linearity of the SOURCE transform in the row
    (L : ℝ) (S : Finset ℤ) (T : Finset ℕ) (d : ℕ → ℂ) (u : ℕ → ℤ → ℂ) (z : ℂ) :
    proposition59RawTransform L S (fun k => ∑ j ∈ T, d j * u j k) z =
      ∑ j ∈ T, d j * proposition59RawTransform L S (u j) z

theorem proposition59RealTransform_of_sum ...  -- its real-row corollary
theorem proposition59Anchor_of_sum ...         -- ℓ(y) = ∑_j d_j ℓ_j
theorem proposition59_anchoredDefect_of_sum ...-- e = ∑_j d_j ψ_j
```

The task asked for the residual `X`-term to be stated exactly rather than silently dropped.
It is its own theorem, and it is zero:

```lean
theorem proposition59_anchor_residual_term_zero
    (L : ℝ) (K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ) (hK : 1 ≤ K)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) :
    proposition59Anchor L y - d 1 * proposition59Anchor L (u 1)
        - ∑ j ∈ Finset.Icc 2 K, d j * proposition59Anchor L (u j) = 0
```

so identity (A) is stated with no residual term at all:

```lean
theorem proposition59_anchored_eigenbasis_decomposition
    {L : ℝ} (N K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ) (X : ℝ → ℝ)
    (hK : 1 ≤ K) (hℓ : proposition59Anchor L (u 1) ≠ 0)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) (x : ℝ) :
    d 1 * proposition59Anchor L (u 1) *
        (proposition59RealTransform L N (u 1) x / proposition59Anchor L (u 1) - X x) =
      proposition59AnchoredDefect L N y X x -
        ∑ j ∈ Finset.Icc 2 K, d j * proposition59AnchoredDefect L N (u j) X x
```

and identity (B), with `a` and `R` **defined by the identity** (the judge's fail-closed
requirement; no fitted object anywhere):

```lean
theorem proposition59_anchored_two_mode_form
    {L : ℝ} (N K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ) (X : ℝ → ℝ)
    (hK : 2 ≤ K) (hℓ : proposition59Anchor L (u 1) ≠ 0) (hd : d 1 ≠ 0)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) (x : ℝ) :
    proposition59RealTransform L N (u 1) x / proposition59Anchor L (u 1) - X x =
      (-(d 2) / (d 1 * proposition59Anchor L (u 1))) *
          proposition59AnchoredDefect L N (u 2) X x +
        (proposition59AnchoredDefect L N y X x -
            ∑ j ∈ Finset.Icc 3 K, d j * proposition59AnchoredDefect L N (u j) X x) /
          (d 1 * proposition59Anchor L (u 1))
```

**Honest generality.** Orthonormality of `u` is *not* a hypothesis of (A) or (B) and is not
used: both are consequences of linearity of the transform and of the anchor along the
expansion `hy`. `X : ℝ → ℝ` is arbitrary. `d` is arbitrary. The interpolation error `e` is
carried as `proposition59AnchoredDefect L N y X`, i.e. by the *same* definition as the
`ψ_j` — which is precisely the verdict's point that the higher-mode tail alone is not the
remainder (`KILL_HIGHER_MODE_TAIL_ALONE_AS_REMAINDER_SUPPLIER`).

### Item 3 — identity (D)

The verdict's normalization `y[0] = u₁[0]` is realized by the explicit row

```lean
def proposition59XiSampleRow (L : ℝ) (u₁ : ℤ → ℝ) (X : ℝ → ℝ) (k : ℤ) : ℝ :=
  (-1 : ℝ) ^ k.natAbs * u₁ 0 * X (proposition59RealPole L k.natAbs)
```

which is even by construction (`proposition59XiSampleRow_even`, from `Int.natAbs_neg`), gives
`y[0] = u₁[0]` when `X 0 = 1` (`proposition59XiSampleRow_at_zero`), and whose transform
matches `ℓ₁X` at every included node (`proposition59RealTransform_xiSampleRow_at_realPole`).
Hence

```lean
theorem proposition59_second_mode_overlap_lattice
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u₁ u₂ : ℤ → ℝ) (X : ℝ → ℝ)
    (h₂ : ∀ k : ℤ, u₂ (-k) = u₂ k) :
    2 * Real.pi * proposition59FullPairing N (proposition59XiSampleRow L u₁ X) u₂ =
      proposition59Anchor L u₁ *
        proposition59LatticeTrace L N
          (fun x => X x * proposition59RealTransform L N u₂ x)
```

`2π d₂ = ℓ₁ Tr_m(X F₂)` with `d₂ = ⟨y, u₂⟩` the exact overlap. Proved from item 1 plus the
node-congruence lemma `proposition59LatticeTrace_congr_nodes` (`Tr_m` sees only the finitely
many included nodes). `X` is still arbitrary; no `Ξ` property is used.

### Item 4 — identity (F)

Two halves, deliberately separated so that the place where orthogonality is spent is visible:

```lean
theorem proposition59_curvature_transfer_split           -- pure Tr-linearity, no orthogonality
    (L : ℝ) (N : ℕ) (G X F₂ : ℝ → ℝ) (α : ℝ) :
    proposition59LatticeTrace L N (fun x => X x * F₂ x) =
      α * proposition59LatticeTrace L N (fun x => x ^ 2 * X x * F₂ x)
        - proposition59LatticeTrace L N (fun x => proposition59JetRemainder G X α x * F₂ x)
        + proposition59LatticeTrace L N (fun x => G x * F₂ x)

theorem proposition59_ground_second_mode_trace_orthogonality   -- identity (E): Tr(G F₂) = 0
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u₁ u₂ : ℤ → ℝ)
    (h₁ : ∀ k : ℤ, u₁ (-k) = u₁ k) (h₂ : ∀ k : ℤ, u₂ (-k) = u₂ k)
    (hℓ : proposition59Anchor L u₁ ≠ 0)
    (horth : proposition59FullPairing N u₁ u₂ = 0) :
    proposition59LatticeTrace L N
        (fun x => proposition59RealTransform L N u₁ x / proposition59Anchor L u₁ *
          proposition59RealTransform L N u₂ x) = 0
```

(identity (E) is exactly `2π⟨u₁,u₂⟩/ℓ₁ = 0` — item 1 divided by the anchor), and their
composition with item 3:

```lean
theorem proposition59_second_mode_curvature_transfer
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u₁ u₂ : ℤ → ℝ) (X : ℝ → ℝ) (α : ℝ)
    (h₁ : ∀ k : ℤ, u₁ (-k) = u₁ k) (h₂ : ∀ k : ℤ, u₂ (-k) = u₂ k)
    (hℓ : proposition59Anchor L u₁ ≠ 0)
    (horth : proposition59FullPairing N u₁ u₂ = 0) :
    2 * Real.pi * proposition59FullPairing N (proposition59XiSampleRow L u₁ X) u₂ =
      proposition59Anchor L u₁ *
        (α * proposition59LatticeTrace L N
              (fun x => x ^ 2 * X x * proposition59RealTransform L N u₂ x)
          - proposition59LatticeTrace L N
              (fun x => proposition59JetRemainder
                  (fun t => proposition59RealTransform L N u₁ t /
                    proposition59Anchor L u₁) X α x *
                proposition59RealTransform L N u₂ x))
```

i.e. `2π d₂ = ℓ₁ (α M − E)` with `M = Tr_m(z²XF₂)` and `E = Tr_m(B F₂)`, on the nose.

**Statement generality, said plainly.** `α` is a free real parameter: the identity holds for
*every* `α`, and in particular for the verdict's exact second jet `α = κ(G) − κ(X)`. This is
weaker than tying `α` to the jet inside the statement, and it is the honest form — the finite
identity genuinely does not need the jet. What ties the two is item 5 plus the two jet facts
below. **No rate is claimed for `M` or `E`.** The verdict's own `SAME_PARAMETER_SUFFICIENT_CONDITIONS`
(`M → M ≠ 0`, `E = o(L⁻²)`) are cofinal and are not in this file.

Both jet conditions the verdict lists for `B` are proved for that exact `α`:

```lean
theorem proposition59JetRemainder_at_zero (G X : ℝ → ℝ) (α : ℝ) (h : G 0 = X 0) :
    proposition59JetRemainder G X α 0 = 0                              -- B(0) = 0

theorem proposition59JetRemainder_secondJet_zero
    (G X : ℝ → ℝ) (hG : ContDiff ℝ 2 G) (hX : ContDiff ℝ 2 X) (hX0 : X 0 = 1) :
    proposition59Kappa
        (proposition59JetRemainder G X (proposition59Kappa G - proposition59Kappa X)) = 0
                                                                       -- B''(0) = 0
```

The second rests on the one calculus fact `d²/dx²(x²X)|₀ = 2X(0)`
(`iteratedDeriv_two_sq_mul`, private). Together these are the judge's `jets: [B(0)=0,
B''(0)=0]` and the fail-closed repair from `STRONGEST ATTACK`: `α` is *the exact second jet*,
never a fitted quadratic.

### Item 5 — identity (G)

```lean
theorem proposition59_second_jet_two_mode_ledger
    (G X ψ R : ℝ → ℝ) (a : ℝ)
    (hG : ContDiffAt ℝ 2 G 0) (hX : ContDiffAt ℝ 2 X 0)
    (hψ : ContDiffAt ℝ 2 ψ 0) (hR : ContDiffAt ℝ 2 R 0)
    (hdecomp : (fun x => G x - X x) = fun x => a * ψ x + R x) :
    proposition59Kappa G - proposition59Kappa X =
      a * proposition59Kappa ψ + proposition59Kappa R
```

`α = a κ(ψ₂) + κ(R)`, by linearity of `iteratedDeriv` (`iteratedDeriv_sub`,
`iteratedDeriv_add`, `iteratedDeriv_const_mul`); the `C²` hypotheses are the ones those
Mathlib lemmas require and nothing more. `hdecomp` is exactly the shape identity (B)
produces, with the same `a` and `R`; the ledger is stated for arbitrary `G, X, ψ, R` so that
it can be instantiated at (B) without carrying (B)'s algebraic side conditions.

**Not claimed.** The verdict's consequence "hence, if `κ(ψ₂) ≠ 0`,
`d₂ = −(d₁ℓ₁/κ(ψ₂))(α − κ(R))`" is a one-line rearrangement of (G) once (B) is instantiated;
it is not written, because instantiating (B) inside the ledger would require carrying the
whole finite-cell hypothesis stack for no new content, and the composed statement is what
the *paper* wants, not what the kernel adds.

## What is deliberately absent

* No cofinal statement of any kind. Every theorem is quantified at a fixed `(L, N)`; there is
  no `Filter.Tendsto`, no `O`/`o`, no family index.
* No fitted polynomial. `α` is either a free parameter or the exact `κ(G) − κ(X)`; `a` and
  `R` are defined by identity (B).
* No resolvent norm, no complement floor, no spectral gap, no eigenvalue at all: `u₁`, `u₂`
  are arbitrary rows, and "second mode" enters only through the orthogonality hypothesis
  `horth : ⟨u₁,u₂⟩ = 0` where it is actually used (item 4).
* No numerical constant used as a proof step; no `native_decide`; no `decide` on ℝ.
* Nothing about the classical `Ξ`. `ClassicalXiInterface.lean` is not imported and
  `centeredXi` does not appear. The "Ξ row" is `proposition59XiSampleRow` for an arbitrary
  profile `X : ℝ → ℝ`; `X` is never identified with anything.
* The verdict's `REQUIRED_MODE_GUARD` (simplicity of `λ₂`, `u₂[0] ≠ 0`, or the
  multiplicity-safe spectral projection) is a source statement about a spectrum and has no
  counterpart here — nothing in this file selects a mode.

## Mathlib facts used

| fact | where |
|---|---|
| `Finset.sum_Icc_succ_top` (`to_additive` of `prod_Icc_succ_top`) | `Mathlib/Algebra/BigOperators/Intervals.lean:74` |
| `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_comm` | big-operator basics |
| `Complex.re_sum` | `Mathlib/Data/Complex/BigOperators.lean:44` |
| `Complex.re_ofReal_mul` | `Mathlib/Data/Complex/Basic.lean:217` |
| `iteratedDeriv_add`, `iteratedDeriv_sub`, `iteratedDeriv_const_mul` | `Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:139,160,171` |
| `contDiff_succ_iff_deriv` | `Mathlib/Analysis/Calculus/ContDiff/Basic.lean:1448` |
| `hasDerivAt_pow`, `HasDerivAt.mul`, `HasDerivAt.add`, `HasDerivAt.deriv` | derivative basics |
| `Real.mul_self_sqrt`, `Even.neg_one_pow`, `Int.natAbs_neg`, `Int.natAbs_natCast`, `Int.cast_negOnePow_natCast` | scalar bookkeeping |

Project facts used: `proposition59RawTransform`, `proposition59RawTransform_at_lattice`
(bridge file), `proposition59RawTransform_at_zero_eq_sqrt`, `proposition59Pole_ofReal`,
`proposition59RealPole`, `proposition59RealPole_ofReal`.

Notes for future agents:

* `HasDerivAt.mul` in v4.26 states its conclusion for the **`Pi` product** `c * d`, not for
  `fun y => c y * d y`; `rw [show (fun x => f x * g x) = f * g from rfl, h.deriv]` is the fix.
* `ContDiffAt.const_mul` does not exist; use `contDiffAt_const.mul h`.
* `Finset.sum_congr` inside a goal produced by `congr n` leaves an undetermined
  `AddCommMonoid` metavariable; the node-congruence lemma
  `proposition59LatticeTrace_congr_nodes` exists to avoid `congr` on `Tr_m` entirely.
* `unfold proposition59LatticeTrace` leaves un-beta-reduced `(fun x => …) 0`;
  `simp only [proposition59LatticeTrace]` beta-reduces and is what the proofs use.

## Registered state

`LEAN_EDIT_PERFORMED: true` (one new file), `NUMERICAL_RUN_PERFORMED: false`,
`ROUTE_PROMOTION: false`, `RH_CLAIM: false`, `PX_RH_CLAIM: NOT_MADE`,
`HONESTY_STATE: CHALLENGER_NOT_RH`, `BUS_010: VOID`. No commit, no push — the orchestrator
commits. The judge's `CURRENT_SMALLEST_GAP`
(`P59_ANCHORED_SECOND_MODE_COEFFICIENT_AND_HIGHER_MODE_TAIL`) and the six
`NEW_ANALYTIC` items of §5 are untouched by this transaction: what is now formal is the
bookkeeping the verdict listed as `LEAN_READY`, and nothing beyond it.
