# Goal 058 G3 — singular Ferrers endpoint regularity closeout

Date: `2026-08-15`

Route state: `CHALLENGER / NOT_RH`

Node verdict:

```text
G3_MODE4_SINGULAR_ENDPOINT_VALUES_NONZERO_PROVED
```

Goal 058 remains open.  This bounded source leaf is not a nodal-count theorem,
mode-selection theorem, G3 closure, Route B promotion, or RH claim.

## Source-locked judge directive

The byte-exact source/dependency packet was:

```text
.playwright-mcp/GOAL058_G3_SELECTED_FERRERS_HALF_INTERVAL_STURM_OSCILLATION_SOURCE_LOCK_2026-08-15.txt
SHA-256 4ae333b4c0db31d3b69982c204c6d4528f1b05d442485f140fbc4175171b21bf
```

Proshka completed naturally after `6m42s` and selected exactly one primary:

```text
PRIMARY: A_LIBRARY
p_le_2_removes_global_singular_dependencies: false
NEXT_BOUNDED_LEAF: G3_MODE4_SINGULAR_ENDPOINT_VALUES_NONZERO
```

The browser-visible response was preserved before execution as:

```text
.playwright-mcp/GOAL058_G3_SELECTED_FERRERS_HALF_INTERVAL_STURM_OSCILLATION_PROSHKA_VERDICT_2026-08-15.json
JSON SHA-256 e6e9be9e6f4210a06a32c8ac1b431ec4398925cbc16fc8158437cc7784bee5f8
decoded text with final LF SHA-256 77dee3eba8f304bad95a2942224d8aaf28ebbfa53f09e8f6dc8ece387cd78d77
```

The judge rejected `A_SPECIALIZED`: restricting to `p <= 2` does not remove
endpoint nonaccumulation, no-extra-zero, phase/exhaustion, or
coefficient-index-to-nodal-index dependencies.  It also rejected
`B_REPRESENTATION` as a relocation of the same unformalized DLMF nodal theorem.
It did not select `STOP_SOURCE_WALL`, because endpoint nonvanishing is a
bounded reusable leaf.

The user's pre-existing Proshka composer draft `wer ist da` was restored
exactly after capture and was not submitted.

## Control and retrieval preflight

Before the production write, `bash specs_docs/session_start.sh` returned exit
code `0` and:

```text
P9_STRICT_PASS
HEAD = origin/rh_clean = d55a8245
worktree clean
```

The exact knowledge query

```text
./orchestrator/kb.py ask "Mode4FerrersRegularEvenProlateSolution endpoint_values_ne_zero singular endpoint zero flux interior_zero_simple"
```

returned no hits.  This is only a discovery receipt.

## Kernel-checked result

Production file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersSingularEndpointRegularity.lean
SHA-256 578eb5ecdbe35ff72bc955496908ab388b380d43d88775e65c773a07695c87aa
289 lines / 11999 bytes
```

It exports exactly the requested theorem:

```lean
theorem
    Mode4FerrersRegularEvenProlateSolution.endpoint_values_ne_zero
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    mode4FerrersSeries S.coefficients (-1) ≠ 0 ∧
      mode4FerrersSeries S.coefficients 1 ≠ 0
```

The proof defines the natural flux

```text
F(x) = (1 - x^2) * f'(x)
```

and derives from the stored ODE, using the actual derivative fields,

```text
F'(x) = -(Λ + G * (1 - x^2)) * f(x).
```

Assuming `f(1)=0`, it takes the maximum `M` of `|f|` on the explicit terminal
interval

```text
a = C / (C + 1),  C = |Λ| + |G|.
```

The zero-flux limit plus the mean-value inequality gives

```text
|F(s)| <= C * M * (1 - s).
```

After cancelling `1-s` from `1-s^2=(1-s)(1+s)`, this yields a uniform
terminal derivative bound.  Applying the same endpoint mean-value lemma to
`f` gives

```text
|f(s)| <= (C * M / (1 + a)) * (1 - s).
```

At the maximizer,

```text
M <= (C * (1-a) / (1+a)) * M,
C * (1-a) / (1+a) < 1,
```

so `M=0`.  The solution then vanishes on an interior interval, giving an
interior zero with zero derivative and contradicting the already proved
`interior_zero_simple`.  Evenness transports right-endpoint nonvanishing to
the left endpoint.

## Validation

All checks were run in the current tree:

- direct `lake env lean Q3/Proofs/RouteB/D0Mode4FerrersSingularEndpointRegularity.lean`: exit `0`;
- named `lake build Q3.Proofs.RouteB.D0Mode4FerrersSingularEndpointRegularity`: exit `0`, `7773` jobs;
- `bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersSingularEndpointRegularity.lean`: exit `0`, `q3_check ok`;
- `git diff --check`: clean;
- forbidden scan for `sorry`, `admit`, `axiom`, `unsafe`, and `exact?`: no hits.

The public axiom surface is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The only build warning is the pre-existing local-change warning in the
external `UnicodeBasic` dependency.

## Honest boundary

This theorem eliminates endpoint zeros and, by closed-interval continuity,
gives zero-free one-sided endpoint neighborhoods for every accepted regular
Ferrers witness.  It does **not** prove:

- zero-freeness of the selected bottom `p=0` witness on the whole interval;
- the exact number of positive zeros of `p=1` or `p=2`;
- an upper bound excluding additional interior zeros;
- a function-space min-max theorem or spectral exhaustion;
- coefficient-space index equals nodal index.

The surviving G3 stop is therefore:

```text
G3_SELECTED_FERRERS_GLOBAL_NODAL_INDEX_LIBRARY_INCOMPLETE
```

The next cheap discriminator selected by the judge is a read-only audit of
whether the current quadratic form can prove positivity/zero-freeness of the
selected `p=0` function without first constructing the full singular Sturm
operator realization.

G1 remains independently open at:

```text
G1_ODD_TAIL_CORRECTION_BOUND_PROVED_CORRECTED_EVEN_HEAD_ROW_EVENNESS_AND_COFINAL_FULL_COMPLEMENT_FLOOR_MISSING
```

Per the judge directive, neither file is staged, committed, or pushed.
