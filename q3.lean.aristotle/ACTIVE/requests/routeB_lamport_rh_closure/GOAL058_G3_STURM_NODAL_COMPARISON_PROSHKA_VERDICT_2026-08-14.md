# Goal 058 G3 — Proshka verdict on the Sturm comparison leaf

Date: 2026-08-14

Status: REPAIRED NODAL-INTERVAL LEAF ACCEPTED; ARISTOTLE SUBMISSION AUTHORIZED

## Provenance

- Living Proshka chat:
  `https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a7afc0e-2aec-83eb-a9ca-469b44c84f83`
- Natural reasoning time: 14m39s; no early-answer control was used.
- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Judgment pin: `46a6fdde2f77b77b2d566f805fb7d69a3f75b832`
- Mythos input report:
  `GOAL058_G3_STURM_SOURCE_ARCHITECTURE_MYTHOS_VERDICT_2026-08-14.md`

## Primary verdict

```text
REPAIR_G3_STURM_COMPARISON_TO_NODAL_INTERVAL
```

The unrestricted statement between any two distinct lower-parameter zeros is
not false, but it needs a separate compact-zero-set and consecutive-subpair
layer.  A single bounded Wronskian/Picone proof needs the lower solution to
have a fixed sign between the two endpoint zeros.  Therefore the executable
leaf must include

```lean
(hNodal :
  ∀ x ∈ Set.Ioo x1 x2,
    mode4FerrersSeries SLo.coefficients x ≠ 0)
```

## Exact family binders

```lean
{mProject K : ℕ}
{ΛLo ΛHi x1 x2 : ℝ}
(SLo : Mode4FerrersRegularEvenProlateSolution mProject K ΛLo)
(SHi : Mode4FerrersRegularEvenProlateSolution mProject K ΛHi)
(hΛ : ΛLo < ΛHi)
```

Shared `mProject` fixes the ODE potential.  Shared `K` retains the same
source-construction family, although `K` itself does not occur in the ODE.
Different `mProject` values are forbidden.

## Interface judgment

Proshka found the current interface sufficient for the compact interior leaf:

- actual first-derivative interface: present;
- actual second-derivative interface: present;
- exact prolate ODE: present;
- interior-zero simplicity: present;
- continuity and compact-interval integrability: downstream consequences, not
  new source assumptions;
- remaining difficulty: Lean calculus and interval-order API assembly.

No singular endpoint theorem is used in this leaf.

## Source order

The compact interior comparison may precede exact external source page pins.
The following remain on HOLD until source-locked singular oscillation and index
theorems are pinned:

- endpoint realization;
- global zero count;
- ordered eigenvalue index;
- third-even / `ψ₄` selection.

## Aristotle authorization

Proshka returned `ARISTOTLE_SUBMISSION_AUTHORIZED` for exactly:

```text
TARGET: GOAL058_G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON
OWNED FILE: Q3/Proofs/RouteB/D0Mode4FerrersSturmComparison.lean
SUCCESS: G3_MODE4_STURM_NODAL_INTERVAL_COMPARISON_PROVED
```

The authoritative prompt was displayed in the Proshka file preview.  Browser
Use opened it and activated the preview download control, but the Codex browser
did not materialize a file in `~/Downloads`; Computer Use is forbidden from
controlling the Codex app.  The complete visible preview text is preserved as
`PROSHKA_GOAL058_STURM_NODAL_COMPARISON_ARISTOTLE_PROMPT_2026-08-14_UI_RENDERED_EXTRACT.md`.
It is an honest UI-rendered extract, not a byte-identical download claim.

## Boundary

This leaf is only an interior comparison kernel between two already existing
regular solutions.  It does not construct the `Λ` family, count zeros, identify
the ordered mode, or contribute the finite-Fourier eigenrelation.

## Nonclaims

- `NO_BYTE_IDENTICAL_PROMPT_DOWNLOAD`
- `NO_COMPACT_ZERO_SET_FINITE_THEOREM`
- `NO_GLOBAL_ZERO_COUNT`
- `NO_ORDERED_PSI4_IDENTIFICATION`
- `NO_MATCHING_ROOT_EXISTENCE`
- `NO_PHYSICAL_SCALE`
- `NO_FINITE_FOURIER_EIGENRELATION`
- `NO_G3`
- `NO_G1`
- `NO_ROUTE_B_PROMOTION`
- `NO_RH`
