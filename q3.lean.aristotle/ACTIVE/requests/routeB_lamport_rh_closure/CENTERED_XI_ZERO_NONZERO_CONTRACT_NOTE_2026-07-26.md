# centeredXi 0 != 0 — queued small contract

Status: `QUEUED / STATEMENTS_ONLY / NOT_RH`.

## Target

```lean
namespace Q3.RouteB

theorem riemannZeta_half_re_neg :
    (riemannZeta (1 / 2 : ℂ)).re < 0 := by
  -- queued

theorem riemannZeta_half_ne_zero :
    riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  -- queued

theorem centeredXi_zero_ne_zero :
    centeredXi 0 ≠ 0 := by
  -- queued

end Q3.RouteB
```

## Exact route

1. Pair the alternating series at `s = 1/2`:
   \[
   \eta(1/2)=\sum_{k\ge1}
   \bigl((2k-1)^{-1/2}-(2k)^{-1/2}\bigr)>0.
   \]
2. Apply DLMF 25.2.3:
   \[
   \zeta(1/2)=\eta(1/2)/(1-\sqrt2)<0.
   \]
3. Hence `riemannZeta (1/2 : ℂ) ≠ 0`.
4. By `riemannXi_eq_zero_iff_riemannZeta_eq_zero` at `s = 1/2`,
   `riemannXi (1/2) ≠ 0`; unfold `centeredXi` and simplify to obtain
   `centeredXi 0 ≠ 0`.

## Reuse and dependencies

- Reuses the sign argument already source-locked for `ζ(1/4)`.
- Source: `D0_7E_CLASSICAL_SOURCE_LOCK.json`, DLMF 25.2.3.
- Local consumer bridge:
  `Q3/Proofs/RouteB/ClassicalXiInterface.lean`.
- Expected Mathlib ingredients for the elementary series layer:
  `Summable`, `HasSum`, alternating-series convergence, `Real.rpow`,
  positivity/strict antitonicity of `x ↦ x⁻¹ᐟ²`, and complex coercions.

## Current blocker

The local Mathlib tree contains no pinned theorem identifying its
`riemannZeta` on `0 < re s` with the alternating eta series.  The finite
pairing/positivity proof is elementary, but the analytic-continuation
crosswalk must be supplied explicitly.

Stop code: `ZETA_HALF_ETA_CONTINUATION_BRIDGE_MISSING`.

No decimal approximation is admissible as a nonvanishing proof.
