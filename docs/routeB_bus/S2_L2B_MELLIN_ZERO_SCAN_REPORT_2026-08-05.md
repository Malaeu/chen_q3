# S2-L2b discriminator — Mellin zeros of v3-class windows inside the open strip

Address: `G6 · SlotS2 · S2-L2b`. Executed on Linux (Claude Code body), 2026-08-05.
Route B = CHALLENGER / NOT_RH. Bus 010 VOID. No promotion, no RH claim.
Script: `scripts/s2_l2b_mellin_zero_scan.py` (exact symbolic algebra, sympy; not float64).

## Question

Mythos registered the missing seam **S2-L2b**: under reading (ii) ("fixed window, Λ→∞")
the required zero-free gauge forces `Mellin h` to have **no zeros inside the open strip**
`Re w ∈ (0,1)`. His prediction R1: at least one generic v3 window has an interior zero,
which would kill reading (ii) and force reading (i) (Müntz density lemma).

Window model: `h(u) = Σ_j c_j u^{a_j}` on `(0,1]`, zero outside. Lipschitz on `Ico 0 1`
forces each exponent `a_j = 0` or `a_j ≥ 1`. Then
`M(w) = Σ_j c_j/(w + a_j) = P(w) / Π_j (w + a_j)`, so zeros of `M` = roots of `P`.

## Structural fact the scan made explicit

For the v3 class, zero-mass is **literally** `M(1) = ∫_0^b h = 0`. So `w = 1` is ALWAYS a
zero — and `w = 1 ⇔ z = −i/2`, i.e. exactly on the **boundary** of the open strip
`|Im z| < 1/2`. The forced zero is therefore always harmless. The only question is whether
any OTHER zero lands strictly inside.

## Results

| Family | Windows scanned | Interior zero | Clean |
|---|---|---|---|
| PL2 witness `u − (3/2)u²` (the one already in Lean) | 1 | 0 | 1 |
| All two-term `u^a − λu^b`, exponents 0..7, λ fixed by zero-mass | 28 | **0** | 28 |
| Three-term, exponents from 0..5, shape parameter on a rational grid | 480 | **1** | 479 |
| Four-term, exponents from 0..5, two shape parameters on a grid | 960 | **0** | 960 |

**Total: 1 interior zero out of 1468 windows.**

### The single witness (exact, not numerical noise)

Exponents `(2,3,5)`, coefficients `1, −11/4, 17/8` (last one fixed by zero-mass):

```
M(w) = 1/(w+2) − (11/4)/(w+3) + (17/8)/(w+5)
numerator P(w) = (w − 1)(3w − 2)
exact zeros: w = 1 (boundary, forced)  and  w = 2/3  (INTERIOR)
M(2/3) = 0 exactly
```

### Two-term windows: interior-free by identity, not by luck

For `h = u^a − λ u^b` with `λ = (b+1)/(a+1)` (zero-mass), the numerator reduces to a
multiple of `(w − 1)`: the only zero is the forced boundary one. So the entire two-term
family is clean for structural reasons, not by sampling.

## Verdict

- **Mythos's R1 is CONFIRMED**: an interior zero exists, and we have an exact witness.
- **His corollary does NOT follow.** "Generic window has an interior zero" refutes
  "any window will do"; it does not refute reading (ii). `SlotS2` quantifies over
  `ClusterData` for a **fixed** `C`, and `C` is ours to construct — we need ONE good window,
  not all of them. 1467 of 1468 scanned windows are clean, including every two-term window
  and every four-term window in the grid.
- Therefore the discriminator should be re-posed: not "do generic windows have interior
  zeros" (answered: rarely, but yes) but **"is there a v3 window that is simultaneously
  interior-zero-free AND carries anchor + Λ→∞ convergence + tail control"**. On the first
  of those four conditions the PL2 witness already in Lean passes.

## Honest limits of this scan

- Only piecewise-polynomial windows on `[0,1]` of the form `Σ c_j u^{a_j}`, integer
  exponents 0..7, coefficients on a rational grid. No hat/Fejér-type or continuously
  parameterized families were scanned.
- Only the **nonvanishing** condition was tested. The other three requirements for reading
  (ii) — anchor `family i 0 = centeredXi 0`, existence of the Λ→∞ limit, and locally uniform
  tail control — were NOT examined here and can still kill this path.
- A clean grid is not a theorem. Turning "the two-term family is interior-zero-free" into a
  Lean statement is a separate obligation.
