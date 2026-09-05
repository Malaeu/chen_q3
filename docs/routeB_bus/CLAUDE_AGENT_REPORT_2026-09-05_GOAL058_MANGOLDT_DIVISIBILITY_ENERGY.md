# CLAUDE AGENT REPORT — GOAL058 / Λ-divisibility energy identity (DIV)

```yaml
REPORT_DATE: 2026-09-05
SUCCESS_CODE: MANGOLDT_DIVISIBILITY_ENERGY_KERNEL_GREEN
BOUNDARY_ID: GOAL058_WEILPROOF_CONTINUATION_ARITHMETIC_PACKETS
SOURCE_VERDICT: docs/routeB_bus/proshka/PROSHKA_VERDICT_WEILPROOF_CONTINUATION_ARITHMETIC_PACKETS_AND_DENSITY_2026-09-05.md
SOURCE_SECTIONS_USED: ["3", "4", "11"]
LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/MangoldtDivisibilityEnergy.lean
LEAN_FILE_SHA256: b88e05747c7152129420ef69299adc87562394e58c9cb1c0b9b530079f650141
LEAN_FILE_GIT_BLOB: 8964b594236fc6a7f615142bf9ae73172033b0f5
LEAN_FILE_LINES: 452
BASE_COMMIT_AT_WORK_TIME: 0d45def1c623f8b992a5332d4049c1dede682025
TOOLCHAIN: leanprover/lean4:v4.26.0 (mathlib rev v4.26.0)
LEAN_KERNEL_RERUN: true
AXIOM_PROFILE: [propext, Classical.choice, Quot.sound]   # all 26 declarations
DECLARATIONS: 26 lemmas/theorems + 7 definitions
NUMERICAL_EXPERIMENT_PERFORMED: true
COMMIT_PERFORMED: false
PUSH_PERFORMED: false
EXISTING_FILES_MODIFIED: none
ROUTE: FINITE_ARITHMETIC_ONLY
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
WEIL_FORM_CLAIM: NOT_MADE
```

## 1. What was asked and what was produced

The judge's §11 head 1, `mangoldt_divisibility_energy_identity` — the finite
factorization (DIV) of §3 Lemma 2 — is now a kernel-checked Lean declaration,
together with the corollaries requested (nonnegativity, the calibration plant,
the prime-operator cap), and, beyond the required scope, the §4 chain
(B)/(PRIME) with Mathlib's Chebyshev constant.

No zeta zeros, no integral, no Weil form, no packet construction, no RH-conditional
statement. The file is pure finite arithmetic over `ℂ` and imports nothing from Q3.

## 2. The statements as the kernel sees them

Definitions (`Q3.RouteB.MangoldtDivisibilityEnergy`, `Λ = ArithmeticFunction.vonMangoldt`):

```
divPairs M      = (Icc 1 M ×ˢ Icc 2 M).filter (fun p => p.1 * p.2 ≤ M)
divisorPairs M  = (Icc 1 M ×ˢ Icc 2 M).filter (fun p => p.2 ∣ p.1)
B M n           = ∑ d ∈ (Icc 2 M).filter (fun d => n * d ≤ M), Λ d / d          -- judge's B(M/n)
diagWeight M n  = Real.log n + B M n                                            -- judge's a_n^{(M)}
primeForm M c   = 2 * (∑ p ∈ divPairs M, ↑(Λ p.2) / ↑(√p.2) * conj (c p.1) * c (p.1 * p.2)).re
energy M c      = ∑ p ∈ divPairs M, Λ p.2 * ‖c (p.1 * p.2) - c p.1 / ↑(√p.2)‖ ^ 2
plantVec        = fun n => if n = 1 then 1 else (↑(√2))⁻¹
```

Main head, printed from the compiled module:

```
mangoldt_divisibility_energy_identity : ∀ (M : ℕ) (c : ℕ → ℂ),
  ∑ n ∈ Finset.Icc 1 M, diagWeight M n * ‖c n‖ ^ 2 - primeForm M c = energy M c
```

Corollaries:

| # | Declaration | Statement |
|---|---|---|
| (i) | `energy_nonneg` | `0 ≤ energy M c` |
| (ii) | `plant_energy_zero` | `energy 2 plantVec = 0` (equality case of DIV) |
| (ii) | `plant_identity_zero` | `∑ a_n |c_n|² − P_2(c) = 0` at the plant |
| (ii) | `plant_primeForm` | `primeForm 2 plantVec = Real.log 2` |
| (ii) | `plant_doubled_edge_eq` | `∑ a_n |c_n|² − 2·P_2(c) = −Real.log 2` |
| (ii) | `plant_doubled_edge_neg` | the same quantity is `< 0` |
| (iii) | `primeForm_le_diag` | `primeForm M c ≤ ∑ a_n ‖c n‖²` |
| (iii) | `primeForm_le_max` | `(∀ n ∈ Icc 1 M, a_n ≤ A) → primeForm M c ≤ A · ∑ ‖c n‖²` |
| (B) | `B_one_le` | `1 ≤ N → B N 1 ≤ Real.log N + (Real.log 4 + 4)` |
| (B) | `diagWeight_le` | `1 ≤ n → n ≤ M → a_n ≤ Real.log M + (Real.log 4 + 4)` |
| (PRIME) | `primeForm_le_log` | `primeForm M c ≤ (Real.log M + (Real.log 4 + 4)) · ∑ ‖c n‖²` |

Supporting lemmas: `mem_divPairs`, `mem_divisorPairs`, `norm_sub_div_ofReal_sq`,
`sum_divPairs_curry`, `sum_divisorPairs_curry`, `sum_divPairs_reindex`,
`sum_vonMangoldt_ge_two`, `divPairs_two`, `sum_divisorPairs_swap`, `card_multiples`,
`sum_log_eq_sum_floor`, `B_one_eq`, `psi_natCast`, `B_eq_div`.

## 3. Deviations from the verdict text (both are strengthenings or named weakenings)

1. **`M ≥ 2` is not assumed.** The identity is proved for every `M : ℕ`; for `M ≤ 1`
   both sides are `0` (`divPairs M = ∅`). The hypothesis in the verdict is not
   load-bearing, so carrying it would have been a dead argument.
2. **The (B) constant is `log 4 + 4`, not `4 log 2`.** Mathlib supplies
   `Chebyshev.psi_le_const_mul_self : 0 ≤ x → ψ x ≤ (log 4 + 4) * x`. The judge's
   sharper `4 log 2 ≈ 2.7726` would need his own central-binomial run of `ψ`
   (`ψ(2m) − ψ(m) ≤ 2m log 2` summed over dyadic scales), which Mathlib does not
   carry in that form. Since (PRIME) only ever needs *some* explicit constant, the
   Mathlib one (`log 4 + 4 ≈ 5.3863`) was taken and is stated in the file. The
   judge's constant is left unproved here; it is not used by anything downstream in
   this file. A numeric scan (`N ≤ 3000`) is consistent with the sharper constant
   too — minimum slack `log N + 4 log 2 − B(N) = 2.7726` at `N = 1` — but that is a
   diagnostic, not a proof.
3. **One missing Mathlib piece was proved here.** `∑_{j ≤ N} log j = ∑_{d ≤ N} Λ(d)·⌊N/d⌋`
   (the Legendre/Mertens counting step of §4) is not in Mathlib. It is proved as
   `sum_log_eq_sum_floor`, re-using exactly the divisor re-indexing that (DIV) already
   needed, plus `Nat.Ioc_filter_dvd_card_eq_div`.

## 4. Proof route (the judge's, unchanged)

`norm_sub_div_ofReal_sq` expands `‖A − z/√s‖²` into `‖A‖² + ‖z‖²/s − 2 Re(conj z · A)/√s`
by real/imaginary parts. Summing over `divPairs M`:

* the `‖c n‖²/d` part currying-splits into `∑_n B(M/n) ‖c n‖²` (`sum_divPairs_curry`,
  `Finset.sum_finset_product'`);
* the `‖c (nd)‖²` part is re-indexed by the bijection `(n,d) ↦ (n·d, d)`, inverse
  `(j,d) ↦ (j/d, d)` (`sum_divPairs_reindex`, `Finset.sum_nbij'`), then collapsed by
  `∑_{d ∣ j, d ≥ 2} Λ d = log j` — `ArithmeticFunction.vonMangoldt_sum` with the
  `d = 1` term dropped through `Λ 1 = 0` (`sum_vonMangoldt_ge_two`);
* the cross term is `−primeForm M c` (`Complex.re_sum`, `Complex.re_ofReal_mul`).

For (B): `N · B(N) = ∑_d Λ(d)·N/d ≤ ∑_d Λ(d)(⌊N/d⌋+1) = ∑_{j≤N} log j + ψ(N)
≤ N log N + (log 4 + 4)N`, then divide by `N`. `diagWeight_le` uses
`B M n = B (M/n) 1` (`B_eq_div`, from `Nat.le_div_iff_mul_le`) and
`log n + log ⌊M/n⌋ ≤ log M`.

## 5. Validation (all commands run, all exit codes captured)

```
$ cd q3.lean.aristotle
$ lake env lean Q3/Proofs/RouteB/MangoldtDivisibilityEnergy.lean
                                   # no output; EXIT_LEAN=0 (via ${PIPESTATUS[0]})
$ lake build Q3.Proofs.RouteB.MangoldtDivisibilityEnergy
✔ [7743/7743] Built Q3.Proofs.RouteB.MangoldtDivisibilityEnergy (10s)
Build completed successfully (7743 jobs).
                                   # EXIT_BUILD=0
$ cd .. && scripts/q3_check.sh Q3/Proofs/RouteB/MangoldtDivisibilityEnergy.lean
lean Q3/Proofs/RouteB/MangoldtDivisibilityEnergy.lean
scan Q3/Proofs/RouteB/MangoldtDivisibilityEnergy.lean
q3_check ok                        # EXIT_Q3CHECK=0
```

`#print axioms` was run from a scratch file importing the module, for **every** one of
the 26 lemmas/theorems. Every line reads

```
'Q3.RouteB.MangoldtDivisibilityEnergy.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no project axiom, no new axiom declaration (the file contains no
`axiom` keyword; `q3_check.sh` also greps for hole markers and found none).

## 6. Second channel — independent numeric check of (DIV)

A numpy re-implementation built from the *statement* (not from the Lean proof):
`Λ` from an independent trial-division factorisation, `a_n` from its own divisor loop,
`P_M` and the energy from their own double loops.

```
M=  50 seed=0  LHS= 342.724819948373  RHS= 342.724819948373  |diff|=5.684e-14 rel=1.659e-16
M=  50 seed=1  LHS= 256.286734342630  RHS= 256.286734342630  |diff|=0.000e+00 rel=0.000e+00
M=  50 seed=2  LHS= 297.625253259116  RHS= 297.625253259116  |diff|=0.000e+00 rel=0.000e+00
M= 200 seed=0  LHS=1893.326999699918  RHS=1893.326999699915  |diff|=2.728e-12 rel=1.441e-15
M= 200 seed=1  LHS=1687.850672714261  RHS=1687.850672714262  |diff|=6.821e-13 rel=4.041e-16
M= 200 seed=2  LHS=1974.119985113213  RHS=1974.119985113211  |diff|=1.592e-12 rel=8.062e-16
plant: diag=0.693147180559945  P=0.693147180559945  log2=0.693147180559945
       rhs=0.000e+00  identity=0.000e+00  doubled=-0.693147180559945  (= −log 2)
```

Random complex vectors, relative agreement at `1e-15`–`1e-16` (double precision).
The plant reproduces all three Lean numbers: energy `0`, `P_2 = log 2`, doubled edge
`−log 2`. The (PRIME) cap was spot-checked as well (`M = 50`: `P = 1.45` against the
cap `740.16`; `M = 200`: `P = 39.77` against `3688.27`; `max_n a_n` under
`log M + log 4 + 4` in both cases).

This is a second channel in the sense of the owner's axiom: the two sides are computed
from independent code paths and an independently written `Λ`, not transcribed from the
Lean development. It is a falsification test, not a certificate; the certificate is the
kernel run in §5.

## 7. What this does and does not buy

Buys: the judge's §3 factorization is now machine-checked, so the sum-of-squares repair
of the sign is no longer relay. The plant is machine-checked too, which is the point of
the plant — a checker testing only Hermitian symmetry accepts the doubled prime edge and
would certify a form whose value is `−log 2 < 0`.

Does not buy: nothing about `S ≥ 0` (§2 kills that), nothing about (PACKET-POS), nothing
about cofinal recovery (§7 kills that), nothing about the Weil form or RH. `primeForm` is
a finite arithmetic operator; the §5 transfer to the source form is a separate head and is
not touched here.

## 8. Files

```
q3.lean.aristotle/Q3/Proofs/RouteB/MangoldtDivisibilityEnergy.lean   (new, 452 lines)
docs/routeB_bus/CLAUDE_AGENT_REPORT_2026-09-05_GOAL058_MANGOLDT_DIVISIBILITY_ENERGY.md (this file)
```

No existing file was modified. Nothing was committed or pushed.
