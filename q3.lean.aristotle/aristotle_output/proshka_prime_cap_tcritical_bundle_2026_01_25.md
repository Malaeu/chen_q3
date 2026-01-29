# Proshka Bundle: prime-term cap at t_critical (single-scale)
Timestamp: 2026-01-25 15:27

## Target lemma (still `sorry`)
File: `Q3/Proofs/Q_nonneg_t_critical.lean`
```lean
lemma prime_term_le_at_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ) := by
  -- TODO
```

## Where it is used
```lean
theorem Q_phi_shift_nonneg_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    Q (fun ξ => phi_shift_critical B τ ξ) ≥ 0 := by
  unfold Q
  have h := prime_term_le_at_t_critical K B τ hK hB hτB
  linarith
```

## Definitions (single‑scale)
**Params:**
```
t_critical : ℝ := 3 / 20
phi_shift_critical B τ ξ := phi_shift B t_critical τ ξ
```

**Q / arch / prime:** `Q3/Basic/Defs.lean`
```lean
def arch_term (Φ : ℝ → ℝ) : ℝ := ∫ ξ, a_star ξ * Φ ξ

def prime_term (Φ : ℝ → ℝ) : ℝ := ∑' n, w_Q n * Φ (xi_n n)

def Q (Φ : ℝ → ℝ) : ℝ := arch_term Φ - prime_term Φ
```

**phi_shift / P_A_shift:** `Q3/Proofs/ShiftedWindows.lean`
```lean
def phi_shift (B t tau : ℝ) (xi : ℝ) : ℝ := fejer_heat_window B t (xi - tau)
```

## Available lemmas/tools
### Nonnegativity / support / summability
From `Q3/Proofs/Q_nonneg_atoms_helpers.lean`:
```
lemma phi_shift_integrable_with_a_star (B t tau : ℝ) (hB : 0 < B) :
    Integrable (fun x => a_star x * phi_shift B t tau x)

lemma phi_shift_prime_summable (B t tau : ℝ) (hB : 0 < B) :
    Summable (fun k => w_Q k * phi_shift B t tau (xi_n k))
```

### Prime‑sum to finite nodes (if needed)
From `Q3/Proofs/Rayleigh_Q_identification` (used elsewhere):
```
prime_term_eq_nodes_sum_shift
```
Use only if you must convert `tsum` to `Finset.sum`.

### RKHS / weight‑sum bounds (two‑scale versions)
`Q3/Proofs/RKHS_cap_rayleigh.lean` has **t_rkhs_cap** and `rho_oneK`, but this
request is **single‑scale t_critical**, so use with care. If you need a new
single‑scale bound, state the minimal lemma required.

## Constraints
- Single‑scale only: `t_critical`, τ = 0 allowed but lemma is general τ.
- No `t_sym`/two‑scale.
- No `sorry`/`exact?`.

## Preferred deliverable
Lean proof for `prime_term_le_at_t_critical`, or a minimal helper list (≤2).
