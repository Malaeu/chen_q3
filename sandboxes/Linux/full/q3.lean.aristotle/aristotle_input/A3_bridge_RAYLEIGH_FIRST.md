# A3 Bridge — RAYLEIGH-FIRST (no Szegő–Böttcher, no M₀)

## Goal

Close the **A3_bridge** axiom in the *Rayleigh-first* way:

- **No Szegő–Böttcher** (no discretization error term, no modulus-of-continuity stuff).
- **No `M₀`** (the statement holds for *every* matrix size `M` once the Toeplitz part is defined via the exact quadratic-form identity).
- Fix the definitional mismatch: the prime/RKHS block must be the **compression matrix**
  `T_P_comp` as a **rank-one sum** (Q3 tex), not the direct “heat Gram matrix on ℕ”.

This matches the docs/PROJECT_SPECS.md plan:
Toeplitz Rayleigh lower bound + A3 floor + RKHS cap ⇒ bridge inequality.

---

## Core idea (one-line)

For any `v ≠ 0`:
\[
\frac{\langle v,(T_M[P_A]-T_P^{(M)})v\rangle}{\|v\|^2}
\;\ge\;
\underbrace{\min_\theta P_A(\theta)}_{\ge c_\*}
\;-\;
\underbrace{\|T_P^{(M)}\|}_{\le \rho(1)\ <\ 1/25}
\;\ge\; c_\*/4.
\]

So you just need:
1) a Rayleigh lower bound lemma for Toeplitz matrices, and  
2) a uniform RKHS cap lemma for the compressed prime matrix.

---

## Constants

```lean
def c_star : ℝ := (11 : ℝ) / 10
def c_star_quarter : ℝ := c_star / 4         -- = 11/40 = 0.275
def rho_one : ℝ := (1 : ℝ) / 25              -- 0.04
```

---

## Minimal helper defs (keep these local; don’t fight Mathlib norms)

```lean
open scoped BigOperators
open Finset

noncomputable section
namespace Q3

def normSq {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  ∑ i, (v i) ^ (2 : ℕ)

def quadForm {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

def rayleighQ {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  quadForm A v / normSq v
```

---

## 1) Toeplitz side (already solved in `rayleigh_v1.lean`)

**Assume/import these (do NOT reprove here):**

```lean
-- Your project already has a concrete ToeplitzMatrix definition (the one that satisfies this lemma).
variable (ToeplitzMatrix : (M : ℕ) → (ℝ → ℝ) → Matrix (Fin M) (Fin M) ℝ)

-- Rayleigh lower bound:
-- If P(θ) ≥ m pointwise, then for every M and v ≠ 0:
--   rayleighQ (ToeplitzMatrix M P) v ≥ m
axiom rayleigh_lower_bound
  {M : ℕ} {P : ℝ → ℝ} {m : ℝ} {v : Fin M → ℝ} :
  (∀ θ, m ≤ P θ) → v ≠ 0 →
  rayleighQ (ToeplitzMatrix M P) v ≥ m
```

And the A3 floor:

```lean
variable (P_A : ℝ → ℝ)
axiom A3_floor : ∀ θ, c_star ≤ P_A θ
```

(These correspond to “A3_FLOOR: P_A(θ) ≥ c*” + “Rayleigh Toeplitz bound”.)

---

## 2) PRIME/RKHS side — **correct definition is the compression matrix** `T_P_comp`

### Data model

We intentionally model the node set as a *finite type* (this is what you actually use in the bridge application).

```lean
-- Node set (prime powers in the window; whatever your code calls it)
variable (NodesK : Type) [Fintype NodesK] [DecidableEq NodesK]

-- Node position ξ_n and weight w_Q(n) (your real project names may differ)
variable (xi_n : NodesK → ℝ)
variable (w_Q  : NodesK → ℝ)

-- Φ_{B,t}(ξ) factor (Fejér×heat / whatever test window you already defined)
variable (Phi_Bt : ℝ → ℝ → ℝ → ℝ)  -- B → t → ξ → ℝ

-- v_n : projection to P_M basis (Q3 tex says v_n[i] = cos(2π k ξ_n) etc.)
-- Keep it abstract here; you already have it somewhere in Q3 tex / Lean.
variable (v_n : (M : ℕ) → ℝ → Fin M → ℝ)
```

### Definition: rank‑one sum matrix

This is the **only** definition that makes uniform `t` plausible (compression; finite-rank operator).

```lean
def T_P_comp (K B t_rkhs : ℝ) (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j =>
    ∑ n : NodesK,
      (w_Q n) * (Phi_Bt B t_rkhs (xi_n n)) *
        (v_n M (xi_n n) i) * (v_n M (xi_n n) j)
```

---

## 3) The new “Rayleigh-first” bridge statement (no M₀)

### New data prop

```lean
def A3_bridge_rayleigh_data (K B : ℝ) : Prop :=
  ∃ t_rkhs : ℝ, 1 ≤ t_rkhs ∧
    ∀ M : ℕ, ∀ v : Fin M → ℝ, v ≠ 0 →
      rayleighQ (ToeplitzMatrix M P_A - T_P_comp (NodesK:=NodesK) (xi_n:=xi_n) (w_Q:=w_Q)
                    (Phi_Bt:=Phi_Bt) (v_n:=v_n) K B t_rkhs M) v
        ≥ c_star / 4
```

**Key: there is no `M₀` here.** We want one uniform `t_rkhs` (pick `t_rkhs = 1`).

---

## 4) What you should assume from RKHS_cap (already proven elsewhere)

You have two equivalent “cap” interfaces. Choose the one that matches your existing RKHS file best.

### Option A (simplest for Lean): bound the Rayleigh quotient directly

```lean
axiom rkhs_cap_rayleigh
  {K B : ℝ} {t_rkhs : ℝ} :
  1 ≤ t_rkhs →
  ∀ M : ℕ, ∀ v : Fin M → ℝ, v ≠ 0 →
    rayleighQ (T_P_comp (NodesK:=NodesK) (xi_n:=xi_n) (w_Q:=w_Q)
                 (Phi_Bt:=Phi_Bt) (v_n:=v_n) K B t_rkhs M) v
      ≤ rho_one
```

### Option B (operator norm): `‖T_P_comp‖ ≤ ρ(1)` and then a generic inequality

If you already have a clean op-norm statement, use it. Otherwise stick with Option A.

---

## 5) Main theorem to prove in this file (glue only)

```lean
theorem A3_bridge_rayleigh_first
  (h_floor : ∀ θ, c_star ≤ P_A θ)
  (h_cap   : ∀ {K B t_rkhs}, 1 ≤ t_rkhs →
                ∀ M : ℕ, ∀ v : Fin M → ℝ, v ≠ 0 →
                  rayleighQ (T_P_comp (NodesK:=NodesK) (xi_n:=xi_n) (w_Q:=w_Q)
                               (Phi_Bt:=Phi_Bt) (v_n:=v_n) K B t_rkhs M) v ≤ rho_one)
  : A3_bridge_rayleigh_data (ToeplitzMatrix:=ToeplitzMatrix) (P_A:=P_A)
      (NodesK:=NodesK) (xi_n:=xi_n) (w_Q:=w_Q) (Phi_Bt:=Phi_Bt) (v_n:=v_n) (K:=K) (B:=B)
:=
by
  refine ⟨1, by linarith, ?_⟩
  intro M v hv
  -- Toeplitz term ≥ c_star
  have hT : rayleighQ (ToeplitzMatrix M P_A) v ≥ c_star :=
    rayleigh_lower_bound (ToeplitzMatrix:=ToeplitzMatrix) (P:=P_A) (m:=c_star) (v:=v) h_floor hv
  -- Prime term ≤ rho_one
  have hP : rayleighQ (T_P_comp (NodesK:=NodesK) (xi_n:=xi_n) (w_Q:=w_Q)
                         (Phi_Bt:=Phi_Bt) (v_n:=v_n) K B 1 M) v ≤ rho_one :=
    h_cap (K:=K) (B:=B) (t_rkhs:=1) (by linarith) M v hv
  -- Combine:
  -- rayleighQ(A - B) = rayleighQ(A) - rayleighQ(B)
  -- so ≥ c_star - rho_one ≥ c_star/4
  -- (You can use `linarith` after rewriting with `quadForm`.)
  -- NOTE: prove/assume a small lemma `rayleighQ_sub` below.
  have hSub :
      rayleighQ (ToeplitzMatrix M P_A - T_P_comp (NodesK:=NodesK) (xi_n:=xi_n) (w_Q:=w_Q)
                   (Phi_Bt:=Phi_Bt) (v_n:=v_n) K B 1 M) v
        = rayleighQ (ToeplitzMatrix M P_A) v
          - rayleighQ (T_P_comp (NodesK:=NodesK) (xi_n:=xi_n) (w_Q:=w_Q)
                         (Phi_Bt:=Phi_Bt) (v_n:=v_n) K B 1 M) v :=
    by
      -- expand definitions: quadForm(A-B)=quadForm A - quadForm B
      -- and divide by normSq v
      -- should be `simp [rayleighQ, quadForm, Matrix.sub_apply, sub_eq_add_neg, mul_add, add_mul, sum_add_distrib]`
      -- plus ring.
      admit
  -- Finish numerics
  -- from hT, hP, and hSub
  -- need: c_star - rho_one ≥ c_star/4 (true since 1/25 ≤ 3*c_star/4)
  -- use `linarith` or `nlinarith`/`norm_num`.
  -- (`simp [hSub]` then `linarith [hT, hP]` will work after you add the numeric lemma.)
  admit
```

---

## 6) Tiny glue lemmas you may need (Lean-ready statements)

These are the “adapter” lemmas that make the proof painless.

### (L1) Quadratic form of a difference

```lean
lemma quadForm_sub {M : ℕ} (A B : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
  quadForm (A - B) v = quadForm A v - quadForm B v := by
  -- unfold quadForm; simp [Matrix.sub_apply, sub_eq_add_neg, mul_add, add_mul, sum_add_distrib]; ring
  admit
```

### (L2) Rayleigh quotient of a difference

```lean
lemma rayleighQ_sub {M : ℕ} (A B : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
  rayleighQ (A - B) v = rayleighQ A v - rayleighQ B v := by
  -- unfold rayleighQ; simp [quadForm_sub, div_sub_div_same]
  admit
```

### (L3) Numeric fact (just to unblock `linarith`)

```lean
lemma cstar_sub_rho_ge_quarter : c_star - rho_one ≥ c_star / 4 := by
  -- c_star=11/10, rho_one=1/25; prove with `norm_num` or `linarith`
  admit
```

Once you have (L2)+(L3), the main theorem is 3 lines of `linarith`.

---

## 7) Adapter lemmas “Fin M ↔ P_M” (reference list)

You *already* proved these in `rayleigh_v1.lean` (don’t redo here), but list them for wiring:

1. `vec_to_trigpoly` (map `v : Fin M → ℂ` to `p ∈ P_M`)
2. Parseval: `∫ |p|^2 = ∑ |v_i|^2`
3. Toeplitz form identity: `quadForm (ToeplitzMatrix M P) v = ∫ P(θ) |p(θ)|^2 dθ`
4. Rayleigh lower bound: `P ≥ m ⇒ rayleighQ(Toep) ≥ m`

On the prime side (optional but useful for future clarity):
- Expand rank‑one sum quadratic form:
  \[
  \langle v, T_P^{(M)} v\rangle = \sum_n \alpha_n \, (\sum_i v_i u_{n,i})^2.
  \]

---

## What Aristotle should output

A Lean file that:

1) introduces `T_P_comp` as above (rank‑one sum),  
2) defines `A3_bridge_rayleigh_data` (no `M₀`), and  
3) proves `A3_bridge_rayleigh_first` using the already-proven Toeplitz Rayleigh lemma + RKHS cap.

No Szegő–Böttcher anywhere.

---

end Q3
