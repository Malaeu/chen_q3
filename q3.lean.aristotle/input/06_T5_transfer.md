# T5: Compact-by-Compact Transfer

## Overview
This file formalizes the T5 compact-by-compact transfer mechanism that propagates positivity from each compact $[-K, K]$ to the full Weil class $W$. This is the final assembly step of the proof.

## Definitions

### Compact Cones
$$W_K := C^+_{\mathrm{even}}([-K, K])$$
the cone of even, nonnegative continuous functions supported in $[-K, K]$ with uniform norm.

### Weil Class (Inductive Limit)
$$W := \bigcup_{K \geq 1} W_K$$
with the inductive (LF) topology: $U \subset W$ is open iff $U \cap W_K$ is open in $W_K$ for every $K$.

---

## Definition T5-LF (Weil Inductive-Limit Topology)

**Statement:**
A quadratic functional $Q : W \to \mathbb{R}$ is (sequentially) continuous in the LF topology iff each restriction $Q|_{W_K}$ is continuous in $\|\cdot\|_\infty$.

---

## Lemma T5-Local-Lip (Local Continuity Suffices)

**Statement:**
If for every $K$ the restriction $Q|_{W_K}$ is Lipschitz in $\|\cdot\|_\infty$ with some (possibly $K$-dependent) constant $L_K$, then the inductive-limit topology guarantees sequential continuity of $Q$ on $W$.

No uniform bound $\sup_K L_K < \infty$ is required: whenever $\Phi_n \to \Phi$ in $W$, the convergence takes place in a single $W_K$, and the corresponding $L_K$ controls $|Q(\Phi_n) - Q(\Phi)|$.

**Proof:**
By definition of the LF topology, a sequence $\Phi_n \to \Phi$ in $W$ means there exists $K$ such that all $\Phi_n$ and $\Phi$ lie in $W_K$ and $\|\Phi_n - \Phi\|_\infty \to 0$. The Lipschitz bound on $W_K$ then gives $|Q(\Phi_n) - Q(\Phi)| \leq L_K \|\Phi_n - \Phi\|_\infty \to 0$.

---

## Lemma T5-Transfer (Transfer Across $K \uparrow$)

**Statement:**
If $Q \geq 0$ on every $W_K$ and the family $\{Q|_{W_K}\}$ is compatible with the natural inclusions $W_K \hookrightarrow W_{K'}$ for $K < K'$, then $Q \geq 0$ on $W$.

**Proof:**
Given $\Phi \in W$, pick $K$ with $\operatorname{supp} \Phi \subset [-K, K]$; then $\Phi \in W_K$ and $Q(\Phi) \geq 0$ by hypothesis. Compatibility ensures independence from the chosen $K$.

---

## Proposition T5-Transfer-Formal (LF-Transfer of Positivity)

**Statement:**
Let $\{W_K\}_{K \in \mathbb{N}}$ be an increasing family of cones of even, nonnegative $C_c$ tests supported in $[-K, K]$, and let $W = \varinjlim W_K$ be their LF inductive limit. Suppose:
1. For each $K$, the quadratic form $Q$ is continuous on $W_K$ in the $\|\cdot\|_\infty$ topology;
2. $Q(\Phi) \geq 0$ for all $\Phi \in W_K$ for every $K$;
3. The embeddings $W_K \hookrightarrow W_{K+1}$ are continuous and compatible with $Q$.

Then $Q \geq 0$ on $W$.

**Proof:**
Given $\Phi \in W$, pick $K$ with $\operatorname{supp} \Phi \subset [-K, K]$; then $\Phi \in W_K$ and $Q(\Phi) \geq 0$ by (ii). Compatibility and continuity ensure independence from the chosen $K$.

---

## Remark T5-Scale-Independence

The Archimedean smoothing parameters $t_{\mathrm{sym}}(K)$ come from A3, while the RKHS heat scales $t_{\mathrm{rkhs}}(K)$ are fixed by RKHS-Tstar. The schedules are monotone in $K$ but otherwise independent; T5 never couples them into a single global constraint such as $\sup_K L_Q(K) < \infty$. Each compact window closes the YES gate with its own data, and the inductive-limit transfer propagates positivity without any cross-$K$ balancing.

---

## Theorem T5-Compact (Main Compact Transfer)

**Statement:**
For each compact $[-K, K]$ with $K \geq 1$:
1. The Archimedean margin satisfies $c_{\mathrm{arch}}(K) > 0$ (from A3)
2. The prime contraction satisfies $\|T_P\| \leq c_{\mathrm{arch}}(K)/4$ (from RKHS)
3. The functional $Q$ is Lipschitz on $W_K$ with constant $L_Q(K)$ (from A2)

Combining these: for all $\Phi \in W_K$ constructed from Fejér×heat atoms,
$$Q(\Phi) \geq 0$$

By density (A1') and continuity (A2), this extends to all $\Phi \in W_K$.

**Proof:**
The A3 bridge (Theorem A3) gives:
$$\lambda_{\min}(T_M[P_A] - T_P) \geq \frac{c_{\mathrm{arch}}(K)}{4} > 0$$

This implies $Q(\Phi_{B,t}) \geq 0$ for all Fejér×heat tests. By A1' density, such tests are dense in $W_K$. By A2 Lipschitz continuity, $Q \geq 0$ extends to all of $W_K$.

---

## Corollary T5-Full (Q ≥ 0 on Full Weil Class)

**Statement:**
$$Q(\Phi) \geq 0 \quad \text{for all } \Phi \in W$$

**Proof:**
Apply Proposition T5-Transfer-Formal with:
- (i) Continuity from A2 on each $W_K$
- (ii) Positivity from Theorem T5-Compact on each $W_K$
- (iii) Natural embeddings $W_K \hookrightarrow W_{K+1}$

---

## Expected Lean Output

```lean
-- Definitions
def W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | ContinuousOn Φ (Set.Icc (-K) K) ∧
       (∀ x, Φ x = Φ (-x)) ∧
       (∀ x, 0 ≤ Φ x) ∧
       (∀ x, |x| > K → Φ x = 0)}

def W : Set (ℝ → ℝ) := ⋃ K : ℕ, W_K K

-- Lemma: Local Lipschitz suffices
theorem T5_local_lip_suffices (Q : (ℝ → ℝ) → ℝ)
    (hLip : ∀ K : ℕ, ∃ L_K > 0, ∀ Φ₁ Φ₂ ∈ W_K K,
      |Q Φ₁ - Q Φ₂| ≤ L_K * ‖Φ₁ - Φ₂‖_∞) :
    SeqContinuous Q := by
  sorry

-- Lemma: Transfer across K
theorem T5_transfer (Q : (ℝ → ℝ) → ℝ)
    (hPos : ∀ K : ℕ, ∀ Φ ∈ W_K K, Q Φ ≥ 0)
    (hCompat : ∀ K : ℕ, ∀ Φ ∈ W_K K, Φ ∈ W_K (K + 1) → Q Φ = Q Φ) :
    ∀ Φ ∈ W, Q Φ ≥ 0 := by
  intro Φ hΦ
  obtain ⟨K, hK⟩ := Set.mem_iUnion.mp hΦ
  exact hPos K Φ hK

-- Main theorem: Q ≥ 0 on W_K
theorem T5_compact (K : ℕ) (hK : K ≥ 1)
    (h_arch : c_arch K > 0)
    (h_prime : ‖T_P K‖ ≤ c_arch K / 4)
    (h_lip : Lipschitz_Q K) :
    ∀ Φ ∈ W_K K, Q Φ ≥ 0 := by
  sorry -- combine A1' density, A2 continuity, A3 bridge

-- Corollary: Q ≥ 0 on full Weil class
theorem T5_full :
    ∀ Φ ∈ W, Q Φ ≥ 0 := by
  apply T5_transfer
  · intro K
    apply T5_compact K
    -- supply A3, RKHS, A2 hypotheses
    all_goals sorry
  · intro K Φ _ _
    rfl
```
