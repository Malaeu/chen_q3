# PROSHKA REQUEST v5: C1 / hA gap at one-scale t_critical

Date: 2026-01-23 (Linux work) + 2026-01-23 (local sync)

Goal: close the remaining math gap in Q3: a true C1 embedding that identifies the
Rayleigh prime block with the RKHS operator at the same heat scale t. We already
built the Lean scaffolding and one-scale bridge; the missing piece is the actual
evaluation identity / feature map.

---

## 0) TL;DR (for Proshka)

We pivoted to a single-scale chain with t_critical = 3/20 and tau = 0.
The arch side is Fourier Toeplitz P_A(B_min, t). The prime side is the Rayleigh
compression operator T_P_comp_real with weights w_Q(n) * fejer_heat_window(B,t,xi_n).

The gap: we need the *true* C1/hA match between the finite matrix T_P_comp and an
RKHS operator on H_t, i.e. an embedding iota such that

  T_P_comp = iota^* T_P_RKHS iota

for the same t (no two-scale). We already encoded the compression lemma and a minimal
RKHS interface in Lean; what is missing is the concrete RKHS data (features and
kernel sections) and the explicit evaluation identity that makes this equality real.

We need you to propose the correct RKHS and provide a Lean-ready statement of the
evaluation identity (including any normalization factors).

---

## 1) The missing statement (Lean target)

We already have a generic lemma that reduces C1 to an evaluation identity:

File: `Q3/Proofs/RKHS_Interface_C1.lean`

```lean
theorem T_P_comp_toCLM_eq_compression
    (ψ : mDim → H) (hψ : Orthonormal ℂ ψ)
    (k : Q3.Nodes K → H)
    (h_eval : ∀ (n : Q3.Nodes K) (i : mDim),
      inner ℂ (ψ i) (k n) = Q3.prime_vec M (Q3.xi_n n) i) :
    (Matrix.toEuclideanLin (Q3.T_P_comp K B t M)).toContinuousLinearMap =
      compression (ι := iota (M := M) (ψ := ψ) hψ)
        (T := T_P_RKHS_like (K := K) (B := B) (t := t) (k := k))
```

We also reduced `h_eval` to a pure evaluation statement:

File: `Q3/Proofs/Heat_RKHS_Interface.lean`

```lean
lemma h_eval_of_eval_eq_conj_prime_vec
    {ψ : mDim → R.H}
    (h_evalFun :
      ∀ (n : Q3.Nodes K) (i : mDim),
        (R.eval (Q3.xi_n n)) (ψ i) = conj (Q3.prime_vec M (Q3.xi_n n) i)) :
    ∀ (n : Q3.Nodes K) (i : mDim),
      inner ℂ (ψ i) (R.k (Q3.xi_n n)) = Q3.prime_vec M (Q3.xi_n n) i
```

**Request:** Provide the concrete RKHS H_t, the kernel sections k(x), and feature
vectors psi_i so that the evaluation identity holds with the right normalization.

---

## 2) What is already built (Lean scaffolding)

### C1 compression / embedding infrastructure
- `Q3/Proofs/C1_Embedding.lean`
  - `compression`, `compression_opNorm_le`, `dictEmbedding`, `dictEmbeddingCast`
- `Q3/Proofs/C1_T_P_comp_dictEmbedding.lean`
  - Option B: reduces opNorm bound to compression using dictionary embedding

### RKHS interface and C1 link
- `Q3/Proofs/Heat_RKHS_Interface.lean`
  - minimal RKHS package: `HeatRKHS` with eval and reproducing vectors
  - converts evaluation identity to the needed inner-product identity
- `Q3/Proofs/RKHS_Interface_C1.lean`
  - constructs `iota` from an orthonormal feature family
  - defines `T_P_RKHS_like` and proves `T_P_comp_toCLM_eq_compression` under `h_eval`

### Nontrivial "hA" target (factorization)
- `Q3/Proofs/RKHS_hA_prime.lean`
  - exact matrix factorization: `T_P_comp = V^* D V`
  - this is *not* an isometry yet; it is the algebraic target

### One-scale A3 bridge (t = t_critical)
- `Q3/Proofs/Params_Critical.lean`:
  - `t_critical = 3/20`, `t0_critical`, and reparam identity
- `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`:
  - single-scale Rayleigh bridge `A3_bridge_data_rayleigh_Fourier_at`
  - assumes floor + weight-sum cap for the *same t*
- `Q3/Proofs/A3_Floor_Critical_Goal.lean`:
  - explicit Prop target for the floor at t_critical (not an axiom)

### RKHS cap (current state)
- `Q3/Proofs/RKHS_cap_rayleigh.lean`:
  - proven cap via weight-sum and a C1 lift
  - currently uses a *placeholder* "kernel dictionary" in EuclideanSpace
    (finite-dimensional model), not the true RKHS

---

## 3) The exact gap (what we need from you)

We need a mathematically correct RKHS model and feature map that makes the
evaluation identity match the prime vectors. Concretely:

1) Choose H_t and kernel k_t(x, y) (Gaussian/heat kernel on the torus).
2) Define feature functions psi_i (likely Fourier basis with t-weight).
3) Prove, for every node n and index i:
   eval(xi_n n) (psi_i) = conj (prime_vec M (xi_n n) i)
   (or an equivalent identity with clear normalization factors).
4) From this, derive `h_eval` and instantiate `T_P_comp_toCLM_eq_compression`.

This is the nontrivial C1/hA match and is the only real mathematical gap in the
single-scale chain.

---

## 4) DO NOT DO (known landmines)

- Do NOT mix two heat scales (t_sym vs t_rkhs). We are single-scale now.
- Do NOT use a_star in A3; the symbol is P_A (period-1).
- Do NOT use sampling Toeplitz; we use Fourier Toeplitz.
- Do NOT assume tau != 0; we fix tau = 0 in the main chain.
- Do NOT use the placeholder kernel_dict as if it were the true RKHS.

---

## 5) Diff map (Linux work, 2026-01-23) with file stats

Use these to open full diffs (`git show <hash>`):

```text
0f695c1  A3_FLOOR@t_critical blocker note + Lean goal
  A  Q3/Proofs/A3_Floor_Critical_Goal.lean
  M  docs/INSIGHTS.md

2afdb4f  Generalize P_A continuity/local finiteness in t
  A  Q3/Proofs/P_A_Properties.lean
  M  Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean

adacbda  One-scale A3 bridge scaffolding + generic weight_sum cap
  M  CLAUDE.md
  M  PROJECT_ORCHESTRATOR.md
  A  Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean
  A  Q3/Proofs/RKHS_cap_generic.lean
  M  docs/INSIGHTS.md

65654a8  Clarify git-vs-proof branches + parallel streams
  M  PROJECT_ORCHESTRATOR.md

6baeee4  Add Aristotle task: Gaussian RKHS kernel integral identity
  A  aristotle_input/gaussian_rkhs_kernel_v1.lean
  A  aristotle_input/gaussian_rkhs_kernel_v1.md

ee52922  RKHS eval->inner bridge cleanup + INSIGHTS update
  M  Q3/Proofs/Heat_RKHS_Interface.lean
  M  docs/INSIGHTS.md

7970386  One-scale t_critical params + hA decision-tree tooling
  M  CLAUDE.md
  M  PROJECT_ORCHESTRATOR.md
  A  Q3/Proofs/OpNorm_Unitary.lean
  A  Q3/Proofs/Params_Critical.lean
  M  Q3/Proofs/Q_nonneg_t_critical.lean
  M  Q3/T5_Transfer.lean
  M  docs/INSIGHTS.md

a947539  RKHS interface + conditional C1 compression matching
  M  CLAUDE.md
  A  Q3/Proofs/Heat_RKHS_Interface.lean
  A  Q3/Proofs/RKHS_Interface_C1.lean
  A  Q3/Proofs/RKHS_hA_prime.lean
  M  Q3/Proofs/RKHS_cap_rayleigh.lean
  A  Q3/Proofs/C1_T_P_comp_dictEmbedding.lean
  M  docs/INSIGHTS.md
```

Local sync (post-Linux):

```text
b4d0985  Wire RKHS cap through C1 kernel dict
  M  Q3/Proofs/RKHS_cap_rayleigh.lean
```

---

## 6) Quick file pointers (high signal)

- `Q3/Proofs/RKHS_Interface_C1.lean` (main C1 statement)
- `Q3/Proofs/Heat_RKHS_Interface.lean` (eval -> inner reduction)
- `Q3/Proofs/RKHS_hA_prime.lean` (matrix factorization target)
- `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` (one-scale A3 bridge)
- `Q3/Proofs/Params_Critical.lean` (t_critical)
- `aristotle_input/gaussian_rkhs_kernel_v1.*` (analytic kernel identity)

---

## 7) Deliverable from Proshka

1) Concrete RKHS model H_t and kernel sections k(x).
2) Explicit features psi_i with evaluation identity against prime_vec.
3) Any necessary normalization factors (2pi, conjugation, etc).
4) Lean-ready statement of the identity, or a math lemma that we can map into
   `h_eval_of_eval_eq_conj_prime_vec`.

If you can also state a minimal proof path (or references) for the kernel identity,
we can feed that to Aristotle.

---

END OF PROSHKA REQUEST v5
