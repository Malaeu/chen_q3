# Proshka Debug Request: Rayleigh_Q_identification (periodization integral hang)

## TL;DR (what we need help with)
We are stuck on the lemma `integral_P_A_eq_arch_term` in
`full/q3.lean.aristotle/Q3/Proofs/Rayleigh_Q_identification.lean`.
Lean **times out** (no error, >600s) when elaborating this lemma.
We want a **simpler / faster proof strategy** for the periodization identity:

```
∫_{-1/2}^{1/2} P_A(B,t,θ) dθ = arch_term (fejer_heat_window B t)
```

Everything else (basis0 lemmas, Toeplitz diag, prime term reduction, T_P_comp diag)
should be OK or close; the periodization lemma is the bottleneck.

We need a clear, Lean-friendly approach that doesn't explode elaboration.

---

## Context + Definitions

**Main target** (Theorem 3.3, Rayleigh-Q identification):

```
theorem rayleigh_Q_identification
  (B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes B)] (hB : 0 < B) :
  (2 * M + 1 : ℝ) *
    Q3.RayleighQuotient
      (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t)
        - Q3.T_P_comp_real B B t M)
      (basis0 M)
  = Q3.Q (fun ξ => Q3.fejer_heat_window B t ξ)
```

Key definitions:
- `P_A` and `g` are in `A3_FLOOR_v22_stage4_floor.lean`:
  - `g B t ξ := Q3.a ξ * w B t ξ`
  - `P_A B t θ := 2 * Real.pi * ∑' m : ℤ, g B t (θ + m)`
- `w` in `A3_FLOOR_v20_bounds_core.lean`:
  - `w B t ξ := max 0 (1 - |ξ|/B) * exp(-4*pi^2*t*ξ^2)`
- `fejer_heat_window` in `Q3/Basic/Defs.lean`:
  - **definitionally equal** to `w`.
- `arch_term` in `Q3/Basic/Defs.lean`:
  - `arch_term Φ := ∫ ξ, a_star ξ * Φ ξ`.
- `a_star = 2*pi * a`, `g = a * w`.

So the goal is the standard periodization identity
(plus the constant `2*pi`):

```
∫_{-1/2}^{1/2} (2*pi * ∑' m, g(θ+m)) dθ
  = ∫_ℝ a_star ξ * fejer_heat_window B t ξ dξ
```

---

## Current status of file

Path: `full/q3.lean.aristotle/Q3/Proofs/Rayleigh_Q_identification.lean`

What is already proven in this file:
- `basis0`, `basis0_norm_sq`, `basis0_ne_zero`
- `quadForm_basis0`, `rayleigh_basis0`, `rayleigh_basis0_sub`
- `ToeplitzEntry_diag`, `ToeplitzEntry_diag_re`,
  `ToeplitzMatrix_Fourier_real_diag`
- `fourier_index_i0`, `prime_vec_i0`
- `T_P_comp_real_diag` (done via algebra)
- `prime_term_eq_nodes` (tsum_subtype + tsum_fintype)

The **only** heavy point is `integral_P_A_eq_arch_term`.

---

## The exact lemma that hangs (current code)

```
lemma integral_P_A_eq_arch_term (B t : ℝ) (hB : 0 < B) :
    (∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ) =
      Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) := by
  classical
  -- Compact support of g gives integrability.
  have hsupp : Function.support (fun ξ => g B t ξ) ⊆ Set.Icc (-B) B := by
    refine (Function.support_subset_iff'.2 ?_)
    intro ξ hξ
    have hnot : ¬ |ξ| ≤ B := by
      intro hle
      have : ξ ∈ Set.Icc (-B) B := by
        exact (abs_le.mp hle)
      exact hξ this
    have hge : |ξ| ≥ B := le_of_lt (lt_of_not_ge (by simpa using hnot))
    exact g_eq_zero_of_abs_ge B t ξ hB hge
  have hcompact : HasCompactSupport (fun ξ => g B t ξ) := by
    exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hint : Integrable (fun ξ => g B t ξ) := by
    exact (continuous_g B t).integrable_of_hasCompactSupport hcompact

  -- Split integral into periods and swap integral/sum
  have hsum_base :
      HasSum (fun n : ℤ =>
          ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, g B t x)
        (∫ x, g B t x) := by
    simpa using
      (MeasureTheory.Integrable.hasSum_intervalIntegral (μ:=volume)
        (f:=fun x => g B t x) (y:=(-1/2 : ℝ)) hint)
  have hsum :
      HasSum (fun n : ℤ => ∫ x in (-1/2 : ℝ)..(1/2), g B t (x + (n : ℝ)))
        (∫ x, g B t x) := by
    refine (HasSum.congr_fun hsum_base ?_)
    intro n
    have hcomp :=
      (intervalIntegral.integral_comp_add_right (f:=fun x => g B t x) (d:=(n : ℝ))
        (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ)))
    convert hcomp using 1 <;> ring

  have hsum_norm_base :
      HasSum (fun n : ℤ =>
          ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, ‖g B t x‖)
        (∫ x, ‖g B t x‖) := by
    simpa using
      (MeasureTheory.Integrable.hasSum_intervalIntegral (μ:=volume)
        (f:=fun x => ‖g B t x‖) (y:=(-1/2 : ℝ)) hint.norm)

  have hsum_norm :
      Summable (fun n : ℤ => ∫ x in (-1/2 : ℝ)..(1/2), ‖g B t (x + (n : ℝ))‖) := by
    have hnorm' :
        HasSum (fun n : ℤ => ∫ x in (-1/2 : ℝ)..(1/2), ‖g B t (x + (n : ℝ))‖)
          (∫ x, ‖g B t x‖) := by
      refine (HasSum.congr_fun hsum_norm_base ?_)
      intro n
      have hcomp :=
        (intervalIntegral.integral_comp_add_right (f:=fun x => ‖g B t x‖) (d:=(n : ℝ))
          (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ)))
      convert hcomp using 1 <;> ring
    exact hnorm'.summable

  have hswap :
      (∫ x in (-1/2 : ℝ)..(1/2), ∑' n : ℤ, g B t (x + n)) =
        ∑' n : ℤ, (∫ x in (-1/2 : ℝ)..(1/2), g B t (x + n)) := by
    -- dominated convergence on restricted measure
    have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
    have hF_int :
        ∀ n : ℤ, Integrable (fun x => g B t (x + (n : ℝ)))
          (volume.restrict (Set.Ioc (-1/2) (1/2))) := by
      intro n
      have hcont : Continuous (fun x => g B t (x + (n : ℝ))) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (continuous_g B t).comp (continuous_const.add continuous_id)
      have hI : IntegrableOn (fun x => g B t (x + (n : ℝ))) (Set.Ioc (-1/2) (1/2)) volume :=
        hcont.integrableOn_Ioc
      simpa [IntegrableOn] using hI
    have hF_sum :
        Summable fun n : ℤ =>
          ∫ x, ‖g B t (x + (n : ℝ))‖ ∂(volume.restrict (Set.Ioc (-1/2) (1/2))) := by
      refine (Summable.congr hsum_norm ?_)
      intro n
      have h := intervalIntegral.integral_of_le (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ)) hab
        (f:=fun x => ‖g B t (x + (n : ℝ))‖)
      simpa using h
    have hswap' :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm
        (μ:=volume.restrict (Set.Ioc (-1/2) (1/2)))
        (F:=fun n : ℤ => fun x => g B t (x + (n : ℝ))) hF_int hF_sum)
    -- rewrite from restricted measure to interval integral
    have hleft :
        (∫ x in (-1/2 : ℝ)..(1/2), ∑' n : ℤ, g B t (x + n)) =
          ∫ x, ∑' n : ℤ, g B t (x + n) ∂(volume.restrict (Set.Ioc (-1/2) (1/2))) := by
      simpa using
        (intervalIntegral.integral_of_le (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ)) hab
          (f:=fun x => ∑' n : ℤ, g B t (x + (n : ℝ))))
    have hright :
        (∑' n : ℤ, ∫ x in (-1/2 : ℝ)..(1/2), g B t (x + n)) =
          ∑' n : ℤ, ∫ x, g B t (x + n) ∂(volume.restrict (Set.Ioc (-1/2) (1/2))) := by
      refine tsum_congr ?_
      intro n
      simpa using
        (intervalIntegral.integral_of_le (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ)) hab
          (f:=fun x => g B t (x + (n : ℝ))))
    calc
      (∫ x in (-1/2 : ℝ)..(1/2), ∑' n : ℤ, g B t (x + n))
          = ∫ x, ∑' n : ℤ, g B t (x + n) ∂(volume.restrict (Set.Ioc (-1/2) (1/2))) := hleft
      _ = ∑' n : ℤ, ∫ x, g B t (x + n) ∂(volume.restrict (Set.Ioc (-1/2) (1/2))) := hswap'.symm
      _ = ∑' n : ℤ, ∫ x in (-1/2 : ℝ)..(1/2), g B t (x + n) := by
            simpa using hright.symm

  calc
    (∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ)
        = (2 * Real.pi) * (∫ θ in (-1/2 : ℝ)..(1/2), ∑' n : ℤ, g B t (θ + n)) := by
            simp [P_A, intervalIntegral.integral_const_mul]
    _ = (2 * Real.pi) * (∑' n : ℤ, ∫ θ in (-1/2 : ℝ)..(1/2), g B t (θ + n)) := by
          simpa using congrArg (fun x => (2 * Real.pi) * x) hswap
    _ = (2 * Real.pi) * (∫ x, g B t x) := by
          simpa using congrArg (fun x => (2 * Real.pi) * x) hsum.tsum_eq
    _ = Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) := by
          unfold Q3.arch_term Q3.a_star g
          simp [w, Q3.fejer_heat_window]
```

**This lemma is what hangs** (Lean takes >600s, no output).

---

## Observed behavior

- `lake env lean Q3/Proofs/Rayleigh_Q_identification.lean` runs for >600s and times out.
- `--profile` shows imports are fast (~3s), so the hang is in elaboration of the lemma.
- Setting `set_option maxHeartbeats 0` at top lets Lean run forever; it still doesn't finish.

So we need a proof that elaborates fast.

---

## NEW: Potential math mismatch (scaling)

We noticed a **potential normalization mismatch** in the final calc chain:

Current statement in code:
```
(2*M+1) * RQ(Toeplitz - T_P_comp, basis0) = Q(Φ)
```

But:
- `ToeplitzMatrix_Fourier_real_diag` gives
  `ToeplitzMatrix_Fourier_real ... i0 i0 = ∫ P_A`.
- `RayleighQuotient` is defined as
  `(∑ v_i A_ij v_j) / (∑ v_i^2)`, and `basis0` has norm² = 1.
  So `RQ(A, basis0) = A[i0,i0]`, **no extra factor**.
- `T_P_comp_real_diag` gives
  `(1/(2M+1)) * ∑ w_Q * Φ(ξ_n)` because `prime_vec` is normalized by `1/√(2M+1)`.

Thus:
```
RQ(Toeplitz - T_P_comp, basis0)
  = ∫ P_A - (1/(2M+1)) * ∑ w_Q Φ(ξ_n)
```

Multiplying by `(2M+1)` fixes the prime term but **also multiplies the Toeplitz term**:
```
(2M+1) * ∫ P_A   ≠  arch_term
```

So either:
1) **Statement should NOT have (2M+1)** (and Q should be defined with the 1/(2M+1) factor), or
2) **prime_vec / T_P_comp should be unnormalized**, or
3) **Toeplitz matrix should carry a compensating 1/(2M+1)** (seems unlikely),
4) or the intended vector is different (but scaling v doesn’t change RayleighQuotient).

We need your guidance: what is the *mathematically correct normalization* here?

### Evidence from the paper (rayleigh_bridge.tex)
In `full/sections/A3/rayleigh_bridge.tex` the model-space vectors are defined as
[
v_n^{(M)}(\theta) := \frac{1}{\sqrt{2M+1}} \sum_{|k|\le M} e^{2\pi i k(\theta-\xi_n)}.
]
This matches our Lean `prime_vec` normalization.

For a trigonometric polynomial
[
p(\theta)=\sum_{|k|\le M} c_k,e^{2\pi i k\theta},
]
with the **L^2(\mathbb T)** inner product, we compute
[
\langle p, v_n^{(M)}\rangle
= \frac{1}{\sqrt{2M+1}} \sum_{|k|\le M} c_k,e^{\pm 2\pi i k\xi_n},
]
so (up to the usual sign/conjugation convention)
[
\langle p, v_n^{(M)}\rangle = \frac{1}{\sqrt{2M+1}},p(\xi_n).
]

Therefore **p(\xi_n) \neq \langle p, v_n^{(M)}\rangle**; instead,
[
p(\xi_n)=\sqrt{2M+1},\langle p, v_n^{(M)}\rangle.
]

So in the Rayleigh pairing, a rank-one term contributes
[
|\langle p, v_n^{(M)}\rangle|^2=\frac{1}{2M+1},|p(\xi_n)|^2.
]

But the paper’s “Rayleigh pairing / A3-rayleigh-identification” writes the prime term
**without** this factor. That looks like the source of the mismatch with the Lean statement.

We need a judgement on the correct normalization:
- either the paper uses a **scaled evaluation functional**, or
- Lean should drop the **(1/√(2M+1))** factor in `prime_vec`, or
- the Rayleigh identification statement should include the **(1/(2M+1))**.

### Теперь по делу: что “правильно” и где именно баг

#### 1) Факт математики: где появляется √(2M+1)

Тут всё железобетонно.

- **\mathcal P_M** — пространство тригполиномов степени ≤ M.
- Базис **e_k(\theta)=e^{2\pi i k\theta}** в **L^2(\mathbb T)** (при стандартной мере d\theta
  на [-1/2,1/2]) — **ортонормированный**.
- Репродуцирующее ядро (aka Dirichlet kernel) для оценки p(\xi) в \mathcal P_M:
  [
  K_M(\theta,\xi)=\sum_{|k|\le M}e^{2\pi i k(\theta-\xi)}.
  ]
  Тогда
  [
  p(\xi)=\langle p(\cdot), K_M(\cdot,\xi)\rangle.
  ]
- Норма этого ядра:
  [
  \|K_M(\cdot,\xi)\|_{L^2(\mathbb T)}^2=\sum_{|k|\le M}1 = 2M+1.
  ]
- Если нормировать до единичной нормы:
  [
  v_\xi^{(M)} := \frac{1}{\sqrt{2M+1}} K_M(\cdot,\xi),
  ]
  то автоматически
  [
  \langle p, v_\xi^{(M)}\rangle = \frac{1}{\sqrt{2M+1}},p(\xi)
  \quad (\text{с точностью до conj/знака}).
  ]

Вывод: в `rayleigh_bridge.tex` одновременно утверждать
- v_n^{(M)} = (1/√(2M+1)) Σ e^{2πik(θ-ξ_n)}
- p(ξ_n) = ⟨p, v_n^{(M)}⟩
нельзя. Там **пропущен множитель √(2M+1)** (или неверно записана нормировка).

#### 2) Что тогда “правильнее” по смыслу проекта: три варианта

Вариант A — правим текст: вставляем фактор 1/(2M+1) в прайм-терм.
- Совместимо с нормированным `prime_vec`.
- Но тогда при p≡1 получаем прайм-сумму, делённую на (2M+1),
  и это **не** Q(Φ) из T0 (там нет деления на M).

Вариант B — убираем нормировку в `prime_vec`.
- Тогда p(ξ_n)=⟨p,v_n⟩ буквально, и прайм-терм без фактора совпадает с текстом.
- Но норма v_n становится √(2M+1), и норма rank-one оператора растёт как 2M+1,
  что ломает uniform cap по M.

Вариант C — признать, что прайм-терм в идентификации должен включать 1/(2M+1).
Это тот же вариант A, просто в виде “правильной формулы”.

#### 3) Вердикт (практично для Lean-цепочки)

- В тексте `rayleigh_bridge.tex` есть несостыковка (пропущен множитель).
- В Lean **лучше оставить нормированный `prime_vec`**, чтобы не ломать RKHS cap.
- Значит, **править нужно формулу идентификации**, а не `prime_vec`.

Идея “правильной” формулы:

```
Q(Φ) = RQ(T_M[P_A], basis0) - (2M+1) * RQ(T_P_comp, basis0)
```

То есть масштабируем **только прайм-часть**, а не всю разность.

---

## Potential simpler route (hint request)

We found archived periodization lemmas in:
`Q3/Archive/04_A3_aristotle.lean`:

- `periodize` and `integral_sum_periodize_abs_eq_L1_norm`
- `periodize_eq_sum_add`

Maybe these can be repurposed:
```
periodize f T x := ∑' k : ℤ, f (x - k*T)
```

We only need the **non-absolute** version for `f = g`, `T = 1`.

If there is a direct lemma like:
```
∫_{0}^{1} ∑' k, f(x+k) = ∫_ℝ f
```
(or with bounds `-1/2..1/2`), that would likely simplify and avoid the heavy
`integral_tsum_of_summable_integral_norm` plumbing.

---

## Additional note (minor but relevant)

`continuous_g` and `g_eq_zero_of_abs_ge` defined in
`A3_FLOOR_v22_stage4_floor.lean` are NOT accessible after `import A3_FLOOR_v22_stage4_floor`.
We had to re-define them locally in `Rayleigh_Q_identification.lean`.
So if you propose lemmas that use those, assume they are in the local namespace.

---

## What we want from you

1) A **fast** Lean-proof approach for the periodization integral
   `integral_P_A_eq_arch_term` (avoid heavy dominated-convergence machinery if possible).

2) If you can, a short lemma you would add (or refactor) to make this trivial.
   Example: a direct `intervalIntegral` periodization lemma.

3) Any suggestions on moving this lemma into a separate file or
   using existing `Q3/Archive/04_A3_aristotle.lean` results safely.

---

Thanks! This is the last blocker before wiring the Fourier A3 axiom.
