# Q Functional is Lipschitz on W_K

## Setup

Let K > 0 be a compact parameter. Define:

- **W_K**: The space of functions Φ : ℝ → ℝ that are:
  - Continuous on [-K, K]
  - Supported in [-K, K] (i.e., Φ(x) = 0 for |x| > K)
  - Even: Φ(-x) = Φ(x)
  - Nonnegative: Φ(x) ≥ 0

- **Archimedean kernel**: a*(ξ) = 2π(log π - Re(ψ(1/4 + iπξ))) where ψ is the digamma function.
  Key property: a*(ξ) > 0 for all ξ (Titchmarsh).

- **Prime weights**: w_Q(n) = 2Λ(n)/√n where Λ is the von Mangoldt function.

- **Spectral coordinate**: ξ_n = log(n)/(2π)

- **Q functional**: Q(Φ) = arch_term(Φ) - prime_term(Φ) where:
  - arch_term(Φ) = ∫_{-∞}^{∞} a*(ξ) · Φ(ξ) dξ
  - prime_term(Φ) = Σ_{n≥2} w_Q(n) · Φ(ξ_n)

- **Sup norm on K**: ‖Φ‖_K = sup{|Φ(x)| : x ∈ [-K, K]}

## Theorem (Q is Lipschitz on W_K)

For any K > 0, there exists L > 0 such that for all Φ₁, Φ₂ ∈ W_K:

|Q(Φ₁) - Q(Φ₂)| ≤ L · ‖Φ₁ - Φ₂‖_K

where ‖Φ₁ - Φ₂‖_K = sup{|Φ₁(x) - Φ₂(x)| : x ∈ [-K, K]}.

## Proof Sketch

**Step 1: Decompose Q difference**

Q(Φ₁) - Q(Φ₂) = [arch_term(Φ₁) - arch_term(Φ₂)] - [prime_term(Φ₁) - prime_term(Φ₂)]

**Step 2: Bound arch_term difference**

arch_term(Φ₁) - arch_term(Φ₂) = ∫ a*(ξ) · (Φ₁(ξ) - Φ₂(ξ)) dξ

Since Φ₁, Φ₂ are supported in [-K, K]:
|arch_term(Φ₁) - arch_term(Φ₂)| ≤ ∫_{-K}^{K} a*(ξ) · |Φ₁(ξ) - Φ₂(ξ)| dξ
                                 ≤ ∫_{-K}^{K} a*(ξ) dξ · ‖Φ₁ - Φ₂‖_K
                                 ≤ 2K · max_{|ξ|≤K} a*(ξ) · ‖Φ₁ - Φ₂‖_K

Let M_a = max_{|ξ|≤K} a*(ξ) (exists and is finite by continuity of a* on compact).

**Step 3: Bound prime_term difference**

prime_term(Φ₁) - prime_term(Φ₂) = Σ_{n≥2} w_Q(n) · (Φ₁(ξ_n) - Φ₂(ξ_n))

Key observation: Only finitely many nodes ξ_n lie in [-K, K].
Since ξ_n = log(n)/(2π), we have |ξ_n| ≤ K ⟺ n ≤ exp(2πK).

Let ActiveNodes(K) = {n ≥ 2 : |ξ_n| ≤ K}. This is a finite set.

For n ∉ ActiveNodes(K): both Φ₁(ξ_n) = 0 and Φ₂(ξ_n) = 0 (outside support).

So: |prime_term(Φ₁) - prime_term(Φ₂)| ≤ Σ_{n ∈ ActiveNodes(K)} w_Q(n) · |Φ₁(ξ_n) - Φ₂(ξ_n)|
                                       ≤ Σ_{n ∈ ActiveNodes(K)} w_Q(n) · ‖Φ₁ - Φ₂‖_K
                                       = W_sum(K) · ‖Φ₁ - Φ₂‖_K

where W_sum(K) = Σ_{n ∈ ActiveNodes(K)} w_Q(n) is finite.

**Step 4: Combine bounds**

|Q(Φ₁) - Q(Φ₂)| ≤ |arch_term difference| + |prime_term difference|
                ≤ (2K · M_a + W_sum(K)) · ‖Φ₁ - Φ₂‖_K

Set L_Q(K) = 2K · M_a + W_sum(K) > 0.

## Key Lemmas Needed

1. **a* bounded on compacts**: For K > 0, there exists M > 0 such that |a*(ξ)| ≤ M for all |ξ| ≤ K.
   (Follows from continuity of a* and compactness of [-K, K].)

2. **ActiveNodes finite**: {n ≥ 2 : |log(n)/(2π)| ≤ K} ⊆ {2, ..., ⌊exp(2πK)⌋} is finite.

3. **W_sum finite**: Σ_{n ∈ ActiveNodes(K)} w_Q(n) < ∞ (finite sum of positive terms).

4. **L_Q positive**: L_Q(K) = 2K · sup{a*(ξ) : |ξ| ≤ K} + W_sum(K) > 0.
   (Since K > 0, a*(0) > 0, and W_sum ≥ 0.)

## Expected Lean Statement

```lean
theorem Q_Lipschitz_on_W_K (K : ℝ) (hK : K > 0) :
    ∃ L > 0, ∀ Φ₁ ∈ W_K K, ∀ Φ₂ ∈ W_K K,
      |Q Φ₁ - Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K}
```
