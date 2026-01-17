# Task: arch_prime

## Goal

**Prove:** `arch_term ≥ prime_term` for Fejér×heat windows via localization argument.

## Mathematical Statement

For the test window $\Phi_{B,t}(\xi) = (1 - |\xi|/B)_+ \cdot e^{-4\pi^2 t \xi^2}$ and prime nodes $\xi_n = \log(n)/(2\pi)$:

$$\int_{\mathbb{R}} a^*(\xi) \Phi(\xi) \, d\xi \geq \sum_{n \geq 2} w_Q(n) \cdot \Phi(\xi_n)$$

for $t \geq t_0$ (threshold around 15-40).

## Key Insight

**π-cancellation magic:**
$$4\pi^2 \xi_n^2 = (\log n)^2$$

Therefore $\Phi(\xi_n) \leq e^{-t(\log n)^2}$, and at $t=40$:
- $\Phi(\xi_2) \approx 4.5 \times 10^{-9}$
- arch_term $\sim O(1/\sqrt{t})$ (polynomial decay)
- prime_term $\sim O(e^{-t(\log 2)^2})$ (exponential decay)

**Exponential beats polynomial.**

## Aristotle Reference

- **Input:** `full/q3.lean.aristotle/aristotle_input/arch_ge_prime_rigorous_v1.md`
- **UUID:** `4b483ef3-eb90-4317-a690-b55981a0b73e`

Check `full/q3.lean.aristotle/aristotle_output/` for completed proofs.

## Proof Strategy

1. **Lemma `pi_cancellation`**: Show $4\pi^2 \xi_n^2 = (\log n)^2$ (algebraic)
2. **Lemma `prime_sum_bound`**: Upper bound $\sum w(n) e^{-t(\log n)^2} \leq C \cdot e^{-t(\log 2)^2}$
3. **Lemma `arch_lower_bound`**: Lower bound $\int a^*(\xi)\Phi(\xi)d\xi \geq c/\sqrt{t}$
4. **Theorem `arch_ge_prime`**: Compare for $t \geq t_0$

## Key Files

- `full/q3.lean.aristotle/Q3/Axioms.lean` — current axioms
- `full/q3.lean.aristotle/Q3/Proofs/` — existing proofs
- `full/q3.lean.aristotle/docs/insights/localization_argument_full_analysis_2026_01_16.md` — detailed analysis

## Success Criteria

- [ ] `pi_cancellation` lemma proven
- [ ] `prime_sum_bound` lemma proven
- [ ] `arch_lower_bound` lemma proven
- [ ] `arch_ge_prime` theorem proven
- [ ] `lake build Q3.Main` passes
- [ ] Changes committed

## Notes

*(Agent: add your notes here as you work)*
