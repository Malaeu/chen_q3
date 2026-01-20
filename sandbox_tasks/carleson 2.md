# Task: carleson

## Goal

**Prove:** Prime sampling measure is a **Carleson measure** for the heat kernel RKHS.

## Mathematical Statement

The measure $\mu = \sum_{n \geq 2} w_Q(n) \cdot \delta_{\xi_n}$ satisfies the Carleson condition:

$$\sum_{n: \xi_n \in I} w_Q(n) \leq C \cdot |I|$$

for all intervals $I \subset \mathbb{R}$, where:
- $\xi_n = \log(n)/(2\pi)$ (prime nodes)
- $w_Q(n) = 2\Lambda(n)/\sqrt{n}$ (von Mangoldt weights)

## Key Insight

**Why it should work:**
- Prime nodes are **sparse**: density $\sim \pi(e^{2\pi\xi})/\xi \approx e^{2\pi\xi}/(2\pi\xi^2)$
- Weights **decay**: $w_Q(n) \leq 2\log(n)/\sqrt{n}$
- Heat RKHS has **smoothing property** — Carleson embedding may be easier

## Aristotle Reference

- **Input:** `full/q3.lean.aristotle/aristotle_input/carleson_rkhs_v1.md`
- **UUID:** `427880cd-3101-4e37-a162-079254ed9ef9`

## Proof Strategy

1. **Local density bound**: For interval $[a, b]$, count prime nodes
2. **Weight sum bound**: Use PNT to bound $\sum_{n: \xi_n \in [a,b]} w_Q(n)$
3. **Carleson condition**: Show sum $\leq C \cdot (b-a)$

## Alternative: RKHS Embedding

Instead of Carleson, show directly:
$$\sum_{n \geq 2} w_Q(n) |f(\xi_n)|^2 \leq C \cdot \|f\|_{\mathcal{H}_t}^2$$

for all $f$ in heat RKHS $\mathcal{H}_t$ with kernel $K_t(\xi, \eta) = e^{-2\pi^2 t|\xi-\eta|^2}$.

## Key Files

- `full/q3.lean.aristotle/docs/insights/localization_argument_full_analysis_2026_01_16.md`
- `full/q3.lean.aristotle/Q3/Proofs/RKHS_cap_rayleigh.lean` — existing RKHS work

## Success Criteria

- [ ] Carleson condition proven (or RKHS embedding)
- [ ] Connects to existing RKHS machinery
- [ ] `lake build Q3.Main` passes
- [ ] Changes committed

## Difficulty Rating

**8/10** — Most promising approach but needs careful PNT estimates.

## Notes

*(Agent: add your notes here as you work)*
