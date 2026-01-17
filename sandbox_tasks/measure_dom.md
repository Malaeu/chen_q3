# Task: measure_dom

## Goal

**Prove:** Measure domination — discrete prime sum bounded by continuous arch integral.

## Mathematical Statement

$$\sum_{n \geq 2} w_Q(n) \cdot \Phi(\xi_n) \leq \int_{\mathbb{R}} a^*(\xi) \cdot \Phi(\xi) \, d\xi$$

via disjoint neighborhoods around prime nodes.

## Key Insight

**Approach:**
1. Around each prime node $\xi_n$, take neighborhood $I_n = [\xi_n - \delta_n, \xi_n + \delta_n]$
2. Make neighborhoods **disjoint** (use prime gap)
3. Show $w_Q(n) \leq \int_{I_n} a^*(\xi) d\xi$ (density comparison)
4. Sum up

## Problem

**Prime gap shrinks:**
$$\xi_{n+1} - \xi_n = \frac{\log((n+1)/n)}{2\pi} \approx \frac{1}{2\pi n}$$

At large $n$, neighborhoods may overlap.

## Aristotle Reference

- **Input:** `full/q3.lean.aristotle/aristotle_input/measure_domination_v1.md`
- **UUID:** `d7bf9689-4431-4ea0-90df-170f7bb82d6c`

## Proof Strategy

### Option A: Truncated Sum
Work with $n \leq N_0$ where gaps are big enough, handle tail separately.

### Option B: Weighted Neighborhoods
Use $\delta_n \propto 1/n$ to match shrinking gaps.

### Option C: Different Approach
Use Stieltjes integral representation instead of explicit neighborhoods.

## Key Files

- `full/q3.lean.aristotle/docs/insights/localization_argument_full_analysis_2026_01_16.md`
- `full/q3.lean.aristotle/aristotle_input/measure_domination_v1.md`

## Success Criteria

- [ ] Disjoint neighborhood construction (or alternative)
- [ ] Density comparison proven
- [ ] Full bound established
- [ ] `lake build Q3.Main` passes
- [ ] Changes committed

## Difficulty Rating

**5/10** — May work with cutoff, but not trivial for all $n$.

## Notes

*(Agent: add your notes here as you work)*
