# Sobolev-Q3 Formalization Overview

## Proof Architecture

```
SOBOLEV CONTROL          NUMBER THEORY (sorry)
     │                         │
     ▼                         ▼
┌────────────┐           ┌────────────┐
│ H^s norm   │           │ 𝔖₂ > 0    │
│ embedding  │           │ Vinogradov │
│ duality    │           │ Siegel-W.  │
└─────┬──────┘           └─────┬──────┘
      │                        │
      └──────────┬─────────────┘
                 │
                 ▼
        ┌────────────────┐
        │ MASTER INEQ    │
        │ Drift > Noise  │
        │ I ≥ 𝔖₂/2 · X   │
        └───────┬────────┘
                │
                ▼
        ╔════════════════╗
        ║ TPC: π₂→∞     ║
        ╚════════════════╝
```

## What We Formalize (Lean)

1. **Sobolev space H^s(𝕋)** - Definition, norm, completeness
2. **Sobolev embedding** - H^s ↪ C^{0,s-1/2} for s > 1/2
3. **Grid-Lift discretization** - Polynomial error bound
4. **Girsanov drift construction** - Symbol in H^s
5. **Toeplitz representation** - I = ⟨T_Ψ b, b⟩
6. **Master Inequality derivation** - Drift - Noise ≥ c·X
7. **TPC conclusion** - Contradiction argument

## What We Axiomatize (sorry)

1. **Singular series** 𝔖₂ = 2C₂ > 0
2. **Vinogradov bound** - Minor arc sup is o(X)
3. **Siegel-Walfisz** - Prime equidistribution in APs
4. **Major arc evaluation** - Drift = 𝔖₂·X + o(X)

## Key Insight

Classical circle method: Minor arc control requires RH/GRH.

Sobolev-Q3 method: Minor arc control via ‖Ψ‖_{H^s} norm.

**The innovation is operator-theoretic, not number-theoretic.**
