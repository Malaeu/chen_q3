# Energy Decay for Navier-Stokes Equations

## Goal
Prove that kinetic energy decreases monotonically for unforced Navier-Stokes.

## Setup
Let T³ = ℝ³/ℤ³ be the 3-torus (periodic boundary conditions).
Let u : [0,T] × T³ → ℝ³ be a smooth velocity field.
Let ν > 0 be the viscosity coefficient.

The incompressible Navier-Stokes equations:
∂u/∂t + (u · ∇)u = -∇p + ν Δu
∇ · u = 0

Define kinetic energy:
E(t) = (1/2) ∫_{T³} |u(t,x)|² dx

Define enstrophy (energy dissipation rate):
ε(t) = ∫_{T³} |∇u(t,x)|² dx

## Target Theorem
```lean
theorem energy_decreases (u : TimeDependentField) (ν : ℝ) (hν : ν > 0)
    (h_sol : IsNavierStokesSolution u ν) (t : ℝ) (ht : t ≥ 0) :
    deriv (fun s => KineticEnergy (u s)) t = -2 * ν * Enstrophy (u t)
```

## Proof Sketch

1. **Energy Derivative**: Taking the time derivative of E(t):
   dE/dt = ∫_{T³} u · (∂u/∂t) dx

2. **Substitute NS Equation**:
   dE/dt = ∫ u · (-( u · ∇)u - ∇p + ν Δu) dx
         = -∫ u · (u · ∇)u dx - ∫ u · ∇p dx + ν ∫ u · Δu dx

3. **Convection Term Vanishes**: Using incompressibility ∇ · u = 0:
   ∫ u · (u · ∇)u dx = (1/2) ∫ (u · ∇)|u|² dx
                      = (1/2) ∫ ∇ · (|u|² u) dx = 0
   by the divergence theorem on a torus.

4. **Pressure Term Vanishes**: By incompressibility:
   ∫ u · ∇p dx = ∫ ∇ · (pu) dx - ∫ p(∇ · u) dx = 0 - 0 = 0

5. **Viscosity Term**: Integration by parts:
   ν ∫ u · Δu dx = -ν ∫ |∇u|² dx = -ν · ε(t)

6. **Result**:
   dE/dt = -ν · ε(t) ≤ 0

   Energy always decreases!

## Key Lemmas Needed
- Divergence theorem on torus: ∫_{T³} ∇ · F dx = 0
- Integration by parts: ∫ u · Δu = -∫ |∇u|²
- Incompressibility condition: ∇ · u = 0

## Physical Interpretation
Energy is dissipated by viscosity at rate ν·ε(t). This is the fundamental energy law of fluid mechanics. Without external forcing, all motion eventually stops.

## Context
This theorem is the first step toward proving global regularity. If energy decreases, solutions cannot blow up in L² norm. The harder step is controlling enstrophy growth.
