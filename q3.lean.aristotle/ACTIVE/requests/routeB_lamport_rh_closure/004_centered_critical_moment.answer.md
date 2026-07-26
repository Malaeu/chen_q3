# 004 — centered critical moment

Date: `2026-07-27`

Verdict:

```text
CENTERED_S1_WEIGHTED_PROJECTION_GAP
```

Success code `CENTERED_TRIAL_CRITICAL_MOMENT_RATIO_PROVED` is not issued.

## Exact source formula

For `i=(m,N)`, `L_m=log m`, and the normalized post-Galerkin coefficients
`c_{i,n}=CoefficientFamily.kTrial i n`,

```text
q_i(t)
  = L_m^(-1/2)
      * ∑_{n=-N}^{N} (-1)^n c_{i,n} exp(2π i n t / L_m).
```

Lean declaration:

```text
Q3.RouteB.D0Pstar.centeredTrialDensity
```

The chain actually present on disk is:

```text
E_star(hTrial_m)
→ gTrial_m
→ P_m_N(gTrial_m)=gTrial_m_N
→ sTrial_m_N * gTrial_m_N=kTrial_m_N
→ c_n=<V_n_m,kTrial_m_N>.
```

The only proved norm statement at the end of this chain is
`norm_kTrial_m_N = 1` in ordinary `H_m=L²(I_m,du/u)`.

## Exact missing inequality

On one fixed cofinal path `p(k)=(m_k,N_k)`, for every
`0 ≤ σ < 1/2`, the missing statement is

```text
∃ Cσ ≥ 0, ∀ k,
  ∫_{-L_mk/2}^{L_mk/2} ‖q_p(k)(t)‖ exp(σ|t|) dt
    ≤ Cσ ‖rawFplus p(k) 0‖.
```

It is materialized as:

```text
Q3.RouteB.D0Pstar.CenteredTrialCriticalMomentRatio
```

A stronger sufficient input is materialized as:

```text
Q3.RouteB.D0Pstar.PostGalerkinCriticalExponentialMoment

∃ M ≥ 0, ∀ k,
  ∫_{-L_mk/2}^{L_mk/2} ‖q_p(k)(t)‖² exp(|t|) dt ≤ M.
```

The current D0 files contain neither estimate.

## Dependence

The required `Cσ` may depend on `σ`; it must be independent of `k`, hence
independent of both `m_k` and `N_k`.  Ordinary orthogonal-projection
contraction controls only the unweighted norm.  The missing weighted
projection constant may depend on `m`, `N`, and `σ`.

## Plants

```text
constant mode:
  sin(zL/2)/(zL/2), removable value 1 at z=0;
  on z=-iσ its moment ratio grows exponentially in L.

endpoint-Dirichlet:
  endpointDirichletWeightedProjectionPlant = PASS;
  the same two-cell orthogonal projection contracts the ordinary square norm
  and strictly expands the endpoint-weighted square norm.
```

Therefore the inference

```text
unweighted L² contraction
⇒ uniform L²(exp(|t|)) contraction
```

is false.

## Weakest repair

Add `CenteredTrialCriticalMomentRatio D p` itself as the explicit S1 source
input.  Alternatively, prove `PostGalerkinCriticalExponentialMoment D p`
together with a uniform positive lower bound for `‖rawFplus D (p k) 0‖`.
No `Set.univ`, float64 fit, `bareTransform` family, RH input, or zero-side
input is used.

## Artifact and validation

```text
Q3/Proofs/RouteB/D0CenteredCriticalMoment.lean
0 sorry
0 admit
0 new axiom
lake env lean Q3/Proofs/RouteB/D0CenteredCriticalMoment.lean: exit 0
lake build Q3.Proofs.RouteB.D0CenteredCriticalMoment: exit 0
```
