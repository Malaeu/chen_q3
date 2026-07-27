## CODEX DIRECTIVE

Целевой target:

```markdown
CENTERED_TRIAL_CRITICAL_MOMENT_RATIO
```

## Statement

Для одного exact cofinal path `p(k)=(m_k,N_k)` и centered density
`q_{p(k)}`, для каждого

```text
0 ≤ σ < 1/2
```

доказать

```text
∃ Cσ < ∞, ∀ k,
  ∫_{-L_mk/2}^{L_mk/2} |q_p(k)(t)| exp(σ|t|) dt
    ≤ Cσ |Fplus_p(k)(0)|.
```

`Cσ` может зависеть от `σ`; равномерность при `σ ↑ 1/2` не требуется.

## Route

```markdown
1. Read actual D0KTrialStage1–3.lean, not answer reports.
2. Expand E_star, gTrial_m, P_m_N, sTrial_m_N.
3. Locate exact sqrt(n)/critical-weight factor.
4. Separate unprojected tail from direct L1 leakage.
5. Run constant-mode and endpoint-Dirichlet planted failures first.
6. Prove the L1 ratio or isolate its smallest direct leakage lemma.
```

## Guard from Proshka, relayed by Mythos

```markdown
Do not prove uniform boundedness of the projection in full L2(exp(|t|)).
That route is unnecessary and probably false.

The target is only the L1 moment ratio with exp(σ|t|), separately for every
fixed σ < 1/2.

Every report must state:
- leakage dependence on (m,N,σ);
- behavior of the denominator Fplus(0).

Outcome codes:
GREEN / REPAIRABLE_LEAK / FATAL_PATH.
```

## Forbidden

```markdown
no float64 as proof;
no unweighted L2 contraction used in weighted space;
no full-weight L2(exp(|t|)) projection route;
no Set.univ claim;
no fitted 0.878 constant;
no return to bareTransform Pstar;
no RH/zero-side input.
```

## Validation

```markdown
lake env lean Q3/Proofs/RouteB/D0CenteredCriticalMoment.lean
lake build Q3.Proofs.RouteB.D0CenteredCriticalMoment
grep -R "sorry\\|admit\\|axiom" Q3/Proofs/RouteB/D0CenteredCriticalMoment.lean
```

## Success

```markdown
CENTERED_TRIAL_CRITICAL_MOMENT_RATIO_PROVED
```

## Failure report

```markdown
GREEN / REPAIRABLE_LEAK / FATAL_PATH:
- exact source formula;
- exact missing inequality;
- leakage dependence on (m,N,σ);
- denominator Fplus(0);
- planted-counterexample status;
- weakest direct L1 repair.
```

---

Гол извлечён Mythos из вердикта Прошки 2026-07-27. Новый guard имеет
приоритет над прежней full-weight L2 формулировкой.
