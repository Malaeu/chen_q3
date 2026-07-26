## CODEX DIRECTIVE

???? ????????? target:

```markdown
CENTERED_TRIAL_CRITICAL_MOMENT_RATIO
```

## Statement

??? exact cofinal path $p(k)=(m_k,N_k)$, centered density $q_{p(k)}$ ? ???????

$$
0\le\sigma<\frac12,
$$

????????

$$
\exists C_\sigma<\infty,\quad
\forall k,\quad
\int_{-L_{m_k}/2}^{L_{m_k}/2}
|q_{p(k)}(t)|e^{\sigma|t|}\,dt
\le
C_\sigma |F^+_{p(k)}(0)|.
$$

## Route

```markdown
1. Read actual D0KTrialStage1�3.lean, not answer reports.
2. Expand E_star, gTrial_m, P_m_N, sTrial_m_N.
3. Locate exact sqrt(n)/critical-weight factor.
4. Separate unprojected tail from weighted projection cost.
5. Run constant-mode and endpoint-Dirichlet planted failures first.
6. Prove theorem or isolate smallest missing weighted-projection lemma.
```

## Forbidden

```markdown
no float64 as proof;
no unweighted L2 contraction used in weighted space;
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
CENTERED_S1_WEIGHTED_PROJECTION_GAP:
- exact source formula;
- exact missing inequality;
- dependence on m,N,?;
- planted counterexample passed;
- weakest repaired theorem.
```

---


(Гол извлечён Mythos из вердикта Прошки 2026-07-27; исполнять дословно. После него — гол 005: centeredPstarFamily + strip-рефакторинг скелета по Kill 7, отдельным коммитом.)
