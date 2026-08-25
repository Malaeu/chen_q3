# STATUS: LEGENDRE_QCOMB_PREFLIGHT — DISCRIMINATOR FAIL WITH EXACT OBSTRUCTION SCALING; H-PART SPLITS OFF UNCONDITIONALLY

```yaml
ARTIFACT_CLASS: LINUX_DERIVATIVE_PREFLIGHT
GOAL: GOAL_058
GAP: W5_LOG_DERIVATIVE_BUDGET_BOUNDED
PARENT_VERDICT: 70d46d5d (Legendre Q-comb preflight selection)
DISCRIMINATOR: LEGENDRE_QCOMB_BOUND_FROM_COMMITTED_WEIGHTED_ROW
DISCRIMINATOR_OUTCOME: FAIL
SMALLEST_MISSING: two alternative packages, quantified below (C1-L1 or C1-L2)
UNCONDITIONAL_SPLIT: TARGET_H_BUDGET_NODE (no source hypotheses, Lean-ready)
AUTHOR_BODY: LINUX_CLAUDE (LINUX_STANDING_GRANT_2026-08-25)
RH_CLAIM: false
```

## 1. Exact representation (per seam cell, all endpoint terms kept)

Physical comb at `u in [lambda^{-1}, lambda]`, active set `n <= M(u) = floor(lambda/u)`,
`g(y) := y * pkt'(y)`:

```
Qcomb(u) = sum_{n=1}^{M} g(n*u).
```

Order-1 Euler–Maclaurin with the periodized Bernoulli `B1~(t) = t - floor(t) - 1/2`
(exact identity, nothing dropped; `g(0) = 0`):

```
Qcomb(u) = (1/u) * INT_0^{Mu} g(y) dy            [leading]
         + (1/2) * g(Mu)                          [edge midpoint]
         + INT_0^{M} B1~(t) * u * g'(t*u) dt      [remainder, |.| <= (1/2)*INT_0^{Mu} |g'|]
```

Leading term, integrated exactly by parts with the ZERO HALF-MASS of the packet
(`INT_0^{lambda} pkt = 0`, even + committed zero mass):

```
INT_0^{Mu} g = Mu * pkt(Mu) - INT_0^{Mu} pkt = Mu * pkt(Mu) + INT_{Mu}^{lambda} pkt,
```

both controlled by the committed C0/edge data (`Mu in (lambda-u, lambda]`,
`|pkt| <= C/lambda^2 + 4|H|` with `H` Gaussian-small near the edge).

Legendre form: with `s = y/lambda`, `pkt'(y) = (scale/lambda) * sum_q a_q P'_{2q}(s)`;
`g` has NO extra physical lambda power, and

```
Qcomb(u) = sum_q a_q * K_q(M, r),  r = u/lambda,
K_q(M, r) = sum_{n<=M} (n*r) * P'_{2q}(n*r)      [finite Faulhaber kernel]
```

with `sum_q a_q * (1/r)*G_q(w)` resumming EXACTLY to the leading term above
(`G_q(w) = w*P_{2q}(w) - INT_0^w P_{2q}`, `G_q(1) = P_{2q}(1) = 1`).

## 2. Budget ledger with exact lambda scaling

`B_k = INT u^{-1/2} |Qcomb(u)| du` over the window; `INT u^{-1/2} du ~ 2 sqrt(lambda)`.

| Term | Bound by | lambda scale | Verdict |
|---|---|---|---|
| leading (zero half-mass + edge C0) | committed F72.6/edge rate | `<= 2(C+132) * lambda^{-1/2}` | CLOSED by committed data |
| edge midpoint `(1/2) g(Mu)` | edge SLOPE `lambda*|pkt'(edge)|`, u-uniform | `~ lambda^{3/2} * sup_edge|pkt'|` | needs edge-slope rate `<= c*lambda^{-3/2}` |
| E-M remainder | `INT_0^lambda (|pkt'| + y|pkt''|)`, u-uniform | `~ sqrt(lambda) * (that L1 mass)` | needs `INT(|pkt'|+y|pkt''|) <= c*lambda^{-1/2}` |

## 3. Why the committed coefficient row cannot pay (the honest kill)

The committed row gives `sum_q (q+1)^2 |a_q| =: R_k < infinity` QUALITATIVELY per k.
Translating the obstruction terms into rows: edge midpoint `<= |scale| * R_k`
(via `|P'_{2q}| <= q(2q+1)`), remainder `<= |scale| * (c1*R_k + c2*sum_q q^3 |a_q|)`
(via `INT_0^1 |P'_{2q}| <= sqrt(2q(2q+1))` and the `P''` row).  But the TRUE
cofinal scaling of `R_k` is NOT bounded: the physical mode has internal scale
O(1) in `y`, hence scale `1/lambda` in `s = y/lambda`; a profile with an
`1/lambda` feature has Legendre mass at `q ~ lambda`, so `R_k ~ lambda`
(consistency check: `||pkt'||_inf <= 2|scale| R_k / lambda` must stay O(1),
which forces `R_k ~ lambda`).  Citing the qualitative summability would hide
exactly this k-dependence — the STRONGEST ATTACK clause fires as predicted.

* P_DERIV_LEGENDRE_1 (0.66): REFUTED as stated.  The representation DOES expose
  the leading cancellation (zero half-mass, term 1 closes), but the surviving
  functionals exceed committed data.
* P_DERIV_LEGENDRE_2 (0.72): CONFIRMED.  The failure is precisely the lack of a
  cofinal uniform bound on the weighted functionals; interchange/differentiation
  legality was never the issue.

## 4. The smallest sufficient missing quantities (defect split)

Split `pkt = 4H + delta`, `||delta||_inf <= C/lambda^2` committed.  Then
`B_k <= B_H + B_delta` and:

**(H-part, UNCONDITIONAL):** `B_H = INT u^{-1/2} |sum_n g_H(n u)| du` with
`g_H(y) = 4 y H'(y)` EXPLICIT (`H = explicitCCMLimitH`).  Same E-M mechanism:
zero half-mass of `H` exact, Gaussian decay pays the large-u region.
`B_H <= D_H` absolute constant — Lean-ready with NO source hypotheses.
This matches the signed-probe numerics (Derivative ~ 0.4467 constant).
Recommend committing this node regardless of the defect decision:
it converts `W5_LOG_DERIVATIVE_BUDGET_BOUNDED` into a pure defect statement.

**(delta-part, the genuine gap) — either package suffices:**

* PACKAGE C1-L1: `INT_0^lambda (|delta'| + y*|delta''|) dy <= c / sqrt(lambda)`
  together with the edge-slope rate `|delta'(y)| <= c * lambda^{-3/2}` on
  `(lambda - 1, lambda]`.  (Then every ledger line above closes.)
* PACKAGE C1-L2: `||delta'||_{L2(0,lambda)} <= c / lambda^2`.
  (Cauchy–Schwarz over the comb: `INT u^{-1/2}|Qcomb_delta| <= 2 lambda^2 ||delta'||_2`.)

**Adjudication of the runner-up as literally stated:** the candidate
`||pkt' - 4H'||_inf <= C1/sqrt(lambda)` is INSUFFICIENT: even with the
cancellation-aware ledger it pays only `INT|delta'| <= lambda * C1/sqrt(lambda)
= C1*sqrt(lambda)`, which the u-integral multiplies to `lambda` growth.  The
sup-norm package would need `lambda^{-3/2}`, i.e. lambda^1 stronger than the
runner-up.  The L2 package (`lambda^{-2}`) is the natural target of the
SECOND_RUNNER_UP Sturm/ODE-residual route: from the C0 rate `C/lambda^2` one
derivative typically costs one internal frequency (O(1) here), so
`||delta'||_2 ~ ||delta||_2 ~ lambda^{-3/2} — sqrt(lambda) short of lambda^{-2}`
unless the energy estimate exploits the eigenvalue defect; that margin is the
exact question for the Sturm route.

## 5. CLOSES / OPENS

CLOSES: LEGENDRE_QCOMB_BOUND_FROM_COMMITTED_WEIGHTED_ROW (outcome FAIL, with
the exact ledger), plus the leading-term half of the derivative wall (zero
half-mass + edge C0 — committed data suffices there).
OPENS: TARGET_H_DERIVATIVE_BUDGET_NODE (unconditional, Lean-ready — proposed).
CARRIES: the delta-part gap, awaiting package selection (C1-L1 vs C1-L2/Sturm).
