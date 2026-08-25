# STATUS: R2_N2_WEIGHTED_COEFFICIENT_IDENTITY_GAP — with the exact identity in hand and a falsity argument for the first conjunct

```yaml
ARTIFACT_CLASS: LINUX_R2_PREFLIGHT
GOAL: GOAL_058
FRONT: G6_S2_D0_SELECTED_PROLATE_PHYSICAL_FOURIER_ENERGY_SOURCE_SUPPLIER_R2
SUBTARGET: PHYSICAL_FOURIER_COEFFICIENT_WEIGHTED_RECURRENCE
PARENT_VERDICT: b2135bd1 (R2 selection)
DISCRIMINATOR: R2_EXACT_N2_WEIGHTED_COEFFICIENT_IDENTITY
DISCRIMINATOR_OUTCOME: FAIL_AS_SPECIFIED
STRONGER_FINDING: FIRST_CONJUNCT_GENERICALLY_FALSE_ON_LITERAL_OBJECT
PROBE: scripts/r2_coefficient_identity_probe.py (registered, DIAGNOSTIC ONLY)
AUTHOR_BODY: LINUX_CLAUDE (LINUX_STANDING_GRANT_2026-08-25)
RH_CLAIM: false
```

## 1. The exact identity (all boundary terms explicit, no vanishing assumed)

Log coordinate `x = log(lambda*u) in [0, L]`, `L = 2*log(lambda)`, `u = exp(x)/lambda`,
`du/u = dx`. The literal coefficient is

```
c_n = inner(V_n_m i n, gTrial_m ...) = L^{-1/2} * int_0^L exp(-2*pi*i*n*x/L) G(x) dx,
G(x) = sqrt(u) * sum_{p>=1} h(p*u),  h = prolateCombination (selected pair).
```

`h` has support in `[-lambda, lambda]`; term `p` lives on `x <= L - log(p)`.
Interior seams sit at `x_p = L - log(p)` for `2 <= p < m` (`m = lambda^2`),
each with jump `-sqrt(lambda/p) * h(lambda-)`, where `h(lambda-)` is the single
edge limit of the packet. Cell-wise integration by parts over the seam
partition gives, exactly, for every nonzero `n`:

```
(2*pi*i*n/L) * c_n
  = L^{-1/2} * G(0+)                                   [left trace]
  - L^{-1/2} * sqrt(lambda) * h(lambda-) * D_n         [seam family + right trace]
  + Ghat'_n                                            [ell^2 part: coefficient of G']

D_n = sum_{p=1}^{m-1} p^{-1/2} * exp(2*pi*i*n*log(p)/L)
```

`D_n` is the length-`m` partial sum of the zeta Dirichlet series on the
critical line, sampled at `t = -2*pi*n/L`. The `p=1` term of `D_n` carries the
right trace `G(L-) = sqrt(lambda)*h(lambda-)`.

No prolate-ODE input is needed to reach this identity, and the ODE cannot
change it: the ODE constrains interior regularity (already held: the mode-4
Ferrers series is C^2 interior, `mode4FerrersSeries_contDiffOn_two_Ioo`),
while every non-ell^2 term above is boundary/seam data.

## 2. Consequence: per-k summability is equivalent to exact vanishing

Given `G' in L^2` per k, the sequence `(2*pi*n/L)*c_n` is in `ell^2(n)` iff
the almost-periodic part `L^{-1/2}*(G(0+) - sqrt(lambda)*h(lambda-)*D_n)`
tends to 0, iff its mean square vanishes:

```
mean square = |G(0+) - G(L-)|^2 + lambda*|h(lambda-)|^2 * sum_{p=2}^{m-1} 1/p
```

(the frequencies `log(p)/L` are distinct for distinct `p < m`; the only
resonance `p <-> p*m` inside range is `p=1 <-> p=m`, and `p=m` has empty
support, so it never enters). Hence the first conjunct of
`SelectedPhysicalFourierEnergyControl` holds iff

```
h(lambda-) = 0   AND   G(0+) = G(L-)   AND   G' in L^2.
```

Both value conditions are the NOT_PROVED_ZERO data of 3e22c100/461f259e. Worse:

* SOURCE_QUERY answered from disk: the constructed modes are series in
  `mode4OrdinaryLegendre` (ordinary even Legendre, `P_{2q}(1) = 1`), so the
  edge value is `sum_q a_q` — no vanishing mechanism exists in the committed
  construction. Answer: NO edge vanishing.
* Even under edge vanishing the row stays non-summable: with
  `h(lambda-) = 0` we need `G(0+) = 0`, but
  `G(0+) = lambda^{-1/2} * sum_{p<m} h(p/lambda)` is the E_star left-edge
  value, which W5 bounded by `O(lambda^{-1/2})` — small, with no exactness.
  By Euler-Maclaurin with the zero-mass packet it is `~ -h(0)/(2*sqrt(lambda))`,
  and `h(0)` has no vanishing mechanism either.
  Consequently `consequence_if_yes` (reopening R1) also fails: periodic H1
  needs the trace MATCH `G(0+) = G(L-)`, which an edge-zero packet reduces to
  `G(0+) = 0` — false for the same reason. R1 stays closed in both branches.

## 3. Numerical confirmation (diagnostic only, registered probe)

`m=9, lambda=3`, packet `(1-(y/lambda)^2)+0.3` (edge `0.3`): identity error is
pure quadrature (`<= 5e-4` relative at `n=200`); `n^2*|c_n|^2` stalls near `0.9`.
Control run edge `= 0`: `|2*pi*n/L * c_n| -> |G(0+)|/sqrt(L) = 2.135` exactly;
`n^2*|c_n|^2` stalls near `0.56`. The left trace alone kills summability.

## 4. Consumer-preserving repair proposal (NOT a weight change)

The receiver's real downstream target is `SelectedProjectionTailDecay S`
(`D0PstarPhysicalFourierEnergyControl.lean`:
`selectedProjectionTailDecay_of_physicalFourierEnergyControl`). The
`n^2`-energy contract was one sufficient supplier pair for it. Proposal: leave
`SelectedPhysicalFourierEnergyControl` untouched as a definition and add an
alternative supplier theorem to the SAME target Prop:

```
selectedProjectionTailDecay_of_decayBudgetAndBandwidth :
  (first-order coefficient budget: |c_n| <= K_k / |n| with K_k eventually bounded)
  -> SelectedPhysicalBandwidthCofinal S
  -> SelectedProjectionTailDecay S
```

Chain: Parseval tail `‖g - P_{m,N} g‖^2 = sum_{|n|>N} |c_n|^2
<= 2*K_k^2/N_k -> 0`, since bandwidth-cofinal forces `N_k -> infinity`
(`L >= log 2`). The needed budget is exactly the closed W5 ledger: the
first-order bound tolerates nonzero traces and seams (they enter `K_k`
linearly through the Jump ledger), which is precisely why W5 was buildable
and the `n^2` contract is not. `BOUNDED_CK_SUFFICES` (a47e9323) already locks
the eventual boundedness shape; the conditional W5 assembly (bceb7d06)
supplies it modulo the one open supplier `W5_LOG_DERIVATIVE_BUDGET_BOUNDED`.

Missing Lean bridge: `|physicalFourierCoefficient| <= K_k/|n|` from the
piecewise-AC structure — the same cell-wise IBP as Section 1, bounding
`|G(0+)| + sqrt(lambda)*|h(lambda-)|*sum p^{-1/2} + ‖G'‖_{L^1}` by the W5
ledgers. This is first-order only; no seam-vanishing is assumed anywhere.

CLOSES: PHYSICAL_FOURIER_COEFFICIENT_WEIGHTED_RECURRENCE (outcome: gap),
SOURCE_QUERY (edge vanishing: NO), R1 reopening question (stays closed).
OPENS: one judge decision — authorize the alternative supplier route.

## 5. Registered predictions

* P_LINUX_R2_GAP_1 (0.90): a second-order ODE pairing will reproduce the same
  seam/trace family at weight `n^2` and cannot restore summability.
* P_LINUX_R2_GAP_2 (0.85): the first-order budget bridge
  (`|c_n| <= K_k/|n|` from the W5 ledgers) formalizes without new analytic
  suppliers beyond the already-open `W5_LOG_DERIVATIVE_BUDGET_BOUNDED`.
