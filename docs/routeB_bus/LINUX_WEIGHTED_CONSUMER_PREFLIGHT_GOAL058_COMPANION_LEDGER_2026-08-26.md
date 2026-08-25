# STATUS: WEIGHTED_CONSUMER_PREFLIGHT — INTERIOR CLOSES UNIFORMLY; EDGE BAND PAYS sqrt(log lambda) UNDER PURE CS; EXACT COMPANION LEDGER RETURNED PER FAIL CONTRACT

```yaml
ARTIFACT_CLASS: LINUX_WEIGHTED_CONSUMER_PREFLIGHT
GOAL: GOAL_058
DIRECTIVE: GOAL058_NODE3_WEIGHTED_CONSUMER (verdict 0c7f8d5a, REQ-2026-08-26-A)
DISCRIMINATOR: WEIGHTED_CAUCHY_SCHWARZ_WITH_TOP_LATTICE_EXPLICIT
DISCRIMINATOR_OUTCOME: PARTIAL_PASS — interior uniform, edge band excess sqrt(log), top point isolated
FAILURE_CODE_INVOKED: GOAL058_WEIGHTED_CONSUMER_COMPANION_OR_TOP_EDGE_MISMATCH (edge-band component)
AUTHOR_BODY: LINUX_CLAUDE (LINUX_STANDING_GRANT_2026-08-25)
RH_CLAIM: false
```

## 0. Setup (committed objects, exact)

Active set `n in Finset.Icc 1 m`, `m = k+2 = lambda^2`, `lambda = sqrt m`.
Log variable `x in (0, L)`, `L = log m`; spacing `u = e^x/lambda in (1/lambda, lambda)`.
Lattice points `y_n = n*u`.  Defect comb target (the delta-part left after the
unconditional H-node 17d7a5a8):

```
Budget_delta = INT_0^L sqrt(u) * | SUM_{n=1}^{m} y_n * gd(y_n) | dx,
```

`gd = delta'`.  Available input (node 1, frozen): weighted energy
`E0 := INT_{-lambda}^{lambda} (lambda^2-y^2) gd(y)^2 dy <= C_E^2/lambda^2`.

Per-`n` non-top range (`y_n <= lambda - u`, i.e. the point is not the
uppermost): `y in R_n = (n/lambda, lambda*n/(n+1)]`, nonempty iff `n <= m-2`.
Change of variables per n: `y = n*e^x/lambda`, `dy = y dx`, so
`sqrt(u)*y*|gd(y)| dx = n^{-1/2} * sqrt(y) * |gd(y)| dy`.

## 1. Exact companion ledger (the sharp per-n chain)

Triangle over n, then per-n Cauchy-Schwarz against the energy weight:

```
T_n := n^{-1/2} INT_{R_n} sqrt(y)|gd| dy
    <= n^{-1/2} * sqrt(companion_n) * sqrt(E0),
companion_n = INT_{R_n} y/(lambda^2-y^2) dy
            = (1/2) * log[ (lambda^2 - n^2/lambda^2) * (n+1)^2
                           / (lambda^2 * (2n+1)) ].
```

EXACT structure of companion_n: for n << lambda^2 it is ~ (1/2)log(n/2+1);
for n = lambda^2 - j it is ~ (1/2)log j.  The log is NOT produced at small u
(many points) per se and NOT only at the single top point: it accumulates
because the n-th non-top sweep approaches the physical edge to distance
`lambda/(n+1)` while still being non-top.  Interior cutoff kills it (Sec. 2).

Summation: `SUM_{n<=m} n^{-1/2} sqrt((1/2)log(n+1)) ~ sqrt(2)*lambda*sqrt(log lambda)`, so

```
Budget_delta(non-top, pure CS) <= sqrt(2)*lambda*sqrt(log lambda)*sqrt(E0)
                               =  sqrt(2)*C_E*sqrt(log lambda).
```

CONSISTENCY CHECK: the same machinery with the unweighted pairing reproduces
the registered C1-L2 number exactly: `T_n <= n^{-1/2}*lambda*||gd||_2`, sum
`<= 2*lambda^2*||gd||_2`.  This validates the ledger against the Q-comb
preflight (0a6d94d6).

ANOMALY RECORD (Rule: strange things are written down when noticed).  The
Sturm preflight 4c62caa5 Section 6 claimed the sliver-free part contributes
`O(sqrt(log lambda/lambda))`.  My exact ledger gives `O(sqrt(log lambda))` —
an excess of `sqrt(lambda)`.  Reading A: 4c62caa5 had a sharper pairing I
have not reproduced.  Reading B: 4c62caa5 Section 6 was optimistic by
`sqrt(lambda)`; the number `2*lambda^2*||delta'||_2` (which my ledger DOES
reproduce) was correct, the weighted claim was not recomputed at the same
rigor.  Distinguishing evidence: two independent pairings (global-CS in x,
dyadic edge shells) both floor at >= sqrt(log); an adversarial profile
`gd ~ 1/sqrt(y(lambda^2-y^2))` on a dyadic range saturates the per-n chain.
I adjudicate B and return the ledger per FAIL contract.

## 2. What CLOSES uniformly right now (no new supplier)

INTERIOR SPLIT at y = lambda/2 (any fixed fraction works):

```
companion_n^{interior} = INT_{R_n cap (0, lambda/2]} y/(lambda^2-y^2) dy
                      <= (1/2) log(4/3)          [ABSOLUTE constant]
Budget_delta(interior) <= 2*lambda * sqrt((1/2)log(4/3)) * sqrt(E0)
                       <= 0.76 * C_E.            [UNIFORM. Lean-ready]
```

This bounds every lattice contribution with `y_n <= lambda/2`, for all u,
all k, at consumer strength, from the frozen node-1 energy alone.

## 3. The exact remaining functionals (edge band)

After the interior split and the top-point separation, the open object is
the EDGE BAND non-top contribution:

```
B_band = INT_0^L sqrt(u) * | SUM_{n: lambda/2 < y_n <= lambda-u} y_n*gd(y_n) | dx.
```

Pure CS pays it only at `sqrt(2)*C_E*sqrt(log lambda)`.  The committed
consumer contract hD (selectedFerrersAbelLogDerivativeBudget <= D uniform,
G6N1SelectedFerrersW5DerivativeBudgetRate.lean:534) requires UNIFORM.
Mismatch: factor sqrt(log lambda) on the band.

Signed alternative on the band (Euler-Maclaurin order 0, NO derivative of gd):
the cell-mean part of the band comb is an EXACT signed integral,

```
(1/u) INT_{band} y*gd(y) dy = (1/u) * [y*delta]_{edges} - (1/u) INT_{band} delta,
```

paid by the C0 rate alone: contribution to the budget
`<= 4*lambda^{3/2}*Cd ~ 4*C/sqrt(lambda) -> 0`.  The residual is the
CELL-DEVIATION functional

```
Dev_band = INT_0^L sqrt(u) * | SUM_{band} [ g(y_n) - (1/u) INT_{cell_n} g ] | dx,
           g(y) = y*gd(y),
```

which measures lattice-sample-vs-mean of g on cells of length u inside the
band — controlled by g' (i.e. delta'') pointwise, which node 1 does NOT
supply, or by an averaged large-sieve-type bound, which is exactly the same
bilinear form as CS and floors at the same sqrt(log).

## 4. Adjudication requests (single follow-up to the directive)

(a) INTERIOR NODE NOW: authorize Lean for the interior bound (Sec. 2) as the
    node-3 deliverable, statement at the same abstract level as node 1
    (hypotheses: E0-bound, gd continuous on the open window), conclusion:
    uniform bound on every contribution with y_n <= lambda/2, top point and
    edge band named separately.  CLOSES: WEIGHTED_CONSUMER_INTERIOR.
    Что меняется: да -> Lean немедленно; нет -> назови другую форму узла.
(b) EDGE BAND: adjudicate the sqrt(log lambda) mismatch. Options:
    (b1) accept relaxed budget hD' : Budget <= D*sqrt(L_m) and re-derive the
         downstream chain (the receiver's hCoeff already carries C^2*L/n^2;
         tail 2C^2L/N with N ~ pi*sqrt(k+2) still -> 0 even with C^2 ~ L —
         the mathematical chain SURVIVES, only the committed uniform-D
         contracts need the sqrt(L) carried through);
    (b2) keep uniform D and name the band supplier
         W5_DEFECT_EDGE_BAND_AVERAGED_BOUNDED (averaged, not sup;
         R_EDGE_FLUX_AVERAGE applies to the band, not only the top point);
    (b3) your stronger pairing, if Reading A of the anomaly is right —
         name it and I recompute.
(c) TOP POINT: unchanged, carried open as W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED.

Registered prediction: P_LINUX_WC_1 = 0.80 that no pairing consuming ONLY
the node-1 weighted energy closes the band uniformly (the adversarial
profile saturates all three pairings tried).

CLOSES: WEIGHTED_CONSUMER_COMPANION_COMPUTATION (exact ledger delivered)
OPENS: WEIGHTED_CONSUMER_INTERIOR (Lean-ready, authorization requested)
CARRIES_OPEN: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED, edge-band adjudication
