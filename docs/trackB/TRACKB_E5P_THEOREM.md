# Theorem `E5p_edge_closure_K`

This is the **paper specification** of the theorem that closes E5p on the
K-cell. Lean formalization is deferred until all four assumptions are
discharged on paper.

> Naming: `E5p = E5-prime = E5′`. See `CODEX_HANDOFF_E5P_SAME_UNIT_BRIDGE.md`
> §1 for the canon.

---

## 0. Notation

For a fixed K-cell with packet support `[2K, 4K]` in raw-log coordinates
(`a = r · log p`, `xi = a / (2π)`):

| Symbol            | Object                                                |
|-------------------|--------------------------------------------------------|
| `G_K`             | Gram / normalization matrix on the K-cell packet basis |
| `Q_K`             | boundary constraint matrix (`ker Q_K = BoundaryNull`)  |
| `P_edge,K`        | prime-power-shift edge matrix                          |
| `P0_edge,K`       | smooth edge baseline (B-spline trapezoid)              |
| `E_edge,K`        | `:= P_edge,K - P0_edge,K`  (raw edge defect)           |
| `mu_K`            | analytic E5p edge budget (Weil-side integral)          |
| `tau_K`           | nonnegative boundary-penalty scale                     |

All five matrices and `mu_K` must live in **one** normalization. Fixing this
is the content of assumption (A3) below.

---

## 1. Theorem statement

> **Theorem (E5p edge closure on the K-cell).** Fix K and Track B finite
> packet data `(G_K, Q_K, P_edge,K, P0_edge,K, mu_K)` as above. Assume:
>
> - **(A1)** `G_K` is positive definite on `ker(Q_K)`.
> - **(A2)** `E_edge,K` is exactly the finite matrix representing the raw edge
>   defect of the E5p ledger (no normalization drift, no double counting).
> - **(A3)** `mu_K` is proved as a lower bound in the same `G_K`-normalized
>   units as `d_K` and `E_edge,K` (the **same-unit bridge**).
> - **(A4)** There exists `tau_K ≥ 0` such that the matrix inequality
>
>   ```
>   mu_K · G_K  -  E_edge,K  +  tau_K · Q_K^T Q_K  ≥  0
>   ```
>
>   holds (the **penalty PSD certificate**).
>
> **Then** for every `v` with `Q_K v = 0`:
>
> ```
> v^T E_edge,K v   ≤   mu_K · v^T G_K v.
> ```

Interpretation: the raw edge defect fits inside the analytic E5p budget on
the K-cell, restricted to the boundary-null subspace.

---

## 2. Proof of the implication (the easy part)

Assume (A1)–(A4). Let `v` satisfy `Q_K v = 0`. Then
`v^T Q_K^T Q_K v = ‖Q_K v‖² = 0`, hence

```
v^T (mu_K · G_K  -  E_edge,K  +  tau_K · Q_K^T Q_K) v
  =  v^T (mu_K · G_K  -  E_edge,K) v.
```

By (A4) the left-hand side is `≥ 0`, so

```
v^T E_edge,K v   ≤   mu_K · v^T G_K v.   ∎
```

This is the Lean receiver pattern already present in the repo: penalty PSD
on `Full` ⇒ form inequality on `BoundaryNull`. The implication step is **not**
where we are stuck.

---

## 3. Where we are actually stuck

The four assumptions are the work. Status as of this file:

| Assumption | Object                              | Status today                                                                            | Path                                              |
|------------|-------------------------------------|------------------------------------------------------------------------------------------|---------------------------------------------------|
| **(A1)**   | `G_K ≻ 0` on `ker(Q_K)`             | **partial.** Numeric check on K∈{2,3,3.5}; no exact rational LDL on `ker(Q_K)` yet.       | finite linear algebra; rational/interval LDL      |
| **(A2)**   | `E_edge,K` equals ledger object     | **partial.** Identical raw shape, no formal correspondence theorem in Lean.              | one Lean equality lemma + S3 bookkeeping audit    |
| **(A3)**   | `mu_K` same-unit                    | **GAP.** No proved lower bound for `mu_K` in `G_K`-units. Currently a supplied constant. | atlas card 009 (Selberg) or 029 (Connes adelic)   |
| **(A4)**   | `mu_K · G_K - E_edge,K + tau · Q^TQ ≥ 0` | **finite witness only** for K∈{2,3,3.5} and supplied μ; not proof-grade structurally. | rational LDL for sym-tridiagonal block + induction |

**(A3) is the binding gap.** Closing (A1), (A2), (A4) without (A3) yields a
finite witness, not an E5p closure — exactly the state reached in commit
`d4554343f` (`GAP_EXACTLY_NAMED`).

---

## 4. Sub-lemmas to file (Lean names will mirror these)

```
lemma G_K_SPD_on_kerQ      : (A1)
lemma E_edge_K_matches     : (A2)
lemma mu_K_same_unit_bridge: (A3)        ← the hard one
lemma penalty_PSD_cert     : (A4)
theorem E5p_edge_closure_K : §1 above, follows from the four lemmas
```

Each sub-lemma gets its own evidence/diagnostic file under
`docs/trackB/lemmas/`. Codex creates these files when the corresponding work
starts; no preemptive stubs.

---

## 5. What this theorem does NOT do

- It does **not** close E5p across all K — only on a fixed K-cell. A separate
  K-collation lemma (`E5p_collation`) glues K-cells; this is a different
  ledger problem and lives outside this theorem.
- It does **not** discharge the explicit-formula identity between the Weil
  quadratic form `Q(Φ)` and the spectral side — that identity is an input
  (current Lean Mathlib + repo-side machinery).
- It does **not** imply RH directly. Q3 / Gate ⟺ RH framing is upstream.

---

## 6. Spoken-form invariants (don't drift)

When discussing this theorem in voice / chat:

- "edge defect" = `E_edge,K`, never "edge cost", never "edge penalty".
- "budget" = `mu_K`, never "reserve", never "allowance".
- "clamp" = `d_K`, never "ceiling", never "bound".
- "penalty PSD" = the inequality in (A4), never just "PSD".
- "same-unit bridge" = (A3), never "normalization fix".

Drift in vocabulary → drift in objects fixed → wrong things get patched.
