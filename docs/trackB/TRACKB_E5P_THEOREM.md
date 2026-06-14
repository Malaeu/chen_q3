# Theorem `E5p_edge_closure_K`

This is the **paper specification** of the theorem that closes E5p on the
K-cell. Lean formalization is deferred until all four obligations are
discharged on paper.

> Naming: `E5p = E5-prime = E5′`. See
> `TRACKB_E5P_SAME_UNIT_BRIDGE_HANDOFF.md` for the canon.

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
is the content of obligation `mu-normalization` below.

---

## 1. Theorem statement

> **Theorem (E5p edge closure on the K-cell).** Fix K and Track B finite
> packet data `(G_K, Q_K, P_edge,K, P0_edge,K, mu_K)` as above. Assume:
>
> - **(G-pos)** `G_K` is positive definite on `ker(Q_K)`.
> - **(E-match)** `E_edge,K` is exactly the finite matrix representing the raw edge
>   defect of the E5p ledger (no normalization drift, no double counting).
> - **(mu-normalization)** `mu_K` is proved as a lower bound in the same `G_K`-normalized
>   units as `d_K` and `E_edge,K` (the **same-unit bridge**).
> - **(tau-PSD-cert)** There exists `tau_K ≥ 0` such that the matrix inequality
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

Assume `G-pos`, `E-match`, `mu-normalization`, and `tau-PSD-cert`. Let `v`
satisfy `Q_K v = 0`. Then
`v^T Q_K^T Q_K v = ‖Q_K v‖² = 0`, hence

```
v^T (mu_K · G_K  -  E_edge,K  +  tau_K · Q_K^T Q_K) v
  =  v^T (mu_K · G_K  -  E_edge,K) v.
```

By `tau-PSD-cert` the left-hand side is `≥ 0`, so

```
v^T E_edge,K v   ≤   mu_K · v^T G_K v.   ∎
```

This is the Lean receiver pattern already present in the repo: penalty PSD
on `Full` ⇒ form inequality on `BoundaryNull`. The implication step is **not**
where we are stuck.

---

## 3. Where we are actually stuck

The four obligations are the work. Status as of this file:

| Obligation | Object                              | Status today                                                                            | Path                                              |
|------------|-------------------------------------|------------------------------------------------------------------------------------------|---------------------------------------------------|
| **G-pos**   | `G_K ≻ 0` on `ker(Q_K)`             | **partial.** Numeric check on K∈{2,3,3.5}; no exact rational LDL on `ker(Q_K)` yet.       | finite linear algebra; rational/interval LDL      |
| **E-match** | `E_edge,K` equals ledger object     | **partial.** Identical raw shape, no formal correspondence theorem in Lean.              | one Lean equality lemma + S3 bookkeeping audit    |
| **mu-normalization** | `mu_K` same-unit           | **NORMALIZATION GAP.** Q3 2025 `A3` / Toeplitz bridge is now a candidate analytic reserve source, but no ledger/scale map identifies its total `T_M[P_A]-T_P` margin with the Track B local raw-edge budget in the B-spline `G_K/Q_K` packet space. | `docs/trackB/lemmas/MU_K_SAME_UNIT_BRIDGE_AUDIT.md` |
| **tau-PSD-cert** | `mu_K · G_K - E_edge,K + tau · Q^TQ ≥ 0` | **finite interval cert pass** for K∈{2,3,3.5} at supplied μ `(0.45,0.51,0.75)`; no same-unit analytic μ source and no all-K structural proof. | rational/interval cert import or Lean receiver |

**mu-normalization is the binding gap.** Closing `G-pos`, `E-match`, and
`tau-PSD-cert` without `mu-normalization` yields a finite witness, not an E5p
closure — exactly the state reached in commit `d4554343f`
(`GAP_EXACTLY_NAMED`).

---

## 4. Sub-lemmas to file (Lean names will mirror these)

```
lemma G_K_SPD_on_kerQ      : G-pos
lemma E_edge_K_matches     : E-match
lemma mu_K_same_unit_bridge: mu-normalization        ← the hard one
lemma penalty_PSD_cert     : tau-PSD-cert
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
- "penalty PSD" = the `tau-PSD-cert` inequality, never just "PSD".
- "same-unit bridge" = `mu-normalization`, never the old Q3 2025 `A3` Toeplitz bridge.

Drift in vocabulary → drift in objects fixed → wrong things get patched.
