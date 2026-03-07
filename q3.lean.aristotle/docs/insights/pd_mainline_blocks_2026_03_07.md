# Exact theorem blocks after the corrected-cone pivot

Date: 2026-03-07

## Verdict

The new theorem-block package matches the corrected-cone pivot and should be treated
as the live mathematical contract for the public manuscript.

## Local search and repo evidence

Successful semantic hits:

- `A1-pd centered packet density positive definite cone autocorrelation`
  returned `full/sections/A1prime.tex` and the active implementation plan, confirming
  that the live mainline already points at centered packet density on the corrected cone.
- `Rayleigh pairing quadratic form Fejer heat packet autocorrelation`
  returned:
  - `full/sections/A3/rayleigh_bridge.tex`
  - `full/sections/RKHS/core.tex`
  - `Q3/Proofs/Q_nonneg_atoms_closure.lean`
  showing that the repo already contains the general quadratic-pairing ingredients
  needed for a packet-level bridge.

Known tooling noise:

- two additional semantic queries hit the local backend issue
  `SQLiteError: database is locked` / `SQLITE_BUSY_RECOVERY`.
  Treat the successful hits above as the actual evidence.

## Exact public objects

Keep the corrected target cone as
\[
  \widetilde{\psi}(x):=\overline{\psi(-x)},
  \qquad
  \mathcal W_{K,0}^{\mathrm{pd}}
  :=\{\psi * \widetilde{\psi}:\ \psi\in C_c^\infty(\mathbb R),\ \operatorname{supp}\psi\subset[-K/2,K/2]\},
\]
\[
  \mathcal W_K^{\mathrm{pd}}
  := \overline{\operatorname{cone}(\mathcal W_{K,0}^{\mathrm{pd}})}^{\|\cdot\|_\infty},
  \qquad
  \mathcal W^{\mathrm{pd}}:=\varinjlim_{K\to\infty}\mathcal W_K^{\mathrm{pd}}.
\]

Freeze the exact centered packet cone as
\[
  \mathcal P_K
  := \operatorname{cone}\{\Phi_\Psi=\Psi*\widetilde{\Psi}:\ \Psi \text{ finite Fej\'er$\times$heat packet},\ \operatorname{supp}\Psi\subset[-K/2,K/2]\}.
\]

## Exact theorem blocks

1. `T0-pd / corrected Weil linkage`

\[
  \mathrm{RH}
  \iff
  Q^\star(t;\Phi)\ge 0 \quad \forall \Phi\in\mathcal W^{\mathrm{pd}}.
\]

2. `A1-pd`

\[
  \overline{\mathcal P_K}^{\|\cdot\|_\infty}
  =
  \mathcal W_K^{\mathrm{pd}}.
\]

3. `packet-Rayleigh`

For every `\Phi_\Psi=\Psi*\widetilde{\Psi}\in\mathcal P_K`, there exist
`M` and `p_\Psi` such that
\[
  Q^\star(t;\Phi_\Psi)
  =
  2\pi\,\langle (T_M[P_A]-T_P^{\mathrm{Ray}}(t,M))p_\Psi,p_\Psi\rangle.
\]

## Mathematical proof skeleton

- Step 1: prove packet density in the pre-square space `C_c^\infty([-K/2,K/2])`,
  preferably in `L^1`.
- Step 2: pass to convolution squares using
\[
  \|\psi*\widetilde{\psi}-\varphi*\widetilde{\varphi}\|_\infty
  \le
  (\|\psi\|_1+\|\varphi\|_1)\,\|\psi-\varphi\|_1.
\]
- Step 3: use the existing quadratic Rayleigh pairing to identify packet
  autocorrelations with the centered Toeplitz/RKHS positivity engine.

## Recommendation

- Treat this theorem-block package as the exact public mainline contract.
- Do not reopen the broad-cone `G1-G3` route as the architectural driver.
- Make the next active proof task the pre-square density route behind `A1-pd`,
  and keep packet-Rayleigh as the next queued bridge theorem on the same packet cone.
