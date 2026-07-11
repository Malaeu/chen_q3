# D0.3g — Pro architectural review decision

Date: 2026-07-11

Source: ChatGPT Pro / Proshka route review in project `RH_März_2026`.

Classification: `ARCHITECTURAL_RATIFICATION / ADVISORY_NOT_PROOF_AUTHORITY`.

Primary verdict: `CANONICALIZE_WEILOP`.

## Ratified scope

For every exact finite index `(m,N)`, canonicalize

```text
Mfin_m_N := WeilOp_m_N
```

as the finite detector carrier on `E_m_N`, with ordered ON basis
`(V_-N_m,...,V_N_m)`, Gram matrix `I`, and matrix `WeilMat_m_N`.

This decision does not define `M_lambda`, does not identify `Mfin_m_N` with
`Dlog^(m,N)` or a continuum operator, and does not prove a detector gap.

## Required namespace firewall

```text
nu_j(m,N)              exact ordered full spectrum of Mfin_m_N
epsilon_plus_j(m,N)    exact ordered even-sector spectrum
epsilon_minus_j(m,N)   exact ordered odd-sector spectrum
theta_j(m,N)           static-Schur/LadderLaw diagnostic quantities
```

The old unqualified pilot symbols `mu1,mu2,mu3` are noncanonical. No exact
identity between `theta_j` and `nu_j` may be inferred from numerical closeness.

## Deferred theorem obligations

- global-bottom-three/sector ordering and no crossings;
- strict same-sector gap and simple-even ground;
- a parameter selector or directed family connecting `(m,N)` to `lambda`;
- finite/continuum or non-internal Galerkin bridge;
- same-vector crosswalk to `Dlog^(lambda,N)` and the entire approximant.

The Pro review chooses theorem shape only. Every mathematical claim below is
proved from the pinned project source, finite-dimensional spectral theory, and
the D0.1/D0.2 certificates.
