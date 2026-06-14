# Track B E5' Lean Bridge Map

Status: READ_ONLY_MAP. This file records actual local names/files found by
`rg`/local inspection. No Lean names are invented and no Lean files were edited.

## Scope

The E5' finite target is not currently a named Lean theorem. The bridge map
therefore separates:

```text
existing reusable receivers / definitions
vs.
missing Track B E5' finite objects
```

## Core Q3 Names

| concept | actual name | file | bridge status |
| --- | --- | --- | --- |
| Q3 prime coordinate | `Q3.xi_n` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | `log n / (2*pi)` |
| active nodes | `Q3.Nodes` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | finite support node set |
| Q prime weight | `Q3.w_Q` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | `2*vonMangoldt n / sqrt n` |
| Fourier prime vector | `Q3.prime_vec` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | old Rayleigh vector |
| arch term | `Q3.arch_term` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | functional term |
| prime term | `Q3.prime_term` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | functional term |
| Q functional | `Q3.Q` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | `arch_term - prime_term` |
| broad Weil cone | `Q3.Weil_cone` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | background only after cone pivot |
| compact broad cone | `Q3.W_K` | `q3.lean.aristotle/Q3/Basic/Defs.lean` | background/broad cone |
| Lipschitz bridge | `Q3.Proofs.Q_Lipschitz_on_W_K_thm` | `q3.lean.aristotle/Q3/Proofs/Q_Lipschitz.lean` | existing theorem |
| transfer theorem | `Q3.Q_nonneg_on_W_K` | `q3.lean.aristotle/Q3/T5_Transfer.lean` | background broad route |
| Toeplitz matrix | `Q3.ToeplitzMatrix` | `q3.lean.aristotle/Q3/Axioms.lean` | old Toeplitz/Rayleigh layer |
| Rayleigh quotient | `Q3.RayleighQuotient` | `q3.lean.aristotle/Q3/Axioms.lean` | old finite matrix layer |

## Rayleigh / Prime / Arch Bridge Names

| concept | actual name | file | bridge status |
| --- | --- | --- | --- |
| shifted prime matrix | `Q3.T_P_comp_real_shift` | `q3.lean.aristotle/Q3/Proofs/Rayleigh_Q_identification.lean` | shifted finite prime bridge |
| shifted arch equality | `Q3.Proofs.arch_rayleigh_eq_shift` | same | arch Rayleigh to `arch_term` |
| shifted prime equality | `Q3.Proofs.prime_rayleigh_eq_shift` | same | finite shifted prime sum |
| shifted full Q equality | `Q3.Proofs.rayleigh_Q_eq_Q_shift` | same | old shifted basis0 equality |
| support-to-nodes bridge | `Q3.Proofs.prime_term_eq_nodes_of_support` | same | finite support bridge |

These are useful for normalization checks, but they are not the current Track B
packet raw-edge domination theorem.

## Finite Penalty / kerQ Receiver

| concept | actual name | file | bridge status |
| --- | --- | --- | --- |
| quadratic form | `Q3.Proofs.quadForm` | `q3.lean.aristotle/Q3/Proofs/PSD_PenaltyCertificate.lean` | reusable |
| boundary-null predicate | `Q3.Proofs.BoundaryNull` | same | reusable `ker(Q)` abstraction |
| boundary energy | `Q3.Proofs.boundaryEnergy` | same | reusable |
| penalty form | `Q3.Proofs.penaltyForm` | same | reusable `M + tau Q^TQ` abstraction |
| Euclidean energy | `Q3.Proofs.euclideanEnergy` | same | old floor normalization |
| rational weighted-square matrix bridge | `Q3.Proofs.penalty_lower_bound_of_ratMatrixWeightedSquare_identity` | same | exact LDL receiver |
| boundary penalty vanishes | `Q3.Proofs.penaltyForm_eq_quadForm_of_boundaryNull` | same | kerQ bridge |
| PSD on boundary null | `Q3.Proofs.quadForm_nonneg_on_boundaryNull_of_penalty_nonneg` | same | direct E5' consumer pattern |
| strict-to-nonnegative receiver | `Q3.Proofs.quadForm_nonneg_on_boundaryNull_of_penalty_pos` | same | reusable |
| finite certificate structure | `Q3.Proofs.FinitePenaltyCert` | same | reusable |
| lower-bound certificate structure | `Q3.Proofs.FinitePenaltyLowerBoundCert` | same | reusable |

This is the best existing Lean landing zone for a future exact E5' certificate.

## Old Step32F Lower-Bound Names

| concept | actual name | file | bridge status |
| --- | --- | --- | --- |
| old coefficient index | `PSDpd.CenteredCoeffPayloadImport.CoeffIndex23` | `q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean` | old 23-center space |
| old boundary index | `BoundaryIndex2` | same | old two-row boundary space |
| old payload data | `CenteredCoeffPayloadData` | same | old A/P/P0/Q payload |
| old primary matrices | `primaryK11A`, `primaryK11P`, `primaryK11P0`, `primaryK11Q` | same | old cell only |
| old primary split | `primaryK11Split` | same | `C = D + theta R` split |
| old control matrices | `controlK9A`, `controlK9P`, `controlK9P0`, `controlK9Q` | same | old cell only |
| old control split | `controlK9Split` | same | `C = D + theta R` split |
| primary penalty constants | `primaryK11TauD`, `primaryK11TauR`, `primaryK11DFloor`, `primaryK11RFloor` | `PSD_CenteredCoeffPenaltyImport.lean` | exact rational constants |
| control penalty constants | `controlK9TauD`, `controlK9TauR`, `controlK9DFloor`, `controlK9RFloor` | same | exact rational constants |
| primary LDL identities | `primaryK11DLDL_identity`, `primaryK11RLDL_identity` | `PSD_CenteredCoeffPenaltyLDLImport.lean` | exact rational LDL |
| primary lower bounds | `primaryK11DLowerBound_ldl`, `primaryK11RLowerBound_ldl` | same | exact old receiver |
| control LDL identities | `controlK9DLDL_identity`, `controlK9RLDL_identity` | same | exact rational LDL |
| control lower bounds | `controlK9DLowerBound_ldl`, `controlK9RLowerBound_ldl` | same | exact old receiver |
| old finite certs | `primaryK11FinitePenaltyCert_ldl`, `controlK9FinitePenaltyCert_ldl` | same | old exact cert |

Verdict for E5':

```text
usable as penalty/LDL pattern: yes
usable as free m_old pre-edge reserve: no, absent new ledger
```

## Step33 / Entry-Hbox Names

| concept | actual name | file | bridge status |
| --- | --- | --- | --- |
| primary entry hbox cert | `PSDpd.CenteredCoeffEntryHboxImport.PrimaryK11BaseEntryHboxCert` | `q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean` | Step32/33 hbox bundle |
| control entry hbox cert | `ControlK9BaseEntryHboxCert` | same | Step32/33 hbox bundle |
| active entry hbox cert | `ActiveCenteredCoeffEntryHboxCert` | same | live Step33 name |
| direct-profile assembler | `activeCenteredCoeffEntryHboxCert_of_directPrimeProfilePayloadHboxes` | same | direct payload receiver |
| delta/live assembler | `activeCenteredCoeffEntryHboxCert_of_deltaLivePrimeProfilePayloadHboxes` | same | delta/live receiver |
| direct prime payload | `PSD_CenteredCoeffPrimeDirectProfilePayloadImport.lean` | `q3.lean.aristotle/Q3/Proofs/` | generated payload file |
| delta/live payload | `PSD_CenteredCoeffPrimeDeltaLivePayloadImport.lean` | same | generated payload file |

These names are PSD Step33 infrastructure, not Track B E5' objects.

## Executable Track B Instrument Names

| concept | actual name | file | bridge status |
| --- | --- | --- | --- |
| packet pilot | `SplinePacket` | `q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py` | executable model |
| packet params | `PilotParams` | same | executable model |
| centers | `build_centers` | same | executable model |
| Gram matrix | `build_G` | same | executable `G_K` |
| boundary rows | `build_Q` | same | executable `Q_K` |
| null basis | `boundary_null_basis` | same | executable kerQ projection |
| prime-power shifts | `prime_power_shifts` | same | executable prime support |
| raw-edge continuum | `build_P0_edge` | `scripts/trackb_edge_operator_probe.py` | Track B raw-edge `P0_edge` |
| raw-edge finite prime | `run_edge`, local `P_edge` | same | Track B raw-edge `P_edge` |
| finite operator mode | `run_finiteop` | same | float finite certificate diagnostic |
| S3 closure mode | `run_clvgate` | same | bookkeeping diagnostic |
| S5C LP mode | `run_s5clp` | same | finite LP diagnostic |

These are not Lean certificates. They are the current source of finite matrices
for Phase 4 diagnostics and for any future rational/interval exporter.

## Missing Lean Objects For E5'

No current Lean declaration was found for:

```text
TrackB_E5P_PacketSpace
TrackB_E5P_G_K
TrackB_E5P_Q_K
TrackB_E5P_E_edge_K
TrackB_E5P_mu_K
TrackB_E5P_penalty_matrix
TrackB_E5P_domination_on_kerQ
```

Required Lean port decision after Phase 4:

```text
1. external rational/interval checker plus docs only;
2. isolated Lean file importing a generated rational matrix payload;
3. reuse `PSD_PenaltyCertificate` with new Track B payload names.
```

Forbidden:

```text
No `Q3.Main` edit.
No reuse of old Step32F `C=A-P` as m_old without new pre-edge ledger.
No buried matrix-Rayleigh resurrection.
```
