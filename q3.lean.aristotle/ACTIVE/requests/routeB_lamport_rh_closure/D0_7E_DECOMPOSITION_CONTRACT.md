# D0.7e.0 — ExactDetectorBDefinitionAndCrosswalk decomposition contract

Status: `MATH_PROVED_DEFINITIONALLY / LEAN_UNPINNED / NOT_RH`

Define `D0.7e ExactDetectorBDefinitionAndCrosswalk` to be the conjunction

```text
D0.7e.1 ImmutableOwnerDefinitionProvenance
AND D0.7e.2 FiniteCentralMellinCalibration
AND D0.7e.3 DependentCentralNormalizationIdentity
AND D0.7e.4 RealityPhaseAndNamespaceFirewall
AND D0.7e.5 ExactWPrimeZeoCrosswalk.
```

The explicit assembly is `D0.7e.6`. Therefore, definitionally,

```text
D0.7e
<-> D0.7e.1 AND D0.7e.2 AND D0.7e.3 AND D0.7e.4 AND D0.7e.5.
```

Proof. Forward implication is record projection. Reverse implication is record
construction. QED.

The decomposition deliberately separates an owner-ratified definition from a
theorem connecting that definition to the spectral and ZEO consumers. A
definition may be accepted without pretending that its proposed crosswalk is
proved. Only `PROVED` closes a child; a theorem shape, prediction, numerical
judge, or `CONDITIONAL` interface does not close `D0.7e.5` or its parents.

The finite definition retains both indices `(m,N)`. The unquantified proposal
`N(lambda)=ceil(kappa*lambda^2)` is not a field of this record because no value
of `kappa` and no selector theorem are supplied. Likewise the large-parameter
nonvanishing and growth bounds remain H4d obligations.

Current child status:

```text
D0.7e.1 PROVED
D0.7e.2 PROVED_ON_TrialNonzero
D0.7e.3 PROVED_ON_BDetNonzero
D0.7e.4 PROVED
D0.7e.5 BLOCKED: D0_7E_XWALK_OPEN
D0.7e.6 BLOCKED_BY_D0.7e.5
```

Exit: `D0_7E_DECOMPOSITION_LOCKED`.
