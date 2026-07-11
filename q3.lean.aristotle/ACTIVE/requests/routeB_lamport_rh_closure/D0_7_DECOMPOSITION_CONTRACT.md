# D0.7.0 — ExactNormalization decomposition contract

Status: `MATH_PROVED_DEFINITIONALLY / LEAN_UNPINNED / NOT_RH`

Define `D0.7 ExactNormalization` to be the conjunction

```text
D0.7a DirichletBoundaryVectorAndFunctional
AND D0.7b TrialScalarAndPhase
AND D0.7c ConditionalGroundBoundaryNormalization
AND D0.7d BNamespaceFirewall
AND D0.7e ExactDetectorBDefinitionAndCrosswalk.
```

The explicit assembly is `D0.7f`. Therefore, definitionally,

```text
D0.7
<-> D0.7a AND D0.7b AND D0.7c AND D0.7d AND D0.7e.
```

Proof. Forward implication is record projection. Reverse implication is record
construction. QED.

The record deliberately separates exact definitions from later estimates.
Uniform nonvanishing/growth bounds for the selected ground normalization or
detector `b` remain H4d obligations. No component may create a hidden
`N(lambda)` selector or identify the historical pilot scalar with detector
`b` without a source theorem.

Current child status:

```text
D0.7a PROVED
D0.7b PROVED
D0.7c PROVED_AS_DEPENDENT_CONDITIONAL_INTERFACE
D0.7d PROVED
D0.7e BLOCKED: D0_7_DETECTOR_B_DEFINITION_MISSING
D0.7f BLOCKED_BY_D0.7e
```

Exit: `D0_7_DECOMPOSITION_LOCKED`.
