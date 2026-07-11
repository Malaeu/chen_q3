# D0.3g.0 — CanonicalFiniteWeilDetector decomposition contract

Status: `MATH_PROVED_DEFINITIONALLY / LEAN_UNPINNED / NOT_RH`

Define `D0.3g CanonicalFiniteWeilDetector` to be the conjunction:

```text
D0.3g.1 CanonicalFiniteCarrierSourceLock
AND D0.3g.2 ParityInvolution
AND D0.3g.3 WeilOpCommutesWithParity
AND D0.3g.4 OrthogonalParityReductionAndSectorSpectra
AND D0.3g.5 SpectralProvenanceFirewall.
```

The explicit assembly is `D0.3g.6`.

Therefore, definitionally,

```text
D0.3g
<-> D0.3g.1 AND D0.3g.2 AND D0.3g.3 AND D0.3g.4 AND D0.3g.5.
```

Proof. Forward implication is record projection. Reverse implication is record
construction. QED.

The record has no fields named `M_lambda`, `mu1`, `mu2`, `mu3`, detector gap,
strict gap, `N(lambda)`, continuum operator, or zero-producing crosswalk.

Exit: `D03G_DECOMPOSITION_LOCKED`.
