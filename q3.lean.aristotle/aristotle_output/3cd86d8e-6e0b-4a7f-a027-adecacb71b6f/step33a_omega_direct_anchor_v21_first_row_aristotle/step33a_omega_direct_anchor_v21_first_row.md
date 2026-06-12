# Step33A.1-A Omega Direct Anchor v21 First Row

## Goal

Prove the first Route B proof-bearing Omega anchor fact for the checked
Step33A.1-A raw-Omega endpoint receiver.

Louise/Pro chose Route B:

```text
Aristotle generic Lean lemmas
-> generated rational endpoint rows
-> existing local row combiners
```

The local combiner is already present in the repository:

```lean
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_endpoint_bounds_generated
```

The first missing proof-bearing fact is only the direct anchor bound for
`step22OmegaArchWeight (1/20)`.

## Current Local Receiver Surface

The repository now also contains a narrower checked re-series adapter:

```lean
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_re_series_interval_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_re_series_interval_and_shape_generated
```

The current narrowest checked adapter consumes the already checked `N = 16`
prefix row internally:

```lean
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_re_series_N16_prefix_generated
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_re_series_N16_prefix_and_shape_generated
```

So there are two acceptable proof shapes.

Preferred if direct proof is hard:

```text
prove explicit premises for
  step22OmegaArchWeight_bounds_from_re_series_prefix_tail_interval
at eta = 1/20:
  bounds for -Real.eulerMascheroniConstant - Real.log Real.pi
  finite prefix bounds for step22OmegaArchWeightReSeriesTerm (1/20)
  signed tail bounds for the remaining series
  rational lower/upper glue into the v21 endpoint interval.
```

The generated theorem
`primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_re_series_N16_prefix_generated`
will turn those premises into the same conjunction below when `N = 16` is used.
The older
`primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_re_series_interval_generated`
surface remains available if a different finite prefix is needed.

Already checked locally:

```lean
primaryFiniteRow0Parent0Split100Sub0OmegaAnchorReSeriesPrefixBoundsN16_generated
```

This supplies the finite-prefix lower/upper bounds for `anchorN = 16`.
If using the re-series route, do not reprove that prefix row; reuse it and
focus on:

```text
constant bounds for -Real.eulerMascheroniConstant - Real.log Real.pi
signed tail bounds after N = 16
rational lower/upper glue into the v21 endpoint interval
```

## Import Context

Use this import:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport
```

You may use existing Q3 lemmas from the imported dependency chain, especially
digamma / trigamma / Stieltjes / Omega helpers reachable from:

```text
Q3.DigammaSeries
Q3.DigammaRemainder
Q3.Proofs.Digamma_Aristotle
Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend
Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker
```

## Known Guard

The existing first-order Stieltjes bridge is useful structurally but far too
coarse by itself for this v21 endpoint interval.

At `eta = 1/20`:

```text
‖1/4 + i * eta/2‖^2 = 101/1600
step22OmegaArchWeightStieltjesErr (1/20) = 400/101 ~= 3.9603960396039604
```

The v21 target interval width is only:

```text
1.103973508967679544746826890882E-21
```

So a proof that only applies
`step22OmegaArchWeight_anchor_bounds_from_stieltjes` with the first-order
`StieltjesErr` cannot close this theorem.  Use a sharper existing
digamma/asymptotic/re-series route, or return the exact missing sharper lemma.

## Target Theorem

Please prove exactly this theorem, or return a compiling helper theorem that
supplies the explicit premises accepted by
`primaryFiniteRow0Parent0Split100Sub0OmegaAnchorPair_of_re_series_interval_generated`.
Use no trusted decimal oracle and no new axioms.

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkIntegral
namespace RawOmegaATaylorModelCertificate

theorem step22OmegaArchWeight_one_twentieth_v21_anchor_bounds :
    ((-85314634821843642073465861701640867472353398314119326820557162830783014314359848985502357 : Real) /
        (16000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)) <=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          ((1 : Real) / (20 : Real)) ∧
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          ((1 : Real) / (20 : Real)) <=
        ((-426573174109218210367240990627486922998187245419326080653670377242934688213891611916507071 : Real) /
          (80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)) := by
  -- Fill this proof.

end RawOmegaATaylorModelCertificate
end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
```

## Acceptance

The returned Lean must compile under:

```bash
cd q3.lean.aristotle
lake env lean <returned-file>.lean
```

Do not add:

```text
sorry
admit
exact?
axiom
unsafe
trusted Arb/acb theorem
trusted decimal theorem
```

Arb/acb numerical output may only be used as motivation for rational
candidates.  The final proof must be Lean-checked from existing local
definitions and lemmas.

## If It Fails

Return the exact missing lemma in this format:

```text
ENDPOINT_ARISTOTLE_BLOCKER:
- theorem:
- missing lemma:
- candidate method:
- nearest existing Q3 lemma:
- failing inequality:
```
