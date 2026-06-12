# Step33A.1-A ShapeSq Endpoint v18 First Row

## Goal

Close only the ShapeSq endpoint package for the first raw-Omega endpoint row.
Do not touch the Omega/digamma endpoint package in this request.

Repo-real correction:

```text
RawOmegaEndpointWorkRowV18 is schematic only.
Do not use it as a Lean type.
```

The local row combiner already exists and Lean-checks:

```lean
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_endpoint_bounds_generated
```

So this request targets the ShapeSq half only:

```lean
primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_aristotle_v18
```

Once this compiles, the Step33A.1-A endpoint blocker is narrowed to the Omega
anchor theorem only.

## Import Context

Use the real Q3 import:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport
```

The relevant checked receiver is:

```lean
primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_of_value_deriv_bounds_generated
```

Additional checked local backend now available:

```lean
Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.realSinc_hasDerivAt_of_ne_zero
Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.deriv_realSinc_of_ne_zero
```

Use this to reduce the derivative side away from zero:

```lean
deriv realSinc u = (u * Real.cos u - Real.sin u) / u ^ 2
```

On the active interval, `u = eta / 40` is strictly positive.

It consumes:

```text
E lower/upper on [a,b]
E' closed-form lower/upper on [a,b]
tight endpoint facts for E(anchor)^2
```

where:

```lean
E eta = centeredBSplineImagTransformRealClosedForm 11 (3/10) eta
E' eta = centeredBSplineImagTransformRealClosedFormDerivClosedForm 11 (3/10) eta
```

## Target Theorem

Prove this theorem, or return the exact missing lemma with no fake proof.

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

theorem primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_aristotle_v18 :
    ShapeSqEndpointBoundsCert
      11
      ((3 : Real) / (10 : Real))
      ((499999999999999999999 : Real) /
        (10000000000000000000000 : Real))
      ((1 : Real) / (20 : Real))
      ((1 : Real) / (20 : Real))
      ((-46448578038952412672149872160407802487877144879577655939872927993464875466132202360827276104665062142415173687016462681408869026457238530060336008763092149959616648869724829277353 : Real) /
        (312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((-3715886243116193013422691188469113889347186857741575631430658701842124693104660254420490862373908779177392095867429176165007789167568948045769667316015512783831667117451096516791 : Real) /
        (25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((37158858560446920756861350578635783668117859273616803460403855154979728937804568063431171 : Real) /
        (62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))
      ((37158858560446920756861350578635783668117859273616803460403855154979728937804569313431171 : Real) /
        (62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)) := by
  -- Fill this proof.

end RawOmegaATaylorModelCertificate
end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
```

## Preferred Route

Use the checked generated helper:

```lean
primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_of_value_deriv_bounds_generated
```

Do not derive the tight anchor-square facts from the full-subchunk E interval.
Prove the two endpoint facts for `E(1/20)^2` directly.

## Acceptance

Returned Lean must compile under:

```bash
cd q3.lean.aristotle
lake env lean <returned-file>.lean
```

Forbidden:

```text
sorry
admit
exact?
axiom
unsafe
trusted Arb/acb theorem
trusted decimal theorem
invented RawOmegaEndpointWorkRowV18 type
```

## If It Fails

Return:

```text
SHAPESQ_ENDPOINT_BLOCKER:
- theorem:
- interval:
- value/derivative/anchor-square:
- missing lemma:
- nearest existing Q3 lemma:
- candidate proof engine:
- failing inequality:
```
