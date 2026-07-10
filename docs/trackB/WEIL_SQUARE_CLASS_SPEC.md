# WEIL_SQUARE_CLASS_SPEC

Status: `SPEC_ONLY / NO_RH_CLAIM`.

This note fixes the test-class gate behind the Weil route.  It is not an
A3/IND/T5 proof step.  Its job is to prevent three different objects from being
silently identified:

- the classical Weil/Bombieri Hermitian-square criterion;
- the broad local cone/PW language used by older A1' prose;
- the current restricted `Weil_criterion_tau0` axiom.

## Correct Target

The exact local target is positivity of the Weil functional on admissible
Hermitian squares, not positivity on arbitrary compact bumps and not positivity
only on the restricted tau0 packet cone.

In additive/log coordinates the square has the shape

```text
g_sharp(x) = conj(g(-x))
Phi       = g * g_sharp
hat Phi(t) = |hat g(t)|^2 >= 0
```

If `supp g subset [-K/2,K/2]`, then `supp Phi subset [-K,K]`.

In multiplicative coordinates the same object is usually written with the
involution

```text
g_tilde(x) = x^(-1) conj(g(1/x))
f          = g * g_tilde
Mellin(f)(s) = Mellin(g)(s) Mellin(g_tilde)(s)
```

On the critical line this is a Hermitian square.  The exact sign convention of
the Weil functional depends on the chosen explicit-formula normalization.

## Finite Boundary Conditions

The square generator also has finite pole-cancelling constraints.  They are not
decorative; without them the explicit formula still contains the boundary/pole
terms and the quoted Weil criterion is not the same statement.

In the multiplicative form used in standard expositions these are the two
moment conditions

```text
integral_0^infty g(x) dx/x = 0
integral_0^infty g(x) dx   = 0
```

Equivalently, they are transform vanishing at the two boundary points attached
to `s=0` and `s=1`.  In the current additive Lean-facing interface this appears
as

```text
WeilBoundaryH g ( 1/2) = 0
WeilBoundaryH g (-1/2) = 0
```

Exact matching between these two displays is a normalization task for `T0`.

## Local Mismatch

Current repository fact:

```text
Weil_criterion_tau0
```

is not the classical Weil criterion.  It asserts the RH equivalence for a
restricted Fejer x heat tau0/fixed-B packet cone.  Positivity on a smaller cone
does not imply positivity on the full Hermitian-square Weil class unless a
separate sufficiency/density theorem is proved.

So the route cannot use the following shortcut:

```text
finite packet positivity
  -> broad A1' density
  -> positivity on PW
  -> RH
```

The corrected route needs the square class explicitly:

```text
ExactWeilCriterion
  -> W_sq / W_sq_K
  -> A1-pd / WeilSquarePacketExhaustion
  -> packet-Rayleigh-pd
  -> PSD-pd or another square-preserving positivity engine
  -> A2 closure
  -> RH
```

## Required Interfaces

The proof route should expose these interfaces separately.

### 1. `WeilSquareClassSpec`

Define the admissible generator `g`, the involution, the Hermitian square
`Phi = g * g_sharp`, compact support, smoothness/decay, real-valuedness, and
the boundary-null constraints.

Local Lean anchor already exists:

```text
q3.lean.aristotle/Q3/Basic/WeilSquareClass.lean
```

with `sharp`, `hermitianSquareC`, `IsHermitianSquareOf`,
`HasWeilBoundaryNull`, `WeilSquareWitness`, `W_sq_K`, `W_sq`, and
`ExactWeilCriterion`.

### 2. `ClassicalWeilLinkage`

State and isolate the external/classical equivalence:

```text
RH <-> forall Phi in W_sq, 0 <= Q(Phi)
```

This must not be replaced by `Weil_criterion_tau0` without an additional
reduction theorem.

### 3. `FiniteBoundaryNormalization`

Prove that the finite transform/moment conditions in the chosen paper
normalization match the current additive boundary-null interface.  This is the
place for the `0,1` versus `+/-1/2` bookkeeping.

### 4. `WeilSquarePacketExhaustion` / `A1-pd`

For every admissible compact-support Hermitian square, construct packet
autocorrelations

```text
Phi_n = Psi_n * Psi_n_sharp
```

inside the finite/directed packet family such that:

- `Phi_n -> Phi` in the topology used by `Q`;
- boundary-null constraints are preserved or corrected;
- supports stay inside the required compact window, up to the stated window
  convention;
- Archimedean and prime pieces of `Q(Phi_n)` converge to `Q(Phi)`.

Broad A1' density on nonnegative compact bumps does not prove this.

### 5. `PacketPSDToWeilSquarePositivity`

Move finite packet positivity to the dense square class.  The positivity engine
must act on autocorrelation packets in the same class that `A1-pd` exhausts.
This is the role of `packet-Rayleigh-pd` plus `PSD-pd`, or any replacement that
keeps the same square-class target.

### 6. `QContinuityOnWeilSquares`

Close the limit step on `W_sq_K`.  The topology must be strong enough for all
terms in `Q`, including boundary corrections and prime/Archimedean pieces.

## Failure Codes

Use these names when the route stalls.

```text
WEIL_SQUARE_CLASS_SPEC_GAP
FINITE_BOUNDARY_NORMALIZATION_GAP
CLASSICAL_WEIL_LINKAGE_GAP
TAU0_RESTRICTED_CONE_GAP
A1PD_PACKET_EXHAUSTION_GAP
BOUNDARY_NULL_CORRECTION_GAP
Q_CONTINUITY_TOPOLOGY_GAP
PACKET_PSD_SAME_CLASS_GAP
```

## Minimal Next Step

Do not spend A3/IND/T5 effort until the class match is explicit.

The next clean move is:

```text
fill or audit WeilSquareClass.lean
  -> state FiniteBoundaryNormalization
  -> state WeilSquarePacketExhaustion/A1-pd as the hard analytic gate
  -> only then connect finite packet positivity to ExactWeilCriterion
```

## Source Anchors

Local anchors:

- `memo.md` -- records that `Weil_criterion_tau0` is not classical Weil.
- `q3.lean.aristotle/Q3/Basic/WeilSquareClass.lean` -- current Lean-facing
  square-class interface.
- `full/sections/A1prime.tex` -- distinguishes broad A1' from corrected A1-pd.
- `full/sections/Notation/qstar_contract.tex` -- promotes
  `W_K^{pd}` / convolution-square cone as the public local target.
- `q3.lean.aristotle/docs/INSIGHTS.md` --
  `WeilSquarePacketExhaustionCheck`.

External anchors checked on 2026-06-25:

- Clay Mathematics Institute RH exposition:
  `https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf`
- Bombieri, `Remarks on Weil's quadratic functional in the theory of prime
  numbers, I`:
  `https://eudml.org/doc/252338`
- Bombieri--Lagarias, `Complements to Li's Criterion for the Riemann
  Hypothesis`:
  `https://math.lsa.umich.edu/~lagarias/doc/bombieri.ps`
