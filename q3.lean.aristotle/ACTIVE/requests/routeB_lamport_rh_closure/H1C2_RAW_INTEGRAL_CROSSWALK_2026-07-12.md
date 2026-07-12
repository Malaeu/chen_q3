# Route B H1c2 exact raw-integral crosswalk — revision 17

Status: `H1C2_PROVED / MASTER_FAMILY_SELECTION_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + EXACT_OBJECT_CROSSWALK`

This worker transaction closes only `H1c2 RawIntegralRhsCrosswalk`.  It does
not change the unique canonical ACTIVE leaf `D0.7e.5a`, choose the Route B
master approximant family, close `H1c`, create Bus 010, or prove RH.

## 1. Exact source-raw transform

For `L != 0`, finite support `S`, coefficients `c`, and `z : C`, define

```text
Raw(L,S,c;z)
  = exp(i*z*L/2)
      * integral_0^L finiteLogFourierTrial(L,S,c;x) exp(-i*z*x) dx.
```

The phase and Fourier sign are forced by the locked D0.6 change of variables
`x = log(lambda*u)`, with `L = 2 log(lambda)`.  The Lean theorem

```text
finiteRawCenteredIntegral_eq_proposition59RawTransform
```

proves, for every complex point,

```text
Raw(L,S,c;z) = proposition59RawTransform(L,S,c;z).
```

There is no excluded source lattice and no limit assumption.

## 2. Constructive lattice closure

The proof first works mode by mode.  Away from
`z = 2*pi*k/L`, Mathlib's `integral_exp_mul_complex` gives the printed
quotient

```text
2*sin(z*L/2)/(z-2*pi*k/L).
```

At `z = 2*pi*k/L`, the exponent coefficient is exactly zero.  The interval
integral is `L`, the centering phase is `exp(i*pi*k)`, and the result is

```text
L*cos(pi*k),
```

which is exactly the `dslope` value already proved in H1c1.  The theorem
`rawModeCenteredIntegral_eq_kernel` joins these two branches.  Interval
integral linearity then lifts the identity to the finite coefficient sum.

Verdict: `RAW_INTEGRAL_PROPOSITION59_RHS_EXACT_CROSSWALK`.

## 3. Mandatory reflection guard

The D0.6 source lock identifies owner `Fplus(z)` with `T(k)(-z)`, not
`T(k)(z)`.  The Lean file separately proves for the corresponding finite
positive-exponent centered integral

```text
finiteFplusCenteredIntegral(L,S,c;z)
  = proposition59RawTransform(L,S,c;-z).
```

No coefficient-evenness, support reflection, or complex conjugation is
silently inferred.  Combining this theorem with the mathematical D0.6 source
lock gives the expected owner representative; the Lean file itself does not
define `T_m`, `kappa_m`, or the owner master family.  Thus H1c2 closes the
source-raw equality at `z`, while the future master-family crosswalk H1c3 must
consume the explicit `-z` reflection.  This prevents
`H1_TRANSFORM_SIGN_OR_PHASE_MISMATCH` from being hidden by a name collision.

## 4. Lean and honesty boundary

Proof artifact:

```text
Q3/Proofs/RouteB/RawIntegralRhsCrosswalk.lean
```

The file compiles without `sorry`, `admit`, or `exact?`.  Its printed axiom
sets contain only `propext`, `Classical.choice`, and `Quot.sound`.

The next exact H1 node is `H1c3`, but it is not an eligible worker leaf:
`D0.8` and the owner master-family architecture choice remain open.  Therefore
`H1c`, `H1c4`, `H1d`, and `H1` stay OPEN.  The canonical scheduler stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`; Route B remains
`CHALLENGER / NOT_RH`.
