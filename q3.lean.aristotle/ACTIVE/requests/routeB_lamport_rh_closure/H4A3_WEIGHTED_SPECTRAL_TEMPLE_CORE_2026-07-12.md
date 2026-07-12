# Route B H4a3 weighted spectral Temple core — revision 19

Status: `H4A3A_PROVED / EXACT_SPECTRAL_INSTANTIATION_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS`

This transaction proves the finite weighted-spectral mathematics below
`H4a3 ResidualToCanonicalAlphaUpper`.  It does not identify the exact Route B
operator carrier, define canonical alpha, prove an operator-domain residual
identity, close SafeAlphaUpper, create Bus 010, or prove RH.

## 1. Finite weighted spectral model

Let a finite spectral expansion have nonnegative weights `p_i` with

```text
sum_i p_i = 1.
```

After shifting the ground level to zero, write the spectral levels as `e_i`,
with distinguished ground index `g`,

```text
e_g = 0,
Delta <= e_i  for i != g,
0 <= Delta.
```

Define the Rayleigh excess and squared centered residual by

```text
alpha = sum_i p_i e_i,
etaSq = sum_i p_i (e_i-alpha)^2.
```

The Lean theorem `weighted_rayleigh_excess_nonneg` first proves
`0 <= alpha` from these exact hypotheses.

## 2. Weighted Temple inequality

For every spectral level,

```text
Delta * e_i <= e_i^2.
```

Multiplying by the nonnegative weights and summing gives

```text
Delta * alpha <= sum_i p_i e_i^2.
```

The weighted variance identity is proved constructively in Lean:

```text
etaSq = sum_i p_i e_i^2 - alpha^2.
```

Combining the two displays yields

```text
alpha * (Delta-alpha) <= etaSq.
```

This is theorem

```text
weighted_residual_sq_ge_rayleigh_excess_mul_gap_sub.
```

It is the finite spectral core of the Kato--Temple residual framework; the
implementation derives it directly rather than importing it as an axiom.  The
external source check agrees that residual estimates are a-posteriori
Rayleigh-quotient bounds and that spectral separation enters their
denominators:

- https://arxiv.org/abs/1207.3240
- https://arxiv.org/abs/1603.06100

## 3. Correct denominator and safe half-gap corollary

When `alpha < Delta`, Lean proves the exact quotient form

```text
alpha <= etaSq / (Delta-alpha).
```

The denominator is the distance from the Rayleigh center to the complementary
spectral floor.  It is not the bare ground gap `Delta`.  This is theorem
`rayleigh_excess_le_residual_sq_div_gap_sub`.

On the certified half-gap locus

```text
0 <= alpha,  0 < Delta,  2*alpha <= Delta,
```

Lean further proves the safe polynomial bound

```text
alpha <= 2*etaSq/Delta.
```

This is theorem `rayleigh_excess_le_two_mul_residual_sq_div_gap`.

## 4. Mandatory falsifier compatibility

Revision 15 proved that the historical composition

```text
sqrt(alpha/Delta) <= eta/Delta
```

is false, already for the two-level vector with
`alpha=eta=1/2`, `Delta=1`.  Revision 19 does not weaken or erase that plant.
For the same values, the exact denominator is `Delta-alpha=1/2`, and the
weighted Temple inequality is an equality:

```text
alpha*(Delta-alpha) = eta^2 = 1/4.
```

Thus the new theorem repairs the direction without reviving the killed
formula.

Verdict: `WEIGHTED_SPECTRAL_TEMPLE_CORE_LEAN`.

## 5. Honest DAG split

`H4a3 ResidualToCanonicalAlphaUpper` is now an AND node:

```text
H4a3
|-- H4a3a GenericWeightedSpectralTempleCore       PROVED
|-- H4a3b ExactRouteBResidualSpectralInstantiation OPEN / INELIGIBLE
`-- H4a3c H4a3Assembly                            OPEN / INELIGIBLE
```

The definitional contract `H4a3.0` is PROVED.  `H4a3b` must still:

1. identify one domain-safe self-adjoint Route B operator;
2. pin its normalized trial vector and spectral weights;
3. identify `alpha` with the Contract-v2 canonical object;
4. identify `etaSq` with the exact ambient residual norm squared;
5. prove that the complementary spectral floor is the true same-carrier gap;
6. prove the Temple locus `2*alpha <= Delta` on the exact cofinal tail;
7. convert `2*etaSq/Delta` to the required SafeAlphaUpper rate;
8. select the exact same-parity error subspace without form/operator
   conflation.

Residual exact stop:

```text
H4A3_EXACT_SPECTRAL_INSTANTIATION_MISSING
```

## 6. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/WeightedSpectralTempleCore.lean
```

It compiles without `sorry`, `admit`, or `exact?`; every printed axiom set is
within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

`H4a3`, `H4a`, `H4`, and RH remain OPEN.  The canonical ACTIVE leaf remains
`D0.7e.5a`, the stop remains `D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is
absent, and Route B remains `CHALLENGER / NOT_RH`.
