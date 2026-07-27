# 007 — centered density factorization

Date: `2026-07-27`

```text
CENTERED_DENSITY_NOT_EXACT_FEJER
```

## Precondition: exact repository normalization

`D0CenteredCriticalMoment.lean:36-43` defines

```text
q_(m,N)(t)
 = (sqrt L_m)^(-1)
   sum_{|n|<=N} (-1)^n c_n exp(2 pi i n t/L_m).
```

The coefficient convention is exactly

```text
c_n = <V_(n,m), kTrial_(m,N)>
```

from `D0KTrialStage3.lean:73-89`.  Thus the multiplier, centering sign, and
coefficient orientation match the goal.

## Exact coefficient mismatch

For a finite amplitude

```text
A(t) = sum_j a_j exp(2 pi i j t/L_m),
```

the Fourier coefficient of `-|A(t)|^2` at lag `n` is

```text
- sum_j a_(j+n) * conj(a_j).
```

The exact repository coefficient at the same lag is instead

```text
(-1)^n c_n
  = (-1)^n <V_(n,m), kTrial_(m,N)>.
```

The first mismatch already occurs at lag `n=0`:

```text
c_0                         -- linear coordinate
versus
- sum_j |a_j|^2             -- negative quadratic mass.
```

Neither `CoefficientFamily`, `TrialNonzero`, `norm_kTrial_m_N`, nor the
Stage-3 bind supplies the required equality

```text
c_0 = - sum_j |a_j|^2
```

or the corresponding nonzero-lag autocorrelation identities.  Unit norm of
`kTrial_(m,N)` constrains the square norm of its coordinate row; it does not
turn the row itself into an autocorrelation row.

## Exact Lean no-go

File:

```text
Q3/Proofs/RouteB/D0CenteredDensityFactorizationFailure.lean
```

The exact one-mode family

```text
kTrial(i,n) = if n=0 then 1 else 0
```

at `(m,N)=(2,0)` satisfies

```lean
theorem centeredTrialDensity_positive_constant_counterexample :
    0 <
      (centeredTrialDensity centeredDensityPositiveConstantRow
        centeredDensityNoGoIndex 0).re
```

with no sampled grid, mpmath, RH input, `sorry`, or new axiom.  Therefore the
requested negative-norm-square theorem is false at the current generic
`CoefficientFamily` interface.

```text
#print axioms centeredTrialDensity_positive_constant_counterexample
[propext, Classical.choice, Quot.sound]
```

## Does the factorization hold before projection?

```text
OPEN / NOT SOURCE-LOCKED.
```

The source-locked pre-projection object is

```text
gTrial_m = E_star(hTrial_m),
E_star(h)(u) = sqrt(u) * sum_{n>=1} h(nu),
hTrial_m = (I4*h0 - I0*h4)/D.
```

This is a signed linear starred sum, not an autocorrelation or modulus-square
definition.  The current source supplies

```text
||hTrial_m||_2 = 1,
integral hTrial_m = 0,
```

but no amplitude, no Toeplitz-PSD certificate, and no identity
`-gTrial_m=|A_m|^2`.  Hence no pre-projection factorization is presently
derivable, and the projected factorization cannot be repaired merely by
deleting `P_m_N`.  This is a source gap, not a proof that no amplitude can
exist for the specialized analytic family.

The completed GIBBS diagnostic is consistent with this source audit but is
not used as proof:

| m | min aligned density, N=120 | N=240 | magnitude ratio |
|---:|---:|---:|---:|
| 53 | `-3.88196915664e-9` | `-5.02676887893e-9` | `1.29490180784` |
| 257 | `-1.51362074517e-8` | `-1.68977260246e-8` | `1.11637780326` |

The violations do not decrease when the number of modes is doubled:
`GIBBS_NOT_CONFIRMED`.

## First non-autocorrelation term

```text
lag n=0:
  repository row       = c_0,
  negative-square row  = -sum_j |a_j|^2.
```

This mismatch precedes every projection-tail estimate.

## Weakest repaired unprojected factorization

The weakest honest replacement is a new source theorem or explicit input:

```text
UnprojectedDensityAutocorrelationData:
  amplitude A_m
  centeredUnprojectedDensity_m(t)
    = -(1/sqrt(L_m)) * |A_m(t)|^2.
```

It must be proved from a new autocorrelation/Gram construction of the source
object; it is not a consequence of the current linear `E_star(hTrial_m)`
definition.  Only after that independent source theorem may one estimate

```text
projected density - unprojected density
```

by a projection budget.

## Six requested corollaries

At the current interface none follows:

| corollary | exact obstruction |
|---|---|
| `centeredTrialDensity_re` | no conjugate-symmetry field on `CoefficientFamily` |
| `centeredTrialDensity_nonpos` | exact positive one-mode counterexample |
| `centeredTrialDensity_ne_zero` | generic zero coefficient family is allowed |
| `centeredTrialDensity_integral_neg` | zero mode has unrestricted sign |
| `c0_neg` | `c_0` is an unrestricted linear coordinate |
| `rawFplus_zero_ne` | available only after assuming `CentralIndex`, not for every pair |

## Hashes

```text
goal:
5c98a55ce899dde1779c00c8bd1029bf4fd35797873d4265780fbaae456e9035

Lean no-go:
affb8756db8710fda2e4d06d77ba50e669eceed90fc1ea89d28c9568ab3a97dc

GIBBS artifact:
8cfbc4f5ab68338634e7cf8914bdd1c723b91416ddc0d3242fcae68dd130b4df
```

Route B remains `CHALLENGER / NOT_RH`.  `UnprojectedRelativeCriticalTail`
was not started.

## Validation

```text
lake env lean Q3/Proofs/RouteB/D0CenteredDensityFactorizationFailure.lean
exit 0

lake build Q3.Main
exit 0

sorry / exact? / admit in the no-go file
0
```
