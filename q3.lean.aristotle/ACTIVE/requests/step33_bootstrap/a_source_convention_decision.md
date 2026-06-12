# Step33A.1-A A-source convention decision note

Date: 2026-06-02

Scope:

```text
Step33A.1-A, Arch-side A finite-tail analytic cert gate.
```

This note is a non-mutating route decision artifact.  It does not edit
`ARadius`, CSV files, radius-floor data, or generated global A radii.

## Local sources checked

1. `full/sections/T0.tex` states the repository normalization under
   `eta = 2*pi*xi`:

```text
int_R (log pi - Re psi(1/4 + i eta/2)) phi_GW(eta) d eta
=
int_R 2*pi*(log pi - Re psi(1/4 + i*pi*xi)) phi(xi) d xi.
```

It explicitly records the canonical `a_star` matching the Guinand-Weil form
under this change of variables.

2. `Q3/Basic/Defs.lean` defines:

```lean
def a (xi : Real) : Real :=
  Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * xi)).re

def a_star (xi : Real) : Real :=
  2 * Real.pi * a xi
```

3. The active Step33 A receiver uses:

```lean
centeredBSplineArchKernelProfile k ell x
= int_R Q3.a_star t *
    (ell * cos(t*x) * centeredBSplineImagTransformRealClosedForm k ell t^2) dt
```

4. The Step22 A payload generator uses:

```text
ell/pi * int_0^infty Omega(t) |E_{ell,k}(it)|^2 cos(t*d) dt
Omega(t) = Re psi(1/4 + i*t/2) - log(pi)
```

5. External formula convention checked:
   - DLMF §5.2 defines the psi/digamma function as the logarithmic derivative
     of Gamma: https://dlmf.nist.gov/5.2
   - DLMF §5.11 records psi asymptotic-expansion context:
     https://dlmf.nist.gov/5.11
   - A standard Weil explicit formula convention writes
     `Psi(t) = -log(pi) + Re psi(1/4 + i*t/2)` and places it in the
     archimedean integral with an explicit `-1/(2*pi)` factor:
     https://en.wikipedia.org/wiki/Explicit_formulae_(L-function)#Weil's_explicit_formula

## Algebraic comparison

With the Step22 notation:

```text
Omega(eta) = Re psi(1/4 + i*eta/2) - log(pi).
```

With the repository T0 normalization:

```text
a_star(xi)
  = 2*pi*(log(pi) - Re psi(1/4 + i*pi*xi))
  = -2*pi*Omega(2*pi*xi).
```

So the sign, Jacobian, and coordinate are coupled.  A valid bridge would also
need to transform the packet factor and cosine:

```text
|E(i*eta)|^2 and cos(eta*d)
```

versus the active receiver's

```text
|E(xi)|^2 and cos(xi*d).
```

This is not a local midpoint recenter theorem at fixed receiver.

## Numerical confirmation

The generated audit
`ACTIVE/requests/step33_bootstrap/a_source_convention_audit.{json,md}` compares
the Step22 source against the active Lean `a_star` receiver on the same finite
window.

Worst primary mismatch:

```text
d = 0.00
Step22 full-even midpoint:  2.467288907278439e-1
Lean a_star full-even midpoint: -7.889774143023172e+1
abs mismatch: 7.91444703209595639e+1
```

Worst control mismatch:

```text
d = 0.00
Step22 full-even midpoint:  5.2497807317549688e-2
Lean a_star full-even midpoint: -7.520513017099184e+1
abs mismatch: 7.5257627978309389688e+1
```

## Decision

The active Lean receiver is aligned with the repository T0 normalization:

```text
Q3.a_star is the authoritative Step33 A source.
```

Therefore the current Step22 Omega-source payload is a legacy-source payload
for the current Step33 A hbox receiver.  It cannot close
`primaryK11AnalyticAFiniteTailAnalyticBoundsCert` or
`controlK9AnalyticAFiniteTailAnalyticBoundsCert` by local recentering.

## Consequence for Step33A.1-A

The local recenter route remains valid as a theorem shape, but it must be fed
with finite/tail data generated for the same source as the receiver:

```text
active source: Q3.a_star
receiver: centeredBSplineArchKernelProfile
payload target: imported A midpoint/radius
```

If the imported A midpoint/radius stays Step22-Omega-sourced, the containment
inequality fails for source reasons, not radius reasons.

## Next allowed route

Do not mutate global radii as a proof route.

The next route fork is now explicit:

```text
A. If global data migration is allowed:
   perform one explicit A source/data migration to Q3.a_star-sourced A data,
   then re-run local recenter containment against the migrated imported A.

B. If global data migration is not allowed in the current goal:
   keep Step33A.1-A open and report this exact source-convention blocker.
```

Under the current hard constraints (`no CSV`, `no ARadius`, `no global radius
payload regeneration`), route B is the only allowed status.  Structural
`a_star` tail lemmas may still be improved, but they cannot by themselves close
the A hbox against the old Step22-Omega imported A table.
