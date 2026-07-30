# RouteB.038 — mandatory plant log

```yaml
status: ALL_PLANTS_FIRED
plant_count: 11
failed_plants: []
checker: check_038_scaled_outer_sign_barrier.py
```

| Plant | Mutation | Detector result |
|---|---|---|
| P038-1 PARAMETRIC_SCOPE | insert the `m=257` certificate into a cofinal slot | `FINITE_TO_COFINAL_PROMOTION` rejected |
| P038-2 SCALED_COORDINATE | replace `a=mz=lambda*u` by `a=r/lambda` | source endpoint/tooth object lock rejects |
| P038-3 OUTER_LOBE_SCOPE | use finite 027 as cofinal outer lobe | `OUTER_LOBE_SCOPE_PROMOTION` |
| P038-4 TERMINAL_DROP | delete the two terminal Green monomials | exact formal ledger differs |
| P038-5 LOWER_BOUNDARY | mutate the formal lower coefficient `a_-1` from zero | a nonzero lower monomial appears |
| P038-6 DUAL_ORIENTATION | replace source-locked `Y` by `-Y` | `L(Y)=A/omega` changes to `-A/omega` |
| P038-7 PSI_TRAP | `Psi=t^2-1/3` | zero mass, sign change, and strict interior transition all verified; no Supplier A kill |
| P038-8 CERTIFICATE_CONTAMINATION | inject `rho_033`, `q=700`, `tau_response`, box width | `TRANSITION_OBJECT_CERTIFICATE_CONTAMINATED` |
| P038-9 COVERAGE | delete an open band, the `4/3` crossing band, or `sqrt(m)` junction | `COVERAGE_INCOMPLETE` |
| P038-10 FINITE_TO_COFINAL | use rehearsal/teeth as `forall m` premise | `FINITE_TO_COFINAL_PROMOTION` |
| P038-11 DIRECTION | feed `[L,U]` with `L<0<U` | `INCONCLUSIVE`; only `L>=0` passes and only `U<0` on positive measure kills |

The P038-7 endpoint identities were replayed exactly:

```text
S_r(1/(r+1)) = -r/(6(r+1)) < 0,
S_r(1/r)     = (3r+1)/(6r) > 0.
```

No sign estimate for the real cofinal discriminator was run.
