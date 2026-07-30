# RouteB.038 — finite Supplier A Green-engine rehearsal at m=257

```yaml
name: finiteSupplierAGreenEngineRehearsal_m257
scope: FINITE_CELL_REHEARSAL_ONLY
status: PASS
secondary_flag: SUPPLIER_A_REHEARSAL_036_PASSED
cofinal_premise: false
positive_controls: 179
zero_compatible: 62
strictly_negative: 0
kill_event: false
```

## Locked inputs

- `PRIORITY_BAND_POSITIVE_PART_CERT.json`: exact 031 tooth alias,
  divided-difference recurrence, symmetrizer and full finite Green ledger.
- `FULL_WINDOW_POSITIVE_PART_CERT.json`: 241 frozen teeth at `m=257`.
- `COUPLED_FULL_SUM_RESPONSE_CERT.json`: live continued-fraction terminal
  response; terminal ratio is not set to zero.

All inputs passed the Route B mirror MANIFEST hash gate.

## Replay ledger

| Check | Result |
|---|---|
| Exact alias `S*_r=r*T_r(Psi)-Psi(0)/2`, every `r=17..257` | PASS |
| Source forcing orientation `L_Theta4(delta)=((Theta4-Theta0)/2)b0` | PASS |
| `delta_0=0` exact before interval arithmetic | PASS |
| Lower Green coefficient `a_-1=omega_0*p_0=0` | PASS |
| Terminal Green term retained live | PASS |
| Frozen tooth coverage | 241/241 |
| Strict nonnegative controls | 179 |
| Zero-compatible teeth | 62 |
| Strictly negative / KILL teeth | 0 |
| Sign-flip receiver mutation | DETECTED |
| Terminal-drop mutation | DETECTED |

The result validates only the finite engine.  The scope checker rejects it
when inserted into a `COFINAL_FAMILY` premise, and goal 036 is absent from
the dependency tree of `scaledOuterSignBarrierFourThirds`.
