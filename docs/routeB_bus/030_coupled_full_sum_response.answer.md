# RouteB.030 — coupled full-sum response

Status: `CHALLENGER / NOT_RH`  
Scope: finite cell `m=257`; bands `r=256,255`; star teeth
`r=257,256,255`; no cofinal-family claim.

## Verdict

`COUPLED_FULL_SUM_RESPONSE_INCONCLUSIVE`

No secondary flag is emitted.

The response backend closes: the certified residual beyond `q=700` is
`2.24186222683824266e-237`, while
`tau_response = 2^-512 = 7.45834073120020674e-155`.  Thus the residual is
about 82 decimal orders below the registered budget.  Nevertheless every
decisive whole-sum enclosure still contains zero, so the contract forbids
another depth or precision escalation.

## Object and tail lock

- Raw gauge: `a0=1` in both modes; the normalization cancellation gives
  `J0_raw=J4_raw=2`.
- The signed constant coefficients are combined before interval arithmetic:
  `delta_0=(b_(4,0)-b_(0,0))/2=0` exactly.
- Finite response depth: `q=700`, selected from the contraction/remainder
  inequality before inspecting any sign.
- Live CF terminal cone: `[0,1/2]`, look-ahead 16 steps; terminal zero is not
  used.
- Mode-0 and mode-4 extensions each overlap 40 pre-existing 029 source boxes.
- Final tail is response-weighted:
  `sum_(k>=1) 2^-k (2(Q+k)^2+(Q+k)+1)
   = 2Q^2+9Q+15`.
  The forbidden final bound `r*epsilon_Psi` is not used.
- Exact rational Legendre response polynomials and a complete single-cell
  Bernstein cover are used on each closed band and on the old witness.

## Certified whole-sum enclosures

| domain | lower_full_sum | upper_full_sum | coupled_tail_radius |
| --- | ---: | ---: | ---: |
| band `r=256`, `[1/257,1/256]` | `-2.24186314076561794e-237` | `2.24186259310442156e-237` | `1.55581318793812588e-96` |
| band `r=255`, `[1/256,1/255]` | `-2.24186277286415691e-237` | `2.24186283704775417e-237` | `2.11591592308908782e-96` |
| tooth `r=257`, `z=1/257` | `-2.24186170455463593e-237` | `2.24186274912185157e-237` | `1.32460769205403364e-96` |
| tooth `r=256`, `z=1/256` | `-2.24186226269275430e-237` | `2.24186219098373319e-237` | `5.68264453901833245e-97` |
| tooth `r=255`, `z=1/255` | `-2.24186189132027319e-237` | `2.24186256235621459e-237` | `2.42885993180531140e-99` |
| old witness `[65281/16711680,32641/8355840]` | `-2.24186245572790388e-237` | `2.24186200259478508e-237` | `2.57115993247981776e-97` |

The large coupled-tail radii above are not appended independently to the
finite core: their exact rational centers are included in the one whole-sum
polynomial.  Only coefficient-box uncertainty
(`1.2046811075e-252`) and the final response remainder are added outward.

## Plants P1–P6

| plant | result | exact witness |
| --- | --- | --- |
| P1 `delta_0` | `FIRES` | failure to cancel changes band `r=256` by the constant `128` |
| P2 old independent tail | `FIRES` | replay preserves the 029 diagnostic `K_ESCALATION_INCONCLUSIVE`; it does not enter this verdict |
| P3 terminal ratio zero | `FIRES` | live terminal response width is strictly positive; the mutation collapses it to zero and changes the full-sum enclosure |
| P4 mode-4 phase | `FIRES` | `delta_0` changes exactly from `0` to `-1` |
| P5 midpoint | `FIRES` | replacing endpoint weight `1/2` by `1` changes the tooth functional exactly by `Psi(1)/2` |
| P6 zero mass | `FIRES` | for `Psi(t)=t^2-1/3`, `integral_0^1 Psi=0`, but `S*_r=(r+1)/(6r) != 0` for all three teeth |

## Independent checker

The checker imports neither the generator nor Arb.  It verifies all source
hashes, rebuilds the live CF extension, rederives `delta_0=0`, reconstructs
all exact response polynomials and rational covers, recomputes the verdict,
and replays all six plants.

```text
PASS COUPLED_FULL_SUM_RESPONSE_INCONCLUSIVE
P1 PASS P2 PASS P3 PASS P4 PASS P5 PASS P6 PASS
```

Certificate SHA-256:
`2e31e67ba9cc9aed78bfed9ed20d052c1917b508958ddff077124e2cf95989da`.

## Guards

- `STATE` untouched.
- `BUS_010` not created.
- Lemma A / result 027 untouched.
- No grid, no decimal sign ladder, no third sign-driven depth, no
  `mu := 1`, no terminal `rho := 0`, and no coefficient center promoted to
  an exact coefficient.
