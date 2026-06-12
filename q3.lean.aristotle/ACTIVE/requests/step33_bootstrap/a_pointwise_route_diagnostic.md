# Step33A.1-A Pointwise Chunk Route Diagnostic

This is a sampled route diagnostic, not a Lean proof object.
It tests whether optimistic pointwise-constant chunk bounds can fit
the current generated finite/tail window targets.

- samples per chunk: `41`
- verdict: `pointwise_constant_route_too_coarse`

## primary k=11

Worst finite:

```json
{
  "distance": "5.50",
  "finite_excess": "3.660710382100367696E+0",
  "finite_sampled_lower_sum": "-3.666415246046872466E+0",
  "finite_sampled_upper_sum": "2.333017867105622029E+0",
  "finite_target_lower": "-5.704863946504770690E-3",
  "finite_target_upper": "-5.704863946504770310E-3",
  "index": 22,
  "tail_excess": "2.480230963870975455E-21",
  "tail_sampled_lower_sum": "-2.470456079105419072E-21",
  "tail_sampled_upper_sum": "2.480230963870975618E-21",
  "tail_target_lower": "1.627623055066903689E-37",
  "tail_target_upper": "1.629182771798841832E-37"
}
```

Worst tail:

```json
{
  "distance": "3.75",
  "finite_excess": "3.628073000718177094E+0",
  "finite_sampled_lower_sum": "-3.641765713625560165E+0",
  "finite_sampled_upper_sum": "1.944557594857786634E+0",
  "finite_target_lower": "-1.369271290738307128E-2",
  "finite_target_upper": "-1.369271290738307012E-2",
  "index": 15,
  "tail_excess": "2.638393505034841221E-21",
  "tail_sampled_lower_sum": "-2.445989034117806298E-21",
  "tail_sampled_upper_sum": "2.638393505034841146E-21",
  "tail_target_lower": "-7.547160862263315632E-38",
  "tail_target_upper": "-7.527602995532354013E-38"
}
```

## control k=9

Worst finite:

```json
{
  "distance": "5.50",
  "finite_excess": "3.889366855225559058E+0",
  "finite_sampled_lower_sum": "-3.895624926792072291E+0",
  "finite_sampled_upper_sum": "2.431892656390405280E+0",
  "finite_target_lower": "-6.258071566513232780E-3",
  "finite_target_upper": "-6.258071566513232520E-3",
  "index": 22,
  "tail_excess": "3.839650143327551957E-18",
  "tail_sampled_lower_sum": "-3.793758378879989882E-18",
  "tail_sampled_upper_sum": "3.871334446931697694E-18",
  "tail_target_lower": "3.168430360414573664E-20",
  "tail_target_upper": "3.168430360414573664E-20"
}
```

Worst tail:

```json
{
  "distance": "4.00",
  "finite_excess": "3.840637792880550710E+0",
  "finite_sampled_lower_sum": "-3.853890431737853249E+0",
  "finite_sampled_upper_sum": "2.065310024543053929E+0",
  "finite_target_lower": "-1.325263885730253900E-2",
  "finite_target_upper": "-1.325263885730253820E-2",
  "index": 16,
  "tail_excess": "3.931384684852465400E-18",
  "tail_sampled_lower_sum": "-3.921520086576360953E-18",
  "tail_sampled_upper_sum": "3.927830706151702523E-18",
  "tail_target_lower": "9.864598276104447575E-21",
  "tail_target_upper": "9.864598276104447575E-21"
}
```

