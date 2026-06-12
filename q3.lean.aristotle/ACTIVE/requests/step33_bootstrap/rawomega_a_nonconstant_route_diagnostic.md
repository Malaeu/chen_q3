# Raw-Omega A Nonconstant Route Diagnostic

This is sampled Arb route evidence, not a Lean proof object.

- samples per chunk: `17`
- verdict: `chunkwise_constant_route_sampled_too_coarse`

The diagnostic checks the active target:

```lean
RawOmegaAAnalyticTailWindowInputs
```

Positive excess means even chunkwise constants on the current grid are
sampled-too-coarse for the generated finite/tail target.  Zero excess
means only that this route is not rejected by sampled point capacity;
Lean still needs checked pointwise comparisons and scalar integral
containments.

## primary k=11

Worst finite window:

```json
{
  "distance": "5.50",
  "finite": {
    "chunk_count": 26,
    "chunk_size": "1.000000000000000000E+1",
    "chunkwise_constant_route_not_rejected_by_samples": false,
    "excess": "2.231744501532018178E+0",
    "left": "0.000000000000000000E+0",
    "lower_excess": "1.499906003545321318E+0",
    "right": "2.600000000000000000E+2",
    "sampled_lower_capacity": "-1.511315731438330860E+0",
    "sampled_upper_floor": "2.220334773639008638E+0",
    "samples_per_chunk": 17,
    "target_lower": "-1.140972789300954138E-2",
    "target_upper": "-1.140972789300954062E-2",
    "upper_excess": "2.231744501532018178E+0",
    "worst_capacity_chunk": {
      "left": "0.000000000000000000E+0",
      "lower_capacity": "-9.944495812007104861E-1",
      "max_sample_lower": "1.691502026195019970E-1",
      "max_sample_lower_eta": "5.882352941176470588E-1",
      "min_sample_upper": "-9.944495812007104861E-2",
      "min_sample_upper_eta": "1.176470588235294118E+0",
      "right": "1.000000000000000000E+1",
      "upper_floor": "1.691502026195019970E+0",
      "width": "1.000000000000000000E+1"
    },
    "worst_floor_chunk": {
      "left": "0.000000000000000000E+0",
      "lower_capacity": "-9.944495812007104861E-1",
      "max_sample_lower": "1.691502026195019970E-1",
      "max_sample_lower_eta": "5.882352941176470588E-1",
      "min_sample_upper": "-9.944495812007104861E-2",
      "min_sample_upper_eta": "1.176470588235294118E+0",
      "right": "1.000000000000000000E+1",
      "upper_floor": "1.691502026195019970E+0",
      "width": "1.000000000000000000E+1"
    }
  },
  "index": 22
}
```

Worst tail window:

```json
{
  "distance": "1.75",
  "index": 7,
  "tail": {
    "chunk_count": 26,
    "chunk_size": "1.000000000000000000E+1",
    "chunkwise_constant_route_not_rejected_by_samples": false,
    "excess": "2.497737519923627198E-21",
    "left": "2.600000000000000000E+2",
    "lower_excess": "2.497737519923627198E-21",
    "right": "5.200000000000000000E+2",
    "sampled_lower_capacity": "-2.497737519923627188E-21",
    "sampled_upper_floor": "2.270450809783450170E-21",
    "samples_per_chunk": 17,
    "target_lower": "9.734208512697355486E-39",
    "target_upper": "1.032615878008123111E-38",
    "upper_excess": "2.270450809783450159E-21",
    "worst_capacity_chunk": {
      "left": "3.100000000000000000E+2",
      "lower_capacity": "-8.718568404932632786E-22",
      "max_sample_lower": "8.187455587027522881E-23",
      "max_sample_lower_eta": "3.123529411764705882E+2",
      "min_sample_upper": "-8.718568404932632786E-23",
      "min_sample_upper_eta": "3.105882352941176471E+2",
      "right": "3.200000000000000000E+2",
      "upper_floor": "8.187455587027522881E-22",
      "width": "1.000000000000000000E+1"
    },
    "worst_floor_chunk": {
      "left": "3.000000000000000000E+2",
      "lower_capacity": "-8.525925516217709369E-22",
      "max_sample_lower": "8.838497944886341453E-23",
      "max_sample_lower_eta": "3.088235294117647059E+2",
      "min_sample_upper": "-8.525925516217709369E-23",
      "min_sample_upper_eta": "3.070588235294117647E+2",
      "right": "3.100000000000000000E+2",
      "upper_floor": "8.838497944886341453E-22",
      "width": "1.000000000000000000E+1"
    }
  }
}
```

## control k=9

Worst finite window:

```json
{
  "distance": "5.50",
  "finite": {
    "chunk_count": 26,
    "chunk_size": "1.000000000000000000E+1",
    "chunkwise_constant_route_not_rejected_by_samples": false,
    "excess": "2.328679882977027138E+0",
    "left": "0.000000000000000000E+0",
    "lower_excess": "1.527487584590997615E+0",
    "right": "2.600000000000000000E+2",
    "sampled_lower_capacity": "-1.540003727724024080E+0",
    "sampled_upper_floor": "2.316163739844000673E+0",
    "samples_per_chunk": 17,
    "target_lower": "-1.251614313302646556E-2",
    "target_upper": "-1.251614313302646504E-2",
    "upper_excess": "2.328679882977027138E+0",
    "worst_capacity_chunk": {
      "left": "0.000000000000000000E+0",
      "lower_capacity": "-1.089991506433735971E+0",
      "max_sample_lower": "1.854976059248940395E-1",
      "max_sample_lower_eta": "5.882352941176470588E-1",
      "min_sample_upper": "-1.089991506433735971E-1",
      "min_sample_upper_eta": "1.176470588235294118E+0",
      "right": "1.000000000000000000E+1",
      "upper_floor": "1.854976059248940395E+0",
      "width": "1.000000000000000000E+1"
    },
    "worst_floor_chunk": {
      "left": "0.000000000000000000E+0",
      "lower_capacity": "-1.089991506433735971E+0",
      "max_sample_lower": "1.854976059248940395E-1",
      "max_sample_lower_eta": "5.882352941176470588E-1",
      "min_sample_upper": "-1.089991506433735971E-1",
      "min_sample_upper_eta": "1.176470588235294118E+0",
      "right": "1.000000000000000000E+1",
      "upper_floor": "1.854976059248940395E+0",
      "width": "1.000000000000000000E+1"
    }
  },
  "index": 22
}
```

Worst tail window:

```json
{
  "distance": "3.75",
  "index": 15,
  "tail": {
    "chunk_count": 26,
    "chunk_size": "1.000000000000000000E+1",
    "chunkwise_constant_route_not_rejected_by_samples": false,
    "excess": "3.812836324515967442E-18",
    "left": "2.600000000000000000E+2",
    "lower_excess": "3.812836324515967442E-18",
    "right": "5.200000000000000000E+2",
    "sampled_lower_capacity": "-3.889730426076660801E-18",
    "sampled_upper_floor": "2.788191976153746537E-18",
    "samples_per_chunk": 17,
    "target_lower": "-7.689410156069335989E-20",
    "target_upper": "-7.689410156069335989E-20",
    "upper_excess": "2.865086077714439897E-18",
    "worst_capacity_chunk": {
      "left": "2.600000000000000000E+2",
      "lower_capacity": "-3.103321065437460780E-18",
      "max_sample_lower": "2.399914196225243960E-19",
      "max_sample_lower_eta": "2.629411764705882353E+2",
      "min_sample_upper": "-3.103321065437460780E-19",
      "min_sample_upper_eta": "2.605882352941176471E+2",
      "right": "2.700000000000000000E+2",
      "upper_floor": "2.399914196225243960E-18",
      "width": "1.000000000000000000E+1"
    },
    "worst_floor_chunk": {
      "left": "2.600000000000000000E+2",
      "lower_capacity": "-3.103321065437460780E-18",
      "max_sample_lower": "2.399914196225243960E-19",
      "max_sample_lower_eta": "2.629411764705882353E+2",
      "min_sample_upper": "-3.103321065437460780E-19",
      "min_sample_upper_eta": "2.605882352941176471E+2",
      "right": "2.700000000000000000E+2",
      "upper_floor": "2.399914196225243960E-18",
      "width": "1.000000000000000000E+1"
    }
  }
}
```
