# Raw-Omega A Full-Window Constant Route Diagnostic

This is a sampled Arb diagnostic, not a Lean proof object.

- samples per window: `257`
- verdict: `full_window_constant_route_sampled_too_coarse`

Positive excess means the full-window constant comparison route is
already too coarse at sampled points and the next target should be
`RawOmegaAAnalyticTailWindowInputs` rather than more constant-route glue.

## primary k=11

Worst finite window:

```json
{
  "distance": "0.00",
  "finite": {
    "excess": "2.967887914225626187E+1",
    "left": "0.000000000000000000E+0",
    "lower_capacity_from_samples": "-2.955551469689233992E+1",
    "lower_excess": "2.967887914225626187E+1",
    "max_sample_lower": "2.806654949594978941E-2",
    "max_sample_lower_eta": "1.517509727626459144E+1",
    "min_sample_upper": "-1.136750565265089997E-1",
    "min_sample_upper_eta": "1.011673151750972763E+0",
    "right": "2.600000000000000000E+2",
    "sample_count": 257,
    "sampled_constant_route_possible": false,
    "target_lower": "1.233644453639219465E-1",
    "target_upper": "1.233644453639219555E-1",
    "upper_excess": "7.173938423583023291E+0",
    "upper_floor_from_samples": "7.297302868946945247E+0",
    "width": "2.600000000000000000E+2"
  },
  "index": 0
}
```
Worst tail window:

```json
{
  "distance": "2.25",
  "index": 9,
  "tail": {
    "excess": "2.302252217756904650E-20",
    "left": "2.600000000000000000E+2",
    "lower_capacity_from_samples": "-2.302252217756904652E-20",
    "lower_excess": "2.302252217756904650E-20",
    "max_sample_lower": "7.591158276726849636E-23",
    "max_sample_lower_eta": "3.126070038910505837E+2",
    "min_sample_upper": "-8.854816222141940969E-23",
    "min_sample_upper_eta": "3.085603112840466926E+2",
    "right": "5.200000000000000000E+2",
    "sample_count": 257,
    "sampled_constant_route_possible": false,
    "target_lower": "-2.174760883333156440E-38",
    "target_upper": "-2.143920573751077708E-38",
    "upper_excess": "1.973701151948980908E-20",
    "upper_floor_from_samples": "1.973701151948980905E-20",
    "width": "2.600000000000000000E+2"
  }
}
```

## control k=9

Worst finite window:

```json
{
  "distance": "0.00",
  "finite": {
    "excess": "3.242715750734199444E+1",
    "left": "0.000000000000000000E+0",
    "lower_capacity_from_samples": "-3.240090860368321960E+1",
    "lower_excess": "3.242715750734199444E+1",
    "max_sample_lower": "2.761909407631794923E-2",
    "max_sample_lower_eta": "1.416342412451361868E+1",
    "min_sample_upper": "-1.246188792449354600E-1",
    "min_sample_upper_eta": "1.011673151750972763E+0",
    "right": "2.600000000000000000E+2",
    "sample_count": 257,
    "sampled_constant_route_possible": false,
    "target_lower": "2.624890365877484289E-2",
    "target_upper": "2.624890365877484551E-2",
    "upper_excess": "7.154715556183891954E+0",
    "upper_floor_from_samples": "7.180964459842666800E+0",
    "width": "2.600000000000000000E+2"
  },
  "index": 0
}
```

Worst tail window:

```json
{
  "distance": "3.25",
  "index": 13,
  "tail": {
    "excess": "7.977573798316753143E-17",
    "left": "2.600000000000000000E+2",
    "lower_capacity_from_samples": "-7.286168739357304914E-17",
    "lower_excess": "7.285153392989229513E-17",
    "max_sample_lower": "3.067907096903337593E-19",
    "max_sample_lower_eta": "2.610116731517509728E+2",
    "min_sample_upper": "-2.802372592060501890E-19",
    "min_sample_upper_eta": "2.620233463035019455E+2",
    "right": "5.200000000000000000E+2",
    "sample_count": 257,
    "sampled_constant_route_possible": false,
    "target_lower": "-1.015346368075401224E-20",
    "target_upper": "-1.015346368075401224E-20",
    "upper_excess": "7.977573798316753143E-17",
    "upper_floor_from_samples": "7.976558451948677742E-17",
    "width": "2.600000000000000000E+2"
  }
}
```
