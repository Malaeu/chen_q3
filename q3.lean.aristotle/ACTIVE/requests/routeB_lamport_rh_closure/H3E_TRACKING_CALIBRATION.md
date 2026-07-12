# H3e tracking-shape calibration — fail-closed input audit

Prediction registered before any T2 computation:

```text
P2: the I-b2 lower bound alone cannot produce a constant A_K.
```

Status: `BLOCKED / H3E_T2_PINNED_INPUT_SET_INCOMPLETE / NOT_RH`.
Raw table: `H3E_TRACKING_CALIBRATION_RAW.csv` with
`calibration_status=NOT_RUN_INPUT_MISSING`.

No value of `sup_K |Fhat-bDet*Xi|` was computed. The requested comparison
cannot currently be formed solely from the pinned persisted corpus:

| required input | status | persisted locator or exact failure |
| --- | --- | --- |
| `(13,120)` normalized `k1` coefficients | AVAILABLE | `out/portable_k_coeffs_lambda_sq_13_N_120.json`, sha256 `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88` |
| `(14,120)` normalized `k1` coefficients | AVAILABLE | `out/portable_k_coeffs_lambda_sq_14_N_120.json`, sha256 `f2ecc3e794728dceff933f2ced8b7e91593fc5d956a3a4d4a7522dda892bfecf` |
| `(17,120)` normalized `k1` coefficients | MISSING | `T1_LAMBDA17_PERSISTED_COEFFICIENT_VECTOR_MISSING` |
| canonical pinned `WPrime` values | MISSING | `H3E_T2_CANONICAL_WPRIME_INPUT_MISSING` |
| canonical pinned `delta_dict` values | MISSING | `H3E_T2_DELTA_DICT_INPUT_MISSING` |
| historical ladder-law W-shaped diagnostics | REJECTED_AS_CANONICAL_INPUT | use diagnostic alpha variants and the superseded `bPilot`, not the requested pinned canonical consumer |
| compact set `K={|Re z|<=2, |Im z|<=1/4}` | AVAILABLE_AS_REQUEST | no filter or asymptotic quantifier is selected by this note |

Using the historical ladder-law table and replacing its amplitude by `bDet`
would manufacture a new W-shaped quantity, violating the no-new-`WPrime` and
no-new-`alpha` firewall. Running only the available 13/14 cells would also
silently change the pre-registered cell set. Therefore `P2` is **not scored**,
the first divergence location in `|Im z|` is **not measured**, and no H3e
theorem-shape conclusion is drawn.

Exit code: `H3E_T2_PINNED_INPUT_SET_INCOMPLETE`.

Nonclaims: no new selector/filter, no new spectral definitions, no asymptotic
claim, no compact-strip theorem, no H3/H4 closure, and no RH inference.
