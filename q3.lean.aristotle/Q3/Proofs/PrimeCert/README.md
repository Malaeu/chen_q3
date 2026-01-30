# PrimeCert (t_critical, tau = 0)

Certificate inputs for the prime-term cap at `t_critical` (single‑scale).

ASCII map:
```
PrimeCert/
  Defs.lean            -- numeric constants from prime cert runs
  Bmin_1826.lean       -- B = B_min certificate axioms
  BrangeGrid_2046.lean -- grid values (B-range)
  BrangeGrid_PrimeSumTail.lean -- prime-term tail/summability scaffold
  BrangeGrid_Pilot_2026_01_30.lean -- pilot hypotheses (2 points)
  BrangeGrid_Pilot_2026_01_30_Data.lean -- pilot data (2 points)
  BrangeGrid_PrimeSum_2026_01_30_Data.lean -- prime-term sum data (all points)
  BrangeGridBounds_2046.lean -- grid bounds lemma (arch/prime)
  BrangeHeatCert_2026_01_28_Data.lean -- heat cert data (constants + axioms)
  BrangeHeatCert_2026_01_28_SumData.lean -- heat prime partial+tail data
  BrangeHeatCert_2026_01_28_Partial.lean -- prime-heat partial-sum scaffold
  BrangeHeatCert_2026_01_28.lean -- heat-weighted bounds data
  BrangeCert_2046.lean -- B-range certificate data + theorems (provenance)
  Brange_2046.lean     -- grid cover + margin lemma
  README.md            -- this file
```

Evidence files (sha256):
- `output/prime_cert_tcritical_2026-01-26_0046.txt`
  - `3af1204fc8f5ddf322e1110b9932bb44a5349e0773d6d1b3cdf5441ec8ef3b5d`
- `output/prime_cert_brange_tcritical_interval_2026-01-30_2206.txt`
  - `451637edeee5b073d7a4b0cfb8439dd6fdaebc9fc2878182cceea49737babc48`
- `output/prime_cert_brange_tcritical_pilot_2026-01-30_2208.txt`
  - `e721a55add5218fc50f01eda07d715c9f5621989ba6cda8abac11e3671b7b0f0`
- `output/prime_cert_brange_heat_L_interval_2026-01-30_2309.txt`
  - `05b044cbc035b285c453631af81eed8bd0a49b2f0866f6f7f3035c09732630d8`
  - Heat cert details: N = 1000000, primes ≤ N = 78498,
    tail_bound_heat = 0.00000000624018533524325430861606353873445952371208136593940599676748
- `output/prime_cert_brange_heat_prime_partial_interval_2026-01-30_2309.txt`
  - `1c9fe427476eb63cfa9e4eb57a23888bdbabf08afc5e1d59095f0a7bee80c1f8`

Generators:
- `scripts/prime_term_cert.py`
- `scripts/prime_term_cert_brange.py`
- `scripts/prime_brange_interval_cert.py`
- `scripts/prime_brange_pilot_points.py`
- `scripts/prime_brange_heat_lipschitz_cert.py`
- `scripts/prime_brange_heat_partial_interval_cert.py`

Integration point:
- `Q3/Proofs/Q_nonneg_t_critical.lean` (prime-term axioms and caps)

Current cert-data axioms (main chain):
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data`
- `Q3.Proofs.PrimeCert.prime_heat_sum_data`
