# PrimeCert (t_critical, tau = 0)

Certificate inputs for the prime-term cap at `t_critical` (single‑scale).

ASCII map:
```
PrimeCert/
  Defs.lean            -- numeric constants from prime cert runs
  IntervalChecker.lean -- generic summation helpers for interval proofs
  Bmin_1826.lean       -- B = B_min certificate axioms
  BrangeGrid_2046.lean -- grid values (B-range)
  BrangeGrid_PrimeSumTail.lean -- prime-term tail/summability scaffold
  BrangeGrid_Pilot_2026_01_30.lean -- pilot hypotheses (2 points)
  BrangeGrid_Pilot_2026_01_30_Data.lean -- pilot data (2 points)
  BrangeGrid_Pilot_2026_01_30_Checker.lean -- pilot bucket checker scaffold
  BrangeGrid_Pilot_2026_01_30_Intervals.lean -- pilot bucketed interval sums
  BrangeGrid_PrimeSum_2026_01_30_UB.lean -- prime-term sum upper bounds (all points)
  BrangeGrid_PrimeSum_2026_01_30_Intervals.lean -- bucketed interval sums (all points)
  BrangeGrid_PrimeSum_2026_01_30_Checker.lean -- full-grid bucket checker scaffold
  BrangeGrid_PrimeSum_2026_01_30_Data.lean -- prime-term sum data (all points)
  BrangeGridBounds_2046.lean -- grid bounds lemma (arch/prime)
  BrangeHeatCert_2026_01_28_Data.lean -- heat cert data (constants + axioms)
  BrangeHeatCert_2026_01_28_Intervals.lean -- heat bucketed partial sums
  BrangeHeatCert_2026_01_28_Checker.lean -- heat bucket checker scaffold
  BrangeHeatCert_2026_01_28_Pilot.lean -- heat bucket pilot scaffold
  BrangeHeatCert_2026_01_28_SumData.lean -- heat prime partial+tail data
  BrangeHeatCert_2026_01_28_Tail.lean -- analytic heat tail bound
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
  - `6b4d3534195471dfe797b1910afbd7068136abfedf3ea0389b9849f917404ddc`
- `output/prime_cert_brange_tcritical_pilot_2026-01-30_2208.txt`
  - `e721a55add5218fc50f01eda07d715c9f5621989ba6cda8abac11e3671b7b0f0`
- `output/prime_cert_brange_tcritical_pilot_interval_2026-01-30_2357.txt`
  - `d2e51b9bea1eff7b50625f3e7c40aeae6a91f3eeab4eb33a5e12e948e460b5db`
- `output/prime_cert_brange_heat_L_interval_2026-01-30_2309.txt`
  - `55e945564c513cefec7d344b8db399214b6739666161c163c55ed5b78098ef77`
  - Heat cert details: N = 1000000, primes ≤ N = 78498,
    tail_bound_heat = 0.000003
- `output/prime_cert_brange_heat_prime_partial_interval_2026-01-31_0009.txt`
  - `622070a7c1684049b1c9147ee39b2e1fdaebe657f4e22acc6490cd452e8493f8`

Generators:
- `scripts/prime_term_cert.py`
- `scripts/prime_term_cert_brange.py`
- `scripts/prime_brange_interval_cert.py`
- `scripts/prime_brange_interval_to_lean_ub.py`
- `scripts/prime_brange_pilot_points.py`
- `scripts/prime_brange_pilot_interval_to_lean_ub.py`
- `scripts/prime_brange_interval_checker_pilot.py`
- `scripts/prime_brange_interval_checker_grid.py`
- `scripts/prime_brange_heat_lipschitz_cert.py`
- `scripts/prime_brange_heat_partial_interval_cert.py`
- `scripts/prime_brange_heat_partial_interval_to_lean.py`
- `scripts/prime_brange_heat_interval_checker.py`

Integration point:
- `Q3/Proofs/Q_nonneg_t_critical.lean` (prime-term axioms and caps)

Current cert-data axioms (main chain):
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data`
- `Q3.Proofs.PrimeCert.prime_heat_sum_data`
