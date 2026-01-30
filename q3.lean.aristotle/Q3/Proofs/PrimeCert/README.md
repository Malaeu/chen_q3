# PrimeCert (t_critical, tau = 0)

Certificate inputs for the prime-term cap at `t_critical` (single‑scale).

ASCII map:
```
PrimeCert/
  Defs.lean            -- numeric constants from prime cert runs
  Bmin_1826.lean       -- B = B_min certificate axioms
  BrangeGrid_2046.lean -- grid values (B-range)
  BrangeGridBounds_2046.lean -- grid bounds lemma (arch/prime)
  BrangeHeatCert_2026_01_28_Data.lean -- heat cert data (constants + axioms)
  BrangeHeatCert_2026_01_28.lean -- heat-weighted bounds data
  BrangeCert_2046.lean -- B-range certificate data + theorems (provenance)
  Brange_2046.lean     -- grid cover + margin lemma
  README.md            -- this file
```

Evidence files (sha256):
- `output/prime_cert_tcritical_2026-01-26_0046.txt`
  - `3af1204fc8f5ddf322e1110b9932bb44a5349e0773d6d1b3cdf5441ec8ef3b5d`
- `output/prime_cert_brange_tcritical_2026-01-26_0050.txt`
  - `a9d5303b2da81886cf64bfc5ee9b5b1ab85ce0b45067a8cd9b499d051a294230`
- `output/prime_cert_brange_heat_L_2026-01-28_0115.txt`
  - `da6a6ac1221f93d376aafecd189169607b40b5d394868e893124445089a3e0a5`

Generators:
- `scripts/prime_term_cert.py`
- `scripts/prime_term_cert_brange.py`
- `scripts/prime_brange_heat_lipschitz_cert.py`

Integration point:
- `Q3/Proofs/Q_nonneg_t_critical.lean` (prime-term axioms and caps)

Current cert-data axioms (main chain):
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_prime_data`
