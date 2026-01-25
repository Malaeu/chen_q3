# PrimeCert (t_critical, tau = 0)

Certificate inputs for the prime-term cap at `t_critical` (single‑scale).

ASCII map:
```
PrimeCert/
  Defs.lean   -- numeric constants from prime cert runs
  README.md   -- this file
```

Evidence files:
- `output/prime_cert_tcritical_2026-01-25_1826.txt` (B = B_min)
- `output/prime_cert_brange_tcritical_2026-01-25_2046.txt` (B ∈ [B_min, 4.9])

Integration point:
- `Q3/Proofs/Q_nonneg_t_critical.lean` (prime-term axioms and caps)
