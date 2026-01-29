# Prime-term certificate (t_critical, B_min, tau = 0) — 2026‑01‑26

**Goal:** certify `prime_term (phi_shift B_min t_critical 0) ≤ arch_term (phi_shift B_min t_critical 0)`.

**Method:** exact prime powers up to `N`, analytic tail bound, numeric arch integral.
- Compute exact sum over prime powers `n ≤ N` via sieve.
- Bound tail with `Λ(n) ≤ log n` and `phi ≤ exp(-t (log n)^2)` (integral estimate).
- Compute `arch_term` by numerical integration (mpmath).

**Parameters used:**
- `B_min = 3`
- `t_critical = 3/20 = 0.15`
- `tau = 0`
- `N = 1_000_000`
- Precision: 50 digits (mpmath)

**Result (numerical):**
- `prime_sum (n≤N) ≈ 8.7135790788318`
- `tail_bound ≈ 2.7839976842107422e-9`
- `prime_upper_bound ≈ 8.713579081615799`
- `arch_term ≈ 9.570036393390224`
- **margin ≈ 0.856457311774425**

**Artifacts:**
- Script: `scripts/prime_term_cert.py`
- Output: `full/q3.lean.aristotle/output/prime_cert_tcritical_2026-01-26_0046.txt`

**Lean integration plan:**
- Keep conservative rationals already in `Q3.Proofs.PrimeCert.Defs`:
  - `prime_cert_prime_ub = 8714/1000 = 8.714`
  - `prime_cert_arch_lb = 957/100 = 9.57`
- Use axioms in `Q3/Proofs/PrimeCert/Bmin_1826.lean` to bridge numeric bounds.
