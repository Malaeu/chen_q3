# h4_cert — hygiene notes from the CLASSFLOOR verdict (2026-09-07, §2.5)

1. "No float on the certificate path" is not literally true: `cert.pack` and `assemble.read_ball` transport values through floats
   with explicit radius padding (2^-50|m|, 2^-48|m|, radius inflation). Protected, but say so.
2. Two optimized error constants (packet `Ebase`, `Ebasem`) were copied as radius-free decimals. `arb_get_str` guarantees last-decimal
   accuracy, not outward rounding. The judge paid a guard of 1e-18 / 1e-26 from the Euler row released by the constant 120 (< 256);
   the stored hulls remain conservative. NEXT RUN: serialize full balls or round upward explicitly; never rely on spare budget.
3. `abs_lower` is not a signed lower endpoint. It was applied only to already-positive values here; a general checker must not use it.
4. Constant 120 (CLASSFLOOR Thm 1 (12)) may replace 256 in budget.py / packbudget.py once independently checked.
5. Requested packets must be rank-checked symbolically before the run (the 2026-09-07 packet had rank 3: h5 = h4 - h4z).
