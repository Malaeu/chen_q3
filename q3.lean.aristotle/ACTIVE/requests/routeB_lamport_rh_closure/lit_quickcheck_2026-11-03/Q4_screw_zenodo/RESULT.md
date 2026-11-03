# Q4 — Suzuki screw-function quick check

**FORMULA_MATCH. DIRECT_POSITIVE_TO t=16.11809565095832, with the numerical
scope below. DIAGNOSTIC_NEVER_A_PROOF.** The external source is reachable.
Its larger-range zero-side certificate and one-sided theorem proofs were
read/extracted, not independently certified in this preflight.

Twenty fixed times t=.05,.10,...,1 at85digits reproduce the retrieved
Proposition2.1 dictionary and our original screw source with maximum absolute
difference1.19e-85. C0=-3.70066771137322231518... and
alpha=2.68609170961283279112... match the source; the independent
zeta'(1/2)/zeta(1/2) check differs from alpha by3.22e-86. P6=.85 passes
this normalization test. No factor or constant is fitted.

The direct arithmetic scan includes every prime power n<=10^7:

| Quantity | Result |
|---|---:|
|largest computed t|log(10^7)=16.11809565095832|
|prime-power checkpoints|665134|
|interior stationary minima in convex cells|10341|
|smallest checkpoint value|0.02777000938058718 at n3109|
|smallest interior candidate|0.027520573353620805|
|location of interior candidate|t8.03906375949627, x3099.70975755946|
|cell containing that candidate|3089<x<3109|
|value at X10^7|0.03797729089184|

All computed checkpoint and interior-minimum candidates are positive.
The smallest20 of each type were replayed at85digits using independently
accumulated prime-power prefixes; the discrepancy is well below1e-7 and
about1e-12 or less. The main scan used NumPy long double. This is **not**
outward arithmetic, an interval theorem or a replication of the paper's
claim through t47.48. Reproduction took100.4seconds. The code writes the
complete raw checkpoint archive; published CSV/JSON retains the minimum
candidates and summary, and all_checkpoints.npz retains the full raw numerical data for the parent
lossless publication archive. FULL_SCAN_ARCHIVE.json records its hash. No external sourcecode was executed.

The requested event-only minimization has a meaningful correction:
Psi' jumps downward at prime powers and Psi''>0 between them forx>=2.
Actual minima may occur inside cells. The numerical example above is
strictly below every checked prime-power event, so event-only searching
would miss the minimum. This discrepancy is in the brief's search
description, not in the paper's formula.

The interval0<t<log2 is checked separately: the only stationary candidates
are a maximum at t.15263091445 (Psi=.05586843963) and a minimum at
t.46400178961 (Psi=.03966175656). The origin limit is0 and its small-t
asymptotic is positive. Accordingly, the infimum on the entire punctured
interval0<t<=log(10^7) is0, not a uniform positive minimum. P7=.90 is
numerically consistent with strict positivity, but no finite scan supplies
the arbitrary-height quantifier or a uniform margin.

EXTRACTION.md gives the exact source claims(a)–(d), PDF pages and the
Landau-transform proof structure of the one-sided criterion for Proshka.
This check does not accept the external proof or assign priority.

Reproduce: `python3 crosswalk.py`, `python3 scan.py --N 10000000`.
The high-precision early-interval observations are retained separately in
early_interval.json. A full direct scan to10^9 was not attempted within the
registered quick-check budget. No arithmetic or RH route is promoted.
