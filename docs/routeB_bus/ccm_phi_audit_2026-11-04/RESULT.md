# CCM Phi audit, independent Arb replay, finite-count growth

Route B = CHALLENGER / NOT_RH. DIAGNOSTIC_NEVER_A_PROOF.

**All eight original m300 gates PASS in python-flint/Arb. All five requested finite cells were completed. No fatal counterexample was found in the requested paper audit.** The independently checked finite inequalities give the bounds below, using explicit external theorem premises. Canon and mirror are identical. No route-state or RH export is changed.

## Finite results

The original score consumer and rational rounding give:

| m | N₊ | simple-on-line lower | lower/N₊ | distinct upper-zero lower | lower/N₊ | integer-refined simple lower |
|---:|---:|---:|---:|---:|---:|---:|
| 300 | 185 | 14 | 7.5676% | 100 | 54.0541% | 15 |
| 600 | 384 | 59 | 15.3646% | 222 | 57.8125% | 60 |
| 1000 | 657 | 126 | 19.1781% | 392 | 59.6651% | 127 |
| 2000 | 1355 | 310 | 22.8782% | 833 | 61.4760% | 311 |
| 3000 | 2066 | 506 | 24.4918% | 1286 | 62.2459% | 506 |

Here N₊ is a **certified upper bound**, not a measured census. Counts concern positive-height zeros below the strict cutoff T. Distinct means distinct complex zeros, not distinct heights. Fractions divide by N₊ and consequently remain safe lower bounds for fractions of the actual count. Decimal percentages are displays; GROWTH.csv records exact rational fractions.

P1 PASS: all eight original gates. P2 PASS in the bounded audit: no fatal error found in (3.4)/(3.5)/(6.1). P3 PASS: 506/2066>0.20. P4 PASS: both original fractions increase strictly on this five-point grid; the refined simple fractions do too. These observations imply no cofinal trend or limiting proportion. The paper's separate asymptotic derivation is audited as a symbolic argument under its named theorem premises, not inferred from these cells.

## Original m300 replay

Fixed precision: **160 bits**, python-flint0.9.0/Arb. No zero list, source arrays, eigensystem, or numerical quadrature is read by arb_replay.py. It evaluates the physical even source H+P−B from analytic digamma/trigamma, elementary functions, exact integer prime powers and explicit positive remainder envelopes. This independently replaces the verdict's mpmath.iv Euler–Maclaurin implementation with Arb special functions. The source matrix and all signs remain unchanged.

| Quantity | Arb enclosure/display | Original rational gate |
|---|---|---|
| tr A | 895.9964353161231271713828631355517 ±8.49e−32 | ≥895.9 |
| ‖A‖²F | 5479.95986411881239296321686525535 ±2.84e−30 | ≤5481 |
| nuclear tail envelope E | 12.402620474830162058934 ±3.89e−22 | ≤12.5 |
| M(T)+.55log T | 185.3596118259435749741289166143432… | <186 ⇒ N≤185 |
| Rosser R(T)/log T | 0.53864992148027706135… | <11/20, decreasing thereafter |
| gamma5 zero-free error | 0.35766971628007473289… | <1/2 |
| F₋−2N₊ | 13.69377706274332155676… | >13 ⇒ s₁≥14 |
| (F₋−N₊)/2 | 99.34688853137166077838… | >99 ⇒ N_d≥100 |

T300=370.17962509312907712492449… and σ=log300+1/5. Full outward enclosures, source decomposition, backend version, rational inputs and gate booleans are in ARB_m300.json; GATES.json joins audit status and predictions. The six source components reproduce the verdict's displayed decomposition. Against the c539c195 binary64 component ledger, the largest absolute difference is7.28e−12 (in H² and P², with opposite signs). Thus literal agreement in every printed digit of that ledger is not claimed. The archived400-bit source Frobenius point lies inside the Arb enclosure. These are diagnostic consistency checks, not inputs to the Arb certificate.

## Paper audit, in requested order

- **(3.4): PASS.** Direct composition of literal truncated shifts has overlap L−max(u,v) for opposite orientations and (L−u−v)₊ for equal orientations. The full Fourier trace has exactly the displayed2/L. It is the uncompressed square; subsequent compression loss is separately paid.
- **(3.5): PASS.** The ordinary adjacent logarithmic gaps are at least1/(n+1); the wrap gap is log2. There is no duplicate n=1 node. Restriction to prefixes increases separation.
- **Parity: PASS.** Reflection commutes with the summed shifts and Fourier projection. The reflected trace bound is actually at most2+1/π<4 for each oriented composition, sufficient for8C₀².
- **Leakage: PASS.** Counting exiting Fourier modes gives min(|r|,2m+1) and the stated β. Even leakage is bounded by full leakage because the summed shift preserves parity. No odd-sector leakage has been omitted.
- **(2.1), (4.1), (4.4): PASS under the cited theorem imports.** The Gamma boundary correction is a PSD rank-one series with the printed normalization, the prime diagonal coefficient is1/3 by quantitative PNT, and all mixed signs and smaller-order terms are retained.
- **(5.1)–(5.2): symbolic assembly checks pass under the external premises.** The inherited weighted Ingham tail, its Stieltjes boundary sign and o(N) score payment were separately checked, as was the exact rank–trace consumer. This audit does not reprove the external zero-density theorem or promote the asymptotic statements to a route export.
- **(6.1): PASS.** Fourier evaluation contributes4/L and pairing the two signs of height contributes the factor2, giving8. The exact denominator difference is2η²(γ²+ω²)+η⁴≥0. Off-line multiplicities are paid per positive-height zero.

AUDIT_GEOMETRY.md, AUDIT_ASYMPTOTICS.md, AUDIT_TAIL.md, AUDIT_INHERITED_DENSITY.md and AUDIT_CONSUMER.md give the derivations and precise boundaries. A separate read-only implementation review in AUDIT_ARB_IMPLEMENTATION.md found no substantive enclosure, sign, remainder or rounding flaw. Geometry falsification attempts cover72 joint/shift cases and190 single atoms; these are floating diagnostics supporting the paper derivation, not interval proofs. No CCM_PHI_AUDIT_COUNTEREXAMPLE is asserted and the interpretation kill-switch was not triggered.

## External premises and their verification limits

Primary source statements were independently retrieved: Montgomery–Vaughan JLMS1974 Theorem1(1.3) is the circular cosecant inequality with local gaps and constant3/2; Faber–Kadiri Theorem1.5 reproduces Rosser's T≥2 all-zero count with constants .137,.443,1.588. The quantitative PNT rate is a standard unconditional theorem; Johnston–Yang provides a stronger sufficient statement. Its proof uses finite-height RH verification internally, so that paper must not be described as avoiding all computational zero verification. No such verification or zero table is an input to this finite replay.

The finite count pipeline itself needs the exact source identity, the elementary gamma5 argument, Rosser’s count bound and the checked rank–trace algebra; it does not need PNT, Hilbert’s inequality or Ingham. The classical uniform Ingham theorem remains an explicit external theorem premise for the separate cofinal tail audit. The exact Weil source/divisor identity and standard zeta strip/symmetry facts are inherited analytic premises. These are not replaced by numerical gates. Original external proofs and Lean formalization were not reproduced. EXTERNAL_SOURCES.json records URLs and PDF hashes; downloaded PDFs/text remain local.

## Sharper finite inequality: integer bookkeeping

The same head consumer yields Φ≤3s+4k and N≥s+2k, where s=s₁ and k=s₂+b are integers. Therefore a candidate s is excluded whenever

F₋ > 3s+4 floor((N₊−s)/2).

At m300 every s≤14 has right side at most383, whereas F₋>383.69377706. Thus the very same inputs imply **s₁≥15**, with N_d≥100 unchanged. The refined simple bounds on the grid are15,60,127,311,506. This strengthening uses no new source estimate; it preserves the original eight gates and original prediction scoring. See AUDIT_CONSUMER.md and the separate refined columns in GROWTH.csv.

## Rational choices, budget and replay

Always c=1/4, b=1/5 and R*(t)=(11/20)log t. The original m300 inputs remain8959/10,5481,25/2,185. At subsequent m, a₋ is tr A rounded down to a tenth, q₊ is ‖A‖²F rounded up to an integer, E₊ is the certified envelope rounded up to a tenth, and N₊ is the count-envelope integer upper bound. Every choice is tested by an Arb comparison. The exact values are in GROWTH.csv and each ARB_m*.json.

All cells use the same160bits, six retained exponential source terms with an explicit remainder, and256 tail-series terms with an explicit positive geometric remainder. The largest cell completed in about49seconds. An initial long trigonometric recurrence expanded its interval radii and failed two gates; direct Arb sin/cos at the same precision removed that dependency wrapping. This was an implementation change, not a precision escalation or a change to the source. No unresolved cell was converted into a pass.

Run `python arb_replay.py --m 300` with python-flint0.9.0 installed; repeat for the requested grid. `verify.py` validates all saved interval gates, rational choices, growth counts, integer refinement, diagnostic comparison and SHA256SUMS. Large source matrices are never stored by this replay. The finite interval results and the bounded paper audit remain DIAGNOSTIC_NEVER_A_PROOF; no RH claim is made.
