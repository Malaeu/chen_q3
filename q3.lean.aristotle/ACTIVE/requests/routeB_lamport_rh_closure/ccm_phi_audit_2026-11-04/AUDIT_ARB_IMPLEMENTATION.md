# Independent read-only Arb implementation review

DIAGNOSTIC_NEVER_A_PROOF. **Bounded implementation PASS: no substantive enclosure, kernel-sign, infinite-remainder, rational-rounding or integer-count flaw found in the assigned files.** This review reads the implementation and existing receipts; it does not rerun any cell, change precision, or independently reproduce the Arb computation. It is conditional on the separately audited exact source/divisor identity, analytic kernel identities, tail/consumer arguments and explicit external count theorem. It does not change Route B or authorize any RH export.

Reviewed: `arb_replay.py`, `ARB_m300.json`, `ARB_m3000.json`, `build_results.py`, and `GROWTH.csv`. The intermediate-grid table was checked for consistency with its displayed rational inputs and count formulas; this is not a new numerical replay of those cells.

## Source enclosure and signs

The 160-bit context is fixed before source evaluation. Integer/rational constants enter Arb directly; no source formula passes through a binary64 approximation. Direct Arb sin/cos of each integer phase encloses the exact trigonometric value; replacing a long interval recurrence by direct evaluation changes enclosure sharpness, not the analytic atom formula.

The digamma/trigamma identities are implemented consistently: q=Reψ(1/4+iw/2)−logπ; f=Imψ/(2w); the diagonal sum is Imψ/(4w)+Reψ′/8; at w=0 both required limits are ψ′(1/4)/4. The off-diagonal divided difference has numerator w_j² f_j−w_k² f_k and denominator w_j²−w_k², with matching signs. Arb special functions enclose the exact analytic functions; no mpmath asymptotic approximation or unbounded remainder has been substituted.

The pole vector matches the pinned physical basis normalization. The arithmetic sieve includes every prime power n<m with coefficient log p/sqrt(n); n=m is omitted because its literal overlap is zero. The stored B is the positive arithmetic R-sum, with diagonal2V−2S/(Lw) and off-diagonal negative divided difference. Thus the assembled source is precisely H+P−B. The mixed decomposition signs HP positive, HB negative, PB negative and the off-diagonal symmetry weight2 are correct. Summing a*a is a valid enclosure even for entries whose balls meet zero; it may widen lower bounds but cannot understate an upper bound for the Frobenius square.

## Infinite source and tail remainders

For the exponential kernel, the omitted r≥6 summand obeys

`a_r² exp(−a_r L)/[(a_r²+w_j²)(a_r²+w_k²)] ≤ exp(−a_r L)/a_r²`.

Bounding the latter by the geometric series beginning at a_R=12.5 gives the exact implemented etail. This omitted sum is nonnegative, so the Arb unit interval[0,1] times the positive envelope encloses it. Subtracting that entire enclosure in H has the correct sign. The common prefactor2d_jd_k/L is applied after the remainder is included.

For the whole-zero tail, the code retains the audited coefficient8 and positive expansions of I and J. With r=κ^−2, the remaining geometric mass after K=256 terms is exactly `r^K[(K+1)/(1−r)+r/(1−r)²]`. Every mode has x_j≤r. The bound using total mode weight2m+1, positive ell=log(T/(2π)), and(1+b) therefore encloses the omitted series. Independent[0,1] intervals can enlarge the result but cannot discard a positive remainder. The reviewed final source explicitly asserts ell>0; all frozen grid cutoffs already satisfy it, so this added domain guard requires no numerical rerun.

E=I+2ηlog(T)w(T)+ηJ agrees with the audited Stieltjes boundary-atom payment. The code checks the Rosser ratio is belowη=.55 and T.log()>1. On that domain its derivative with respect to log t has numerator .443(1−log log t)−1.588<0, so the point check extends to the required half-line. The separate gamma5 envelope is unchanged and checked against1/2.

## Rational rounding and interval serialization

`floor_cert` uses a binary64 midpoint only to nominate an integer. Its full-ball assertion x<n+1 is sufficient for the integer upper bound on N. For a trace lower gate the subsequently checked full-ball inequality tr>a validates the nominated rational independently; the Frobenius and tail upper rationals are likewise checked by F<q and E_exact<E. Therefore a midpoint too close to an integer would fail a gate rather than silently certify an incorrect bound. The helper is not a general-purpose two-sided certified floor, but its actual uses are safe.

`ceil_lower_cert` also treats the midpoint as a candidate only: it returns n only after the entire ball is strictly above n−1, otherwise checks the next weaker integer. This is a valid lower bound for an integer count. A fallback to None would stop the caller rather than fabricate a number.

At m300 the fixed rational gates are exactly895.9,5481,12.5,N_upper185. At larger m the generated rationals are outwardly checked. All score arithmetic uses these exact rationals and Arb sigma=log(m)+1/5. The stored Arb strings include explicit radii and are parsed back by `build_results.py`; displayed decimal rounding is represented by the ball radius rather than treated as an exact midpoint. Decimal fraction columns in GROWTH are presentation only: the authoritative rational columns and the P3/P4 comparisons use exact Python Fractions.

## Count ceilings and the integer refinement

N_upper=floor(Nreal) is safe because N is an integer and the code checks Nreal<N_upper+1. It does not require Nreal itself to be an integer or use a zero census. An inclusive N(T) upper bound also safely bounds the strict head count.

The recorded original lower counts are consistent:

| m | simple lower | distinct lower | refined simple lower |
|---:|---:|---:|---:|
|300|14|100|15|
|600|59|222|60|
|1000|126|392|127|
|2000|310|833|311|
|3000|506|1286|506|

The integer-refinement envelope `3s+4 floor((N_upper−s)/2)` is the correct largest permitted bad-block score at a fixed proposed simple count s. The loop certifies exclusion of every consecutive integer from0 until the first unexcluded candidate; it does not assume this parity-dependent envelope is monotone. Consequently using the length of the excluded prefix as the lower bound is valid. `assert ss>=s0` protects consistency with the original ceiling bound. No fraction was rounded up to meet the1/5 target: the original m3000 fraction is exactly506/2066>1/5.

## Metadata and scope

The immutable raw receipt label PENDING_PAPER_AUDIT_NO_RH_EXPORT describes the stage at which the receipts were generated. The final GATES file can separately record completed bounded audits; this difference does not alter any numerical assertion. The parent will include this implementation report in the final audit-file provenance. Hardcoded P1/P2 metadata in the result joiner is not a substitute for the individual interval gates and audit reports; those underlying checks are separately retained.

No mathematical counterexample was found in this bounded review, so the failure marker is not emitted. This implementation review does not upgrade the broader analytic claims beyond their explicit audited premises.
