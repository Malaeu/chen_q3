# MP scalar-spectrum escalation for C

DIAGNOSTIC_NEVER_A_PROOF. Full-spectrum coverage is complete forζ and the planted world, every integer m16..120:210 receipts. The original floating source matrices, capacities, projectors, δ and Schur computations are unchanged. DH escalation is a separate worker partition.

`COVERAGE.json` and `RECEIPT_HASHES.csv` are the final coverage/hash ledger. Each spectrum supplies all three cutoff choices and their edge variants by index, so no new eigenproblem is needed for a different q or r.

## Pilot and method validation

The independentζm65 pilot used the same literal even N=m source at100 decimal working digits, first GL128 then GL160. Build/eigen CPU times were4.68/1.12s and6.62/2.27s. Full matrix change was5.96875e−99 in Frobenius norm, and maximum eigenvalue change6.99982e−100. At the C indices:

|Cut|q|r|λ_r|
|---|---:|---:|---:|
|primary quarter|35|31|2.67195922764391299046e−10|
|secondary half|41|25|2.05457521103004936156e−24|
|κ1|28|38|2.79696485725554702545|

The relative changes at these indices were≈7.5e−93,1.3e−76,7.2e−101. This is a numerical refinement check, not an interval bound.

A bounded alternative-solver benchmark compared `flint.acb_mat.eig(algorithm="approx")`,400 bits, against existing independent MP references. At m65 the full-spectrum discrepancy was7.78322e−100; at m120 it was4.95692e−119. Largest imaginary midpoint was below7.7e−241. CPU times were1.19s and4.19s. The method is explicitly **approximate**, without interval eigenvalue bounds; the use of the Arb/ACB library does not turn it into a certificate.

## Coverage and the deliberate method switch

|Receipt method|Cells|Precision/scope|
|---|---:|---|
|mpmath eigsy|167|100-digit working precision; geometric-source matrix|
|reused MP spectrum|30|Original source provenance retained; values serialized to100 digits|
|ACB approximate eig|13|400-bit approximate solver on100-digit source matrices; no eigenvalue enclosures|

The final seven m values114..120 use the400-bit approximate solver for new spectra. Theζm120 spectrum is reused from its existing MP source. The underlying arithmetic matrix construction did not change. Existing cached MP matrices/eigenvalues were reused where available; their original precision and quadrature metadata remain in `source_metadata`. A requested GL value in the filename applies to a **fresh** source build, not retroactively to an inherited cache.

Priority cells m54,55,56,64,65,66,76,77,78,79 used requested fresh GL160; other fresh builds used GL128. The initial priority receipts had a generic GL128 phrase in `quadrature_status`; finalization corrected that metadata to the actual requested GL and inherited-cache scope, without changing any numbers. Consumers must use the final receipt hashes.

Coefficient arrays were computed once per process at100 digits. All three process-level arrays are byte-identical, SHA256`45917497d1013d79745a9c5970baf0797ec2f1e4af88466472cfcda66ac55c73`. The planted update is the same raw physical E-row update as the matrix supplier, with no extra√2.

## Bounded-run costs

|Phase|Cells|Recorded CPU|Wall|
|---|---:|---:|---:|
|priorityζ/plant|20|50.13s build+eig|51.47s|
|initial remaining sweep|176|597.16s|602.70s|
|authorized final tail|14|53.83s|54.15s|

The initial sweep's580CPU-second stop was checked only after finishing an m. Its final cell caused a17.16s granularity overshoot; it stopped after m113 and marked its completion record false. The parent then authorized one additional90CPU-second sweep **only** for the exact14 missing cells. That final sweep completed in53.83CPU seconds. No completed spectra were rerun for the tail. Total recorded phase CPU is701.12s; the separate pilot and alternative-solver validations add≈20.08s. No hidden unbounded scan or additional experiment followed closeout.

## Precision limits retained

- Every MP source matrix matches its original saved float matrix within the conservative diagnostic guard; maximum discrepancy/guard is0.011452. This coarse check does not certify tiny eigenvalues.
-100 working digits are not a claim of100 correct digits. Source quadrature was independently refined at m65; a paired high-end source-quadrature refinement was planned but was **not run** under the final bounded/no-rerun instruction. The m120 alternative-solver comparison checks the eigensolver on a cached source matrix, not its source quadrature.
- The planted update and matrix/eigenvalue scalar data have upgraded arithmetic precision. The zero/root inputs used to build E and their accuracy have **not** been upgraded by this bundle; the main C ledger retains their own provenance.
- δ, E, capacity, Schur and projector computations retain their separate original precision. A new100-digit numerator does not make λ_r/δ a fully-MP ratio or a certified gap. A δ comparable with its source-matrix guard remains unresolved.
- Full spectra may contain tiny signed values below their numerical floor. They are retained, not clipped, and are not assertions about the true ground-state sign. The supplied `roundoff_heuristic` is a guard, not an interval proof.
- Nothing here certifies RH, global positivity, or a route-state promotion.

The final receipts are immutable after this closeout. Numerical values, primary source hashes and measured timings were preserved during metadata finalization. The caller's final C integration should refresh provenance from `RECEIPT_HASHES.csv`.
