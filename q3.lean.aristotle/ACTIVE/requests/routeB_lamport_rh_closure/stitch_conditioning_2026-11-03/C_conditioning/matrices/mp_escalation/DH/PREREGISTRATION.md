# Missing DH native spectra escalation

DIAGNOSTIC_NEVER_A_PROOF. No B edits; no route-state change.

Scope: nativeevenN=m for every integer16<=m<=120 whose matrix metadata lacks
an existing fullMP spectrum; also skip already completed dedicated files.
40existing values (20..55,60,80,100,120) are reused by the C integrator,
not recomputed. Missing65values are requested in ascending order at100digits,
Gauss-Legendre160 per each of8panels, using the reviewed source helper.
All missing matrix_cache fields are null: these jobs build fresh source100
matrices, so an older cache does not silently cap precision or quadrature.

Prediction(prior.99): freshMP source matrices agree with their independent
float prototypes within the already registered diagnostic Frobenius radii.
The helper enforces this before saving a spectrum. A positive tiny lambda
is not accepted merely because float eigensolvers rounded it positive.
Full spectra and explicit MP roundoff heuristics are supplied for C's
actual r-index; unresolved source/input precision is retained as unresolved.

Budget:600CPU seconds for this worker, hard630seconds. Every completed
spectrum is checkpointed independently. If budget expires, record the
unfinished m list without relabelling missing values as positive. No partial
current-cell result is consumed. Source coefficient recurrence retains every
integer coefficient of-DH'/DH, including non-prime powers, correct conductor5
gamma term and no pole. This is finite diagnostic arithmetic, not Arb.
