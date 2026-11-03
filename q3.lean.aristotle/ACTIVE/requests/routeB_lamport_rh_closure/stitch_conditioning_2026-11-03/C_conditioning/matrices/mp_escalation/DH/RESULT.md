# Missing DH full spectra: completed scalar-source escalation

DIAGNOSTIC_NEVER_A_PROOF. No B changes, interval certification or route promotion.

All65previously missing native DH full spectra are now supplied. Together
with40existing cached MP spectra, this covers **every integer m16..120**.
Every new matrix is freshly built at100decimal digits and GL160 on each
of8panels; all final eigenvalues use the original mpmath eigsy backend.
No approximate-ACB eigenvalue array was published. The source carrier is
exactly C's normalized even cosine carrier,N=m, not B's physical step space.

SPECTRUM_INDEX.json binds every new file's final SHA256. coverage.csv lists
the105m values and distinguishes new computations from reused metadata.
guard_summary.csv retains the positive/negative/unresolved counts against
an explicit MP roundoff heuristic. C must select its actual lambda_r from
the full sorted array and respect source/input precision; this packet does
not declare every tiny eigenvalue positive. The independent float-source
Frobenius comparisons all pass C's previously registered diagnostic radii;
maximum observed discrepancy is1.113e-12. Those radii and MP roundoff
heuristics are numerical controls, not interval enclosures.

Source/guard review is in REVIEW.md. Important adapter detail: the shared
helper's fixed GL128 prose was misleading for requestedGL160. Only this
worker's final output text was corrected; actualGL fields and source metadata
have always recorded160. All new jobs have null inherited matrix_cache,
so no80digit source was silently promoted by a100digit eigensolve.

## Execution and budget closeout

The primary phase preserved60complete new files throughm114. Its configured
RLIMIT_CPU600/630 did not terminate the process when observed; the controller
stopped it at697.73observedCPU seconds and recorded the real value. The
receipt does not falsely claim a600second measured completion.

The parent then authorized one bounded missing-only continuation. It computed
m115..118 in166.74CPU seconds, verified all60prior file hashes unchanged,
and stopped conservatively before119 after the m118cell cost spiked. The
remaining197CPU allocation was not silently exceeded.

A separately authorized missing119 attempt used the already benchmarked
ACB400 approximate eigensolver with a30second hard wall timer. It timed out
before a full spectrum was written; no values from that attempt were consumed.
That failure was a budget event, not a mathematical or precision obstruction.

The parent explicitly authorized a final119-only replay using the original
mpmath100/GL160 method under a separate120CPU watchdog. It completed in
24.36CPU seconds (23.80wall), with9.43CPU seconds in eigsy. This final
checkpoint closed the only remaining m. All earlier completed source files
were preserved. No further numerical replay is pending.

RUN_RECEIPT_primary.json, TAIL_RECEIPT.json, FINAL119_RECEIPT.json and
FINAL119_ORIGINAL_RECEIPT.json retain the actual phase outcomes and methods.
The failed30wall attempt's CPU time was not recorded; no invented aggregate
CPU total is reported. Final metadata strings and all numerical-file hashes
are frozen for the C integrator's final recursive lambda replay.

## Reproduction

The shared adapter is ../batch_mp.py and imports the reviewed first-party
Q2 source builder. Recompute a selected missing cell using the same native
matrix and output schema:

```
python ../batch_mp.py --ms 119 --worlds dh --dps 100 --order 160 --out /tmp/dh_mp_replay --label replay
python finalize.py
```

A fresh full bounded sweep can use run_missing.py; completed data produce a
read-only no-op. run_tail.py and final119_original.py preserve the historical
bounded recovery recipes. The optional failed finish119.py requires python-flint
and is not needed to reproduce any published spectrum. No source floor,
RH implication or rigorous positivity follows from these finite computations.
