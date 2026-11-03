# Independent source/guard review of batch_mp.py

DIAGNOSTIC_NEVER_A_PROOF. Scope is the shared spectrum helper, not B again.

The reviewer did not author batch_mp.py, but previously authored the Q2
source builder. This is an independent review of the batch adapter and its
guards, not a second independent audit of that source builder.

The helper imports our reviewed Q2 source builder. Its first return value
is the physical-L2-normalized even cosine matrix, with N=m, constant mode
and phases matching C's native float carrier. DH has its actual conductor5
archimedean constant/kernel and all-n logarithmic-derivative recurrence;
it has no zeta pole. Coefficients are generated at requested MP precision
before their cache is installed. For the requested missingDH cells, every
matrix_cache field is null; therefore all new data use a fresh MP100 source
build at the actual requested GL160 order.

Guard limitations found and retained:

- dps is eigensolver precision. It does not upgrade inherited matrix-cache
  input precision. Consumers must retain source_metadata.origin.input_dps;
  the new missingDH cells avoid that issue by fresh builds.
- The generic helper's quadrature_status text is hardcodedGL128 even when
  --order160 is passed. Actual GL and fresh-source metadata record160.
  This worker corrects only its dedicated output text, without touching
  numerical values or another worker's shared helper.
- The roundoff_heuristic is a floating diagnostic, not a rigorous spectral
  error enclosure. It does not certify quadrature, inherited-cache precision
  or tiny eigenvalue positivity. C must test its actual lambda_r against all
  relevant input/roundoff guards, retaining unresolved cases.
- The enforced MP-to-float Frobenius comparison checks source/carrier
  consistency within C's diagnostic radius; it is not an interval bound.
- Filenames with requestedGL can be misleading for inherited caches. All
  missingDH jobs are fresh, so those filenames accurately describe our source.

No external code, spectral-zero positivity premise, eigenvalue clipping,
source sign promotion or proof claim is used. Saved full spectra allow all
base and EDGE r-index cells to share one native matrix result.
