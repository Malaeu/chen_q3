# Replay

DIAGNOSTIC_NEVER_A_PROOF. Use the repository at b785505e and the unchanged arithmetic source (origin 89e8c969). Python dependencies are numpy, gmpy2, scipy, mpmath; python-flint is needed for the independent ground-source check. Matplotlib is optional for the figure.

Set SECOND_BASE to the absolute arithmetic_coupling_2026-11-03 directory and SECOND_LOCAL to scratch storage. The scripts' workspace defaults record this run and may be overridden. Run:

1. `python source_moments.py --workers 2` (400-bit, GL192, eight panels; all 285 m).
2. `python source_moments_mp_pilots.py` and `python source_moments_validate.py` (same precision, GL256 pilots).
3. `python normalization_check.py` (independent m16 ground-source gate).
4. `python sigma_sharp.py`, `python measure.py`, `python additional_tables.py`.
5. `python package_report.py`, `python plot.py` are report assembly helpers; package_report.py uses the recorded local checkout path to create input receipts. Adjust that checkout path for another machine, without changing the pinned builders.
6. `python verify.py` checks the complete committed scalar packet, with no regeneration or network needed.

Use OPENBLAS_NUM_THREADS=1 to limit BLAS oversubscription. Dense arrays remain in scratch storage; hashes are recorded in SOURCE_MOMENTS.csv. Receipt fields with local absolute paths are provenance, not committed dependencies. Recompute SHA256SUMS only after intentionally regenerating artifacts.

The primary source A is independent of the chosen census cutoff T; its moments are reused for κ controls. The census tables are point datasets with their stated multiplicities, not newly certified root enumerations. All raw and unpaid finite scores remain diagnostic and are not finite lower bounds.
