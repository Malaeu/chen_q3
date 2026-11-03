# Fresh literal even matrices, m121–300

DIAGNOSTIC_NEVER_A_PROOF. All **540 requested world/m cells** are complete: ζ, plant, DH for every integer m121–300. Float64 matrices and sorted spectra are in `../matrices/`; per-cell JSON contains MP shifted LDL counts and numerical guards. Six additional m80/120 regression cells are retained separately by their m labels.

All shifted negative-count ranges are ordered. Every ζ cell has guarded lower count0; every plant cell has guarded lower count1. This does not resolve the many tiny modes nearzero. Atm300 the guarded ranges are ζ[0,106], plant[1,105], DH[7,41]. Raw threshold-zero LDL counts are explicitly flagged as uncertified and must not be used as definite inertia.

Source builds use400bit MPFR, GL192 with8panels, and direct coefficient recurrence. GL192/256 pilots at80,120,121,300 differ by less1.2e−115 per entry. Independent saved-source regression atDH80/DH120/ζ120 differs by less4.7e−116. The fixed1e−70 shifted guard is empirical, not an interval error bound.

Initial checkpoints use Python MP LDL; later checkpoints use the parent-provided native MPFR helper, validated on all3worlds×3shifts atm121. Native helper does not report minimum nonzero pivots, and its metadata explicitly flags this limitation. Both backends trap exact zero pivots. No full MP eigensystems were built.

`SUMMARY.csv`, `COMPLETION.json`, `REGRESSION_MP.json`, `PROVENANCE.json`, and `METHOD.md` record scope and limitations. `SHA256SUMS` covers scripts, metadata, and matrices. No remote writes or route-state changes.
