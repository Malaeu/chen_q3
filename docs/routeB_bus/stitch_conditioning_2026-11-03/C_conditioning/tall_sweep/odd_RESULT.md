# Odd DH half-cutoff capacity upgrade

DIAGNOSTIC_NEVER_A_PROOF. All20 assigned odd cells m81,83,...119 completed. This is a fixed-decimal input-matrix computation, not a source positivity certificate.

Process CPU:166.825652057s, below the strict300s limit. No source eigenproblem or root rerooting was performed. Original A/E/J/Schur definitions and source files were retained. Only the assigned base c_half singular-value/weak-vector receipt and corresponding cell fields were updated.

Each cell used200 and240 decimal arithmetic digits on the same frozen approximately80-digit DH zero table. Both smaller-Gram inverse iterations had relative residual and final change<1e-30, and the helper explicitly required relative200/240 agreement<1e-20 before setting RESOLVED_FIXED_DECIMAL_MATRIX or updating the main cell.

Independent receipt postvalidation checked all20 outcomes, dimensions, equal row counts at both precisions, both convergence gates, cross-precision agreement, every weak-left coordinate/mass list, normalized total mass, and consistency between squared coordinates and stored masses. All passed. Maximum observed200/240 difference was4.55077e-114; maximum240-digit relative residual was9.21171e-31; at most5 inverse iterations were needed.

The endpointσ119 is approximately8.61615122016665e-66. Full160-digit stored values are arithmetic output for the frozen table; they are not160-digit claims about the true DH zeros. Root errors were not enclosed or propagated. Precision refinement of the arithmetic does not improve the input root accuracy.

Full weak-left coordinates, squared masses and real/imag row labels are stored at both precisions. Using the stated best-adjacent-pair mass≥1/2 criterion,1 of these20 vectors is localized (m=85), while19 are diffuse. No pair localization is invented for the diffuse cases.

`odd_receipts.csv` contains all final σ receipt hashes and compact statistics; SHA256=7705a8d72382873cb51cc80aca4eeb8bb084616c9f4f73ebd312d6bc27d338bf. `odd_source_hashes.json` pins the shared helper, core, physical Fourier-row supplier and frozen zero table. Their modification timestamps precede this odd run. `odd_POSTVALIDATION.json` records the independent checks. Main cell hashes may subsequently change when the C owner performs the separate finalλ/provenance integration; the σ receipt hashes are final.

No RH/global(P) claim or route-state change follows.
