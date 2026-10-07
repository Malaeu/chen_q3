# External ZF78: bounded textual dependency inspection

Pinned OpenAI commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, inspected2026-10-07. mobius_source_audit performed the bounded read-only trace; root reread the wrapper, unconditional assembly, certified-existence and zero-supremum sources. This is NOT a fresh Lean build, comparator pass, semantic audit of the Hecke definitions, or transitive axiom closure.

Nonvanishing.lean29–31 forwards the correctly scoped zeta statement to ProbeFinalAssemblyUnconditional.zeta_nonzero. FinalAssemblyUnconditional.lean43–44 applies zeta_of_certified to detector_certified_bands, constructed at15–34 from terminal_certificate and fixed parameter inequalities. CertifiedExistence.lean40–48 obtains the terminal band through certified_bands19–38; the induction's analytic step actual_successor and its ancestry remain unaudited here. Conditional internal beta inequalities are hypotheses of intermediate lemmas and must be supplied by the assembly, not silently assumed globally.

Hecke/ZeroSupremum.lean10–16 defines beta as the supremum of actual Hecke zero real parts together with a1/2 sentinel. Its LFunction_ne_zero_of_beta_lt48–53 follows directly from that definition and the proved upper-bound machinery. This is not itself the7/8 conclusion. The input Hecke LFunction/Character definitions, base-change semantics and probe contradiction remain crucial unaudited dependencies.

The bounded source scan found no explicit sorry/admit/axiom or assumed RH/nonvanishing conclusion in the inspected path. Absence of these tokens in selected files does not establish absence in the import closure, successful elaboration, or correctness of the analytic argument. External ZF78 remains UNVERIFIED and every direct Q3 transfer remains conditional.

Exact root-reread file hashes:
- Nonvanishing.lean: d98c4a7e074469b429890e1c21b8cc76c410026525a776895293cdc0f9e6ae89
- Detector/FinalAssemblyUnconditional.lean: 0f52159a2929e7b20646f8394589d25a1a637c2f78746ad9d1447871577af615
- Energy/CertifiedExistence.lean: 2d48b75fdd14ba8eabb428f79f98e0a6e532c28083075bacf16e1d57f020d7a9
- Hecke/ZeroSupremum.lean: 3b3ca749fb669e5a278a5d956a61eec73bab919e0369f7d46d2abae2e0f0011e

## Linux handoff received after this calculation

Linux commit9a0f8507, integrated through883a1fa8, supplies COMPARATOR_VERIFICATION.md reporting successful default-kernel Comparator validation of the exact zeta7/8 challenge with the three permitted axioms. It supersedes the earlier statement-inspection-only status, subject to that report's explicit trust boundary. Mac has read the committed report but has not accessed its Linux-local raw log or rerun the build. Dirichlet/Hecke/Siegel challenges remain outside that reported verification. Historical request/response bytes and their conditional labels are preserved. This changes the reported external-zeta verification status, not the still-open signed descent or RH.
