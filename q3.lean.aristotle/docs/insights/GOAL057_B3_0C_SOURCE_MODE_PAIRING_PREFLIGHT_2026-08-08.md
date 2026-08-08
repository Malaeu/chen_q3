# Goal 057 B3.0C — source archimedean mode-pairing preflight

Status: `IN_PROGRESS / SOURCE_LOCKED / SCRATCH_LEAN_PASS / NOT_AUTHORIZED`

1. `D0_2_EXACT_WEIL_SESQUILINEAR_FORM.md:38-64,149,228-230` fixes the
   source convention: the Weil form is antilinear in its first argument, so
   the Fourier-side mode pairing must conjugate the `n` mode and leave the
   `r` mode linear.
2. The exact next public atom named by Proshka is
   `sourceArchimedeanModePairing_integrable`; it is a fixed `(i,n,r)`
   integrability theorem, not the source form, operator graph, or a uniform
   cofinal estimate.
3. The right `L²` factor is already production-proved by
   `sourceArchimedeanMultiplier_mul_fourier_logWindowZeroExtendedMode_memLp`.
4. The unweighted left Fourier mode must **not** be obtained by dividing by
   the source symbol, which may vanish.  It follows monotonically from the
   B3.0B1 envelope-weighted theorem because
   `1 ≤ vModeLogGrowthEnvelope t` for all `t`.
5. Conjugation preserves the left `MemLp 2` certificate by `MemLp.congr_norm`;
   this toolchain requires `open scoped ComplexConjugate` for the `conj`
   notation.
6. Mathlib's exact Hölder receiver is `MemLp.integrable_mul` in
   `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1066`; the official
   Hölder API is documented at
   `https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/Holder.html`.
7. `/tmp/Goal057B3_0C_Scratch.lean` compiles directly with one import;
   SHA-256 `b9982a75e5258b556474353ec5ad2a849b465f23d223d9564cfc78a68e173e5e`,
   2,251 bytes / 57 lines.
8. The source-audited proof shape is therefore
   `B3.0B1 -> unweighted L² -> conjugated L²` and
   `B3.0B3 -> exact-symbol-weighted L²`, followed by `L²×L² -> L¹`.
9. Still open after success: the full source Weil-form decomposition, prime
   and pole components, associated operator graph, form/operator domain,
   compression identity, continuum numerator, H4a1b, all ten coarse
   checkpoints, promotion, PX, and RH.

Recommended next action: one release review in the same living Proshka chat;
do not create the production Lean file before that verdict.

