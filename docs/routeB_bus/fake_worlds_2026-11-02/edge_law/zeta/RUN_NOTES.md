# Run notes

The initial m160120dps run completed its eigensolve but failed while constructing a reporting field: its QR reconstruction residual rounded to zero at the working precision, and the diagnostic divided by zero. The other three active jobs were stopped and all four restarted. No numerical result from those unsuccessful runs was published, and the preregistered prediction was unchanged.

The reporting guard was fixed, QR residuals are evaluated with30 extra digits, and local matrix checkpoints were added before the restart. A raw-eigenpair checkpoint was subsequently added to the replay code immediately after the eigensolve/normalization, before endpoint and other reporting diagnostics. The already-running restarted processes had loaded the earlier guarded version; they were not restarted again solely to install that additional checkpoint.

A zero reconstruction residual at working precision is not treated as a conditioning proof. The table retains the extra-precision residual, a triangular-inverse singular-value lower bound, and the explicit higher-precision validation.

After the completed calculations, the replay-only matrix cache key was additionally bound to the matrix-builder and Mangoldt-helper source hashes, preventing stale cache reuse after future source changes. This does not change the computed matrices. The completed cells bind their actual source helper hashes; no claim is made that the final replay-script hash equals the earlier in-memory script version.
