# Optional performance-probe timer qualification

The original `shifted_low_probe.json` and `shifted_low_probe_m300.json` retain their original bytes and timer labels. Their field `source_CPU` is actually `meta.seconds`, a **wall-clock source-build duration**, not CPU time. The corresponding original probe scripts use the same legacy label. Do not subtract that field from CPU totals.

The separately instrumented `shifted_low_timing_m300.json` records actual source-build CPU time and computes the LOW-phase comparison from like CPU timers. The Fourier checks added after the original m300 timer are included only in the explicitly named later total fields. These optional benchmarks change neither HIGH source matrices nor preferred ordered eigenpairs. All reported speed ratios are finite performance probes, with separate quality gates; they supply no mathematical bound.
