# Ground-state spectral run: pre-run discriminator and budget

Frozen before scaling the grid on 2026-11-03. Target is literal finite CCM, L=log(m), N=m, m=16,...,300, all integers; worlds zeta, DH and planted pair. Both parity blocks are constructed from the same archimedean source and finite signed atom sums. No zero Gram replacement and no RH assumption are used.

Prediction: zeta has a positive even ground with an exponentially small isolation scale, so fixed double precision or fixed 120-decimal precision will eventually fail to distinguish the actual ground from the near-null cluster. The DH odd block can undercut the even block when its genuine negative direction enters this truncation. The planted world has a macroscopic negative direction whose even/odd comparison must be computed, not inferred from symmetry.

Primary discriminator: compare both lowest eigenvalues in each block and the two parity grounds, escalating source arithmetic and eigensolver precision. Resolve a unique ground only if the eigenvector (modulo sign), lambda0 and relevant isolation gaps converge and the error diagnostics are substantially smaller than each reported gap. A floating near-null cluster is a failure to resolve, never a selected ground.

Pilot grid: 16,24,40,80,160,300. Initial decimal working precision is selected above the expected exponential floor, with a second higher-precision complete source rebuild and eigensolve. Record elapsed source and solve costs. Scale to every integer only after the source shortcut is independently compared to literal quadrature and the pilot identifies a feasible method.

Budget: first benchmark bounded pilot computations and inspect runtime; use C-backed high-precision full eigensolves when feasible, otherwise a verified isolated-eigenspace refinement. Atomic per-cell outputs preserve completed work. If a cell remains unresolved it receives explicit failure metadata and no purported unique vector. A finite numerical run is empirical evidence, not a theorem or interval certificate for the original source functional.
