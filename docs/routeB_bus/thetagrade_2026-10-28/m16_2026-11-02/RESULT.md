# F/X m=16, branch-A continuation

STATUS: DIAGNOSTIC_NEVER_A_PROOF

The handoff was read before computation. Results were assessed in its required order:

1. `entry_ctrl = 8.43e-81` at 80 dps (independent 100-dps replay: `3.57e-101`). PASS.
2. At i=1, `F_partial = [4.22739e-33, 4.22739e-33, 4.22739e-33]` at mode cutoffs 36, 56, 76. All four levels have stable displayed F partials. PASS at the emitted precision; no rigorous tail enclosure claimed.
3. `D_ext(i=1) = 9.47626e-5 < 1/4`. Branch A persists at m=16.

For i=1: lambda=4.73342e-32, a=-0.0394812, T=4.2269934e-33,
F=4.2273939e-33, X_closure=-4.00561e-37. The eigenvector sign fixes these signed values; D_ext is sign invariant.

X is calculated by closure X=T-F, not independently. This does not check NOESCAPE identity (4.8) independently. The G partials are not stable; no convergence claim is made for G or k(h_out,v) obtained from it. In particular, F stability is not silently transferred to G.

The completed run uses the existing shared-Gauss implementation `leakage_split_shared_gl.py`, with identical source formulas and unchanged `full_center_probe.matrix_K(16)` eigenproblem. Eight-panel GL96 at 80 dps and GL128 at 100 dps give identical emitted Z and all four level dictionaries. The larger number of window modes (M=76) is used only in the leakage sum, not the eigenproblem.

Commands (from docs/routeB_bus/thetagrade_2026-10-28):

```sh
UV_CACHE_DIR=/tmp/rh-uv-cache FX_GL_ORDER=96 uv run --with mpmath python3 leakage_split_shared_gl.py 80 60 16
UV_CACHE_DIR=/tmp/rh-uv-cache FX_GL_ORDER=128 uv run --with mpmath python3 leakage_split_shared_gl.py 100 60 16
```

The exact requested adaptive command `uv run --with mpmath python3 leakage_split_probe.py 80 60 16` was also launched. Its completion status is recorded separately in `execution_status.json`; it must not be inferred from the completed shared-Gauss outputs. Independent adaptive-integral spot checks are in `spotcheck.json` with replay code `spotcheck.py`.
