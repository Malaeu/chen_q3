# Restore and replay

This packet is **DIAGNOSTIC_NEVER_A_PROOF**, separate from D0. The preferred HIGH spectra use native MPFR round-to-nearest arithmetic; source regressions and precision repeats are empirical. Rounded-polynomial root checks have a narrower scope, documented in `roots/`.

The lossless archive keeps the full vectors, root lists, assignments and large precision ledgers. Direct CSV digests and plots can be read without extraction. From this directory:

```bash
python3 unpack_data.py
python3 analyze.py --complete
python3 boundary_roots.py --all
python3 make_result.py
python3 review/audit_payload.py --complete
```

The first command verifies each archive part, the complete compressed stream and every restored member against SHA256. It rejects a differing pre-existing file. `ARCHIVE_REPLAY.json` records an independent extraction into a fresh scratch directory.

Python dependencies are `gmpy2`, `python-flint`, `mpmath`, `numpy`, `scipy` and `matplotlib`; for example, use `uv run --with gmpy2 --with python-flint --with mpmath --with numpy --with scipy --with matplotlib python3 SCRIPT.py ...`. The recorded producer scripts prepend the original optional `/workspace/conditioning_deps` installation directory; if absent, normal Python package lookup still works. No credential or network dependency is needed for numerical replay. Original absolute paths in raw provenance describe the run location; the audit resolves the restored vector basename within this packet when the original path is absent and verifies its exact stored SHA256.

For a new spectral run, use a **separate copy** of the packet to keep committed source receipts unchanged. Install a C compiler and MPFR/GMP development headers, then build:

```bash
cc -O3 spectra/loweig.c -lmpfr -lgmp -o spectra/loweig
python3 spectra/run.py --ms 16
python3 roots/batch.py --ms 16 --repeat --workers 1
```

`run.py` computes all three worlds and both parity blocks for each requested integer. The complete range is `--start 16 --stop 300`; it is substantially more expensive than reading the saved scalar diagnostics. `roots/batch.py` computes the even restricted ground and, when different, the actual global odd ground. Source zeros are used only for comparison after numerator roots are discovered. See `spectra/README.md`, `roots/METHOD.md` and `NORMALIZATION.md` for numerical conventions, precision/fallback gates and the distinction between polynomial, structural and source zeros.

Compiled executables and Python caches are omitted from Git. Their C/Python sources and exact producer snapshots remain available. Historical producer hashes, the two explicit terminal-LF aliases, and reviewed performance variants are retained rather than silently relabelled.
