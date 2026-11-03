# Reproduction

Dependencies: Python, NumPy, SciPy, mpmath; gcc, GMP and MPFR4 shared libraries
for the byte-pinned native frame helper. No gmpy2 dependency is required here.

    python restore_data.py
    python run.py --world zeta             # requested30 m, three c
    python run.py --world dh plant --m 310 450 600
    python run.py --world zeta dh plant --m 600 --bits 1024
    python controls.py
    python source_check.py
    python annotate_scope.py
    python finish.py
    python verify.py

run.py defaults to the restored inputs/ directory. GAUSSIAN_INPUTS can override
it. Existing cells are reused; remove owned cell outputs for a fresh numerical
run. finish.py expects exactly the reported36 base cells, plus three precision
repeats, and packages every raw sector receipt and exact input bytes losslessly.
Additional exploratory cells should be kept in a separate directory.
Matplotlib is optional for reproducing the published plot. Executables, caches
and dense matrices are excluded; the archived scalars and complete sectors are
sufficient to audit reported counts and bounds. Hashes verify actual committed
bytes; compression bytes can vary across Python/zlib versions when regenerated.
