# Reproduce the bounded v2 artifact

Requires a checkout containing arithmetic_coupling_2026-11-03 at the pinned
base, Python, numpy/scipy/mpmath/gmpy2/cvxpy with SCS and Clarabel, and gcc plus
GMP/MPFR4 for the unchanged native frame helper. BUILD_INFO.json records actual
versions. No paid calls or external mathematical review transport are required.

Set STIFFNESS_BASE to that packet and STIFFNESS_LOCAL to an owned scratch
folder. Set QUIET_DEPS if its pinned builder needs a nonstandard dependency
location; set PYTHONPATH as needed. All scripts are run in this directory.

    python regenerate.py
    python binary.py
    python finalize_binary.py
    python mp_prices.py prices 16 24 40
    python p5.py float 16 24 40 80 120 200 248 300
    python p5.py mp 16 24 40
    python p5_summarize.py
    python p5_s4_confirm.py
    python check_frames.py
    python reference_controls.py
    python aggregate_v2.py
    python plot_v2.py
    python verify.py

The first step verifies pinned builder hashes, restores existing scalar/vector
receipts and invokes the unchanged fixed-scope builders. It never surveys
16..300 wholesale. MP prices prepares three local caches at the unchanged
precision and reuses them. Dense arrays/dual matrices/caches are NOT publication
artifacts; only their hashes and numerical receipts are retained. Reference
controls do not invent zeros for double2.

The published binary archive omits dense Y but retains singular values,
kernel vectors, candidate vectors, prices, scalar residuals and a local-array
hash. Inspect without numerical rerun using restore_binary.py, which verifies
all member/part hashes and refuses conflicting files. The normal verify.py
checks archive bytes directly and does not need dense arrays or local deps
other than mpmath. SHA256SUMS identifies the delivered files; regenerated
compressed bytes may vary with zlib/Python. Per-member hashes identify receipts.
A replay can produce rotated near-degenerate eigenspaces or different conic
candidates. It must retain dimensions, gates, residuals and unresolved labels.
Do not demand byte-identical NPZ frames or invent a source error certificate.
