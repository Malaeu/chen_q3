# Literal even source matrices for separator trend

DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH.

Thirty m values310,320,…,600 and three worlds ζ, plant, DH; N=m, L=logm. The source builder is copied from the previously regressed zero_extension engine. It retains400bit MPFR/MPC arithmetic, the literal even cosine source, finite prime/Dirichlet coefficient recurrence, analytic archimedean tail, ζ pole only, and plant addition4Re(e(w)e(w)^T), w=2π/log2+i/4. No source eigensystem is built at MP precision.

Main quadrature: GL256 per panel with8panels. Independent paired GL256/320 pilots at m310 and600 differ by less1.4e−115 per matrix entry. These are empirical checks, not interval error bounds. Fresh m300 GL256 source matrices regress to saved zero_extension float matrices entry-for-entry.

Float64 symmetric eigenvalues are sorted. The numerical radius is64 eps (m+1) max(1,spectral radius). `negative_count_range` is [number below−radius, number below+radius]. Its lower endpoint is supplied only for guarded candidate seeding in the downstream trend scan. It is NOT new MP inertia, a rigorous negative count, or an interval enclosure. All modes inside the radius remain unresolved. No shifted LDL is run for this trend-only task.

Each `../matrices/{world}_m{m}.npz` contains A,eigenvalues,lambda_,m,numeric_radius. JSON records contain N,bits,quadrature,radius,heuristic count range, and timing. Source tag1d3818c is the requested provenance reference; this derivative engine adds no change to the literal operator. No route-state export or remote write is performed.

Run `PYTHONPATH=/workspace/conditioning_deps OPENBLAS_NUM_THREADS=1 python trend.py --pilot`, then `python trend.py` with the same environment. Bulk uses two workers. `source.py` retains the old unused LDL functions, but trend.py never calls them.
