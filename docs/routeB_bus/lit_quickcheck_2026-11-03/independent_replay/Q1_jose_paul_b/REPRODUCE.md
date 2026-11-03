From this directory, with python-flint0.9.0 and mpmath1.3.0 available:

```
python our_mp.py --N 16 --dps 90 --order 80
python our_mp.py --N 32 --dps 130 --order 128
python our_mp.py --N 32 --dps 160 --order 160
python independent_vector.py 100 64 1.1147
python independent_vector.py 130 80 1.1147
python independent_vector.py 130 80 1.114
python -I isolated_runner.py weil_certificate/cert_weil.py 4/5 200 200 0
python -I isolated_runner.py weil_certificate/cert_weil.py 4/5 200 200 1
python -I isolated_runner.py weil_certificate/cert_weil.py 31/32 600 460 0
python -I isolated_runner.py weil_certificate/cert_weil.py 31/32 600 460 1
python -I isolated_runner.py semilocal/poly_upper.py 2 11147/10000 61 1
python summarize.py
```

The isolated runner defaults to the included reviewed external_source snapshot. Q1_EXTERNAL_ROOT selects another fresh pinned snapshot. Q1_TRUSTED_DEPS selects a trusted installed dependency directory; set it empty to rely on standard installed packages. The session used /workspace/python_deps for python-flint and a separately materialized empty snapshot at /workspace/q1_external_empty. Verify Git blob hashes in SOURCES.json before external execution. Do not copy untrusted .pkl files into the snapshot; poly_upper creates its own rational-polynomial cache.

External runtime depends heavily on CPU; the two large full certificates use460 modes and12 subprocesses each. Small full runs were46/116s in this session. Large quadrature stages took388/354s while concurrent; total large runs500/498s. Lower P2/P3/P5 continuum certificates were not rerun here. No pip command or network access is required by these scripts once dependencies and the pinned snapshot are present.
