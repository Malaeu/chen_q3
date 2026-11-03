# Prepublication static preflight

PASS for the reviewed code paths, with the final frozen-data audit still
pending. This preflight ran no eigensolve, root search, source build or
numerical regeneration. Exact reviewed file hashes and issue dispositions
are in prepublication_issues.json. Root-owned files were read only.

The review scripts now resolve a missing original absolute vector path by
its basename within this packet's spectra/vectors directory. They retain
the exact stored SHA check. Existing original paths with different bytes
are not silently bypassed. The source receipt resolver accepts exact
current/archived producer bytes and only the two explicit, byte-verified
terminal-LF aliases in SOURCE_BYTE_NORMALIZATION.json.

Three integration issues found during this preflight were repaired by the
root owner and re-read: missing actual LOW/HIGH replay no longer qualifies
as zero error, complete integration rejects duplicate root/cutoff keys,
and every archived raw member's current size/SHA is rechecked before it is
omitted from direct Git. The complete replay gate applies to the primary,
Omega and 0.8Omega rows. Archive unpacking checks parts, combined compressed
bytes, member sizes/hashes, duplicate members, and safe relative paths;
existing differing files are rejected. Reproduction instructions restore
raw data before analysis and retain exact producer/source history.

LOW shifted-refinement records preserve null LOW lambda1/vector1/residual1
and null second-pair replay entries, with an explicitly empirical HIGH-based
Weyl range. Native fallback records a computed LOW pair and its rejection
reason. Preferred HIGH pairs, signed-second-level flags, actual full-ground
parity and both isolation gaps remain distinct. Final review will verify
these per-cell fields and the signed-second flags against their error
diagnostics, plus all 855 world/window cells and required current-SHA roots.

The authoritative roots/PRECISION_SCOPE_ERRATUM.md is correct. At fixed L,
the coefficient perturbation factor is sqrt(sinh(|Im z|L)/|Im z|), with
limit sqrt(L) only on the real axis. It does not include carrier changes,
exact-source eigenvector error or a rigorous root-location enclosure.
Observed all-real positive-height strip roots and pure-imaginary axis roots
are counted separately. The corrected inventory binds the frozen raw
diagnostics rather than relabeling their old off-axis expression.

The earlier argument-principle check remains a partial sampled numerical
check with disclosed coarse-grid and tiny-axis limitations. It is not a
source or contour certificate. Separate sign-bracket completeness applies
only to the frozen supplied decimal-vector polynomial.

make_result.py still contains fixed pilot values and transition examples.
Their agreement with final tables, complete replay coverage, strict SHA
closure, archive restoration and final inventory remain final-freeze checks.
No publication or mathematical-status promotion is authorized by this note.
