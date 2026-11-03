# Q3 — edge, Hadamard, kink and tail crosswalk

DIAGNOSTIC_NEVER_A_PROOF. Sources are reachable and retained; mathematical
proofs in them are not independently verified in this literature preflight.

**Verdicts against the requested saved CCM diagnostics:**

| Law | Verdict | Reason |
|---|---|---|
|Edge trace|DIFFERENT_OBJECT|Their continuum traceA is a logarithmically renormalized limit; our finite Fourier endpointf(b) is an ordinary nonzero boundary value.|
|Hadamard|DIFFERENT_OBJECT|Their derivative is for a sector-simple continuum eigenvalue and traceA. Our saved values use finite carriers or separately unresolved resolution limits. The formal half/full-width crosswalk adds a factor1/2.|
|Kink/echo|DIFFERENT_OBJECT|Their object is an eigenfunction's interior logarithmic singularity; ours is a derivative jump of a fixed-history Schur predictor as its targettime changes. Both involve prime shifts but are not the same functional.|
|Sharp zero tail|DIFFERENT_OBJECT|Their scale is A²/T; our fixed-carrier endpoint-jump scale is |f(b)|²*logT/T. ReplacingA by the ordinary endpoint is invalid.|
|Smoothed second-order tail|DIFFERENT_OBJECT|Their source needs continuum traces, a smoothingmeasure and sector simplicity; none is measured by our rawR table.|

The underlying full quadratic forms have matching normalization for pole
weight1 and full support lengthell=2L. Thus these verdicts do not mean
that the underlying forms differ; they distinguish the actual objects to
which the formulas apply. No constant multiplier alone converts a finite
endpointjump into the renormalized traceA.

`our_cells_comparison.csv` preserves the requested zeta m160/200/240 and
DH matched/native values from the committed edge-law table. For zeta,
R=3.919361712,4.525479493,4.143167889. The source explicitly warns that
smalltraceA can postpone its asymptotic regime. None of these cells supplies
an independently resolved continuumA, and every finite cosine profile with
nonzero endpoint has sqrt(log(1/r))*f(b-r) diverging as r↓0 instead of
approaching that finite trace. Therefore the new formula cannot be honestly
evaluated on these vectors as a theorem test. DH has a different arch/gamma
source and is not covered by the paper's zeta statement.

P5 (prior.5, sameedge scale up to constant) **fails as an identification of
these objects**. This is not a counterexample to the external asymptotic law.
No field or eigenvalue was recomputed from the foreign code. Exact formulas,
assumptions, pages and caveats are in EXTRACTION.md. The stronger-source
question is retained as unverified, not promoted by its literature presence.
