# Method and replay

DIAG only; CHALLENGER / NOT_RH. No matrices, eigensystems, positive ℚ Frobenius or cofinal floor are constructed.

## Inputs and pre-registration

The verdict is pinned to Git blob7cf72ea5ae3f3370eee05b9cc688887e10c37852 at inboxf96a9072071c13011cc0fb4a6408e2214ed64181. Census and saved address data are pinned to rh_clean34af3956b5bb33620695a579e871aed909eacbe8. INPUTS.json records Git blobs, SHA256 and actual byte sizes for every consumed input. The analytic-source file is a pin-only reference and is not imported or run.

The large saved CSV was read by its Git blob after the contents wrapper returned no inline data. The locally materialized bytes were checked against blob364281a907e0da23aafeab6d442407ba68c2a01a. No events were reconstructed from a fresh source calculation. The matching local census was likewise checked against35396541cbc976d0dc8a1c76bf45802c8602bb84 before use.

PREDICTIONS.md contains the exact registered threshold line and paragraph from the verdict and independent predictions C1–C4. The immutable registration object precedes all numerical runs. It is not a second branch update; final delivery adds one scoped commit to rh_clean. Upstream registration/design hashes are declared IDs copied from the pinned YAML, not independently reconstructed preimages.

## Independent source calculation

Write H(s)=ζ(s,1/5)+τζ(s,2/5)−τζ(s,3/5)−ζ(s,4/5). independent.py uses analytic Hurwitz derivatives to evaluate H′/H−log5, independently of the appendix's mp.diff(dh,s). Newton refinement uses H and H′ starting from the numerical census. The completion is evaluated through exp(s log(5/π)/2+logGamma((s+1)/2)−slog5)H(s). This retains the DH odd Gamma and conductor5 with no ζ pole.

M_D=i[log(5/π)/2+ψ((s+1)/2)/2+H′/H−log5], s=1/2−iz. The fullζcontrol uses i[1/s+1/(s−1)−logπ/2+ψ(s/2)/2+ζ′(s)/ζ(s)] with mpmathζ and its derivative, not an Euler truncation. The curve is M_E=log3 tan(log3 z). The plant is M_Xi−Σ_v1/(z−v) over v=w,−w,conj(w),−conj(w), w=7+i/3.

For each source, S=(M−i)/(M+i) is evaluated directly and compared with the exact alternative defect−4Im(M)/|M+i|². All requested points are in the upper half-plane because ε is smaller than the positive displacement. The positive address corresponds to the conjugate s-plane zero, as documented in FORMULA_REVIEW.md. No assumption that critical-line roots are complete is made.

## Verbatim comparator and gates

appendix_a.py is the exact extracted executable including the final newline specified by the verdict's extractor. APPENDIX_REPLAY.json is an unmodified copy of that executable's raw output, containing run time. APPENDIX_REPLAY.md documents hashes, environment and corrected execution order. The prematurely started first execution is unused local provenance, not a published comparison record or evidence used for choosing the independent formulas.

compare_replays.py enforces the original fixed inequalities at45/70dps and eps0.001/0.0001 on both producers. The common mathematical comparison uses the preregistered1e−29scaled tolerance, appropriate for the appendix's32significant-digit output. Run time and algorithm-dependent residual/roundoff diagnostics are not required to match bitwise; the defined error gates are enforced separately. Root residuals are descriptive, not interval root certificates or a new acceptance threshold. Appendix A does not itself assert these gates and does not serialize ζ/curve controls at plant points; the independent program explicitly covers both.

## Saved-screen matching

address_saved.py reads only the saved event CSV, saved SUMMARY and numerical census. At each requested m it computes j0=nearest integer toγlogm/(2π), retains only valid j0±1neighbors and looks up those tuples in the frozen event dictionary. No tie occurs; using the refined/full censusγ gives the same j0. Negative diagonal/minor flags and margins are copied exactly for hits. A missing row means NO_SAVED_EVENT, with no invented nonnegative value. Integer-neighbor selection is reported separately from continuous grid distance, and target distances are retained.

## Replay commands

With mpmath1.3.0 and an existing checkout containing the pinned commits, set CCM_REPO to that checkout and run:

```bash
python prepare_inputs.py
python independent.py
python appendix_a.py
# The unmodified appendix creates diag_results.json beside itself.
cp diag_results.json APPENDIX_REPLAY.json
python compare_replays.py
python address_saved.py
python summarize.py
python verify.py
```

The supplied published raw receipt remains the actual execution record; a new replay naturally changes elapsed time and its file hash. Preserve the original artifact bundle when verifying SHA256SUMS, or deliberately regenerate a separate manifest after a fresh replay. The independent and appendix implementations share mpmath; no independent backend, interval root inclusion or formal proof is claimed. No result here supplies a positive Frobenius for ℚ, a cofinal floor, a quantitative finite-m threshold law, or RH.
