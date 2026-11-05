# Task A instrument-fix preregistration

DIAG only. No RH claim or (7.4) claim. This rerun is explicitly authorized by
the owner and changes the instrument, not the mathematical source.

Base: rh_clean@2cd805e0abf59d21ab103410548e9b011e5ee7a5.
Reuse ../scripts/task_a.py primitives and exactly ../SOURCE_VERDICT.md,
Git blob2b5e02a0aa816da34c204f2a56a9033e6ac6b542, from source commit
62f782316d2ba4f83d27db82d0b64e1e8361cad2. Preserve previous results unchanged.

Before any numerical run, fix:

- t=0,0.5,1,1.5,2; floor(exp(t+12)) prime-power cutoff.
- mpmath dps50, independently repeated at70.
- Both zeta and zeta plus the quartet a=1/3,gamma=7.
- Same H quadrature, j, c_*, C and complex F squares as the original script.
- Absolute gate |arithmetic-zero|<=1e-15.
- Plant c_*+1e-10, changing arithmetic by -1e-10 C(t), in both worlds.
- Baseline must PASS and plant must FAIL for every t at both precisions;
  otherwise report INSTRUMENT_FAILURE, retaining all rows without retuning.
- Bound the omitted arithmetic tail independently using Lambda(n)<=log n,
  an integral comparison and a Gaussian polynomial envelope; require <1e-18.
- Retain the original zero-side cutoff gamma<=60 and its analytic tail bound.

Prediction from the formula, before computation: baseline PASS everywhere,
plant FAIL everywhere; cutoff at Gaussian distance12 should give an omitted
arithmetic tail below1e-18. The observed residual may remain larger than the
true zeta response; the goal is finite-precision normalization, not resolving
that response relatively or inferring signs/growth.

Proposed analytic majorant: b=log(floor(exp(t+12)))-t, D=b-1/2-9/b.
For b>11.99, |C(v)|<=2 v^8 exp(-v^2/2)/sqrt(2pi), v>=b.
The omitted tail is bounded by
4 exp(t/2)(b+t)b^8 exp(b/2-b^2/2)/(sqrt(2pi)D).
Verify its monotonicity hypotheses and round its evaluated value upward.

Delivery: commit this file first and retain its commit in a Git bundle; amend
that local commit after the run, producing one final commit and ordinary push.
No source, old result, Task B/C, or route-state edits.
