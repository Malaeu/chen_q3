# PDF Build Sanity Checklist

Quick pre-build checklist to catch regressions before compiling.

## Critical Constants
- [ ] `c^* = 0.898624` defined in `appendix/notation.tex`
- [ ] `YES-cap = 1/25 = 0.04` defined in `appendix/notation.tex`
- [ ] Both appear in `sections/A3/param_tables.tex` global constants section

## Monotonicity Statements
- [ ] `A3_bridge.tex` Theorem A3-gap: `c_0(K)` is **non-decreasing**
- [ ] `A3_bridge.tex` has direction sanity remark (rem:a3-direction)
- [ ] No "non-increasing" claims about `c_0(K)` anywhere

## RKHS Cap
- [ ] `RKHS_bridge.tex` has uniform cap lemma (lem:rkhs-uniform-cap)
- [ ] Uniform cap value `1/25` consistent throughout
- [ ] Remark explaining why uniform beats local (rem:uniform-vs-local)

## CI Tests
- [ ] `tools/stress_test_arch_bounds.py` runs without errors
- [ ] All 4 critical tests pass (positivity, floor, monotonicity, YES-gate)
- [ ] Regression check `c_0(1) == min(c_0(K))` present
- [ ] YES-gate slack ≥ 0.185 for all K

## Cross-References
- [ ] `\ref{lem:arch-floor}` resolves (referenced from RKHS_bridge)
- [ ] `\ref{thm:A3-gap}` resolves
- [ ] `\ref{lem:rkhs-uniform-cap}` resolves
- [ ] `\ref{rem:uniform-vs-local}` resolves
- [ ] `\ref{rem:a3-direction}` resolves

## Build Commands
```bash
# Quick test
python3 tools/stress_test_arch_bounds.py

# Full build
cd Q3_paper_clean && pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex

# Check for undefined references
grep -i "undefined" main.log
grep -i "multiply" main.log
```

## Post-Build Verification
- [ ] PDF compiles without critical errors
- [ ] No "undefined reference" warnings for critical labels
- [ ] Table in param_tables renders correctly with global constants
- [ ] All critical equations render properly

---

**Last updated:** 2025-01-20
**Status:** All items verified ✅
