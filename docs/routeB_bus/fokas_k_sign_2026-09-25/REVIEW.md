# Independent review record

2026-09-25. Native read-only agent /root/sign_algebra_review; report observed directly by root. This is a PAPER/code review, not a Lean kernel receipt.

## Algebra and literal K/plane functions

No material findings. Divided-difference recurrence and Delta^4 factorization correct. Quartic Rayleigh identity requires Hermitian K and theta=tr(Pi K Pi); root added these explicitly. Matrix K matches canonical entries; removable WR limit is -1/L+q0/4. Q5 phase belongs in b_n and cancels from boundary2G'(b)/sqrt(L). 162 Fraction recurrence controls passed. Gaussian sum truncation/quadrature are not certified by the diagnostic.

## Uniform 4m-start energy width

Reviewer independently checked the source lemma, exact 2m ratio count, weighted norm, and the finite spectral identification inherited from R2. Backwards nonvanishing is justified using b_N nonzero and positive denominator >=2G/3, including boundary t=0. Conclusion: the stated G/8*((16m-3)/(24m-3))*4^(-2m) width is valid PAPER-level with the same accepted R2 inputs. No source splice changed and no source sign obtained from it.

## Full diagnostic R3-R8 arithmetic

No material findings in main: both gradient signs/product-rule terms, R7 Hessian constants, R8 half-weighted double sum, index5m-1 tail bound, Frobenius norm upper bounds and budget algebra. Independent numerical differentiation at m=2, dps60 matched the gradients with absolute errors7.61e-51 and8.26e-53. Positive finite diagnostics establish neither certified arithmetic nor a cofinal result.

## Root integration correction after review

The initial diagnostic used Gamma_F=||K||_F in the remainder bound. This sharpens the fixed analytic Gamma_m in the committed B(m), so its D_minus must not be advertised as the unchanged canonical TEST. Root added a separately named canonical-budget result. The same remainder proof uses only an upper bound on ||K||, so a certified Frobenius bound can support a separately proved B_F remainder; it does not justify relabelling the old B. Independent review of the strict interval implementation is pending.

## Final strict interval certificate review

Frozen arb_m2_certificate.py SHA-256: bcfff2a3b3e011390a354d3081ca3985974496abe966a37b0ac3cad560670ccb.
Independent reviewer /root/sign_algebra_review reran the final100-dps certificate read-only: no material findings. Reviewed rational Sturm counts, F phases, full K analytic quadrature, Gaussian tail constants304/8952, geometric series bound, Q5 projection and all interval/sign operations. Whole-rectangle form [-26.1300 +/-5.19e-5]; sharpened margin [25.77492 +/-8.05e-6]; canonical margin [-28.1612 +/-5.29e-5]. Required y_lower>eta verified. Scope explicitly finite algebra, source implication conditional on applicable identities; no selected-tail membership/cofinal positivity/Lean admission. Root independently reran the same frozen bytes successfully.
