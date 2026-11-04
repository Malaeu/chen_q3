# Bounded read-only control implementation review

DIAGNOSTIC_NOT_RH. **PASS for implementation and normalization consistency.** Reviewed `scripts/controls.py` and `CONTROLS.json` without rerunning them. `CLASS_REVIEW.md` remains unchanged. This review does not turn mpmath quadrature into an interval certificate or authorize a CCM commutant scan.

The positive control uses exactly the prescribed m16 carrier with d17, b=L/2, rho=cb=1 and D=((b²−x²)f′)′−c²x²f. Under y=x/b the unitary rescaled basis is d_j(−1)^j cos(πjy)/sqrt(2). The derivative part becomes −∫(1−y²)phi_i′phi_j′ and the potential part −rho²∫y²phi_i phi_j, so there is no missing b or L factor. The code's J/T formula matches these integrals, including D00=−1/3 and D01=−2sqrt(2)/π². Its five direct-integral spot checks use the same physical phase convention through an independently evaluated weak form and agree to approximately10^−80 in the stored receipt.

The sinc kernel has the exact spectral representation K(x,y)=(2π)^−1∫_(−c)^c exp(it(x−y))dt. The Fourier transform of the stated physical cosine is sqrt(L) F_j(bt), with F0(z)=sin(z)/z and Fj(z)=sqrt(2)z sin(z)/(z²−π²j²). Therefore its even Galerkin matrix is exactly `(2/π)∫_0^rho Fi Fj`. The implementation uses this prefactor, the correct phase cancellation and the removable value F0(0)=1. At rho1, every j≥1 denominator stays away from zero; the finite quadrature integrands are smooth. Symmetric entries are copied consistently.

The computed commutator is **D K−K D**. `CLASS_REVIEW.md` proved that the opposite convention K D−D K has positive(0,1) entry. Thus the negative stored entry−1.4007126301417371e−5 is consistent with that proof; it is not a basis-phase or kernel-sign discrepancy.

The Frobenius helper sums every real matrix entry squared. All matrices in this implementation are real, so no conjugation is missing. The fixed-control residual is

`||[D,K]||F/(||D||F ||K||F)`.

This is precisely `||[D/||D||F,K]||F/||K||F`, so it applies the task's image-space Frobenius normalization of D. The stored norms3512.59748, .57258304 and .10839087 are consistent with the reported normalized residual5.3892191437783304e−5. It exceeds the prescribed10^−25 threshold by about20 orders of magnitude. The test is the fixed nonconstant Slepian differential operator, explicitly distinguished from the degenerate optimization over the whole literal class.

The negative control uses a real symmetric rational-entry matrix with the recorded seed and the admissible witness I/sqrt(17). Its norm1 and commutator0 agree with the exact universal scalar argument. A zero optimized minimum therefore cannot supply the requested order-one negative discrimination. This checks an exact witness; it does not establish anything about non-scalar minimizers or universal same-D robustness under a planted perturbation.

The script first requires Gate0 PASS, computes controls only, and records positive-control failure plus `CCM_scan_run=false` and `non_scalar_commutant_scan_run=false`. No source matrix or repaired metric is substituted. The stop status `SCAN_VOID_POSITIVE_CONTROL_FAILURE` is consistent with the prescribed control rule. The quadrature receipt is an80-decimal-digit diagnostic, not a rigorous quadrature-error enclosure; the separate analytic argument establishes strict finite-projection noncommutation, while this receipt supplies its high-precision magnitude.
