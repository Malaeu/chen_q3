# Independent polynomial-kernel validation

The validation constructs the quiet space without using the main SVD. With y=(t/omega_m)^2, let Z(y) be the product over the q selected zero ordinates. The numerator polynomials Z(y)T_j(2y-1), j=0,…,m-q, generate the kernel. Modal residues are P(y_n)/product_(k!=n)(y_n-y_k), divided by d_n to recover orthonormal-basis coordinates. Column scaling and two-pass reorthogonalization produce Q at220 dps.

This polynomial parametrization has dimension m+1-q: the modal nodes are distinct, and the evaluated zero ordinates are distinct from them. Multiplication by Z and the residue map are injective. The numerical residuals check its implementation; no singular-value tolerance is used to choose the validation dimension.

All12 distinct m40 cutoff counts q16…27 were checked. Boundary canaries are m16:q8,9,10; m24:q12,13,14,15; m32:q17,18,20,21, totaling23 cases. Main kernels use row-scaled SVD. Maximum projector Frobenius difference is1.3962e-187. Full ||AQ|| operator norms agree to relative3.513e-150; compressed norms to2.059e-150, limited by the150-digit serialized norm fields. Polynomial-kernel residuals are at most1.043e-199 and orthogonality residuals at most8.60e-221.

`validation_source.json` separately compares160dps/GL128 and180dps/GL160 arithmetic matrices on every m40 polynomial kernel. Source matrices and the180-digit zero table remain numerical inputs. This validates algorithms and precision stability, not an exact cofinal theorem or an interval enclosure.
