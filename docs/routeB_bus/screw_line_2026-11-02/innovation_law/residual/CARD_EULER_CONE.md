# HYPOTHESIS — arithmetic residual cone

DIAGNOSTIC_NEVER_A_PROOF. Status: KILLED for the literal condition Q_f*(log p^k)<=0 on every prime power. This does not kill an averaged or weighted inequality and does not change Route B.

**Registered claim and prior.** The zeta whole-history minimizing step residual lies in the proposed Euler cone; prior 0.25. Tested at six times 1,...,6 and meshes 32,64, retaining all active prime powers.

**Evidence.** At t=1, all prior zeta prefixes are positive and the optimum is a genuine minimum. Already Q(log 2)=+0.499426889731470336 on mesh32 and +0.367939575135568127 on mesh64. Both are far from the 1e-40 sign threshold. At t=2, Q(log 7) is negative (-9.19076231587302e-5 and -0.00851116667159428), so neither uniform sign describes the later residual. At t=6, positive/negative counts are 72/26 and 89/9 respectively. DH and planted positive-history controls also have positive Q(log2) at t=1.

**Validation.** Arithmetic-coefficient perturbations at n=2 are reoptimized independently at eps=1e-10 and eps/2. Their central derivatives agree with -Q, with the expected quadratic truncation decrease. The result confirms the source gradient, not the sign cone. Direct Toeplitz quadratic replay and the arch/constant/pole/arithmetic source split agree with the signed innovation to at most 7.16e-89 across all 36 residual samples at 90 digits. Independent physical arch quadrature, retaining the infinite tail, agrees within 3.32e-64 on the saved mesh32,t=1 profiles in all three worlds; the profile serialization has 65 digits.

**What would kill this finding.** An indexing/normalization error reversing Q or substituting a stationary saddle for the t=1 optimum. Neither is supported: the same positive Q controls a negative reoptimized source derivative, and all t=1 past prefixes are positive. The files retain the piecewise constant profile itself for independent replay.

**What to hand Proshka.** Equation (11) is numerically reproduced, but any usable sign must control the jointly compensated source expression. At zeta mesh64,t=6 it is

`+4.88057502195755 -11.75689431950361 +28.34942525731067 -21.46487687825995 = 0.00822908150465320`.

The terms are arch, constant, both poles together, and all arithmetic atoms. No one-term positivity law survived. The residual is spread through the history: its L2 norm squared is 2.18847597001783, while the fixed terminal-bin mass is 1/64 (0.714% of the norm); 67.7% lies in the last quarter, not the last bin. No asymptotic shape claim is made.

**Reproduction.** Run `residual.py`, then `shape.py`, with mpmath/numpy/scipy. Entries whose `past_negative_index` is nonzero are stationary signed residuals only; their variational infimum is -infinity. They are never labelled positive prediction variances.
