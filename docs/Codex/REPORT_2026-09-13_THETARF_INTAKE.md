# THETARF intake: the fixed two-channel relative bound is impossible

STATUS: ACCEPTED_FIXED_TWOCHANNEL_RF_DIVISOR_OBSTRUCTION_PAPER.
RAW_VERDICT: ACCEPT_FIXED_TWOCHANNEL_RF_DIVISOR_OBSTRUCTION.
SCOPE: FIXED_T12_T13_ALL_POSITIVE_DELTA_EXCLUDED_AT_PAPER_LEVEL.
ACTUAL_V_SIGN: OPEN. GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. RH: OPEN.
PX_RH_CLAIM: NOT_MADE. No Lean proof or canonical admission.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The fixed diagonal-normalized carrier demands a holomorphic square root that the source diagonal cannot possess; the source form itself is not shown negative.

## 1. Exact received object and independent review

The full GitHub response is
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_THETARF_2026-09-13.md`
at commit `1a380a221f0b967f8ea0d11225c444d6b9ff7365`:
89215 bytes / 1343 LF / CR0 / final LF,
SHA256 `933707739367e05a34d07c273fc94d1455a8ddfef9d5e16b33189afd209aa93e`.
The parent read all 1343 lines, including every appendix. The sole checker
`/root/sibling5_check` independently read the entire exact response and
returned `ACCEPT_FIXED_TWOCHANNEL_RF_DIVISOR_OBSTRUCTION`. Its retained
read-only review receipt has SHA256
`cbf36efba1973e66e43d1b22f134a1941e0da3bc20c253c85195a32407867f02`.
The checker also replayed the certificate; this is independent review,
not an external signed receipt or canonical node closure.

At 15:23 UTC the exact living ChatGPT task was idle with the commit/path
notice. A successful Git fetch independently found the expected response.
The received commit adds only that file; the clean math worktree advanced
by fast-forward. The app notice alone was not treated as mathematical intake.
The response cites the original THETARF/RESUME contracts; FINISH is the same
attempt. Its analytic divisor proof does not depend on the later H/Z/C
Gaussian-deformation diagnostics, and contradicts none of their limits.

All seven R/I/C/A/W/S/L files were compared byte-for-byte to their Git objects
at `8eacfe77fd5f70775f25715876611c36eafb94f1`. Their complete SHA256, Git blob,
byte and LF counts match the response's table. C:T12/T13 was reread in full
for the actual carrier projection. Earlier accepted dependencies retain
their stated scope; this is not a claim to reread every recursive archive.

## 2. Accepted theorem and its proof

Keep the complete source f=Phi/A, A=||Phi||_2, Z=int Phi=xi(1/2), A distinct
from Z, and exactly the fixed J of
`REPORT_2026-09-13_TWOCHANNEL_LAPLACE_BRIDGE.md`, T12/T13.
Write calV=A^2 V, d(z)=calV(z,z), calW=A^2 W. This common positive scale
preserves the original RF and its delta; no source or carrier is replaced.

**Theorem.** There is no delta>0 such that V[c]>=delta W[c] for all finite
families of real nodes and complex coefficients. Indeed, the response gives
a source-defined sequence of finite real-coefficient rows b_k, with nodes
in [0,1/k], for which W[b_k]>0 and |V[b_k]|/W[b_k]->0.
No sign of V[b_k] separately is supplied.

The proof has three independently checked ingredients:

1. Full calV is jointly holomorphic for |Im z|,|Im w|<pi/4, and
   d'(z)=-2z Phi(z)^2. The full-source certificate places exactly one zero
   counted with multiplicity in B((237019+715864i)/10^6, 10^-5).
   It is therefore a simple zero of the bilinear analytic diagonal d.
2. Orthogonal projection of the existing independent w_+ channel onto j_0
   gives calW[c]>=|sum c_i u(x_i)|^2, with u(x)=sqrt(d(x)) a(x).
   On |z|<77/100, r=sqrt(z^2+4), r(0)=2, and
   a(z)^2=(r-1) exp(z)/[(2r cosh(z)+1) cosh(r)^2].
   The branch bounds in response section 5 make this holomorphic and
   nonzero throughout the disk, with the positive real branch at zero.
3. A hypothetical RF forces each Taylor coefficient to satisfy
   delta |u_n|^2 <= v_nn <= 2^122 (77/100)^(-2n).
   This follows from finite real-node differences at each fixed order,
   followed by the Cauchy coefficient bound for calV. Hence the germ u
   extends holomorphically to that disk. Identity gives U^2=d a^2 there,
   impossible at the certified simple zero. Delta was arbitrary and
   positive, so the argument excludes every such delta.

The ordered limits are fixed derivative order then h->0. The explicit
all-rank family subsequently chooses orders n_k and dyadic steps h_k
through the full source. It satisfies
|V[b_k]|/W[b_k] <= 2^123 (76/77)^(2n_k)+2/k -> 0.
For every delta>0, (V-delta W)[b_k]/W[b_k]<-delta/2 eventually.
No numerical values of n_k or h_k were claimed computed. Increasing ranks
is not needed to establish the theorem.

The accepted analytic propagation theorem A additionally excludes a
uniform all-rank RF on any nonempty real open interval: such a local RF
would propagate to the already excluded global one. This uses the thin
complex neighborhoods of W available near real compacts, without assuming
that W itself extends across the certified nonreal zero.

## 3. Certificate replay and analytic error audit

Appendix A was extracted verbatim to
`certificates/THETARF_DIVISOR_20260913.py`: 8994 bytes / 214 LF,
SHA256 `578dcb6eb0705c93fe26c5668f960e9789fd276df0220055f62bba89adab52a8`.
The parent's Python 3.14.7 / libmpdec 4.0.1 executions at 60 and 90 digits
both exited zero with empty stderr and byte-identical producer stdout:

| Local output in certificates/ | Bytes | SHA256 |
|---|---:|---|
| THETARF_DIVISOR_20260913_60.stdout | 1207 | `1ca45a858a318fc136089ebb613fc803748e138a0bc050609abebc8239db9013` |
| THETARF_DIVISOR_20260913_90.stdout | 1627 | `db2cc93b85553e3f11276fa1f65d44b062c12b5a1ff846bcfdc287a67541e0cf` |

The proof uses the rational bounds |d(center)|<1/100,
|d'(center)|>9000 and sup_disk |d''|<10^8. The Rouché margin is exactly
9000/100000 - 1/100 - 10^8/(2*100000^2) = 3/40 > 0.
The observed second-derivative upper bound is below 3.296*10^6.

The parent checked the analytic budgets as well as replaying code:
whole Taylor-cell remainders via disks of radius 1/32; all theta terms
n>=13 via geometric majorants; both full-source integral differences;
and the entire real integration tail t>=3. No agreement of quadratures
is used as an error bound. Appendix C's rational disk/tube, channel,
Cauchy and Rouché inequalities were independently recomputed exactly.

The standard analytic dependencies were reread directly:
[Cauchy's formula](https://dlmf.nist.gov/1.9.E31),
[Rouché's theorem](https://dlmf.nist.gov/1.10.iv), and the documented
[Decimal exponential rounding](https://docs.python.org/3.14/library/decimal.html#decimal.Decimal.exp).
The source polynomial recurrence, interval arithmetic operations, Machin
pi bounds, trigonometric remainder and directed rounding were inspected.
No diagnostic Newton/contour run, old source-node sweep or Lean run was
needed or repeated. Two precisions alone are not independent acceptance.

## 4. Consumer consequence, boundaries and next action

CLOSES: the named GLOBAL_TWOCHANNEL_J_RELATIVE_DOMINATION candidate as a
possible sufficient interface. Its fixed all-rank RF is false, even though
the carrier is positive and its real diagonal and both leading end limits
were matched correctly. This is an isolated mathematical paper verdict,
not a canonical registry mutation or a positive theorem supplied to Weil.

OPENS: return to the actual consumer V[c]>=0 on all finite complex rows,
or a different sufficient interface derived with its entire source
remainder paid. The new obstruction is an admissibility test for any
proposed comparison, not permission to replace the failed J silently.
The full RH objective remains unchanged and active.

No negative V row was obtained. A simple nonreal zero of calV(z,z) is not
a zero of xi and is not negativity of calV(conjugate(z),z). For example,
the positive real kernel 1+xy has simple complex zeros of its diagonal.
Full IC, ODD2, all-order source sign, RH and simplicity of xi zeros remain
unproved here. The prior Gaussian controls also give no a=0 witness.

Historical completed attempts without an actual source-sign supplier
advance once from 6 to 7; completed attempts since the explicit THETARF
owner resumption advance from 0 to 1. Technical retries do not add attempts.
This is concrete exclusion evidence, not a repeated idle/blocked turn.
It does not meet the owner's three-attempt threshold in the resumed run.
No new mathematical request is dispatched by this intake.

## Exact intake review receipt

The sole checker returned CLEAN_INTAKE for the complete 8288-byte / 147-LF
draft, SHA256
`a59005e71a8b0e6925914ea056ada2756cb3554720e8ec03d518e7f300303312`.
Retained review receipt SHA256:
`ab1eb1ed94810579df7ffe7714841fc0c58bf3c898386f67d2ade74f5e6d34a4`.
Only the acceptance status and this receipt were added after that review.
