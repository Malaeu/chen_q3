# Independent readback of geometry/innovation.py

DIAGNOSTIC_NEVER_A_PROOF. Read-only formula/code review; no duplicate
geometry run or new source calculation was performed.

**PASS: source_g normalization.** With x=exp(-t/2), the code's

    Li_2(x)-Li_2(-x) + 2 Im Li_2(i x)

equals 4 sum_(n=1 mod4) x^n/n^2, hence
sum_(k>=0) exp(-(2k+1/2)t)/(2k+1/2)^2. The minus sign before
2 Im Li_2(i x) instead selects n=3 mod4, giving the DH nu=3/2
tail. Subtracting this from psi_1(nu/2)/4 yields exactly the full
archimedean constant-window series. The code retains the source-specific
constant, all signed arithmetic coefficients, and the zeta-only pole.
Its final factor -1/2 therefore agrees with g=-K_source[chi]/2.

**PASS: arithmetic conventions.** The strict log(n)<t hinge is continuous
at equality because its multiplier t-log(n) is zero. The derivative jump
has sign +b(n)/sqrt(n). The DH recurrence retains non-prime-powers and
signed coefficients.

**PASS: covariance and recursion.** The sequence r[0]=-2g(Delta),
r[k]=2g(k Delta)-g((k-1)Delta)-g((k+1)Delta) is the increment covariance
from four differences of Suzuki's G_g. The real Durbin update and
v_new=v_old*(1-reflection^2) have the standard signs for this covariance.
Prefix positivity gives a nonnegative, nonincreasing innovation variance;
the code's first nonpositive pivot detects a loss of that condition.

Two reporting guards must remain explicit:

- After a first nonpositive pivot, any continued unpivoted recursion is
  signed Schur-complement algebra, **not a positive prediction-error
  variance**. Monotonicity conclusions only apply while prefixes remain
  positive definite. A later positive pivot does not repair an earlier
  failed prefix.
- The implementation uses N=floor(mesh*log(240)). Thus its last interval
  length is N/mesh, at most log(240), with a mesh-sized endpoint shortfall.
  It does not sample the irrational endpoint log(240) exactly. Coefficients
  through n=240 suffice on this stated range. This fixed-mesh screw-curve
  experiment is distinct from the nonnested finite cosine sequence N=m.

No formula or sign error was found in the source_g, covariance, or
Durbin recurrence on this bounded readback. No Weyl-radius identification
or cofinal positivity is inferred.
