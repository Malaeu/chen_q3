# The polar target retains the original spectral difficulty

Root check while question2 runs; no new Pro message and no status promotion.
Use the independently accepted exact identity (31),(34) of answer1,
on the same full complex V_m, with L=log m and H=R+R*.

 W(f)=D_arch(f)-<f,D f>+<f,E f>,
 E=-cA I+2H-2(Y-X).

Since H is the compression of convolution by exp(-|x|/2),
0<=H<=4I (the full-line L1 norm is 4). Also 0<=X,Y<=LI, so

 -(cA+2L)I <= E <= (-cA+8+2L)I.

Let B_m be the Hermitian form matrix on V_m of D-D_arch, and let
b_m=lambda_max(B_m). The exact full source matrix is K_m=-B_m+E_m,
where E_m is the compression of E. Min-max therefore yields

 b_m+cA-8-2L <= -lambda_min(K_m) <= b_m+cA+2L.

In particular |b_m+lambda_min(K_m)|<=cA+8+2L. The two sufficient targets
are equivalent at subpolynomial scale, including the good-subsequence-per-
eta version after absorbing O(log m) by a slightly larger exponent.
The criterion in answer1 (36) is exactly b_m<=C_eta m^eta.

This equivalence does not refute the polar approach: source structure of
F could still give a useful estimate. It does show that constructing M,Y,D
or repackaging the old source form as a double commutator cannot by itself
count as reduction of the missing spectral inequality. A new estimate must
use the arithmetic F, not just these exact identities. Question2 already
asks for such an estimate; no duplicate or interim addendum was sent.

## Actual ambient F norm cannot be subpolynomial

Root derivation, accepted in one bounded independent pass by
causal_algebra_audit. Fix integer m>4, L=log m. Simultaneous recurrence of
the finite torus of phases supplies omega_k->infinity with
exp(-i omega_k log n)->1 for every n<=m. Periodic recurrence also gives
arbitrarily large returns, so no irrational-independence premise is needed.
Take unit ambient vectors u_omega(x)=exp(i omega x)/sqrt(L). Then

 Z u_omega(x)=exp(i omega x)/sqrt(L) A_omega(x),
 A_omega(x)=sum_(n<=exp x) n^-1/2 exp(-i omega log n).

For fixed m the finite sums converge uniformly to A_0(x). Explicit
integration of Ru_omega gives ||Ru_omega||2<=2/|omega|. Since RZ=ZR and
||Z||<=sum_(n<=m)n^-1/2 is finite for fixed m, ||RZ u_omega_k||2->0.
Consequently

 ||F||^2 >= (1/L) integral_0^L A_0(x)^2 dx.

For x>=log4 and N=floor(exp x), comparison with integral_1^(N+1)t^-1/2 dt
gives A_0(x)>=2(sqrt(N+1)-1)>=sqrt(N+1)>=exp(x/2). Thus

 ||F_L|| >= sqrt((m-4)/log m), m>4.

This rules out a subpolynomial AMBIENT operator-norm bound for the actual
F_L: an estimate ||F_L||<=C_eta m^eta for eta<1/2 cannot hold eventually.
The witnesses can have arbitrarily large frequencies beyond the actual
carrier cutoff. No claim is made about F_L restricted/compressed to V_m,
its inverse, bottom eigenvectors, or the signed double commutator. The
question2 source-form estimate is untouched. No interim addendum was sent.
