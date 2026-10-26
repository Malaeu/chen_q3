# Original sparse schedule: numerical nontriviality threshold

2026-10-26. Read-only mathematical diagnostic prompted by the precision
question, while Q46 is pending. No new source estimate or spectrum run.

The already checked CCM_Q09_ATTAINABLE_DENSITY.md parametrizes original-P
vectors by polynomials of degree<=2M-3, giving dimension2M-2 for M>=1.
Equivalently the three constraint vectors are independent on j=-1,0,1:
a linear dependence between 1,1/(a-i omega_j),1/(a+i omega_j), a=1/2,
after multiplication by a²+omega_j² is a polynomial of degree<=2 with
three distinct roots. Its coefficients force all three scalars to zero.
Nonzero endpoint/exponential column normalizers do not change rank.
Thus for M=1 the original projected space is zero; for M>=2 it is nonzero.

Under the actual fixed schedule M=floor(m^epsilon),0<epsilon<1/32,
nontriviality requires m^epsilon>=2, hence m>=ceil(2^(1/epsilon)).
In particular every admissible epsilon requires m>2^32=4294967296.
At epsilon=1/33 the first integer m is8589934592; at1/64 it is
18446744073709551616. These thresholds concern nontrivial dimension only,
not the potentially later asymptotic onset of any receiver or estimate.

Consequences for experiments: a direct small-m calculation under this exact
schedule tests a zero-dimensional P and cannot reveal the desired source
sign. A diagnostic using m=16,M=2 has changed the band schedule; it may
check literal kernel algebra but is not a cell of the chosen epsilon<1/32
family. Higher precision cannot fix that mismatch. This does not invalidate
properly labeled finite kernel controls or their exact identities, and it
is unrelated to the separate archived CF22 panel.
No claim that fast exact prime-sum algorithms cannot reach these thresholds;
no finite test establishes the cofinal one-sided estimate in any case.
The next numerical proposal must pin epsilon,m,M and check rank before
spending on precision, prime enumeration or interpreting a sign.
