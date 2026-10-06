# Uniform density input for answer4

Chourasiya–Simonic, An explicit form of Ingham's zero density estimate,
arXiv:2507.15184v2 (30 September 2025), printed p2 Corollary1 and the
explicit display immediately after it. Root fetched and read 2026-10-06.
https://arxiv.org/pdf/2507.15184
SHA256 11ebae58b467d14a20835eb732130c2c084f9440ef5e2fdbe38d697ba1e0d261.

Quote: "Corollary 1 implies that" (followed by the explicit estimate).
The display gives, uniformly for sigma in [.500,.625], T>=3*10^12,
 N(sigma,T)<=8.185 T^[3(1-sigma)/(2-sigma)]
 (log T)^[(7-5sigma)/(2-sigma)]+9.461(log T)^2+167.8log T.
N counts multiplicities with beta>=sigma and 0<gamma<=T.

EXACT_FIT for answer4 (20): sigma=1/2+alpha_m with
alpha_m=8loglog(m)/log(m)<=1/16 eventually; T=m(log m)^2 eventually
exceeds the fixed height. Constants are uniform, so substitution of
alpha_m tending to zero is legitimate. Conjugation covers both signs
of gamma with factor2. The log exponent is <=3 on the whole interval.
The paper uses an established finite-height RH verification to fix a
numerical threshold; its displayed estimate is unconditional, not an
assumption of global RH. It bounds NUMBER of exceptional zeros, not
their absence or the norm/sign of exceptional source rows.

Root shelf grep found no prior exact theorem hit in docs/literature;
this is a focused source check, not a global absence claim.

## Answer5: full strip weighted count

Root additionally read the entire Table1 on printed p2. Its 16 intervals
cover [1/2,1], including the final [.96875,1] row. The maxima are
B1=46.06, B2=9.461, B3=167.8. Since p=3(1-sigma)/(2-sigma)>=0 and
the logarithmic exponent is <=3, their sum 223.321<224 proves the
uniform simpler bound N(sigma,X)<=224 X^p (log X)^3 at X>=3e12.
This is not an extrapolation of the narrower display used for answer4.
HSW Cor1.2, printed p2 of the PDF already stored in
../joint_hilbert_2026-10-06/, was re-read: its explicit total count bound
implies N(X)<=X log X for X>=3e12. No new source download was needed.
Combining these inputs by layer cake pays the weight m^|Re(w)| before
taking the full high-zero trace; the application and independent audit
are in HIGH_ZERO_TAIL_AUDIT_2026-10-06.md in the source-observability bus.
