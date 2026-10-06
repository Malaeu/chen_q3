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
