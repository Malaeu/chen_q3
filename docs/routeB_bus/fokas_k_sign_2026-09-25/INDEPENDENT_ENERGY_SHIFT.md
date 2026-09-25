# Ground tracking with an independently certified energy cut

2026-09-25, source baseline 43d67116. Finite PAPER lemma and reference-cell
certificate task. This does not identify the rational reference row with the
selected exact-energy Ferrers row and makes no cofinal claim.

## The change in the sufficient condition

The m8 diagnostic failure is a failure of positivity above a=q*Kq. It is not
failure of positivity above every energy cut. Keep the SAME K and q; choose a
separate real number mu. Require BOTH

    lambda_min(K) <= mu,
    B_mu = Q(K-mu I)Q restricted to q-perp >= d I, d>0,
    Q = I-qq*, ||q||=1.

No comparison mu>=a is assumed. Merely lowering mu to make B_mu positive
would not suffice: the independently certified ground upper bound is essential.

## Proof of the inverse-residual tracking bound

Let lambda0 be the bottom eigenvalue. Interlacing gives lambda1>=mu+d>mu,
so the ground space is one dimensional. Choose unit u in it and write
u=cq+w, c=q*u, w⊥q. If c=0, w*B_mu w=lambda0-mu<=0, impossible.
Set t=mu-lambda0>=0 and r=(K-aI)q. Projecting the eigen-equation yields

    w=-c (B_mu+tI)^-1 r.

In the common eigenbasis of B_mu and B_mu+tI, division by b_l+t cannot
increase the norm relative to division by b_l>0. With R_mu=||B_mu^-1 r||,
unit normalization therefore gives

    ||q-u(u*q)|| <= R_mu/sqrt(1+R_mu²).

This is the same phase-independent projection error used by the current
tracked-transform consumer. Its kernel and central-normalization factors
remain unchanged (CELLWISE_INVERSE_TEST.md, (C)-(E)). No weighted cofinal
rate or real-zero premise is supplied by this finite statement.

## Noncircular certificate for one reference cell

An LDL* inertia count of K-muI equal to one negative pivot certifies
lambda0<mu. An all-positive LDL* of

    C_mu-d I,    C_mu=Q(K-muI)Q+qq*,

certifies B_mu>dI (C_mu acts as identity on q). Ball LU solve C_mu v=r
then encloses R_mu=||v||. All pivots must strictly exclude zero; an
inconclusive pivot is a failed certificate, not a sign conclusion.

Certified exact rational cuts: m=8, mu=10^-18, d=3*10^-17. The reference row uses the explicit fixed rational approximations to the
numerical energy centers printed in m8_negative_certificate.py; neither
energy is asserted to equal an exact spectral midpoint or selected root.
The full K includes diagonal, WR integral and prime-power terms.

## Review and boundaries

Independent native read-only /root/sign_algebra_review checked the lemma:
no material findings. lambda0<=mu and B_mu>0 are sufficient without mu>=a.
Existing graph-operator Lean wrappers have stronger Rayleigh-floor hypotheses;
the multiplied eigenvector identity remains usable, but those wrappers cannot
be relabelled as already proving this new interface. No Lean changes or build.

The reference-cell arithmetic certificate is recorded separately by
m8_negative_certificate.py and m8_shifted_ground_certificate.py. Successful
arithmetic does not close source applicability, family decay, parity/real-zero
premises or RH. It tests whether changing the energy cut is a real finite
repair rather than a renamed impossible Rayleigh-floor demand.

## Executed certificates and independent reproduction

At 100 and 140 decimal digits, the interval LDL certificates have:

| Matrix | Negative pivots | Positive pivots |
|---|---:|---:|
| K - 10^-18 I | 1 | 16 |
| C_mu - 3*10^-17 I | 0 | 17 |
| K - 10^-12 I | 4 | 13 |
| K - 10^-10 I | 4 | 13 |

The last two cuts also certify a cluster of four lowest eigenvalues below
10^-12, with all others above 10^-10: external spectral gap >9.9*10^-11.
This concerns the exact literal m8 matrix, without assuming an approximate
basis is exactly orthonormal. It does not select q within the low cluster.
The independent-shift certificate supplies that separate projection estimate.

At 140 digits the rigorous ball upper estimate for the projection error is

    [0.055349925591024360266096710330046 +/- 4.63e-34] < 0.05536.

The Rayleigh-shift witness remains strictly negative, approximately
-1.1400227617190263443e-11. Thus on the SAME reference K,q we have both a
failed Rayleigh-shift floor and a successful independent-energy tracking
certificate. This proves the stronger old sufficient condition is unnecessary
for finite ground tracking; it does not establish the new family inputs.

Independent native reviewer /root/sign_algebra_review reread both scripts,
checked the interval construction, and separately recomputed at 100 digits:
no material findings. Reviewed script SHA256:

- m8_negative_certificate.py: 31cbe43e8914b3d378357ba7dd5ee84aaefcbbeef34fb2602508f7d4114448a4
- m8_shifted_ground_certificate.py: 9bbc48fb4ff16d2791a0505b527dd91c19a25440def68569212f94967003df49

Reproduce from the repository root:

    .venv/bin/python docs/routeB_bus/fokas_k_sign_2026-09-25/m8_negative_certificate.py --dps 100
    .venv/bin/python docs/routeB_bus/fokas_k_sign_2026-09-25/m8_shifted_ground_certificate.py --dps 100

## Exact next family obligation

On the actual selected schedule, independently construct mu_j (for example
by an explicit better test vector giving Rayleigh <=mu_j), prove
B_(mu_j)>0, and establish the central-anchor/kernel-weighted decay of
||(B_(mu_j))^-1 r_j||. Choosing the unknown ground eigenvalue as mu_j would
merely hide the task. The zero-set/odd-sector requirements also need their
own compatible argument. No replacement of the source family is proposed.
