# m248 residual spike: one dominant quiet direction and a cutoff event

DIAGNOSTIC_NEVER_A_PROOF. This dissects the pinned literal-even source
matrix; no matrix or source eigenspectrum is replaced.

At the best admissible m248 sector, q=127,r=122,
`delta=2.105038491662235`, `lambda_r=2.153837773001046`, gap=.048799281338811.
The cutoff sector is T in (282.4651147650521,283.2111857332339], or
kappa in (.9994361084879524,1.0020759044348455]. Thus kappa=1 excludes
zero128 at283.2111857332339. Omega=282.6244843128529.

The residual is carried by a well-separated direction: the first two
singular values of AQ are2.10503849 and.71184856. The top squared value
accounts for89.6942% of ||AQ||_F^2 (89.7380% within the top two). Its unit
carrier vector f=Qy is the top eigenvector of Q^T A^2 Q, not an eigenvector
of D=Q^T A Q. It has98.2260% squared overlap with D's largest eigenvector
(lambda_D=1.46327069), but its D Rayleigh value is1.44479527 and its full
residual is larger:

    delta^2 = ||Dy||^2 + ||By||^2
            = 2.10634921161276 + 2.32483783976685,
    B=U^T A Q.

The complement leakage B supplies52.4654% of residual energy, so replacing
delta by ||D|| or the Rayleigh value misses the main scale. The identity
closes to4.45e-15 absolute. The full A decomposition is also revealing:
87.7248% of f's squared mass lies in a resolved A eigenmode at1.06735961,
contributing.99941078 to delta^2, whereas just2.6861% in the eigenmode
at7.51460560 contributes1.51680378. Another.7651% at7.57195251 contributes
.43864078. Small high-energy components substantially amplify ||Af||.
No interpretation is assigned to numerically unresolved near-zero A modes.

The carrier vector is concentrated near the carrier ceiling: coefficients
n247 and246 carry38.1309% and15.3626% of its norm; n248 carries2.6021%.
Its endpoint value is f(L/2)=5.29187581. Squared directional overlap with
the full carrier endpoint functional is.31065952, and with that functional
projected into J is.49007004. This is appreciable endpoint coupling, not a
pure endpoint direction. `vectors.csv` saves the top two unit residual
vectors; `profiles.csv` saves physical and Fourier profiles. Their overall
signs are conventional; f0 is chosen nonnegative for the first vector.

The next zero row explains a concrete removable component. The normalized
new constraint at zero128 has squared overlap.85936757 with this top quiet
mode: adding the row removes85.9368% of its squared norm before
renormalization. At the next sector q128 the largest residual drops to
1.02781704. However lambda_r simultaneously drops to1.06735961, leaving
gap=.03954258, slightly worse than the q127 optimum. At q129 delta falls
to.62057580 but lambda_r=.35787474, so the gap is negative. A smaller
residual alone does not identify the best separator.

The adjacent sizes separate the cutoff effect from source/carrier changes:

| m | best q,r | delta | lambda_r | gap |
|---|---|---:|---:|---:|
|247|127,121|1.23364713|1.55545141|.32180428|
|248|127,122|2.10503849|2.15383777|.04879928|
|249|128,122|1.22300680|2.15486894|.93186214|

At m249, kappa=1 already includes zero128; at m248 it does not. The
m249 q127 counterfactual is below kappa1 and has delta4.56400908 and
negative gap−2.26478575; its top residual mode has99.9877% squared overlap
with the row entering at zero128. Conversely m247 already benefits strongly
from including zero127. This is a moving cutoff/carrier interaction and
large B leakage, rather than evidence for a new exceptional zero pair.
`neighbors.csv` contains all21 sectors q125..131 across these three m,
including those below kappa1, and the next-row removal masses.

The consecutive zero127/128 gap is.7460709682. Its normalization using the
local zero density is.45220278, while the carrier normalization
Delta gamma*L/(2pi) is.65466939; these are different conventions. The gap
before zero127 has local normalization1.95993834. At the kappa1 cutoff,
zero127 is.09652893 local spacings below it and zero128 is.35560694 above
it. These values indicate a close pair following a wider gap, without
establishing a Lehmer or causal law. `nearby_zeros.csv` records both gap
normalizations and distances from Omega and both sector endpoints; it
includes zero129 because it is within one local spacing of the upper
sector endpoint, though1.3424 local spacings above Omega.

Independent768/1024-bit MP row constructions at m248 give identical
float-converted quiet projectors and delta at printed precision; the top
mode squared overlap is.999999999999997. These checks validate frame
arithmetic on the supplied decimal nodes, not interval root completeness
or a source-quadrature enclosure. Source SHA256 and full scalar details
are recorded in MODE.json. Reproduce with analyze.py using numpy/scipy,
gmpy2 and the sibling zero_extension source/helper paths.
