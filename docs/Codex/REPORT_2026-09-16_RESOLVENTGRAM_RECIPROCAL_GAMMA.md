# Does the exact reciprocal pairing cancel the Mellin gamma correction?

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; SPECIFIED_AVERAGE_NONCANCELLATION_ONLY.
SCOPE: one exact symmetrization of the published RESOLVENTGRAM_MELLIN_PREFLIGHT,
not a rejection of every reciprocal Gram transport and not a V-sign result.
Source base: 2e38b141f063d869745454308c283c64b56940df.

Use its H(a)=E T^a=2xi(2a), J(a)=Gamma(2-a)H(a), and
H(a)=H(1/2-a). On -3/2<Re a<2 both J(a) and J(1/2-a)
are defined by their convergent full-source Mellin integrals. Thus

  J(a)=Gamma(2-a)/Gamma(3/2+a) * J(1/2-a).              (R1)

This is an exact reflection multiplier, not an isometry of the raw J values.
On a=a_u=5/4-iu/2, write x=u/2. Euler and Gamma nonvanishing license
both logarithmic quotients: the reflected H equals the original nonzero H.
Define B(a)=J'(a)/J(a). Differentiating H's reflection yields

  R_2(u)=1/2[psi(2-a_u)+B(a_u)]
        =-1/2[psi(3/2+a_u)+B(1/2-a_u)].               (R2)

Averaging these two EQUAL exact expressions gives

  R_2(u)=C(u)+D(u),
  C(u)=1/4[psi(2-a_u)-psi(3/2+a_u)],
  D(u)=1/4[B(a_u)-B(1/2-a_u)].                        (R3)

At real u the gamma recurrence and conjugation give

  psi(3/2+a_u)=psi(11/4-ix)
     =psi(3/4-ix)+1/(3/4-ix)+1/(7/4-ix),

  Re C(u)=-1/4[(3/4)/((3/4)^2+x^2)
                       +(7/4)/((7/4)^2+x^2)]<0.     (R4)

Indeed psi(3/4+ix)-psi(3/4-ix) is purely imaginary. In particular
C(0)=-10/21, without numerical approximation. Both simple reciprocals in
R4 are normalization terms produced by the reflected Gamma ratio; their
physical interpretation as selected original Weil terms is not asserted.

For the corresponding atom component

  K_C(u,v)=[conj(C(u))+C(v)]/[4+i(u-v)],

one obtains

  K_C(u,u)=Re C(u)/2<0 for EVERY real u,
  K_C(0,0)=-5/21.                                    (R5)

Thus this exact reflection-and-average does not cancel the correction and
does not make that component PSD. It produces a strictly negative diagonal
for it along the entire consumer line. The remaining component K_D is
retained exactly, with K_2=K_C+K_D; R5 is not a statement about the sign
of their sum.

A second check of the normalization is the modulus of R1's multiplier:

  |Gamma(2-a_u)/Gamma(3/2+a_u)|
    =1/sqrt[((3/4)^2+x^2)((7/4)^2+x^2)].              (R6)

This follows from Gamma conjugation and two applications of Gamma(z+1)=zGamma(z).
R6 is nonconstant and equals 16/21 at u=0. It does not preclude a suitably
weighted isometry; it only rules out an unweighted modulus-one reading of R1.

Decision: source reciprocity cannot be invoked to simply erase the Gamma
correction in P5 of the preceding preflight by this particular pairing.
A proof still must control K_C+K_D jointly, or use a genuinely different exact
map. No broad impossibility theorem, new lower bound, or negative V witness
is claimed. This is a direct analytical calculation using the previously
accepted full source identities and the Gamma recurrence.

## Independent acceptance and source links

Parent verified the recurrence inputs against [DLMF 5.5.1](https://dlmf.nist.gov/5.5.E1) and [5.5.2](https://dlmf.nist.gov/5.5.E2), read the full independent review, and checked the reflected derivative sign, consumer normalization, and factors in R4-R6.

Candidate SHA256: `1ca682ca6d49948ef13037022b5202cc705be24b99a41299f2687ec3f9322115`. Review SHA256: `e2a3f1c4686b00653c3b6ba93fdd7155cd70dbf82e920283fdd94d0424a81bbe`.
Reviewer: `/root/sibling5_check`; verdict: ACCEPT_SPECIFIED_RECIPROCAL_AVERAGE_GAMMA_NONCANCELLATION_ONLY.
Only status and this source/acceptance receipt were added after review.
No Lean certification or canonical admission. The stated negative diagonal
belongs to the named component, not the full Weil atom kernel.
