# Which direction does the positive-complement split remove?

Status: exact pole-profile calculation plus finite floating diagnostic.
No statement about the cofinal profile of CCM bottoms is proved.
This was proved while GREEN was running and was not sent as an interruption.
GREEN later proved lowest-J-space escape without the conditional P4 norm ratio;
see GREEN_VERDICT_AUDIT. P1–P4 below retain their original scope.

## The normalized original pole direction itself escapes

Let L=log m, I=[-L/2,L/2], p(x)=sqrt(2)cosh(x/2), and p_I=p 1_I.
The exact physical norm is

    ||p_I||²=L+2sinh(L/2)=L+sqrt(m)-1/sqrt(m).             (P1)

In the COMPLETE even Fourier basis of the interval, the pole coefficients
are the same formula used in the finite matrix,

    u_i=4sqrt(2)d_i L^(3/2)sinh(L/4)/(L²+16pi²i²),
    d_0=1, d_i=sqrt(2) for i>0.

The basis's shifted-cosine phase is included in this expression. Parseval
and sum_{i>m} i^-4 <=1/(3m³) give

    ||p_I-P_m^E p_I||²
       <= L³ sinh²(L/4)/(12pi^4 m³).                    (P2)

Indeed for i>0, u_i²<=L³sinh²(L/4)/(4pi^4 i^4).
Dividing P2 by P1 makes the relative squared error tend to zero, with
order O(L³/m³). Hence the normalized finite pole vector differs by o(1)
in physical L² from p_I/||p_I||. (Normalized-vector difference is at most
twice the relative unnormalized error.)

For every fixed compactly supported L² test phi, <phi,p_I> is bounded
independently of m once its support is contained in I, while ||p_I|| grows
as m^(1/4). Density of compactly supported tests and unit normalization imply

    P_m^E p_I / ||P_m^E p_I||  weakly converges to zero.   (P3)

In particular EVERY fixed finite theta-jet projection vanishes on this
normalized direction. This is an unconditional statement about the pole
vector, NOT about the selected bottom f_m and NOT about the lowest mode of J.

## A conditional relation to the lowest jump mode

Let q=u/||u|| and choose any unit lowest eigenvector e1 of
B=A-uu*=J-C I. Writing M=||A|| and U=||u||, Rayleigh comparison with q gives

    -M-U²|<e1,q>|² <= lambda_min(B) <= M-U²,
    1-|<e1,q>|² <= 2M/U².                              (P4)

Thus an independently proved M/U²->0 would force e1 to follow the escaping
pole direction (up to sign/phase). Such an estimate has NOT been proved here;
the existing coarse bound M<=100m² does not suffice. P4 is only conditional.
Consequently even successful retention relative to e1 would need additional
fixed-jet analysis; e1 must not be assumed a fixed theta reference vector.

## Actual finite diagnostic

The same full-source 90-dps calculations as the positive-complement probe give:

| m | squared overlap of e1(J) with normalized pole | ||A||/||u||² |
|---|---:|---:|
|4|0.995269321865|0.627426575657|
|8|0.998332442983|0.610556943969|
|16|0.998765951750|0.524367601382|

These are diagnostics, not interval certificates and not evidence of an
eventual rate by themselves. The m16 squared h-overlap of the actual CCM
bottom was approximately0.9984375, while its squared e1(J) overlap was
approximately0.2564569. These are distinct reference vectors.
The crude P4 bound is vacuous in all three cells (2M/U²>1); it was not used
to certify the much stronger measured alignment.

## Consequence for the open mechanism

The positive-complement construction has not isolated a known retained
theta mode. It removes a direction numerically close to a pole vector whose
own escape is proved by P1–P3. A useful Green or Schur argument must therefore
control the physical/fixed-jet profile of the FULL reconstructed state,
including the complement, and not merely retain a coefficient of e1.
This does not rule out such an argument or prove that e1 itself escapes.

Independent bounded PAPER audit confirmed P1–P4, the shifted-basis phase,
the factor1/(12pi^4) in the omitted even tail, and the weak-zero argument.
Its scope is the normalized pole vector; no missing source norm ratio was
assumed and no cofinal spectral claim was inferred from the table.
