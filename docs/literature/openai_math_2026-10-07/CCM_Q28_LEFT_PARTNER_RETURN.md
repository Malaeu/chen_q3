# Adding the actual reflected left residues on original P

2026-10-26. Own calculation while Q28 is pending; not sent as another
message. Bounded independent PAPER PASS by all_p_contour_extension: symmetry,
actual multiset, full fees and real-part convention checked. No material
defect; upstream Q27 source estimates inherited. Root also verified three
scalar identities in exact SymPy. No favorable arithmetic bound.

Keep all notation and the SAME u,H,P from
CCM_POST_Q27_ORIGINAL_P_CONTOUR.md. Let Zright be the multiset of actual
zeros with z=rho-1/2 satisfying Re z>u and |Im z|<H. Functional equation
maps it bijectively, with multiplicity, to Zleft=-Zright. No critical-strip
zeros with |Re z|<=u are added or removed from the accepted contour identity.

Directly from v_+(-z)=-v_-(z) and v_-(-z)=-v_+(z),

 S_P(-z)=S_P(z).

This is an analytic transpose identity on the original P, not positivity.
Define the entire reflected left contribution

 Lsign=He sum_(z in Zright) mult(z) m^(-z) S_P(-z).

The right-side x=Re z>=u permits the inherited bounds
||S_P(z)||<=3L and ||S_P(z)||<=8V2/|Im z|^4 for |Im z|>=2Omega.
Since m^(-x)<=exp(-u L)<=exp(-1), Q27 (4.4),(7.2) with the exponential
weight replaced gives

 ||Lsign|| <= exp(-1) C_N W_m
 <= (256/e) C_N L(1+Omega)log(20+Omega) =: d_m.       (1)

Here C_N includes the same fixed covering of unit ordinate bins as Q27,
including multiplicities. Summing the finite Zright by the complete bin
majorant introduces no new source terms into the equality. All mixed
entries are retained before using operator norm to pay this added part.
For original M=floor(m^epsilon), each fixed epsilon>0 gives

 d_m=O_epsilon(m^epsilon L+L^2)=O_epsilon(m^(2epsilon)).

Let Ototal=Rsign+Lsign, the actual full reflected orbit sum outside the
central strip and below the SAME height H. Then the accepted identity is

 A=-H_decay+V-Ototal+Lsign+E.

Consequently

 T_>R <= -Ototal-H_decay+(B+e+b+d_m)P,
 P K_m P >= Ototal+H_decay-(B+e+d_m+50L+8)P.         (2)

This pays the whole left-partner replacement, without moving the contour
through imaginary transfer poles. It therefore claims no residue theorem
on a new contour and incurs no omitted contour-crossing fees. If one later
uses a new contour to evaluate Ototal, its transfer poles and edges must
still be treated separately.

For z=x+iy representing one right conjugate pair (y>0), real P implies
S_P(conj z)=conj S_P(z). That full four-zero orbit is exactly

 2 mult(z) Re[(m^z+m^(-z))S_P(z)]
 =4 mult(z) Re[cosh(z L) S_P(z)].                    (3)

Here Re is entrywise, equivalently Hermitian part for these symmetric
matrices. No sign follows from (3): cosh is complex, and S_P contains analytic
transpose squares. All-P one-sided lower control of Ototal is equivalent
to lower control of Rsign up to (1), hence to the original target up to
the already paid vanishing-exponent fees. No lower control was obtained.
This is a paid representation change and a check for Q28, not a second
arithmetic mechanism or a new exponent. Await Q28 without another send.
