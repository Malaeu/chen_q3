# Q48 — same-prime deficit and complete continuous return

Status: PROCESSED_NO_NEW_POWER. Full original-P target remains OPEN.
Original107104bytes/2013LF, SHA256
7c7225a2e2056d95d5acb06b6a2115f388aacfe7e296e5df8f910220b9976959.
Root read the entire original and inspected all seven assets. Both recorded
stages replayed JSON-byte-identically;11source frames,8planted algebra errors
and one-byte corruption verified. No actual spectrum, Lean or Arb run.
Independent q44_bounded_audit qualified bounded PAPER PASS §§3–7, bound to
that hash. Upstream source/receiver assumed; no full-chain recertification.
Primary DLMF27.2.14 and27.5.1/2/5 checked for classical coefficients only:
https://dlmf.nist.gov/27.2#E14 ; https://dlmf.nist.gov/27.5 .

Original P, both times and full prime powers retained. C=A+D,0<=D<=4I.
Physical decaying kernel has trace L and HS square2(L-1+exp(-L)). Thus for
rho=TrD/d,q=||D-rhoI||HS², rho<=min(4,L/d),q<=2L.
Full mixed identity V=V_A+2Tr(Acirc Dcirc)+q gives
 |U2(C)-U2(A)-rho|<=sqrt((d-1)q/d)<=sqrt(2L).
No sign is assigned to the mixed term. Continuous-source replacement A=-D
returns mean and variance to zero exactly before inequalities.

For actual complete prime-power channel
 A_p=log(p) sum_(p^k<=m) p^(-k/2)H(k log p),
linear whole-line compression of its geometric series gives
 -ell_p I<=A_p<=u_p I, ell_p=2logp/(sqrtp+1),u_p=2logp/(sqrtp-1).
Both explicit Euler squares checked. E_p=(u_p I-A_p)(A_p+ell_p I)>=0 and
 A_p²=c_p A_p+gamma_p I-E_p,
 c_p=4logp/(p-1),gamma_p=4(logp)²/(p-1).
Writing a_p=TrA_p/d, F_p=A_p-a_p I,
 Dpp=sum TrF_p²=dGamma+TrRcal-d sum a_p²-sum TrE_p.
||Rcal||<=2048, Gamma<=8L(6+3L), hence
 Dpp<=d[2048+8L(6+3L)]=O(dL²).
This is all same-prime powers, not merely their individual diagonal.

Full V_A=Dpp+2sum_(p<q)TrF_pF_q. Different-prime term AND actual mean
remain unbounded at the required scale. There is no cutoff p^k q^ell<=m:
the tensor has two independent cutoffs. Original-P halfperiod check proves
K2(L/2,L/2)>=2(M-3),M>=4; its actual prime-square atom has small weight
O(m^(epsilon-1/2)). It is not a full variance/spectral lower or route no-go.

Available completion s_trial=12sqrt(dm)+4+sqrt(2L) has exponent1/2+epsilon/2.
Keep inherited s_keep<=6sqrt(m)+6m^(1/4), T_>R<=(s_keep+b_div)P,
PKP>=-(s_keep+50L+8)P. No second D fee, no short fee in direct K return.
Conditional improved U2 would return with only4+sqrt(2L); none supplied.

Rollback before trace square to Tr(WC)=sum_p Tr(WA_p)+Tr(WD), SAME
W=PWP>=0,TrW=1 throughout. Exact map has zero extra fee, but this is not
itself a new inequality. Do not optimize a single-prime channel without an
independent joint input. Neither U2 actual family nor CCM is killed.
No Q49 sent. Goal OPEN; CF22/PySR parked; RH unclaimed.
