# CCM moment Q1: complete background paid, arithmetic open

2026-10-07. Full197 rendered response blocks read. Downloaded original38136bytes,
SHA256357e6435ab54f48d73f4f0224f83768a7986a1effc1f31a9c849e743770bc8f5.
Request205432bytes SHA2564b51de0ab0cd0b06ec26cf8d762c9034d331c7e8740822651fdc401fe65b95e5.
Chat Derive CCM Drift: https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac65a73-ba24-83eb-aa2a-97c07f5e0214
Terminal observed15:23UTC. No Q2 sent. PAPER only; SP/RH OPEN.

## Accepted bounded output

Literal K=B-C. B=A_arch-c_A I+2R, R kernel exp(-|x-y|/2),
c_A=gamma+log(8pi)+pi/2. C retains the full joint prime-pole measure.
For L=log m>=256, with zero-padding of old matrices,

    B_(m+1)-pad(B_m) >= (L/64) P_new -5000/(m L) I.

Independent read-only moment_compensation_map PASS, relying on prior
full-window ||A-diag(a)||<=20 from attached request659–729. Root reread
that prior proof: diagonal error10/L+2b_L and Hilbert commutator error
2+pi/2+2b_L total<20 for L>=1. No dependence on mode count is introduced.
Reviewer checked literal constant, dilation derivative, noninteger boundary
term in xv', both coupling columns, least eigenvalue of full two-mode block,
and square completion retaining L/64 credit. Exact coupling cost
10+64*512/7<5000. No kernel verification claimed.

Root checked sections4–7: companion D_p=2m+1+sum_j(-K_jj)_+^p is
nonnegative and its scalar moment <=Tr(K_-^p) by Jensen. For the actual
zero-padded affine endpoint path H_t, Wbar=integral[H_t,-^(p-1)+
diag((-H_t,jj)_+^(p-1))]dt is positive. The exact identity is

    delta Z=2-p Tr(Wbar delta B)+p Tr(Wbar delta C).

TraceWbar<=Zold+Znew and b=5000p/(m L)<=1/(4m), for L>=20000p,
give Znew<=(1+2/m)Zold+p Omega/(1-b),
Omega=Tr(Wbar delta C)-(L/64)Tr(P_new Wbar).
This pays only background drift; Omega is not bounded at the target scale.

The full arithmetic correlation is exactly the prime-power sum minus
continuous pole integral against rho(s)=Tr(Wbar Q_new(s))-
1_(s<=L)Tr(Wbar_old Q_old(s)). All early powers and actual grids remain.
The boundary values rho(Lnew)=0, rho(0)=2Tr(Wbar_new) and continuity at L
are correct. Hilbert-coordinate formula retains the nonzero interface
h_old(j)/(pi(j-k)); padding h is not padding its commutator.
The proposed trace Hessian has nonnegative curvature; no cost is deleted.

## Remaining sufficient estimate and next action

For arbitrarily large fixed even p, prove
Omega<=Zold/(p m)+u_(p,m) Zold/p with nonnegative summable u.
This would give coefficient4/m independent of p and hence SP. It remains
OPEN. Retaining the full background credit Gamma is a weaker sufficient
interface than retaining only L/64 mass. No necessity is asserted.
ZF78 currently supplies only Z_p<<m^(1+(3/8+eps)p), not a uniform exponent.

Next own attempt: keep the exact adaptive prime-pole contraction and full
background credit together; test whether spectral commutation supplies an
actual signed constraint before another Pro question. Do not re-import the
entrywise graph moments, discard h-padding interfaces, or count a rewrite
of the original endpoint moment increment as a gain. The normalization
followup in FULL_CCM_MOMENT_SCHEDULE.md is independently checked and was
written after dispatch; not part of the sent attachment.
