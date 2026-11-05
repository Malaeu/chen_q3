# Intake of the coupled-source flux test

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; SCOPED_LOCAL_METRIC_AND_MIXED_FLUX_OBSTRUCTIONS_ONLY.
Date: 2026-09-16. Isolated analytic research only.
Raw response commit: 4a4575555554947d3db865819ee74652f9ec7639.
Path: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_COUPLEDFLUX_2026-09-16.md.
SHA256: 258fe6d40ab6b92b4c7a5645fb75ad5dadecd7848a7567e18c0553a65b28b0c4.
Full read: 55102 bytes, 611 LF, UTF-8, no CR, final LF. The raw file is unchanged.
Request REQ-2026-09-16-COUPLEDFLUX at
5b4a75973184495c4a33417f4aac8b664d3a9a34 and its context hash were locally
reverified. Only the assigned response was added in the received commit.

## The exact consumer remains unchanged

The target is A^2 V[c]=-E_c'(0)/2 for every finite complex row with nodes
in I=(-log(2)/2,0), where A=||Phi_2||_2 and

 U_(alpha,k)(X)=sum c_i exp[-2k(X+x_i)]Phi_alpha(X+x_i),
 E_c(k)=int_0^infinity |U_(2,k)(X)|^2 dX.

The full source uses r_alpha=r_2 convolved alpha/2 times and
Phi_alpha(x)=exp(5x/2)r_alpha(exp(2x)). Only Phi_2 is assumed even.
This test neither changed V nor established a negative V witness.

## Parent reproduction of the exact flux

Set u_alpha=U_(alpha,0), v_alpha=U_(alpha,1), and
z_alpha=-partial_k U_(alpha,k)|_0/2,
w_alpha=-partial_k U_(alpha,k+1)|_0/2.
All four fields are made from the same row. With
P_alpha=(D+alpha)^2-1/4, Q=D-1/2,
a_alpha=alpha(alpha+1), b_alpha=alpha^2*pi/2, direct differentiation gives

 a_alpha z_(alpha+2)
 =P_alpha z_alpha-b_alpha Qw_alpha-2(D+alpha)u_alpha+b_alpha v_alpha.

The terms -2(D+alpha)u and +b_alpha v are necessary. Integrating the
undifferentiated equation and applying -partial_k/2 gives, at alpha=2,

 (15/4)A^2 V[c]
 =4 E_2+A_2+T_2-|u_2(0)|^2+6 R_24+2pi S_2.                 (I1)

Here E_2=||u_2||^2 and all remaining symbols are the literal signed forms
in raw CF10: A_2=2 Re<u_2',z_2'>;
T_2=Re[conj(z_2)u_2'+conj(u_2)z_2'](0)
      +4 Re[conj(u_2)z_2](0);
R_24=Re[<z_2,u_4>+<u_2,z_4>];
S_2=Re[<z_2,Qv_2>+<u_2,Qw_2>-<u_2,v_2>].
Inner products conjugate the first argument. In particular the last
negative term in S_2 is retained. The raw CF14 also exposes its trace.

The alpha=4 balance has coefficients 63/4,8,20,8pi and the new mixed pair
R_46, not an opposite copy of R_24. Merely using that equation does not
close I1. Both balances keep the original physical norm and X=0 traces.

For fixed l, C_l=sup exp(pi t)|r_2^(l)(t)|/t is finite by the complete
theta tails and reciprocity. Flat endpoints and exact convolution imply

 |r_(2n)^(l)(t)| <= C_l C_0^(n-1) t^(2n-1)exp(-pi t)/Gamma(2n).

This pays all displayed operations for each fixed finite row, alpha and
compact k interval. No bound uniform over infinitely many alpha is claimed.

Our separate Green preflight G1-G7 used an antisymmetric pairing with a
weighted scalar product. The response differentiates an unweighted norm
identity instead. These are compatible distinct identities; one must not
identify their different traces or interpret either as a proved sign.

## The precisely excluded positive metric

The actual gauge Y_(alpha,k)=exp((alpha+2k)X)U_(alpha,k) gives the block

 L_tilde=(D^2-1/4)I_2-6exp(-2X)N,  N=[[0,1],[0,0]].

All original right-hand forcings remain present. For formal self-adjointness
on arbitrary compactly supported two-component test functions in a C^2
local Hermitian weight H(X), coefficient comparison forces

 H'=0, HN=N*H.

Writing H=[[a,b],[conj(b),d]], the second relation forces a=0 and real b.
Hence H cannot be positive definite. If H is positive semidefinite, b=0,
and precisely H=diag(0,d), constant d>=0, remains. It erases the alpha=2
source component (the first vector component), which carries V.
A boundary form cannot repair this formal-adjoint obstruction on interior
compactly supported tests. No density of actual source rows in the whole
test-function space is presumed; source-restricted or nonlocal identities
are not excluded by this theorem.

The physical norm is still
E_c(k)=int exp(-(4+4k)X)|Y_(2,k)[c]|^2 dX.
The gauge satisfies Y_(alpha,k)[c]=Y_(alpha,0)[diag(exp(-2kx_i))c].
Thus removing k from the differential coefficients does not turn k into a
proved dissipative time or remove the derivative of the coefficient row.

## A negative mixed contribution on actual source rows

The exact R_24 kernel is

 C_24(x,y)=(1/2)int_0^infinity(2X+x+y)
  [Phi_2(X+x)Phi_4(X+y)+Phi_4(X+x)Phi_2(X+y)]dX.

The parent independently recovered the full Gamma-tail comparison

 0<=1-r_alpha(t)/(c_alpha t^(alpha-1)exp(-pi t))<=d_alpha/t,
 c_alpha=(2pi)^alpha/Gamma(alpha),
 d_alpha=3alpha(alpha-1)/(4pi),

by keeping the entire n>=2 source remainder. It yields
Phi_4(s)/Phi_2(s)~(2pi^2/3)exp(4s).
For fixed d and x=R,y=R+d, endpoint Laplace scaling with
lambda=2pi(exp(2x)+exp(2y)) gives the normalized mixed correlation

 C_24(R,R+d)/sqrt(C_24(R,R)C_24(R+d,R+d))
       -> cosh(2d)/cosh(d).                                (I2)

The source ratio supplies cosh(2d); the normalized overlap supplies
1/cosh(d); the remaining (x+y)/(2sqrt(xy)) tends to one. The full-source
majorant 4exp(-v/2), also integrable after multiplication by v, pays the
scaling limit. For d=log(2), I2 is 17/10>1. A normalized difference of
these two positive-diagonal columns therefore has R_24<=-1 for sufficiently
large R. These two nodes are positive and are not falsely placed in I.

The complex convolution for r_4 and the reciprocal small-end bound for r_2
give joint holomorphy of C_24 on Omega x Omega, |Im z|<pi/4. The accepted
all-rank analytic propagation argument then implies a negative finite row
on every nonempty open real interval, including I. This proves existence,
with no bound on the rank in I and no common row with other negative forms.

This refutes automatic nonnegativity of R_24, not of the full right side
of I1. Other terms of I1 can compensate its negative contribution.

## Decision and next return point

The local positive multiplication-metric ansatz is closed in its named scope.
Increasing alpha or assuming the next mixed term positive is not a next step.
I1 alone is the original unknown sign rewritten, not a cheaper supplier.
The full V sign, original negative witness and RH remain open.

Before selecting a different mechanism, return to the exact obstruction:
one-way coupling, the image of the original row map, its physical norm and
its nonzero trace. A semantic search may compare nonlocal symmetrization,
operator Sylvester/transmutation methods and boundary-aware source-image
energy identities. A candidate must explicitly preserve the physical flux;
diagonalizing a formal differential expression is insufficient. This is a
search criterion, not a selected new positive construction or dispatch.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The tested positive local metric cannot retain the original flux; the full signed identity still has the original unpaid sign.

No RH, full-V, Lean or canonical admission claim is made.

## Independent acceptance

Complete response review SHA256: `04f6f6ed87cf04291f11dd1b4c7dc0a908012bb9484a2ba32bf9e6eb8e506f8f`.
Complete intake candidate SHA256: `ea6c63d0c43baf23e47a26fb8a58c6a2222503d33081189837fe01f3e3ae882c`;
CLEAN_INTAKE review SHA256: `1bef38d9938a62ab40ca93606dcba13fcee101f23b249b444994f377b6deae55`.
Reviewer `/root/sibling5_check` independently checked both exact payloads.
Only the status line and this receipt were added after intake review.
The parent independently reproduced the flux, matrix obstruction, full-tail
correlation and analytic propagation, preserving all scopes.
