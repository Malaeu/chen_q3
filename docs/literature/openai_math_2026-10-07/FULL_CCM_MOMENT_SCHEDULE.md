# Full CCM negative moments: exact schedule receiver

2026-10-07. PAPER algebra; SP and RH OPEN. Source: literal entries in
`CCMFiniteWeilSourceMatrixN1.lean:40–104`, full mode family in
`CCMFiniteWeilSourceMatrix.lean`. External mechanism candidate:
`linux_needle_scan/REPORT.md`, Ramanujan manuscript `early.tex:1030–1068,1310–1325`.
The external random-pairing drift estimate is not established for CCM.

## Keep the actual schedule

Let K_N(L) use all modes -N,...,N, the literal archimedean terms and all
prime powers q<=exp(L). Production K_m=K_m(log m), m>=2. For p>=2 set
M_p(H)=Tr(H_-^p). The scalar function (-x)_+^p is convex C1 and
its matrix trace derivative is -p Tr(H_-^(p-1) H').

At L=log(m+1), reorder the full next matrix as H=[[A,B],[B*,C]],
where A=K_m(log(m+1)) and C contains the two new modes ±(m+1).
Define G_p=M_p(H)-M_p(A)-M_p(C). Pinching with U=diag(I,-I)
and trace convexity gives G_p>=0. With E_B=[[0,B],[B*,0]],
H_t=diag(A,C)+t E_B, the exact identity is

    G_p = -p integral_0^1 Tr((H_t)_-^(p-1) E_B) dt.

Consequently the actual schedule increment equals

    M_p(K_(m+1))-M_p(K_m)
      = -p integral_log(m)^log(m+1)
             Tr(K_m(L)_-^(p-1) K_m'(L)) dL
        + M_p(C) + G_p(A,B,C).

The integral includes motion of every old entry. The two nonnegative terms
cannot be discarded for an upper bound. A=C=0 with rank-one B of norm R
has G_p=R^p; reflection-even B is possible. This rejects rank/reflection-only
smallness, not a bound using the actual arithmetic CCM entries.

## Prime-power events and proposed second account

At L=log q the new prime atom has value zero, hence K_N is continuous.
Differentiating the literal q-kernel gives the derivative jump

    [K_N'] = -alpha_q vv*,  alpha_q=2 Lambda(q)/(log(q) sqrt(q)), v=1.
    [M_p'] = alpha_q p v* K_N_-^(p-1) v >= 0.

The path is piecewise C1 and the moment absolutely continuous on compact
positive-L intervals. These are slope jumps, not atoms in M_p: do not add
another jump term to the schedule integral. Zero eigenvalue crossings also
produce no jump in M_p.

For even p>=4 consider Q_p=v*g(K_N)v, g(x)=(-x)_+^(p-1).
At the same event, in an eigenbasis of K_N,

    [Q_p'] = -alpha_q sum_(i,j) g[lambda_i,lambda_j] |v_i|² |v_j|² >= 0.

The divided difference of decreasing g is nonpositive; at a repeated
eigenvalue use g'(lambda)<=0. Thus a positive multiple of Q_p does not cancel
prime-event slope jumps in M_p+kappa Q_p. This says nothing about the sign
of smooth motion or total increments; it is not a global no-go.

## Exact missing import

A sufficient coupled estimate would be Z_p(m)=1+M_p(K_m)+kappa_p D_p(m),
D_p>=0, with

    Z_p(m+1) <= (1+C_star/m+u_(p,m)) Z_p(m),
    u_(p,m)>=0, sum_m u_(p,m)<infinity,

for arbitrarily large fixed even p, with C_star independent of p.
It implies M_p(K_m)<=C_p m^C_star, hence
lambda_min(K_m)>=-C_p^(1/p) m^(C_star/p), which gives SP by choosing p.
A finite p-dependent starting index is harmless. Dependence of C_star on p
is not harmless. The external paper supplies this architecture in its own
random process; no CCM D_p or full drift bound has yet been supplied.
Any proposed import must pay the displayed old-block integral AND new-mode
terms together. Q_p alone has no automatic local jump cancellation.

Verification: root derivation plus read-only independent algebra audit by
squarefree_conductor_check: schedule normalization/endpoints PASS; companion
divided-difference identity PASS. No Lean formalization or SP admission claimed.
