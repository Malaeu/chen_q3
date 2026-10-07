# Own attempt: two source actions from finite Cauchy columns

PAPER own derivation, one bounded independent pass by causal_algebra_audit
confirmed row conjugation, both H actions, anchors and projector feedback. This is input to one bounded
source-cancellation test, not a new sign or estimate. H=H_m(0) throughout.
Read source rows directly in rollover pack lines2161–2169,2373–2382.

## Exact endpoint/conjugation map

Set kappa=2pi/L, D=diag(j), u_j=1, h_j=Im Phi(omega_j;m),
R_z=(zI-D)^-1. For the actual Mellin row a_w,j=2sinh(wL/2)/
[sqrt(L)(w+i*kappa*j)], define

    z_w=conj(w)/(i*kappa),
    t_w=2sinh(conj(w)*L/2)/(i*kappa*sqrt(L)).

Then a_w^*=t_w R_{z_w}u as a column, exactly. Thus column w of
C=L0* is sqrt(r_w/2)*(t_w R_{z_w}u-t_{wdagger}R_{z_wdagger}u).
Both endpoints and conjugation are retained; the actual off-line rows
have nonreal z, so the finite diagonal resolvents exist. No invented zero
or asymptotic row replacement is used.

## Two H actions with explicit anchors

Let A=Hu, Hh=H h, A2=H²u (A is an anchor vector, not a regular block).
For any f,

    H R_z f = R_z Hf
       +(u*R_z f)R_z h/pi -(h*R_z f)R_z u/pi.

This follows from [D,H]=(u h*-h u*)/pi and
[H,R_z]=-R_z[D,H]R_z. Set
s_z=u*R_z u/pi, t_z=h*R_z u/pi. Then

    X_z=H R_z u=R_z A+s_z R_z h-t_z R_z u,
    Y_z=H²R_z u
       =R_z A2+(u*R_z A)R_z h/pi-(h*R_z A)R_z u/pi
        +s_z*(R_z Hh+(u*R_z h)R_z h/pi-(h*R_z h)R_z u/pi)
        -t_z*X_z.

Apply the SAME endpoint paired combination to X_z and Y_z to obtain
U=H C and V=H² C. No moment higher than four is introduced.
The unprojected anchors have explicit full-source coordinates
A_j=a(omega_j)-d_j-(1/pi)sum_(k!=j)(h_j-h_k)/(j-k),
(Hh)_j=(a(omega_j)-d_j)h_j
 -(1/pi)sum_(k!=j)(h_j-h_k)h_k/(j-k), and A2=H A.
The same signed primitive defines d and h; separate absolute estimates
lose exactly the correlations being sought.

## Keep the projector before testing the covariance

Let I=(C*C)^dagger, Q=C I C*, Pi=I_carrier-Q. For v=C z,

    b=Pi U z,
    w=Pi*(V-U I C*U)z = Pi H b,
    q0=z*C*U z, N=z*C*C z,
    M=||b||², d3=<b,w>, d4=||w||²,
    c=d3+epsilon M, e=d4+2epsilon d3+epsilon²M.

The feedback term U I C*U cannot be dropped. These expressions compute
exactly the existing projected D2,D3,D4, not the unprojected A2,A3,A4.
All seven signed pieces of H are already inside A,Hh,A2,U,V.

## What the own attempt does not achieve

Substitution alone leaves joint anchor correlations in A,Hh,A2, evaluated
at paired actual zero parameters and with the same projector feedback.
No bound for that combined expression has been obtained here. Norm bounds
on those anchors reproduce the old full-source envelope and do not prove
an all-eta shift. Thus this algebraic setup is not claimed as progress in
SP or as a source obstruction. The bounded follow-up must test a genuine
cancellation in these exact anchors, stop if none is found, and retain the
separate q>=0 test on ker(B) intersect E.
