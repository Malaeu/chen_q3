# Own source check while Q6 is running

PAPER own derivation; one bounded independent pass by answer10_pair_audit
confirmed the source algebra. Q6 final answer not yet received.
Input read directly: HIGH_ZERO_TAIL_AUDIT_2026-10-06.md, lines37–44.
H0 >= G_low-L0*L0-epsilon I on the original complete carrier.
Therefore P=H0+epsilon I+L0*L0 >= G_low >=0.
In the fixed R=ker L0, E=R-perp splitting, its blocks are

    P = [ T, B ; B*, D0+epsilon I_E+(L0*L0)|E ].

This retains the actual full H0; no arithmetic component is dropped.
For v in E, b=Bv, define p=<v,(D0+epsilon I+L0*L0)v>
=q0+epsilon N+||L0v||². Positivity of P on span{(b,0),(0,v)}
gives the positive two-by-two Gram matrix [c,M;M,p], hence

    p>=0, c>=0, M²<=c*p.

If b!=0, M>0, so c>0 and Tb!=0. Thus the formal Tb=0,b!=0
degeneracy in the generic moment test is impossible for this actual source.
This does not control the size of p relative to ||L0v||² or prove the sign.

For b!=0 let w=c²/e and a=M-w (e>0). Cauchy–Schwarz gives
0<w<=M, a>=0. Direct partial fractions of the already checked L3 give

    L3 = q - a/g - w/(g+e/c).

In particular the source certificate L3>=0 requires q>=a/g;
this is necessary only, while the exact requirement is
q>=a/g+w/(g+e/c). Its nonnegative variance mass a cannot be discarded. This is an identity
on the actual moments, not a claim that a has any stated asymptotic size.
The source Gram estimate above bounds M² by c*p but supplies no smallness
of a=M-c²/e. No hypothetical moment distribution is a source obstruction.
A useful Q6 result must control these actual quantities, not only their
nonnegativity. No new SP or Schur sign follows here.
