# Own attempt: finite hyperbolic aspect primitives

PAPER derivation, independently checked once by answer10_pair_audit, no
correction found in endpoints, Jacobian, logarithmic sectors or ODE.
Input: rollover Q4, exact
double-interior formula (14)/(27). No signed bound or SP claim.

For one positive index tuple h,d,k,ell and r=k*ell/(d*h), fix x>0 and
put A=sqrt(2*pi^2*r*x), u_c=A/(pi*k), a_c=h*A/(2*pi*ell).
Then u=u_c*exp(v), a=a_c*exp(-v), a_c*d*u_c=x.
The Jacobian of (x,v)->(z,w) has absolute value 2*pi^2*r.
Consequently its product with (2*pi^2*r)^(s-1)*(zw)^(-s) is x^(-s).

The exact base aspect interval has lower bound

    alpha=max(log(a_c/A0), log(1/u_c), log(U/(d*u_c)))
    beta=log(a_c/U).

The first and third lower constraints are strict; the second is inclusive.
The upper constraint is strict. At a tie, enforce all original inequalities.
Empty intervals contribute zero. Singleton aspect sets have zero Lebesgue
integral here; prescribed atomic values belong to Q4's separate boundary
operations and must not be erased there.

For the short sector intersect this interval with v<=log(V/u_c); its
amplitude is log(u_c)+v. For the long sector intersect with
v>log(V/u_c); its amplitude is -log(d). The baseline d=1 has amplitude
-2 on the base interval. The common product restriction remains Y0<=x<=y.
All these intervals are finite for every fixed tuple and x.

Define, for signs eps,delta in {+1,-1},

    Q(v)=eps*exp(v)+delta*exp(-v),
    J_j(A;alpha,beta)=int_alpha^beta v^j exp(i*A*Q(v)) dv, j=0,1.

Thus each short aspect term is log(u_c)*J_0+J_1, each long term
is -log(d)*J_0, and each baseline term is -2*J_0, with exactly the
mu(h)/(d*h), mu(d), and (-1)^k weights in Q4's grouped coefficient.
This evaluates the logarithmic structure into two finite primitives; it
does not estimate their complete weighted sum.

There is a precise boundary-forced Bessel-type relation. With alpha,beta
held FIXED under A differentiation, write

    L_A=A^2*d_A^2+A*d_A+4*eps*delta*A^2,
    F(A,v)=exp(i*A*Q(v)).

Since Q''=Q and (Q')^2=Q^2-4*eps*delta, L_A F=d_v^2 F.
Finite integration by parts therefore gives exactly

    L_A J_0 = [d_v F]_alpha^beta,
    L_A J_1 = [v*d_v F-F]_alpha^beta.

These are partial-derivative identities for independent A,alpha,beta.
The actual endpoints depend on A and switch among the displayed branches;
total differentiation requires their chain-rule terms. The factor
log(u_c) also depends on A. Hence a homogeneous full-Bessel equation is
not available by simply replacing the finite primitives with a named
whole-line special function. No asymptotic remainder has been introduced.

Summing the four sign quadrants before estimates gives the exact real kernel

    sum_(eps,delta) exp(i*A*(eps*exp(v)+delta*exp(-v)))
      =4*cos(A*exp(v))*cos(A*exp(-v)).

The common x^(-it) factor remains; this identity is not positivity.
The next bounded test is to combine these finite boundary primitives with
Q4's zero-first-alias term Z, both boundary operations B, and D_U before
estimating the signed aggregate. Q4's small analytic tails remain separate;
Delta10 and the actual norm(J_r v) remain in the Schur return.
