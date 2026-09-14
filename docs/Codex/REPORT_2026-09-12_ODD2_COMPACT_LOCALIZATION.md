# ODD2: the small-node tail and compact localization

Status: ACCEPT_COMPACT_LOCALIZATION_ODD2_OUTSIDE_EXISTENTIAL_SQUARE.
Author: parent mathematical task. PAPER scope only; no canonical admission.
Consumer: exclude actual ODD2 negative witnesses outside one bounded square,
including the regime where one positive node approaches zero.
All constants below are exact source-defined finite quantities; no numeric
value of the final square size is claimed.

## Dependencies

Unchanged theta f, full V, odd kernel K and normalization A are inherited
from the accepted ODDCURV response, SHA256
3309c6fb3f5c3a0e20979c14b9a36471e753feed18a42017b4f211fafe6ea840.
Its equations (17)-(19) supply the exact U,W,I representation used below.
Full-source derivative decay and OD1, K(s,t)>0 for s,t>0, are accepted.
The imported strict pointwise source inequality J_f>0 is documented with
its exact normalization in SLACK_INDEPENDENT_CHECK_2026-09-11.md section4,
SHA256 14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc.
It is Csordas 1309.0055 Remark4.3(a), not an inference of strict second
derivatives from abstract strict concavity.

The regional diagonal estimate is K(x,x)>=x f(x)^2/(8 alpha_x), x>=4,
alpha_x=pi exp(2x), accepted with the min4/gap4 theorem in response SHA256
2281280161631905987633e895c34e980470bbeda517e3bc4c1df2ce2d0e9833.
The independently accepted REPORT_2026-09-12_ODD2_JOINT_TAIL.md, final SHA256
2643695929014d3c7bab32aa05c1e560aa91328a909963f5741346727e1d0fb6,
commit4a9b84c335174b03b64ca754290b0c5954be5deb, proves ODD2 for all
x,y>=one finite S0>=4. These dependencies are not reproved here.

## 1. The diagonal has a strictly positive quadratic coefficient at zero

The even smooth f and its derivative tails make V,K smooth on all real
nodes. V is symmetric and satisfies V(-s,-t)=V(s,t). To see the latter,
the integrand (s+t+2u)f(s+u)f(t+u) is odd about u=-(s+t)/2 and absolutely
integrable on the real line; its integral is zero. Substitute u=-v in
V(-s,-t). Consequently K is symmetric and odd in each coordinate, and
K(s,0)=K(0,t)=0.

From the exact mixed-derivative formula for V,

    V_st(0,0)=integral_0^infinity [2 f f'+2v f'^2] dv
             =-f(0)^2+2 integral_0^infinity v f'(v)^2 dv.

Reflection gives K_st(0,0)=2 V_st(0,0). Define kappa=K_st(0,0). The
accepted source inequality is

    J_f(v)=v[f'(v)^2-f(v)f''(v)]+f(v)f'(v)>0,  v>0.

Integration by parts has zero boundary term v f(v)f'(v) at both ends.
Since integral f f'=-f(0)^2/2, it gives

    integral_0^infinity J_f(v) dv
       =2 integral_0^infinity v f'(v)^2 dv-f(0)^2,
    kappa=2 integral_0^infinity J_f(v) dv>0.                 (1)

All integrals are absolutely convergent by the full-source derivative
bounds. The integral of J_f is strictly positive because J_f is continuous
and strictly positive on every positive finite subinterval.

Smoothness, the zero axes and K_st(0,0)=kappa imply

    K(y,y)=kappa y^2+o(y^2),  y->0.                        (2)

Fix any B>0. Extend K(y,y)/(y^2 f(y)^2) continuously at zero by
kappa/f(0)^2. It is strictly positive everywhere on [0,B], by (1) at
zero and by OD1 elsewhere. Its attained minimum

    mu_B=min_{0<=y<=B} K(y,y)/(y^2 f(y)^2)>0              (3)

is therefore finite and positive, using the stated endpoint convention.
In particular K(y,y)>=mu_B y^2 f(y)^2 for 0<y<=B. This does not assume
the two-node determinant sign; only the already proved positive entries
and the new coefficient (1) are used.

## 2. A full mixed-entry bound uniform down to the axis

Use the exact ODDCURV U,W of equations (18), with v(z)=log(1+z)/2:

    U(y,z)=(1+z)^(5/4)[f(y+v)-f(y-v)]/[2f(y)],
    W(y,z)=(1+z)^(5/4)[(y+2v)f(y+v)+(y-2v)f(y-v)]/[2f(y)].

Both are smooth and odd in y. Define Ubar=U/y and Wbar=W/y, extended at
y=0 by their y derivatives. Explicitly these quotients equal the integrals
from 0 to1 of U_y(theta y,z), W_y(theta y,z), respectively. This formula
and the full derivative tails prove smoothness and uniform bounds at the
axis, without dividing an estimate by a vanishing y.

At z=0, Ubar(y,0)=0 and Wbar(y,0)=1 on the whole interval [0,B]. Set

    L_B=1+sup_{0<=y<=B,z>=0}
                    (|partial_z Ubar|+|partial_z Wbar|).   (4)

This is finite. For bounded z use smoothness and min_[0,B] f>0. For large
z, |theta y +/- v(z)|>=v(z)-B uniformly in theta,y. The accepted source
bound on every fixed derivative then gives O(exp(-c_B(1+z))) for the
needed f derivatives. The remaining factors are powers/logarithms of
1+z and bounded reciprocal powers of f(theta y), while partial_z adds
factors (1+z)^-1. Thus the differentiated quotients in (4) tend uniformly
to zero at infinity. The definition of L_B contains no unknown K sign.

For x>=1, P=xU+W satisfies, on 0<y<=B,

    |P(x,y,z)/y|<=1+L_B(x+1)z.                            (5)

The exact full integral is

    K(x,y)/(f(x)f(y)y)
       =1/H(alpha_x) integral_0^infinity exp(-alpha_x z)
                 H(alpha_x(1+z)) [P(x,y,z)/y] dz.          (6)

For alpha_x>=100 the accepted full-source bounds are
197/200<=H(alpha_x)<=1 and 0<H(alpha_x(1+z))<=1. Therefore (5)-(6) give

    0<K(x,y)/(f(x)f(y)y)
      <=(200/197)[1/alpha_x+L_B(x+1)/alpha_x^2].           (7)

If alpha_x>=2L_B(x+1), this is at most
300/(197 alpha_x)<2/alpha_x. Positivity in (7) uses OD1; the upper bound
uses absolute values inside the entire integral, so discards neither a
reflected part nor any tail.

## 3. Strict ODD2 on the entire small-node tail

Choose an integer X_B>=max(4,B) satisfying

    alpha_{X_B}>=max(100,2L_B(X_B+1)),
    X_B alpha_{X_B}>=64/mu_B.                             (8)

Such an integer exists by exponential growth. Since alpha_x/(x+1) and
x alpha_x are increasing for x>=1, the same inequalities hold for all
x>=X_B. The diagonal lower bounds and (7) now imply, for 0<y<=B,

    Delta(x,y)=K(x,x)K(y,y)-K(x,y)^2
      >=y^2 f(x)^2 f(y)^2 [x mu_B/(8alpha_x)-4/alpha_x^2]
      >=x mu_B y^2 f(x)^2 f(y)^2/(16alpha_x)>0.            (9)

To avoid a spurious diagonal contradiction, X_B may and will be chosen
strictly larger than B. Then every pair in (9) has x>y. Positive diagonal
and (9) give actual PSD on all complex two-node coefficients. Its original
four-node odd V form is exactly twice that form, as in the accepted source
transfer. No higher-rank conclusion follows from this statement.

## 4. Localization of every possible ODD2 negative witness

Take B=S0 from the accepted joint-tail theorem, and choose X_B>B using
(8). Put L=X_B. If max(x,y)>=L, use symmetry to take x>=L. If y>=S0,
the joint-tail ODD2 theorem applies. If 0<y<=S0, equation (9) applies.
Consequently

    Delta(x,y)>=0 whenever x,y>0 and max(x,y)>=L.           (10)

Thus any actual negative ODD2 witness must have both nodes in (0,L).
The unresolved set is bounded; its closure is a compact square. This does
not assert a finite certificate exists, establish positivity inside the
square, remove its diagonal/axis degeneracies, or compute L. It does not
localize witnesses for arbitrary matrix sizes or the full Weil form.

Proposed delta: the previous all-large-pairs family omitted an unbounded
region with one node small. Equation (9) covers that region uniformly down
to the axis, and (10) excludes every ODD2 negative witness at infinity.
The exact unproved consumer is now the determinant sign for 0<x,y<L.

## Acceptance receipt

The sole read-only independent checker /root/sibling5_check accepted the
complete 162-line, 7318-byte candidate with SHA256
d37e25b249e3f725025b8baf3e0f30ca6c360956c4c95d2f9374b692c7892258.
Its mathematical content is unchanged; only status and this receipt were
added. The parent separately rechecked K parity, both integrations by parts,
the positive endpoint quotient, the smooth U/y and W/y extensions, the
entire integral upper bound, the factor64 determinant threshold and the
cover of every pair with max(x,y)>=L. Reviewer and author are distinct.

Accepted scope: (1)-(10) and compact localization of possible actual ODD2
negative witnesses, with the displayed complex-coefficient interpretation.
The finite L is not evaluated. No assertion is made that ODD2 is positive
inside the remaining square, that finitely many evaluations decide it, or
that this localizes higher-rank/full-Weil-form witnesses. RH remains open.
