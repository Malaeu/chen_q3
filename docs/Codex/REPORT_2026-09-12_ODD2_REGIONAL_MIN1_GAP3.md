# Actual theta ODD2 for min >= 1 and gap >= 3

Status: ACCEPT_REGIONAL_MIN1_GAP3_ALL_COMPLEX_ONLY.
Author: parent mathematical task. No Lean certification, canonical admission,
global IC, full ODD2, higher odd/even positivity or RH claim.
Consumer: all complex two-node odd coefficients on the stated infinite region.
Base own-branch commit: a0d5124a0802e480ac443546e83c5fb7c88620ef.

## Source and exact claim

The source, normalization and full-integral identities are those in
REPORT_2026-09-12_ODD2_JOINT_TAIL.md, SHA256
2643695929014d3c7bab32aa05c1e560aa91328a909963f5741346727e1d0fb6.
We use its equations (1), (2), (7)-(9) as exact identities, not asymptotics.
In particular f=Phi/A is unchanged, A=||Phi||_2, and

    V(x,y)=integral_0^infinity (x+y+2v) f(x+v)f(y+v) dv,
    K(x,y)=V(x,y)-V(x,-y),
    Delta(x,y)=K(x,x)K(y,y)-K(x,y)^2,
    alpha_z=pi exp(2z).

Accepted OD1 gives K(x,y)>0 for x,y>0. K is real symmetric.
For x>=y>=1 with d=x-y>=3, the new claim is

    Delta(x,y) >= xy f(x)^2 f(y)^2 / (216 alpha_x alpha_y).    (T1)

For every c1,c2 in C, the associated Hermitian form satisfies

    c* K_2 c >= xy / [324 (x alpha_y+y alpha_x)]
                  * (f(x)^2 |c1|^2+f(y)^2 |c2|^2).           (T2)

Symmetry gives the same statement for min(x,y)>=1 and |x-y|>=3.
The original V form on (x,y,-x,-y), with coefficients
(c1,c2,-c1,-c2), is exactly twice c* K_2 c by the accepted odd assembly.
The previous explicit regional theorem required min>=4 and gap>=4;
(T1)-(T2) enlarge its domain, with their own conservative constants.

## 1. A bound on the complete H for every positive argument

The full theta source has the exact representation, for every real z,

    f(z)=(4pi^2/A) exp(9z/2-q) H(q),  q=pi exp(2z),
    H(q)=sum_{n>=1} (n^4-3n^2/(2q)) exp(-(n^2-1)q),
    H(q)=(pi/q)^(9/2) exp(q-pi^2/q) H(pi^2/q).               (1)

We prove

    0<H(q)<=1              for every q>0,
    H(q)>=1-3/(2q)         for q>=pi.                       (2)

For q>=pi>3 all summands in (1) are positive. The n=1 term gives
the lower bound. Put zeta=exp(-3q); then zeta<1/4096, since
e^3>16. For n>=2, n^2-1>=3(n-1), so the remaining sum E obeys

    E=H(q)-1+3/(2q)
       <= sum_{n>=2} n^4 zeta^(n-1)
       <= 16 zeta / (1-81 zeta/16)
       <= 17 zeta.                                        (3)

The ratio bound in the middle follows from
((n+1)/n)^4 zeta <= (3/2)^4 zeta for n>=2.
The last inequality holds for zeta<=16/1377, in particular zeta<1/4096.
The function q exp(-3q) decreases for q>=3; therefore

    17 q exp(-3q) <= 51 exp(-9) < 51/4096 < 3/2.

Consequently E<3/(2q) and H(q)<1 for q>=pi.
For 0<q<=pi, put u=log(q/pi)<=0. The logarithm of the positive
reciprocity prefactor in (1) is

    -(9/2)u+2pi sinh(u).

Its derivative is -9/2+2pi cosh(u)>0 and its value at u=0 is zero.
Thus the prefactor is at most one; pi^2/q>=pi proves (2) on this
remaining range as well. In particular no small-q reflected tail is omitted.

For a node z>=1, alpha_z=pi e^(2z)>21, using pi>3 and
e>8/3 (hence e^2>7). Equation (2) then gives

    H(q)>=13/14       whenever q>=alpha_z.                  (4)

## 2. Diagonal lower bound with the entire reflected integral

Fix z>=1 and alpha=alpha_z. For c>=1 define

    w=arcosh(c),
    B_alpha(c)=H(alpha exp(w))H(alpha exp(-w)),
    phi(c)=w/sinh(w),  phi(1)=1.

Equation (2) gives 0<B_alpha(c)<=1; also 0<phi(c)<=1.
Specializing the exact source identity (9) of the joint-tail report to
m=z and c=1 gives, with a fresh integration variable u,

    K(z,z)/f(z)^2 = 1/H(alpha)^2 * integral_0^infinity exp(-2alpha u)
       * { [z+log(1+u)/2](1+u)^(7/2) H(alpha(1+u))^2
                             - phi(1+u)B_alpha(1+u)/2 } du. (5)

This is an exact equality. In particular its second term includes the
whole reflected integration range, even when alpha exp(-w) becomes small.
By (4), the positive term in braces is at least z(13/14)^2.
The subtracted term is at most 1/2. Since z>=1,

    z(13/14)^2-1/2 >= z[(13/14)^2-1/2]
                    = (71/196)z > z/3.

The prefactor 1/H(alpha)^2>=1 is positive. Integrating the resulting
positive lower bound over the complete half-line proves

    K(z,z)/f(z)^2 >= z/(6 alpha_z)       (z>=1).             (6)

## 3. Mixed upper bound on the full source

Let x>=y>=1. The integrand defining V(x,-y) is nonnegative since
x-y+2v>=0, so the accepted OD1 and the exact subtraction give
0<K(x,y)<=V(x,y). With u=exp(2v)-1, the full source (1)-(4) gives

    f(z+v)/f(z) <= (14/13)(1+u)^(9/4) exp(-alpha_z u),
                                                 z>=1,v>=0.

Writing B=alpha_x+alpha_y (unrelated to the normalization A), the exact
Jacobian dv=du/[2(1+u)] yields

    V(x,y)/(f(x)f(y)) <= (98/169) integral_0^infinity
       (x+y+log(1+u))(1+u)^(7/2) exp(-B u) du.              (7)

Use log(1+u)<=u and (1+u)^(7/2)<=exp(7u/2), and put beta=B-7/2.
Because alpha_x>21, beta>=5alpha_x/6>0. Hence (7) is at most

    (98/169)[(x+y)/beta+1/beta^2]
      <= (98/169)[(12/5)x/alpha_x+36/(25 alpha_x^2)]
      <= (98/169)[12/5+36/(25*21)] x/alpha_x
       = (6048/4225) x/alpha_x
       < (3/2)x/alpha_x.                                  (8)

Here x+y<=2x and x>=1 were used; every integral is over the full half-line.
Thus

    0<K(x,y)/(f(x)f(y)) <= 3x/(2alpha_x),   x>=y>=1.        (9)

This estimate also applies at x=y, giving a diagonal upper bound.

## 4. Determinant and all complex coefficients

Let M_ij=K(z_i,z_j)/(f(z_i)f(z_j)) for z_1=x,z_2=y.
The bounds (6) and (9) imply

    det M >= xy/(36alpha_x alpha_y)
                      * [1-81(x/y)exp(-2d)],  d=x-y.       (10)

For d>=3 and y>=1, x/y=1+d/y<=1+d.
The function (1+d)exp(-2d) decreases for d>=3, so it is at most 4e^-6.
The elementary exponential series gives

    e > sum_{j=0}^5 1/j! =163/60 >19/7,
    324e^-6 <324(7/19)^6
            =38118276/47045881 <5/6.

Thus the bracket in (10) is greater than 1/6, giving

    det M >= xy/(216alpha_x alpha_y)>0.                    (11)

Both diagonal entries are positive by (6); hence M is positive definite.
Its trace is at most (3/2)(x/alpha_x+y/alpha_y) by (9).
For its positive eigenvalues lambda_min<=lambda_max,
lambda_max<=tr M, so

    lambda_min=det M/lambda_max >= det M/tr M
       >= xy/[324(xalpha_y+yalpha_x)].                     (12)

Multiplying (11) by f(x)^2 f(y)^2 proves (T1).
Apply (12) to the arbitrary complex vector (f(x)c1,f(y)c2) to prove (T2).
There is no restriction to real coefficients or a common phase.

## Validation and limits

The parent derived (5) from the directly reread exact full-integral
identity, checked the direct Jacobian and reciprocal transformation,
and checked the rational inequalities with Python fractions.Fraction.
No theta parameter sweep, numerical grid, truncated-source sign claim,
asymptotic threshold, or new computational certificate is used here.
Independent review of the complete candidate is recorded below.

The claim is only the stated infinite separated-node region. The new
diagonal bounds (6), (9) hold for every z>=1, but do not alone prove
ODD2 when 0<|x-y|<3. No source negative witness is asserted.
All remaining ODD2, higher odd/even signs and RH remain open.

## Acceptance receipt

Sole read-only independent checker /root/sibling5_check accepted the full
7157-byte, 186-LF candidate, SHA256
e81852a8da28cac99aaf74a1ac3c896a7e0c1bcd7d81f68d335a978bdf3cb463,
with verdict ACCEPT_REGIONAL_MIN1_GAP3_ALL_COMPLEX_ONLY. The checker was
not an author. The mathematical proof above is unchanged; its pending
status and validation sentence were updated and this receipt appended.

The parent separately checked the exact joint-tail identity at c=1,
the complete small-q reciprocity bound, the mixed-term Jacobian, all
displayed rational inequalities with fractions.Fraction, and the
determinant-to-complex-form coefficient and four-node factor 2.
This is a new explicit actual-source sign region. It is PAPER acceptance
only, with no canonical production or global-sign promotion.
