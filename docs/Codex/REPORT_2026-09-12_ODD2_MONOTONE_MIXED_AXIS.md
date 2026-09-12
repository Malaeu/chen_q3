# Monotone mixed-entry bound and full theta strips down to the axis

Status: ACCEPTED_PAPER_MONOTONE_MIXED_AXIS_STRIPS.
Parent mathematical task, 2026-09-12; no Lean or canonical admission.
Fixed consumer: original all-complex ODD2 in two whole unbounded strips,
including arbitrarily small positive second node. Accepted theorems:

    Delta(x,y)>=19 x y^2 f(x)^2/(96000 alpha_x A^2)>0,
                            x>=2, 0<y<=1/4;              (T1)

    Delta(x,y)>=17 x y^2 f(x)^2/(9600 alpha_x A^2)>0,
                            x>=3/2, 0<y<=1/256.          (T2)

Both transposed regions follow by symmetry. The stronger lower constant
in(T2) applies only to its much narrower small-node range. The entire
remaining lower-node region is not closed. Full ODD2, IC, higher odd/even
PSD and RH stay open. No source grid, quadrature or new theta evaluation
is used: only full-source accepted premises and exact rational arithmetic.

Use the unchanged F=Phi, A=||Phi||_2, f=F/A, Kraw=A^2 K and
Deltaraw=A^4 Delta, with K(s,t)=V(s,t)-V(s,-t).
Base published branch commit59a0936e87619beeb8db7c88d09426bffad98698.

## 1. Accepted full-source premises

- REPORT_2026-09-12_ODD2_SMALL_NODE_TAIL5.md, SHA256
  088cfa2fcaa28a3d7d17e7e4da7f59722561907f5e177d2dc47b08bff4557766:
  h(u)=log F(sqrt(u)) satisfies h''<=-1/4 globally and h'(0)<0.
  Thus F is positive, even and decreasing on[0,infinity).
  Its exact accepted endpoint enclosure in SOURCE_HCURV_20260912.json,
  SHA256ee0d03ac11775bdc3f96519077ab0c1f0617852098b573b71764c11c2e964dd2,
  gives F(0)<9/10. This bounds F on the entire real line.
- REPORT_2026-09-12_ODD2_REGIONAL_MIN1_GAP3.md, SHA256
  9d568cc75aa42d2e9ee30cee62869eafa9f93bea825ddbcbe8bf6afb16011050:
  Kraw(x,x)/F(x)^2>=x/(6 alpha_x), x>=1, alpha_x=pi exp(2x).
  The complete H bounds imply, for every x>=1,v>=0,

      F(x+v)/F(x)<=(14/13)exp(-beta_x v),
      beta_x=2alpha_x-9/2.

- REPORT_2026-09-12_ODD2_ORIGIN_QUARTER_BOX.md, SHA256
  d694654cf04951289ccf49cb828a8fbcce24ad07d70ab3823ea7c7ebe3ab2f72:
  its accepted entire divided-kernel enclosure is Kraw(s,t)/(st)>19/1000
  for0<s,t<=1/4, including continuous axis limits. In particular

      Kraw(y,y)> (19/1000)y^2, 0<y<=1/4.                  (1)

- PROSHKA_RESPONSE_GOAL058_ODD2COMPACT_2026-09-12.md, SHA256
  819511db9d46801e87b54e728faf7c55e7ce21e4e20e48d9d95d49a71b175e07:
  accepted equation(17) gives kappa=Kraw_12(0,0)>0.0864=54/625.
  Equations(21),(23) give M13<171 on the entire[-1/256,1/256]^2 and

      |Kraw(y,y)/y^2-kappa|<=M13 y^2/3, 0<y<=1/256.

  Hence the exact rational budget is

      Kraw(y,y)/y^2 >54/625-57/65536
                   =3503319/40960000 >17/200.             (2)

The full original K(x,y)>0 for positive nodes is the already accepted OD1
consequence of squared-variable source concavity and its exact integral
representation. This entrywise statement is not assumed to imply ODD2.

## 2. A one-sided mixed-entry bound retaining the useful sign

The exact full source identity is

    Kraw(x,y)=integral_0^infinity F(x+v){(x+2v)D(v,y)
                                      +y[F(v+y)+F(v-y)]}dv,
    D(v,y)=F(v+y)-F(v-y).                                 (3)

For v,y>=0, |v-y|<=v+y. The even monotone full source gives D(v,y)<=0.
Since x+2v>0 and F(x+v)>0, this term is nonpositive pointwise. Also
F(v+y)+F(v-y)<=2F(0)<9/5 on the entire improper integral.
Combining these facts with OD1 and the full ratio envelope gives

    0<Kraw(x,y)
       <=2y F(0) integral_0^infinity F(x+v)dv
       <(28/13)(9/10) F(x)y/beta_x,    x>=1,y>0.           (4)

Thus the absolute mixed entry has this upper bound too. No cancellation
at y=0 is lost, and no reflected or integration tail is omitted. Dropping
the nonpositive term is used only for the upper bound; positivity of K
comes from the independently accepted source OD1 argument.

For x>=2, alpha_x>128 and therefore beta_x/alpha_x>503/256.
Consequently

    Kraw(x,y)<F(x)y/alpha_x,      x>=2,y>0,                (5)

since (28/13)(9/10)(256/503)=32256/32695<1.
For x>=3/2, alpha_x>60 and beta_x/alpha_x>77/40. Hence

    Kraw(x,y)<(21/20)F(x)y/alpha_x, x>=3/2,y>0,            (6)

since (28/13)(9/10)(40/77)=144/143<21/20.
These uniform raw-scale bounds use F(0), not a rough bound on F''.

## 3. Whole quarter-node strip

For x>=2,0<y<=1/4, combine(1),(5) with the accepted x-diagonal:

    Deltaraw(x,y)>=F(x)^2 y^2
                     [(19/1000)x/(6alpha_x)-1/alpha_x^2]. (7)

The function x alpha_x increases for positive x. At x=2,

    x alpha_x=2pi e^4>(25/4)(19/7)^4
                        =3258025/9604>6400/19.            (8)

Here pi>25/8 and e>19/7. The constant6400/19 is exactly
6*(1000/19)*(16/15). Thus the subtracted term in(7) is at most15/16
of the positive term, giving

    Deltaraw(x,y)>=19x F(x)^2 y^2/(96000alpha_x).

Divide by A^4 and use F(x)^2/A^4=f(x)^2/A^2 to prove(T1).

## 4. Whole narrower strip and the entire far-axis limit

For x>=3/2,0<y<=1/256, equations(2),(6) instead give

    Deltaraw(x,y)>=F(x)^2 y^2
                      [(17/200)x/(6alpha_x)-(21/20)^2/alpha_x^2]. (9)

For every x>=3/2,

    x alpha_x >=(3/2)pi e^3>(75/16)(19/7)^3
                              =514425/5488>1512/17.       (10)

The last constant is exactly6*(21/20)^2*(200/17)*(8/7).
The subtracted term in(9) consumes at most7/8 of the positive term.
The remaining1/8 gives(T2) after the same A^-4 normalization.

In particular let B(x)=Kraw_2(x,0) and
Haxis(x)=kappa Kraw(x,x)-B(x)^2. Taking the smooth y->0 limit of(T2)
in raw scale proves a full source-specific axis estimate

    Haxis(x)>=17x F(x)^2/(9600alpha_x)>0,    every x>=3/2. (11)

The limit follows from exact parity and smoothness of the full source:
Deltaraw(x,y)/y^2 tends to Haxis(x). This extends the old isolated AX
interval near1/2 to a whole unbounded axis range; it does not decide
Haxis on1/4<x<3/2, nor prove every positive y below1.

## 5. Original complex form and scope

For a=K(x,x)>0 and b=K(x,y), every c1,c2 in C satisfies exactly

    c* K2 c=a|c1+(b/a)c2|^2+[Delta(x,y)/a]|c2|^2.

Consequently(T1),(T2) exclude all complex negative two-node witnesses on
their full stated strips. The original V form on(x,y,-x,-y), with
coefficients(c1,c2,-c1,-c2), is exactly twice this expression.

The still unpaid lower-node region {0<y<1,y<x<5,x>1/4} can now have
the two strips removed. In particular: when y<=1/256 a remaining pair
has x<3/2; when1/256<y<=1/4 it has x<2; when1/4<y<1 it still has x<5.
The whole quarter square and previously accepted AX/DG pieces stay excluded.
The min>=1 branch remains the separate live ODD2STRIP request.
No global IC/ODD2, larger odd/even form, full Q positivity or RH follows.

## 6. Exact rational verification

The parent executed these exact fractions checks; no source was sampled:

```python
from fractions import Fraction as Q
assert Q(28,13)*Q(9,10)/(2-Q(9,256)) < 1
assert Q(25,8)*Q(19,7)**4 > 128
assert Q(25,4)*Q(19,7)**4 > Q(6400,19)
assert Q(54,625)-Q(57,65536) > Q(17,200)
assert Q(25,8)*Q(19,7)**3 > 60
assert Q(28,13)*Q(9,10)/(2-Q(3,40)) < Q(21,20)
assert Q(75,16)*Q(19,7)**3 > Q(1512,17)
assert 6*Q(1000,19)*Q(16,15) == Q(6400,19)
assert 6*Q(21,20)**2*Q(200,17)*Q(8,7) == Q(1512,17)
```

## 7. Independent acceptance receipt

The sole reserved checker /root/sibling5_check read and independently
reviewed the complete7270-byte,180-LF candidate, SHA256
1a004a223af4f41ce0916c522b0fd0e953828345fb556ca7ad61f9bd8c1b428c.
It returned ACCEPT for(T1),(T2), the whole far-axis estimate(11), and the
residual-domain refinement, at the stated all-complex PAPER scope.
It separately checked the inherited full-source domains and constants,
the sign of D, distinct use of OD1, the entire ratio-envelope integral,
all9 exact rational comparisons, both determinant budgets, the A^-4
normalization and the axis limit. It found no unpaid integration tail
or missing phase/coefficient condition.

The parent independently executed all9 comparisons and reread the exact
source equations(17),(21),(23) supplying kappa and the complete M13 domain.
It verified the accepted whole-quarter P bound, full source endpoint bound
and monotonicity, both beta thresholds and both retained determinant fractions.
After review only status/introduction and this receipt were updated.
No extra theta evaluation or quadrature was performed. This acceptance
does not admit a canonical node, Lean theorem, full ODD2/IC, larger odd/even
positivity or RH. The original goal and its unpaid consumers remain intact.
