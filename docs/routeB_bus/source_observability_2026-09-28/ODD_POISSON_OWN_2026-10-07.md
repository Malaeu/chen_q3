# Own next bounded attempt: odd-lattice transform with endpoint correction

PAPER own representation, independently checked by causal_algebra_audit. Return point is answer2 Eqs7–9;
not a new bound. This representation is selected only after the current
finite-inversion/absolute-Euler completion is recorded as stalled.

Let I have nonzero finite length [ell,h] with either endpoint included or
excluded, ell>=1, and F be C1 on [ell,h]. Let c_I(x)=+1/2 at an included
odd-integer endpoint, -1/2 at an excluded odd-integer endpoint, zero otherwise.
Then the proposed exact formula is
 sum_(odd n in I) F(n) - (1/2)int_ell^h F(u)du
 = lim_(K->infty) (1/2)sum_(0<|k|<=K)(1-|k|/(K+1))(-1)^k
       int_ell^h F(u) exp(i pi k u)du
   +c_I(ell)F(ell)+c_I(h)F(h).
For a singleton odd endpoint included in I, use its full F mass separately;
empty intervals contribute zero. A singleton cannot be represented by two
unqualified endpoint halves if it is excluded.

Reason: periodize the zero-extended amplitude by spacing2. Its Fourier
coefficients are half the displayed integrals. Fejer convergence at the odd
lattice evaluation point gives half the sum of one-sided traces, hence half
weight on either geometric endpoint. Add +/-half to restore the actual
interval convention. No uniform K rate, norm estimate, or interchange with
the a-integral has yet been proved. That interchange is a required next step;
finite d-sums alone do not remove it.

For the exact Q2 E_s^j(I), take F=u^(-s)(log u)^j, j=0,1. The zero alias
is already in Theta_U and must not be counted again. Applying this to the
three terms in Eq8 retains mu(d)d^(-s), -logd, and discrete -2 separately
inside their joint signed sum. The endpoint corrections must be integrated
against BOTH parts of d rho_U. Atomic a-flux can hit a product endpoint;
it cannot be dismissed as a measure-zero event for the continuous part.

At s=1/2+it, the alias phase is phi_k(u)=pi k u-t logu.
Stationarity occurs at u=t/(pi k)>0; it lies in the clipped interval only
for k of the sign of t with |t|/(pi h)<=|k|<=|t|/(pi ell).
Thus there are actual nonzero stationary aliases at the original top band.
For example t=Omega, k=1 has u=2m/L, below X only when2U<L,
which fails eventually: this particular alias is outside b<=X, illustrating
why the exact d/product ranges matter. Higher aliases k>=3 can be inside
u<=X for d=1, but the long d=1 coefficient -logd is zero, so this is
not a surviving-term witness. For d=3 and k=7, u=2m/(7L) and au*d<=m
when U<a<=7L/6; this is a nonempty geometric range eventually and u>V.
The coefficient mu(3)(-log3) is nonzero. This only checks geometric
compatibility; it asserts neither a nonzero final a-integral nor a lower
bound for the whole signed alias sum. No smallness follows from the phase.

Next discriminating calculation: justify the summed/integrated transform,
retain all endpoint terms, and estimate the joint stationary alias aggregate
with the actual a-flux and Theta before taking absolute values. A generic
unit-amplitude bound or a mean-square in t does not supply that estimate.

## Fixed-cell interchange attempt

There is a coarse domination sufficient for exchanging the Fejer limit with
the a-integral at each FIXED m (it is not a useful estimate as m grows).
All free intervals lie in[1,X]. For j=0,1, |u^(-s)(logu)^j|<=1+L,
independently of real t. A spacing2 periodization has at most floor(X/2)+2
nonzero translates at any point. Its sup norm is therefore at most
B_m=(floor(X/2)+2)(1+L). Positivity and unit mass of the normalized Fejer
kernel bound every Fejer mean by B_m, uniformly in its order and in the
clipped interval. Subtracting the zero alias and adding endpoint corrections
costs at most another fixed multiple of B_m. The finite d-sum costs at most
sum_(d<=X)d^-1/2(1+logd)<infty. Finally a>=U and the finite signed measure
rho on(U,A0) has finite total variation. Dominated convergence therefore
passes the limit through BOTH atomic and continuous a-flux parts. Singleton
interval contributions are separated exactly. This justifies the transform
for each m and each t, but gives no small operator norm or growing-m rate.

Independent check confirmed the fixed-cell interchange and all normalizations.
Clarification: d=1 LONG coefficient vanishes; short d=1 aliases with roots
in u<=V still have the logu weight and must remain.
