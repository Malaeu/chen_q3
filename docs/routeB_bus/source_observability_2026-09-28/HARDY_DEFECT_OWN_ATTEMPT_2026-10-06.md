# Own attempt: the proposed Hardy defect already detects every fixed off-line zero

PAPER_OWN rev deduction before growth question7. Same full V_m, L=log m,
T=mL², alpha=8logL/L. No off-line zero is asserted to exist.
Theta is the FIXED inner function xi(2+iz)/xi(2-iz).
Let F be the unitary Fourier transform with exp(+ixt) convention.
P_+ projects onto F(L²(0,infinity)).
U_m f=F(f shifted from [-L/2,L/2] to [0,L]).
Pfrak_m=U_m* Pi_Theta U_m, D_m=I-Pfrak_m.
For f in the original carrier,
 <f,D_m f>=||P_+(conj(Theta)U_m f)||².
No asymptotic for Theta or its derivatives will be used.

## Conditional lower bound

Fix an actual off-line zero w=delta+i gamma with delta>0 and multiplicity r.
Eventually its negative row belongs to B=L0. Its Riesz vector before
finite Fourier compression is
 h_L(t)=sqrt(2r) sinh(delta t) exp(-i gamma t) 1_{[-L/2,L/2]}.
Let b_m=P_m h_L be the exact original-carrier Riesz vector. Then
 ||h_L||²=r(sinh(delta L)/delta-L) ~ r m^delta/(2delta).

Its Fourier coefficients outside |j|<=m obey
 |<psi_j,h_L>|²<=C_w r m^delta L/j² eventually:
integrate the two exponentials, their endpoint numerator is O(m^(delta/2)),
and |gamma+2pi j/L|>=pi|j|/L for |j|>m.
Thus ||h_L-b_m||²<=C_w r m^delta L/m.
After multiplication by m^(-delta/2), this error tends to zero in L².
Both U and P_+ M_conjTheta are contractions, so this compression error
also tends to zero in the scaled defect norm.

In x=t+L/2 coordinates, up to a global unit phase,
 m^(-delta/2) h_L(x-L/2)
 =sqrt(r/2)[a_L(x)-ell_L(x)],
 a_L=e^{delta(x-L)}e^{-i gamma x}1_[0,L],
 ell_L=e^{-delta x}e^{-i gamma x}1_[0,L].
Here ell_L -> ell_infinity=e^{-(delta+i gamma)x}1_[0,infinity] in L².
Also a_L differs by O(e^-delta L) in L² from
 e^{-i gamma L} tau_L a_infinity,
 a_infinity(x)=e^{(delta-i gamma)x}1_(-infinity,0].
Both limiting profiles have squared norm 1/(2delta).

For any fixed v in L²(R),
 ||P_+(e^{i L z}v(z))||² -> ||v||² as L->infinity
by translating the inverse-Fourier variable. The translated functions
e^{iLz}v converge weakly to zero (L² products are L¹).
Apply this to v=conj(Theta)F(a_infinity), whose norm is unchanged because
|Theta|=1 a.e. The projected translated right profile has norm² ->1/(2delta)
and its cross term with the fixed projected left profile tends to zero.
Therefore
 lim m^(-delta) <b_m,D_m b_m>
 = (r/2)[1/(2delta)+||P_+(conjTheta F ell_infinity)||²]
 >=r/(4delta),
while m^(-delta)||b_m||² ->r/(2delta).
In particular liminf <b_m,D_m b_m>/||b_m||² >=1/2.

Let R_m=C op P op B be the full finite source row stack,
E_m=ran B*. Since v_m=b_m/||b_m|| belongs to E_m, selecting that one B row gives
 ||R_m D_m Pi_E||²
 >= |<b_m,D_m b_m>|²/||b_m||²
 >= c_w m^delta
for every sufficiently late original cell.

## Scope and next consequence

For every fixed eta<delta, the proposed bound
||R_m D_m Pi_E||²<=C_eta m^eta on unbounded original cells
is impossible CONDITIONAL ON THIS OFF-LINE ZERO. No actual zero was found.
Conversely under RH, B has no rows and E={0}, so this defect is exactly zero.
Thus the proposed all-eta common-cell defect bound is itself RH-equivalent
given the above unconditional fixed-inner setup. It is not a supplied
weaker estimate, and positivity/contractivity of the model projection
cannot be spent as a source-form transfer.
This does not kill a differently weighted, signed defect or another source map.

Independent bounded review by growth_symbol_attempt passed: Riesz phases,
exact carrier tail, right-translation/P_+ limit, weak cross-term decay,
row-space restriction and cofinal quantifiers. No off-line zero is asserted.
The compression identity is exact: D_m=U_m*(I-Pi_Theta)U_m, since U_m*U_m=I.
