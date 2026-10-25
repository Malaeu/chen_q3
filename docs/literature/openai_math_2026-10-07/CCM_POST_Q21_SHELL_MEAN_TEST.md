# After Q21: common shell averaging before Young, fixed broad-plateau gauge

Fixed Delta>0 and Q21 original P/energy identity. For each pole pair x,y=x+d,
let Z_n=u(x+log n), mu=E_pi Z_n, V=E_pi|Z_n-mu|², using actual shell pi.
Take tau=tau(x,d)>0 independent of n. Exactly
 E_pi[(1+tau)|Z_n-u(x)|²+(1+1/tau)|Z_n-u(y)|²]
 =(1+tau)|mu-u(x)|²+(1+1/tau)|mu-u(y)|²+(2+tau+1/tau)V.
Subtract the variance term BEFORE bounding. The resulting Hmean is still
Epole+Xi_mean, Xi_mean integrand=rho(x)rho(y)|tau(mu-u_x)+(mu-u_y)|²/tau.
It is smaller than H but not automatically close to Epole or Eplus.
Small unrouteable shells are kept exactly as Q21.

Concrete admissible gauge rho_(L,B)=int_(-B)^(L+B)Phi(t-b)db, with fixed
large B. On I it differs uniformly from bPhi=int_R Phi by at most
int_(|t|>B)Phi(t)dt. Its reciprocal therefore tends uniformly to 1/bPhi
as B->infinity, independently of L. B will be fixed BEFORE m grows.

Use the symmetric smooth bump eta supported in (2Delta,5Delta/2), maximal
at v0, and q=(-eta''+eta/4)/N, N=L2 norm of that numerator. Both exponential
contacts vanish; q>0 near v0. Let f_L=(q(t)+q(L-t))/sqrt2 and its real unit
original sparse-P return f_m as in Q21. All full prime/mixed returns paid.
For x,v near v0, y=L-v,d=L-x-v, EVERY shell intermediate z=y+s,0<s<=Delta,
lies inside I for large L. All corresponding n<m since h_n=d+s<L.
The actual shell mean of the unweighted physical right profile tends to

 mu_f(v)= [integral_0^Delta exp(s/2) q(v-s)ds]
                  /[2sqrt2(exp(Delta/2)-1)].

This is fixed-shell weighted PNT with actual Lambda and includes all prime
powers. At v=v0, the support to the left is fully included, and
 integral_0^Delta exp(s/2)q(v-s)ds
 =-(eta'(v)+eta(v)/2)/N <0.
(The identity follows by differentiating exp(-t/2)(eta'(t)+eta(t)/2).)
Choose a closed interval J near v0 with q>=a>0 and mu_f<=-b<0.
Choose fixed B sufficiently large that replacing f by f/rho changes the
shell mean by less than b/(2bPhi). Uniform Fourier/P return in sup norm
and uniform PNT on x,v in J then give mu_u<0 on these pairs eventually,
while f_m(x),f_m(L-v)>0. No uniform statement over arbitrary gauges is made.

Both averaged increments mu_u-u(x),mu_u-u(y) are negative. AMGM yields
 Xi_mean integrand>=4 f_m(x)f_m(y), uniformly every positive tau(x,d).
Integrate x,v in J: k(d)>=constant sqrt(m), so Xi_mean[f_m]>=c sqrt(m).
Contacts cancel full signed PNT main and Q[f_m]=o(sqrt(m)) by Q21 return.
Thus Hmean-Eplus>=c sqrt(m) on this unit original-P vector, for every tau.
Upper: choose tau=1; Hmean<=H and the Q21 integrated upper proof adapts to
rho_(L,B) with constants depending only on fixed B,Delta,Phi, hence O(sqrt(m)).
Moments and prime convolution acquire at most fixed exp(B/2) factors.
Therefore for this specified gauge family, inf_tau sup_unitP[Hmean-Eplus]+
retains order sqrt(m). Averaging first removes variance but not mean-level
cancellation. This does NOT establish inf over all gauges, nor actual CCM
spectral growth, nor exclude the genuine zero pair or a signed covariance
estimate. Every lower-bound shell used here is entirely interior.

Root derivation and shell_mean_covariance_preflight bounded independent PAPER PASS,
conditional on inherited Q21 source and original-P return. No favorable arithmetic
exponent, no numerical spectral run, no Pro send. Bounded shelf check: Q21 section8 already contains the covariance identity;
its algebra is not new. Q12 radial, Q15 Vaughan and Q17 translation averages
do not perform this same-shell mean completion. The evaluated fixed-gauge
application is distinct; no global novelty or literature-absence claim.

Explicit upper details: rho_(L,B)(t)>=a_B=int_(-B)^B Phi>0 on I and
rho<=bPhi globally. The pole diagonal on I is bounded by C_B sqrt(m)
from the two exponential moments. With the same Gamma_Phi as Q21,
sum_n c_n rho_(L,B)(z-log n)<=2 Gamma_Phi exp(B/2) exp(z/2)
<=2 Gamma_Phi exp(B/2)sqrt(m) for z in I. Thus Q21 H_z and diagonal
bounds apply with a_B and fixed exp(B/2), paying short/empty shells,
all tails and both orientations. No support preservation after P is used.

Scope of acceptance: tau depends on x,d but not shell index n; Delta and
large B are fixed before m grows. No infimum over arbitrary gauges is
bounded here. Actual all-prime Eplus, small/empty shells, outside edges,
complex mixed products and original normalization remain. Independent
checker verified exact PNT mean, original-P signs and the adapted upper.
AUTOPSY: dropped=CANCELLATION; note=Removing common shell variance exactly does not remove cancellation between the two mean increments.
