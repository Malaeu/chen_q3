# Botha / literal CCM normalization crosswalk

DIAGNOSTIC_NEVER_A_PROOF.

Botha's L is a **halfwidth**. Our physical support length is ell=log m,
so L_Botha=ell/2 and m=exp(2L_Botha). Their endpointL=2 corresponds to
m=exp4=54.59815003, hence requestedm55 is slightly outside the claim.
The requestedm47 has L_Botha=log47/2, close to but not identical with the
registered gap1.92364501953125. Neither rounding is hidden.

Fourier sign may be reversed without changing this real quadratic form.
Both conventions have Plancherel integral|F|²/(2pi)=||f||². Our basis is
L2-normalized on[-ell/2,ell/2]: e0=1/sqrt(ell),
en=sqrt(2/ell)*(-1)^n cos(2pi*n*x/ell),
on=sqrt(2/ell)*(-1)^n sin(2pi*n*x/ell).
The modal phases are orthogonal basis changes and do not rescale eigenvalues.

In physical space the common form is

k[f]= integral_0^infinity j(s)||f-T_s f||² ds
 -(EulerGamma+log(8pi)+pi/2)||f||²
 -sum Lambda(n)/sqrt(n)*Q_f(logn)+2Aplus(f)Aminus(f),

j(s)=exp(-s/2)/(1-exp(-2s)), Q_f=2autocorrelation(f),
Aplus/minus=integral exp(plus/minus x/2)f(x)dx.
This matches the external equation(1.1) term by term: spectral multiplier
Re psi(1/4+it/2)-logpi has constant psi(1/4)-logpi
=-EulerGamma-log(8pi)-pi/2 and difference
2integral j(s)(1-cos(ts))ds. The pole term includes both signs;
it is positive in the even block and negative in the odd block.
Thus for this explicit full form and norm the scale is alpha=1 and
additive shift beta=0. No affine fit to observed eigenvalues is used.

Independent numerical crosscheck is in normalization_controls.csv, script
normalization.py. Constant entries are replayed through the separate exact
screw source -2g(ell)/ell. First odd entries are replayed through direct
physical correlations C(s)=(1-s/ell)cos(2pi*s/ell)+sin(2pi*s/ell)/(2pi),
with the whole infinite arch tail, every prime power and both poles.
The planted addition is checked through a direct physical sine transform,
not inferred from a difference of eigenvalues. Across m3,7,20,47 and all
three worlds, maximum entry discrepancy is7.39e-80 at80digits. This is a
normalization/sign replay, not an interval certificate or external proof audit.
