# Retrieved Botha edge/kink/tail claims

DIAGNOSTIC_NEVER_A_PROOF. These are extracted claims from unrefereed,
AI-assisted sources, not accepted mathematical suppliers or priority findings.
Primary paper: Zenodo23834265, v0.2.0, PDF in
`/tmp/lit_external_sources/Q3_edge_laws/extracted/AlexGenusCore-weil-edge-laws-9505fdd/paper/main.pdf` (downloaded copy; source URL and PDF hash published).
PDF page numbers below equal its printed page numbers. Source archive hashes/URLs
are in SOURCES.json; primary PDF hashes are in SOURCE_FILE_HASHES.json. Earlier notes v0.1.2 are retrieved as well.

## Form and window contract

Paperp1 Eq(1.1), p2 norm: real f supported in [-L,L],
F(w)=integral f(x) exp(ixw)dx, ||f||²=(1/pi)integral_0^infinity|F|².
With c_n=Lambda(n)/sqrt(n), a(t)=Re psi_Gamma(1/4+it/2)-log pi,

`Q_L(f)=(1/pi)integral_0^infinity[a(t)-2sum_(log n<2L)c_n cos(t log n)]|F(t)|²dt +2F(i/2)F(-i/2)`.

Section2,p9 permits pole weight s, with s=1 the true form. Its physical
form is exactly our archimedean jump form, constant, all prime-power shifts
and both poles. Their L is our full support length ell/2, so literal
CCM m=exp(2L). There is no additional2pi or eigenvalue factor after matching
the physical unit L2 norm. Derivatives satisfy d/dell=(1/2)d/dL.

## Edge law

Theorem4.1,p14: for L in a compact positive range, pole weight s in a
compact range and eigenvalue |lambda| bounded, eigenfunctions are bounded
and have continuous zero-extended representatives. No simplicity, parity
or arithmetic condition on exp(2L) is required. With l(r)=log(1/r),

`A_±=lim_(r↓0) psi(±(L-r))*sqrt(l(r))`,
`psi(±(L-r))=A_±*l(r)^(-1/2)+O(l(r)^(-1))`.

Theorem7.1,p25 improves this to
`psi(±(L-r))=A_±*l^(-1/2)+O(l^(-3/2))`
uniformly in the stated compact ranges, and at fixedL gives
`psi(±(L-r))=A_±*(l-D)^(-1/2)+O(l^(-5/2))`,
`D=lambda+log(2pi)+EulerGamma`.
The second-order constants degenerate near activation2L=logn.
In particular the ordinary boundary value is ZERO; A is a renormalized trace.

## Hadamard law

Theorem5.6,p18: if lambda_k^sigma(L0) is simple in its parity sector,
it is C1 and remains sector-simple locally, and for unit eigenfunctions,

`d lambda/dL=-(A_+²+A_-²)=-2A²`, with |A_+|=|A_-|=A.

No exclusion of prime-power activation windows is made. For two nearby
windows, the cross identity has remainder O(delta*l(delta)^(-1/2)).
In our full-length parameter ell, the formula becomes d lambda/dell=-A².
This statement is about eigenfunctions of the full continuum operator,
not Ritz vectors in a fixed Fourier carrier.

## Kink/echo law

Theorem7.3,pp25–26: at a chain pointz of generationk>=1, let W_±(z)
be the weighted contributions of minimum-length prime-shift chains from
the two edges. Then

`psi(z-d)-psi(z)=[(k+1)W_+-kW_-]/(2k+1)*l(d)^(-k-1/2)+O(l^(-k-3/2))`,
`psi(z+d)-psi(z)=[-kW_++(k+1)W_-]/(2k+1)*l(d)^(-k-1/2)+O(l^(-k-3/2))`.

At y_n=L-logn, genericL and no chain from the opposite edge give W_+=c_nA_+,
W_-=0: the two coefficients are (2/3)c_nA_+ and -(1/3)c_nA_+.
Theorem7.5,p27 gives the second-order odd-part expansion
`Dpsi(z;d)=Omega_k(z)*(l-D)^(-k-1/2)+Omega_(k+1)(z)*l^(-k-3/2)+O(l^(-k-5/2))`.
Corollary7.6,p27 gives the exact-point jump ratio
`1/rho_n(d)=l-D-beta_n+O(1/l)` and prime-power boosts.
The notes' transfer to Galerkin traces is explicitly heuristic.
Corollary7.4,p26 claims a dense singular set when L>(1/2)log6 and failure
of every positive-order interior Holder condition when the trace is nonzero.

## Fourier and zero tails

Theorem8.8,p31 uses h(w)=F(w)F(-w), complex zero parameters
rho=1/2+i gamma_rho and cutoff|Re gamma_rho|>T, with multiplicities:

`Z(T)=sum h(gamma_rho)=(A_+²+A_-²)/(pi*T)+O_psi(1/(T*logT))`.

It is asserted absolutely convergent and real without RH; h at a complex
zero is not replaced by an absolute square. If sector-simple, pi*T*Z(T)
equals |lambda'(L)|+O(1/logT). The explicit error involves A and a source
remainder constantB; relative asymptotics require logT sufficiently larger
than B/A. No informative finite-height error is supplied for our cells.

Theorem9.2,p32 distinguishes the ordinary Fourier integral tail:
`integral_(|t|>T)|F(t)|²dt =4A²/(T*logT)+O(1/(T*log²T))`.
For the smoothed zero tail and a measure nu with the specified finite
moments, it gives
`Z_nu(T)=2*m1(nu)/T*[A²+(lambda*A²+c_X*A_+*A_-)/logT] +O(|nu|(R)/(T*log^(3/2)T))`.
For parityepsilon and nonzero trace, its normalized form is
`Upsilon_nu=1+(lambda+epsilon*c_X)/logT+O(log^(-3/2)T)`.
The sharp second-order cutoff version remains Conjecture11.1.

## Earlier notes

The v0.1.2 notes have no fixed PDF pagination; exact labels K1–K6 and
T0–T6 are in `notes/tail_kink_laws_note.md`, table near its lines112–125.
They distinguish an accepted internal-AI first-order sharp tail from the
open sharp cross-term improvement. Neither version receives peer-reviewed
or historical-priority status in this quick check. No external code was run.
