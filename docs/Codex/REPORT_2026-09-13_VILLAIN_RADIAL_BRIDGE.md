# Villain sibling: exact planar lift, finite-model realization open

STATUS: ACCEPTED_PAPER_EXACT_PLANAR_LIFT_AND_CONDITIONAL_TRANSFER.
INCOMPLETE_NO_CONSUMABLE_TARGET: canonical theorem/consumer edge unbound.
GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. ALL_ORDER_SOURCE_SIGN: OPEN. RH: OPEN.
PX_RH_CLAIM: NOT_MADE. No Lean or canonical admission.

The owner resumed the mathematical search on 2026-09-13 after the joint
brainstorm. This report proves one geometric representation of the actual
source and identifies the remaining Villain construction. It does not reset
the historical source-sign no-delta count of 3.

## Source pins and published transfer

Repository source commit: fb57d13a506b1fa763fd601c1c639a4ef6a85121.

- `docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md`, section 4 and BP1:
  SHA256 14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc.
- `docs/Codex/REPORT_2026-09-12_LYGSPHI_INTAKE.md`, source normalization,
  positive gammaPhi, and exact scope of the spin-lift exclusion:
  SHA256 2e4ace719a20964deab21d7be0d5457ac651080d8f317eefab52138343a5702f.
- `docs/Codex/REPORT_2026-09-12_ALL_ODD_TO_RH.md`, Fourier identity:
  SHA256 760fd70fd1e6c3f5b07f8c6eced03bf3f2dfb69698cfb67f597ead219ff8940a.

Keep p=Phi/Z, Z=integral_R Phi=xi(1/2)>0, and
M(h)=integral_R exp(hx)p(x)dx=xi(1/2+h)/xi(1/2), h in C.
Z is not the physical L2 normalization A. Previously accepted source facts
are used only at their stated scope, without a new recursive archive audit.

New primary source: C. M. Newman and W. Wu, *Lee--Yang Property and Gaussian
Multiplicative Chaos*, CMP 369 (2019), 153--170.
https://link.springer.com/article/10.1007/s00220-019-03453-0
PDF: https://link.springer.com/content/pdf/10.1007/s00220-019-03453-0.pdf
Fetched PDF: 362966 bytes, SHA256
1dd55b77b6ff1437cbf46c91926bfa1f57ada1d21357c28e96b2e5942b717002.
Locators: equations (3)--(5), Theorem 3, printed p.155; Definition 6,
Theorem 7 and Remark 9, p.157; proof of Theorem 7, pp.158--159.
Short quote, Remark 9: "it suffices to show weak convergence".

The imported theorem preserves Lee--Yang type under weak convergence.
Its input laws are symmetric, each has some finite Gaussian exponential
moment, and each field transform has only imaginary zeros. The Gaussian
moment parameter need not be uniform. Finite free-boundary Villain models
have the required zero property for nonnegative observable weights.

Our application uses J_e>0 and lambda_v>=0 on each finite graph, with

    V_J(a)=sum_(m in Z) exp(-J(a+2pi m)^2/2),
    dP_G(theta)=Z_G^-1 product_e V_Je(theta_u-theta_v) product_v dtheta_v,
    Y_G=sum_v lambda_v exp(i theta_v), X_G=Re Y_G.

Angles lie in (-pi,pi]. Global rotation gives symmetry, and finite bounded
X_G supplies the individual Gaussian moment. Therefore weak convergence of
THESE SAME X_G to p is sufficient. This weakens the older sufficient
interface; it does not construct the approximants. J=0 is avoided because
the displayed unnormalized Gaussian sum then degenerates.

## Exact theta-to-circle dictionary

Let vartheta(t)=sum_(n in Z) exp(-pi n^2 t), t>0. Termwise differentiation
of the locally convergent source series gives

    r(t)=2t vartheta''(t)+3 vartheta'(t),
    Phi(x)=exp(5x/2)r(exp(2x)).

For K_J(a)=sqrt(J/(2pi))V_J(a), the Fourier series is

    K_J(a)=(1/(2pi))sum_(n in Z) exp(-n^2/(2J)) exp(i n a).

Thus vartheta(t)=2pi K_(1/(2pi t))(0). This is an identity of heat kernels.
The source variable x is logarithmic heat time; the complex field h couples
to X_G. Differentiating in t or changing x cannot silently replace that
observable. No graph or couplings have been extracted from this identity.

## Exact positive planar lift of the actual source

The accepted source gives v(s)=-log p(sqrt(s)) with v''(s)>0 for s>0 and
gammaPhi=-(log Phi)''(0)>0. Even analyticity implies v'(0)=gammaPhi/2>0.
Consequently p'(x)=-2x p(x)v'(x^2)<0 for x>0. The full source decay applies
to fixed derivatives, and p'(x)=O(x) at zero.

Define a density per unit planar area, using a new radius variable a,

    g(a)=-(1/pi) integral_a^infty p'(u)/sqrt(u^2-a^2) du, a>=0.

It is nonnegative. The lower singularity is integrable for a>0; at a=0,
p'(u)=O(u) pays the endpoint. The full source derivative decay pays infinity.
For x>=0, Tonelli and the change r^2=x^2+(u^2-x^2)s give

    integral_x^u r dr/(sqrt(r^2-x^2)sqrt(u^2-r^2))=pi/2,
    2 integral_x^infty g(r)r/sqrt(r^2-x^2) dr
      =-integral_x^infty p'(u)du=p(x).

At x=0 the same identity follows directly or by Tonelli. Reflection covers
x<0. The left side is the first-coordinate marginal of g(|y|)d^2y.
Integrating over x proves its total mass is 1. In particular

    rho(da)=2pi a g(a)da

is a probability law, and R cos U has density p when R has law rho and U
is an independent uniform angle. This is an exact source representation,
not an approximation or a claim that g is a Villain Gibbs density.

Every finite Y_G above is rotationally invariant. Conversely, tightness of
Re Y_G implies tightness of |Y_G|: for R>2L a uniform angle has probability
at least 2/3 that |R cos U|>L. Thus the planar-lift requirement is necessary
for this route, and the displayed Abel construction pays that requirement.

## Negative control and the exact remaining task

The already accepted control f_c(x)=exp(-x^2)(1+3x^2/10+x^4/25) is decreasing
on x>0, since

    f_c'(x)=-2x exp(-x^2)(7/10+11x^2/50+x^4/25)<0.

Its normalized density therefore has the same positive Abel lift. Yet its
known transform is exp(h^2/4)(h^4+42h^2+472)/472, whose h^2 roots are
-21 +/- i sqrt(31). Planar positivity alone cannot provide Lee--Yang.
The extra hypothesis required here is realization by the finite Villain laws,
not a positive radial mixture or a formal Hamiltonian -log g.

The previous entropy-corrected binary-spin joint law remains excluded.
That exclusion does not forbid a different microscopic realization of p.
One next bounded test is to construct source-derived G_N,J_e,N,lambda_v,N
whose radial magnetizations |Y_N| converge weakly to this rho. Their common
uniform angle then gives X_N=>p. Direct X_N=>p is also sufficient.
No unknown xi zeros, presumed Lee--Yang property, or assumed all-order sign
may define or justify the construction.

No source evaluations, quadratures, finite Hankel campaign or Lean run were
needed for the displayed proof. No new actual full-sign supplier is obtained.

## Discovery and independent receipts

The existing source-pinned physics-brother brief and prior shelf receipts
were reconciled. Lee.Yang, Griffiths.Simon, reflection positivity, Herglotz,
Asano, random-cluster and stability-preserving queries remain INCOMPLETE:
semantic-index freshness failed; the last three also encountered the recorded
ask.sh unbound-array error. These are not no-hit or literature-absence claims.
The dictionaries were spin probability, complex zero preservation, and
circle heat kernels. No index repair or source registration is performed.

Sole independent checker sibling5_check verified the published transfer,
theta dictionary and necessary rotational fit, receipt SHA256
7d61af1a6271a5b6411e56b8a766a318f7a18a453138aa30c39d6fcb4b7b3489.
The exact Abel proof and control limitation were independently checked,
receipt SHA256 886b454ee4523a4bd1218feca78e00431ac55c140f9112a7a4f2eca71600b4b9.
These receipts concern the displayed mathematical mechanisms; the complete
assembled file is separately reviewed before dispatch.

Complete-file independent review: CLEAN_DISPATCH_CANDIDATE on 7422 bytes /
149 LF, SHA256 13fbbd203d40a9c2a6f89062f757265d0e65e612d4d996262c1db52ef948aec8.
Review receipt SHA256
03d4e27b9cedc28c9ccf4b1a6d3620472cd3e47ec947fecf1df2e714c4f09eee.
The status and this receipt are the only post-review additions. Acceptance
is restricted to the stated PAPER lemmas and conditional transfer.
