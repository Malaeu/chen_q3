# Physics brother: Lee–Yang and a ferromagnetic realization of Phi

STATUS: SOURCE_VERIFIED_DISCOVERY; independently reviewed and parent checked.
Production status: INCOMPLETE_NO_CONSUMABLE_TARGET. The canonical exact
theorem/consumer edge is unselected; this is an isolated PAPER discovery.
RH, global IC, global ODD2 and all-order Hankel positivity remain OPEN.
Source-sign no-delta counter remains 2: this is the owner-directed change
of dictionary, not a completed new full-sign attempt. RENEWALH is unsent/parked.

## Finding

The useful physical brother is the Lee–Yang mechanism, specifically the
Griffiths–Simon construction of a continuous spin from ferromagnetically
coupled binary spins. Its extra structure is a microscopic realization
with nonnegative pair couplings and positive observable weights.

For our exact source, the normalized complex-field partition function is

    M(h) = integral exp(hx) p(x) dx = xi(1/2+h)/xi(1/2),
    p = Phi/Z,  Z = integral Phi = xi(1/2) > 0.

Thus imaginary-axis zeros of this physical partition function would give
exactly the required RH zero statement. This identity does not supply
an Ising realization. The present result identifies a constructive route
to seek and tests its first ready-made supplier against the actual source.

## Source evidence

1. B. Simon and R. B. Griffiths, *The (phi^4)_2 field theory as a classical
   Ising model*, CMP 33 (1973), 145–164, DOI 10.1007/BF01645626.
   Author-hosted PDF: https://math.caltech.edu/SimonPapers/47.pdf
   SHA256 bc3aa5a0bfa6729a659802c7a481d2aa9462b08a2d66abe2e528869915d93dec;
   1,453,749 bytes. Section 2, pp.147–153, was read; relevant displayed
   equations on pp.148,150,152 were also visually inspected.
   Theorem 3, p.151: “provided each” field “is either 0 or has strictly
   positive real part.” The theorem asserts nonvanishing of the normalized
   partition function under those conditions. Theorem 1, pp.148–151,
   constructs the quartic family exp(-a s^4-b s^2), a>0, b real, as strong
   ferromagnetic limits. The definition on p.148 includes a uniform
   Gaussian envelope of every order for the approximating densities.
   Strength: verified constructive sibling; applying it to Phi is conditional.

2. M. Aizenman and R. Fernandez, *On the critical behavior of the
   magnetization in high-dimensional Ising models*, JSP 44 (1986).
   Author-hosted PDF:
   https://webspace.science.uu.nl/~ferna107/papers/_86_Aiz_Fern_highd.pdf
   SHA256 62ca48a17157bb0024d1899f14bf0031f5a83f363b04bb3ab12c8b9801f85dc4;
   2,542,230 bytes. Appendix C, pp.449–451, equations (C.2)–(C.6).
   The observable is a weighted sum of microscopic Ising spins,
   “with positive coefficients” (p.449). The class uses ferromagnetic
   intrablock interactions and limits. This supports seeking unequal
   weights and several blocks; it supplies no construction for Phi.
   Strength: verified structural definition, conditional source fit.

3. Yuri Kozitsky, *Mathematical theory of the Ising model and its
   generalizations: an introduction*, ICMP–03–08E (2003).
   https://icmp.lviv.ua/sites/default/files/preprints/pdf/0308E.pdf
   SHA256 bcea5e2d2c87c0cfb67d80836217ee959d507d88be2b107ea1965810ac88b459;
   495,329 bytes. Definition 7, printed p.12 (PDF page index 7): BFS
   densities have the form C^-1 exp(-v(s^2)); the condition is “it is
   convex on” the nonnegative real axis, with a quadratic lower bound.
   Proposition 10, p.13, is the four-point Lebowitz inequality.
   Definition 13 and its following paragraph, p.15, distinguish GS from
   the larger correlation-inequality classes. Strength: verified dictionary
   and diagnostic distinction, not a full-sign supplier.

Only short quotations and our analysis are retained here; the PDFs are
local reading evidence, not redistributed in the repository.

## Explicit transport interface and its conditional proof

Take finite zero-field spin systems, with probability proportional to

    exp(sum_(i<j) J_(ij,N) sigma_i sigma_j),
    sigma_i in {-1,+1}, J_(ij,N) >= 0.

Absorb inverse temperature into J. Set X_N=sum_i q_(i,N) sigma_i,
q_(i,N)>0, and M_N(h)=E exp(h X_N). The microscopic external fields
are h_i=q_(i,N)h. All their real parts have the same strict sign when
Re h != 0. The finite multivariate Lee–Yang theorem therefore gives
M_N(h)!=0 in each open half-plane; spin-flip symmetry handles the left one.
No scalar-curvature hypothesis is used in this finite theorem.

Sufficient unpaid approximation conditions for our application are:

    law(X_N) converges weakly to p(x)dx;
    for every R>0, sup_N E exp(R |X_N|) < infinity.

These imply local uniform convergence M_N -> M. Indeed, on |h|<=R,
the contribution from |X_N|>L is bounded by
exp(-L) sup_N E exp((R+1)|X_N|). A continuous cutoff reduces the remainder
to weak convergence; the truncated transforms are equicontinuous on
the compact h-disk, so a finite net gives uniform convergence. The same
tail estimate holds for the limit by truncation and weak convergence.

Apply one-variable Hurwitz separately on Re h>0 and Re h<0. The limit
cannot be identically zero there: for real h its defining positive integral
is strictly positive. Hence M has no zeros off the imaginary axis.
Together with the pinned xi identity, this would prove RH.

This is a sufficient physical construction task. We have not proved that
every Lee–Yang density has such a realization, nor that Phi does.
Exponential integrability of the limiting p alone does not discharge
uniform integrability of a proposed sequence. Fitting finitely many
moments or discretizing p without proving the coupling signs does not
discharge either approximation condition.

## Completed first source-fit test

The ready-made construction in Simon–Griffiths Theorem 1 produces a
quartic density. Its explicit binomial weights on p.150 are proportional to

    binom(N,(N+mu)/2) exp(mu^2/(2N)-b mu^2/N^(3/2)),
    X_N = mu/N^(3/4).

For fixed b and large N the pair coupling is nonnegative. The limiting
log-density is -x^4/12-bx^2; rescaling changes the quartic coefficient.

Our source is not in this ready-made family. From the pinned theta series,
put t=exp(2x). For x->+infinity the n=1 term gives

    Phi(x) = 4 pi^2 exp(9x/2-pi exp(2x)) (1+o(1)),
    -log p(x) = pi exp(2x)-9x/2+O(1).

To justify dropping n>=2, divide by the leading n=1 term: for t>=1
the resulting tail is bounded by a constant times
sum_(n>=2) n^4 exp(-pi(n^2-1)t), which tends to zero by domination.
Evenness gives the negative tail. Therefore -log p is not any quartic
polynomial, including after a nonzero linear rescaling of the spin.
It does satisfy every Gaussian/exponential tail requirement on the limit.

Verdict: the standard quartic construction does not supply the actual Phi.
This does NOT rule out a different ferromagnetic construction, unequal
weights, coupled blocks, or another admissible limiting scheme.

## Why the already-paid curvature stops short

Let v(u)=-log p(sqrt(u)), u>=0. The accepted full-source curvature gives
v''>=1/4 (with its smooth extension at zero). The source tail and continuity
give v(u)>=v0+v1 u for some v1>0. Thus p is a BFS density, in precisely
Definition 7's sense. Its one-spin Lebowitz inequality is
E X^4 <= 3(E X^2)^2: a named physical sibling of an already-paid scalar sign.
It is not all-order Hankel positivity and does not imply Lee–Yang.

The existing negative control checks that distinction without a new search:
Q(u)=1+3u/10+u^2/25 and v_c(u)=u-log Q(u) satisfy

    v_c''(u) = (1/100+3u/125+2u^2/625)/Q(u)^2 > 0.

Also v_c(u)>=u/2-C for some C, so the normalized control is BFS.
Nevertheless its already-accepted transform is

    M_c(h)=exp(h^2/4)(h^4+42h^2+472)/472,

with h^2=-21 +/- i sqrt(31). Thus BFS alone cannot imply the full zero
statement. This control cannot admit the finite-spin realization PLUS
the convergence hypotheses above. In the narrower strong-limit definition
of Simon–Griffiths p.148 it also fails the every-Gaussian-envelope condition.
We do not use that latter tail mismatch to exclude our actual Phi.

## Source defects checked before transport

On p.150, N^-1/2 in plain-text extraction must be read as N^(-1)/2,
not N^(-1/2). The displayed Hamiltonian correctly matches the explicit
critical coefficient 1/(2N). Independent visual review corrected the
parent's initial misreading; this is not a source typo.
Lemma 4 on p.152 does claim nonvanishing on D from approximants nonvanishing
only on D' subset D. That literal general statement is false. Our transport
uses the usual valid Hurwitz statement on each entire open half-plane,
where every approximant is nonvanishing. The erroneous literal lemma
is not imported as an assumption or a new theorem.

## Routing and next bounded construction test

Three dictionaries were covered: equilibrium partition functions;
probability/block-spin limits; passive/Herglotz operator response.
The Herglotz realization abstract (arXiv:math/0510464) starts from a function
already having the Herglotz property. Its full source was not fetched;
it is an excluded, unverified lead and supplies no new passivity here.
The general Lieb–Sokal closure theorem also presupposes the single-site
Lee–Yang property; applying that assumption directly to p would be circular.
Its full paper was not fetched; no verified-candidate status is assigned.

The selected next task is constructive: derive finite pair couplings and
positive block-spin weights from the actual theta source, prove convergence
to p and the required uniform tails, or exhibit the precise construction
step where nonnegative couplings are lost. A statement merely assuming
that p is Lee–Yang/GS is not a solution. This discovery pass ends here;
the production edge remains unbound and no proof admission is requested.

Input: BRIEF_2026-09-12_SOURCE_SIGN_PHYSICS_BROTHER.md,
SHA256 ef34f99ad4ae0a9aca7487b9c7c103d33490987df185b83195c78946d6756a7a,
which pins the exact accepted normalization, theta source, curvature,
all-order conditional consumer, and existing negative control at owned
commit a470fbdb6280669c2e75706050c32805831ee9c1.
Registered shelf receipts are INCOMPLETE because semantic-index freshness
validation failed; they are not absence claims. No canonical control,
index, goal registry, source-sign counter or owner claim was changed.

## Parent intake and independent receipt

Root rechecked all six local input pins, the fetched source pages, the
normalization and quantifiers, the theta tail and the exact scope of the
negative control. The mathematical body is the independently reviewed
candidate; only its status and this receipt section were added. No Lean
execution or new numerical source evaluation was needed for this discovery.

Independent reviewer: /root/sibling5_check. Exact receipt SHA256
d29c24f742e88a7c72bafcd47f6c9993221929b68724e4529f86611037d60836.
The receipt follows verbatim.

# Independent review receipt: physics brother

**Verdict:** `SOURCE_VERIFIED_DISCOVERY` at the stated conditional scope.

Reviewed candidate: `PHYSICS_BROTHER_CANDIDATE_20260912.md`, 10,365 bytes,
198 LF, final LF, no CR, SHA-256
`60f14f158c1f2ff8844034bb0f9118ca612227945d4a1c21b87b287b45f7fc82`.

The normalized identity \(M(h)=\xi(1/2+h)/\xi(1/2)\) and the following
transfer are correctly scoped: for zero-field finite ferromagnetic pair Ising
systems, \(X_N=\sum_i q_{i,N}\sigma_i\) with \(q_{i,N}>0\), weak convergence
\(X_N\Rightarrow p(x)dx\), and \(\sup_N\mathbb E e^{R|X_N|}<\infty\) for every
\(R>0\), normalized transforms converge locally uniformly on \(\mathbb C\).
Lee--Yang is then zero-free in each open half-plane, and Hurwitz applied on
each entire half-plane puts zeros of the nonzero limit on \(\Re h=0\).

This is conditional: no such finite-spin realization, convergence proof, or
uniform exponential-tail proof for the actual \(p=\Phi/Z\) is supplied.
The Simon--Griffiths quartic construction has limiting log-tail polynomial
quartic, whereas the theta source satisfies
\(-\log p(x)=\pi e^{2x}-9x/2+O(1)\) as \(x\to+\infty\); it therefore does
not furnish the actual source, while not excluding a general
Griffiths--Simon realization.

The BFS comparison and the control calculation are correctly limited:
convexity of \(v(u)=-\log p(\sqrt u)\), and likewise
\(v_c''=(1/100+3u/125+2u^2/625)/Q(u)^2>0\), do not imply Lee--Yang. The
control's off-axis zeros rule out the conjunction of the finite-spin
realization and convergence hypotheses for that control; they do not refute
all possible GS representations absent those hypotheses.

Source erratum check: the p.150 coefficient is \(N^{-1}/2=1/(2N)\), so its
Hamiltonian agrees with the displayed binomial weight; it is not a typo.
Lemma 4 on p.152 is false as literally printed with nonvanishing only on
\(D'\subset D\). The candidate correctly avoids it and uses standard
one-variable Hurwitz on each full half-plane.

No source-sign gain, source-sign counter change, canonical admission, or RH
claim is warranted by this discovery.
