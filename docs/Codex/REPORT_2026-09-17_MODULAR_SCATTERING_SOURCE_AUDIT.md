# The same zeta source in modular scattering: the exact energy boundary

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete.

This is the third return recorded in the existing global Pick mechanism brief,
based at a9ec16240e8f87b3d97987e359d34db3d46af12e. It is an isolated analytic
source/domain audit. The canonical production HOLD, goal, phase, counters and
PAUSED heartbeat are unchanged. Consumption: INCOMPLETE_NO_CONSUMABLE_TARGET;
the canonical exact theorem/consumer edge is not selected. No admission or new
proof dispatch is made.

**Result in plain language.** The sought arithmetic brother exists: modular
scattering contains exactly the same zeta function. Its positive truncated
energy is also real mathematics. But a zeta zero corresponds to a field whose
untruncated norm is infinite. The full cutoff identity explicitly accounts for
that infinity and does not select the critical line. This identifies a precise
failed inference, not a proof or disproof of original V. A published route from
truncated energy to Weil-type lower bounds was found; its correction terms and
normalizations cannot be dropped.

## S0. Source and target kept separate

The actual source is

\[
r(t)=\sum_{n\ge1}(4\pi^2n^4t-6\pi n^2)e^{-\pi n^2t},\quad
\Phi(x)=e^{5x/2}r(e^{2x}),\quad
F(z)=\xi(\tfrac12+iz)/\xi(\tfrac12).
\]

Here the project's **entire** xi is
\(\xi(w)=\tfrac12w(w-1)\Lambda(w)\), whereas
\(\Lambda(w)=\pi^{-w/2}\Gamma(w/2)\zeta(w)\) is meromorphic.
The full original target, with \(f=\Phi/\|\Phi\|_2\), is

\[
V(x,y)=\int_0^\infty(2X+x+y)f(X+x)f(X+y)\,dX,
\qquad \sum_{i,j}\bar c_iV(x_i,x_j)c_j\ge0
\]

for all admissible finite complex families. No identity equating this form to
an Eisenstein norm is assumed or established here. The previously audited full
Weil transfer remains the consumer; the new objects are exploratory suppliers.
Source pins are embedded in the review certificate.

## S1. Verified discovery evidence and exact dictionary

Three primary PDFs were fetched and read; the critical equations on PRR p.4,
Goldfeld p.8, and Wong pp.12,19,20 were also visually inspected. Quotes below
are short literal excerpts; mathematical formulas following them are separately
normalized and checked. No novelty claim is made.

| Source and locator | Short quote | Local PDF SHA256 | Mapping and strength |
|---|---|---|---|
| [Petridis, Raulf, Risager, arXiv:1111.6615v1](https://arxiv.org/pdf/1111.6615v1), p.2, paragraph preceding (1.4); p.4, (2.1)-(2.3) | “As these states are not in L²” | 2f132fcc98f76f3c79853b497bdf6f2ddf292c672cc21022bbcc65c46eb82fb6 | Exact same-zeta scattering formula. Their xi is our Lambda; their simple-pole state is extended below using the highest Laurent coefficient, without a simplicity assumption. Not positivity of V. |
| [Goldfeld, Arthur's Truncated Eisenstein Series for SL(2,Z) and the Riemann Zeta Function, A Survey](https://www.math.columbia.edu/~goldfeld/Exploring.pdf), p.8 Theorem 4.1; p.9 Lemma 4.2; pp.10-12 applications | “Maass-Selberg Relation” | da2ce5e958da27fb20f17b1cc0cbff4f17c24e28efa76590f47aba7d5d4f0209 | Exact truncated inner-product identity, cutoff Y>=1. Applied below on the actual modular quotient, not an abstract positive operator. Applications give known zero-free regions, not RH. |
| [Tian An Wong, Explicit formulas for the spectral side of the trace formula of SL(2), arXiv:1608.02296v2](https://arxiv.org/pdf/1608.02296v2), pp.18-20, Lemma 5.1, Remark 5.2, section 5.2; pp.10-12 test map | “an integral of the usual L²-inner product of truncated Eisenstein series” | bc4c09e40a2e1d9d01797274bba875357f9d689688e288c1ba61ffd5aa01a7ae | Verified partial analogue: averaging cutoff norms on convolution-square tests. The explicit zero-sum lower bound is NOT imported as an exact original-Weil estimate; see S6. |

The three dictionaries were arithmetic (completed zeta, Eisenstein constant
term, prime divisor sums), operator theory (self-adjoint Laplacian, domain,
truncation, Maass-Selberg), and scattering (resonance, outgoing state, boundary
flux). The negative control for the bare positive-operator inference is S7.
It fails the finite-energy eigenvector hypothesis but has a positive operator,
as do the actual resonant states in S3. It is not a modular or V counterexample.

Registered shelf queries were run once for these exact strings:

- `modular surface Eisenstein scattering zeta resonances`;
- `Maass Selberg truncation residue cusp L2`;
- `Robin half line positive operator resonance outgoing`.

All returned exit 2 / INCOMPLETE due to semantic-index freshness validation,
not a no-hit result. Receipt SHA256s respectively:
1117bfb6affd3b39502b1770c8e264e188e3805f07baac9548b28dec23bc36e9,
b5715f0c7b6a04debc0c7a60280e3907fead9f7ace0787437888bcbad58b896a,
a144e97c4d7a596de00d100ba6004317fa5193e950cc708ad65ce5cf72b43a8a.
Local reservoir, hyperbolic-source and Bessel reports were reconciled first;
none supplied this exact modular source/domain check. The old broad
Maass-Selberg query was reused, not repeated. Two bounded Consensus discoveries
and primary title/URL resolution supplied the three sources above. No index
refresh, shelf mutation or additional source-family search was performed.

## S2. Exact zeta-zero to scattering-pole map, including multiplicity

Let \(\mathscr X=\mathrm{PSL}_2(\mathbb Z)\backslash\mathbb H\),
\(d\mu=dx\,dy/y^2\), and initially for Re s>1 set
\(E(z,s)=\sum_{\Gamma_\infty\backslash\Gamma}\operatorname{Im}(\gamma z)^s\).
Its meromorphic continuation has constant term

\[
E_0(y,s)=y^s+C(s)y^{1-s},\qquad
C(s)=\frac{\Lambda(2s-1)}{\Lambda(2s)}
=\frac{\Lambda(2-2s)}{\Lambda(2s)}
=\frac{s}{s-1}\frac{\xi(2s-1)}{\xi(2s)}. \tag{S2.1}
\]

The rational prefactor in the entire-xi notation must not be omitted. It
follows by cancelling the factors in \(\Lambda(w)=2\xi(w)/(w(w-1))\).

For any nontrivial zeta zero \(\rho=\beta+i\gamma\), 0<beta<1, of
multiplicity m, put \(s_0=\rho/2\). Then
\(\Lambda(2-2s_0)=\Lambda(2-\rho)\ne0\): Re(2-rho)>1, where the Euler
product converges absolutely and is nonzero, and the gamma factor is finite
and nonzero. Thus C has a pole of **the same order m** at s0. No numerator
cancellation and no simple-zero hypothesis were used. Conversely a pole in
0<Re s<1/2 can only come from a nontrivial zero in the denominator, since
the numerator is holomorphic there.

This is where a concrete property of primes works: absolute convergence and
nonvanishing of the Euler product on Re w>1 rules out cancellation of the
pole. Theta reciprocity supplies the functional equation used in the numerator.
Neither fact locates this pole on Re s=1/4. RH is equivalent to that location
for all these poles. The coordinate map is rho=2s, not rho=s.

## S3. The actual pole field is outside the positive operator's L2 domain

Write
\(C(s)=A(s-s_0)^{-m}+O((s-s_0)^{1-m})\), A!=0, and let U be the
coefficient of \((s-s_0)^{-m}\) in E. The full Fourier expansion PRR (2.2)
shows that U has constant term \(Ay^{1-s_0}\) and exponentially decaying
nonconstant terms. The factor \(1/\Lambda(2s)\) gives at most order m in
those terms, so this is the highest Laurent coefficient of E as well.
All statements hold for each fixed s0; locally uniform convergence and
derivatives follow from exponential Bessel decay for y bounded below in the
cusp and bounded spectral parameters.

Let sigma=Re s0=beta/2. By the mean-square inequality in x, for Y>=1,

\[
\int_Y^\infty\int_{-1/2}^{1/2}|U(x+iy)|^2\frac{dx\,dy}{y^2}
\ge |A|^2\int_Y^\infty y^{-2\sigma}\,dy=\infty. \tag{S3.1}
\]

Consequently U is not an L2 eigenvector of the positive self-adjoint modular
Laplacian. It still satisfies the differential equation
\(\Delta U=s_0(1-s_0)U\), obtained from the highest Laurent coefficient.
For gamma!=0 its spectral parameter has imaginary part
\(\operatorname{Im}s_0(1-2\sigma)\ne0\), consistent with its failure to
belong to the operator domain. Positivity of the self-adjoint operator does
not impose real spectral parameters on these continued, non-L2 solutions.

## S4. Full Maass-Selberg identity and its exact pole limit

For a fixed Y>=1 use Arthur truncation \(\mathcal T_Y\); on the standard
fundamental domain it removes \(y^s+C(s)y^{1-s}\) above y=Y, retaining all
nonconstant terms. Goldfeld Theorem 4.1 and Lemma 4.2 give, at regular
parameters (singular denominators interpreted by continuation),

\[
\begin{split}
\langle\mathcal T_YE(s),\mathcal T_YE(w)\rangle={}&
\frac{Y^{s+\bar w-1}}{s+\bar w-1}
+\overline{C(w)}\frac{Y^{s-\bar w}}{s-\bar w}
+C(s)\frac{Y^{\bar w-s}}{\bar w-s}\\
&+C(s)\overline{C(w)}\frac{Y^{1-s-\bar w}}{1-s-\bar w}.
\end{split} \tag{S4.1}
\]

Here the inner product is linear in the first variable. Set w=s and
multiply by \(|s-s_0|^{2m}\). Since 0<sigma<1/2 and Im s0!=0, all displayed
denominators have nonzero limits. The first term and both mixed terms vanish;
the last term survives. On the left, the Laurent expansion after truncation
converges in L2: the domain below Y is compact, and above Y the remaining
Fourier series has uniform exponential decay near the fixed pole after
multiplication by \((s-s_0)^m\). Therefore

\[
\boxed{\|\mathcal T_YU\|_2^2
=\frac{|A|^2}{1-2\sigma}Y^{1-2\sigma}
=\frac{|A|^2}{1-\beta}Y^{1-\beta}.} \tag{S4.2}
\]

This is an exact positive norm for the actual scattering field, including
the entire source, all Fourier modes, and the truncation boundary. It is not
an asymptotic tail estimate. Its right side is positive for every beta in
(0,1); the identity therefore supplies no contradiction for a hypothetical
off-critical zero. This does not assert the existence of such a zero.

For u=U/A the coefficient is exactly 1/(1-beta). Subtracting that entire
cutoff contribution leaves zero for every Y, irrespective of beta. This
renormalized zero has erased the information one would need for RH; it is
not a positive representation of V. For example, an additional bound
\(\|\mathcal T_Yu\|^2=O_{\rho,\epsilon}(Y^{1/2+\epsilon})\) for every
zero and every epsilon>0 would force beta>=1/2. By functional-equation
reflection that would give RH. But by (S4.2) it is **equivalent** to that
restriction on zeros, not an independently obtained source estimate.

## S5. Where this energy method already works, and why that does not transfer

Goldfeld pp.10-12 explains the actual Selberg/Sarnak use of Eisenstein series
to obtain zero-free statements at Re rho=1 and near that line. The mechanism
is concrete. In the completed series \(E^*(z,s)=\Lambda(2s)E(z,s)\) the
constant term is

\[
\Lambda(2s)y^s+\Lambda(2-2s)y^{1-s}. \tag{S5.1}
\]

If hypothetically rho=1+i gamma were a zero, at s=rho/2 both coefficients
would vanish, because 2-rho=bar rho. The nonzero, rapidly decaying field
would then be a cusp form, orthogonal by unfolding to the Eisenstein family;
continuation to itself contradicts its positive norm. This is the known
mechanism described in that source, not a new theorem claimed here.

In the interior 0<beta<1 only the first coefficient vanishes. The second
is nonzero by S2. That is the precise break in this proof when moving toward
the critical line. The source's further lower-bound argument uses nonconstant
Fourier coefficients and the divisor sums \(\sigma_{-2it}(n)\). At primes
these are \(1+p^{-2it}\); the stated sieve input supplies a positive proportion
not too close to cancellation and hence a lower bound for an averaged norm.
We record this as the published application's input, not as an independently
proved sieve estimate or an estimate in the missing critical strip.

## S6. Wong's lower-bound brother: verified structure, unimported correction

The found paper is a useful **partial** match, beyond a mere similar name:
Lemma 5.1 proves positivity of the truncated spectral distribution on group
convolution squares. Remark 5.2 gives the classical scalar mechanism
\(\int\|\mathcal T_YE(1/2+it)\|^2|h(t)|^2dt\ge0\).
That nonnegativity itself is immediate whenever the integral exists; for
compactly supported smooth h away from t=0 it needs no endpoint prescription.
It includes all mixed coefficients when h is a finite linear combination.
It still is not V, and compact spectral support is not the original full
compact spatial test class.

In the paper's unitary-axis coordinate v=2s-1, its normalizing scalar is
\(m(v)=\Lambda(v)/\Lambda(1+v)=C((1+v)/2)\). Thus its imaginary axis
corresponds to Re s=1/2, while zeta-zero poles occur at v=rho-1. This is not
the original Fourier coordinate z in F(z). The paper's test transport and
involution must be tracked under this change, not identified by their names.

There are explicit unpaid points before importing its advertised lower bound:

1. Section 3.1 after Lemma 3.4 asserts all scalar tests can be obtained, but
   the displayed spherical Harish transform lands in the **Weyl-invariant**
   space. The proof of Theorem 4.1 also uses evenness of the transformed test
   (p.12). A lift preserving the required complex convolution square for our
   entire target class is not supplied by that assertion alone. This is a
   gap in this proposed import, not a claim that no suitable lift exists.
2. The introduction, section 2.1, and Remark 5.2 use differently centered
   involutions. A correct full Weil test uses the appropriate conjugation as
   well as inversion and its weight. We do not silently identify those stars.
3. In the fetched v2, the scalar expression on p.12 Theorem 4.1 and its use
   on p.20 section 5.2 have opposite printed signs for the gamma constant
   (log(4pi)-gamma versus log(4pi)+gamma) and for the quarter-star term inside
   the first integral. These differences were checked in rendered pages;
   they are not extraction artifacts. We do not choose one formula or repair
   them without a separate derivation. This does not refute the core norm
   positivity of Lemma 5.1.
4. Even a corrected exact identity retains cutoff, scattering, pole and
   archimedean terms. Positivity of their total yields a lower bound with
   these terms present, not the zero lower bound needed for the full Weil
   form. No sign of that complete correction is proved here.

Thus no formula from the explicit RHS of the paper's (1.4) is consumed in
this report. S2-S4 rely on the separately fixed full Fourier expansion and
Maass-Selberg identity and are unaffected by these discrepancies.

## S7. Elementary negative control for the abstract inference

On the half-line let H=-d²/dx² with u'(0)=a u(0), a>0. Its self-adjoint
quadratic form is \(\int_0^\infty|u'|^2dx+a|u(0)|^2\ge0\).
For the incoming/outgoing solution
\(u=e^{-ikx}+R(k)e^{ikx}\), the boundary equation gives

\[
R(k)=\frac{ik+a}{ik-a}.
\]

It has modulus one for real k, but a pole at k=-ia. The outgoing solution
there grows as e^{ax} and is not in L2. Hence positive energy and real-axis
unitarity do not force all poles of a meromorphically continued response to
be real eigenvalues. This calculation diagnoses only that bare inference;
it preserves neither the modular arithmetic source nor the target V.

## S8. Decision and bounded stopping point

The arithmetic mapping, the pole multiplicity, and the precise cutoff norm
are usable audited facts if independently accepted. They answer why a
positive field by itself does not solve the problem. The PRR and Goldfeld
sources are exact matches for that diagnostic; Wong is a partial analogue
whose explicit full-form import remains unverified.

No hypothesis about zeros was inserted into a positive square root or field
construction. Conversely, no source property in this audit proves a zero
lower bound for original V. This pass therefore stops before another request
to prove a renamed RH-equivalent growth bound. A continuation using Wong
would first need one corrected, consistently centered scalar identity with
all boundary terms and a proved test-class transfer, then an independently
justified sign mechanism. That is a distinct bounded normalization audit,
not a current proof request and not automatic expansion of this hunt.

No original negative witness, global Pick result, global VAR result, full-V
sign result, or RH proof/refutation is obtained. No Lean run is claimed.

## Independent acceptance and source version check

Verdict: ACCEPT_MODULAR_SCATTERING_SOURCE_AND_CUTOFF_AUDIT_ONLY.
Candidate SHA256: 4a844ca2122f77b3767aa3f03af031a3c6724a6c2836a7db7603e814ac5ad9d6.
Full review SHA256: b373962164cfbd98d3609e6a7e655b96d63e62d9a9203e3429699db6260d6894.
Full parent check SHA256: f436ee054c5929134a7459c4bb3d91c16330d3dde5b496a51c34bf76059d4da2.
The parent read the entire review before accepting these limited conclusions.
No formula correction to the candidate was needed. A further version check
against the published PRR article (CMB 56 (2013), pp.815,817-818,
(2.1)-(2.2)) confirmed all Fourier/scattering formulas used here; published
PDF SHA256 013330e90be70232d12aa90fbdd7ab82f1745f69fd36322fc356e509c1a95e26.
None of PRR's quantum-limit asymptotic theorems is used.
The certificate embeds both full checks and source hashes. This accepts no
original-V sign, no RH claim, and no exact import of Wong's explicit RHS.
