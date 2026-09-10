# Local completeness of the exact theta derivative shells — 2026-09-10

STATUS: INDEPENDENTLY_CHECKED_PAPER_LEMMAS_L1_L5; L6_UNPROVED
BASE: 72c59971433a2b79cef5a58f886dffb73ce87fe9
SCOPE: fixed-window E-density and existential transfer, not a cofinal energy estimate or a lower-sign proof.
PX_RH_CLAIM: NOT_MADE

## 1. Exact objects and proposed conclusion

Use BRIDGE section 1 verbatim: E has squared norm W+D, where

\[
W[f]=\int_{\mathbb R} e^{2|x|}|f(x)|^2dx,\qquad
D[f]=\int_0^\infty A_0(u)\|f(\cdot-u)-f\|_2^2du,
\quad A_0(u)=\frac{e^{-u/2}}{1-e^{-2u}}.
\]

Fix any real a>0. Let V_a be the E-closure of C_c^infinity(-a,a), and V_a^even its even subspace. Reflection is an isometry of E: W is invariant and the L2 norm of a forward translation difference equals that of a backward difference. Thus symmetrizing the compact smooth core gives a dense core for V_a^even.

Retain the exact theta source Phi, g_0=(partial_x^2-1/4)Phi and g_{2j}=partial_x^{2j}g_0. Put N^2=||1_in Phi||_2^2, p=1_in Phi/N, alpha_j=N^(-2)<1_in Phi,1_in g_{2j}>, and d_j=1_in(g_{2j}-alpha_j Phi). Pairings are antilinear first. N>0 and ||p||_2=1. These are exactly BRIDGE's unscaled source directions.

The proposed fixed-window statements are

\[
\overline{\operatorname{span}_{\mathbb C}\{1_{(-a,a)}g_{2j}:j\ge0\}}^{E}
=V_a^{\rm even},                                                   \tag{L1}
\]
\[
\overline{\bigcup_m S_{m,a}}^{E}
=\{z\in V_a^{\rm even}:\langle p,z\rangle=0\}.                    \tag{L2}
\]

No assertion about density of the uncut radical in global E, or about density on the unbounded exterior, is made.

## 2. A bounded sharp-cut map, including endpoints

For a C1 profile v on [-a,a], write M_0=||v||_infinity and M_1=||v'||_infinity and f=1_in v. Over the overlap of the two intervals the mean-value bound gives 2a u^2 M_1^2. Their symmetric difference has measure at most 2u, giving 2u M_0^2. Consequently, for 0<u<=1,

\[
\|U_uf-f\|_2^2\le 2a u^2M_1^2+2uM_0^2.
\]

This also holds when u>=2a: the intervals are disjoint and 4a M_0^2<=2uM_0^2. For u>=1 use ||U_uf-f||_2^2<=4||f||_2^2<=8aM_0^2. Concavity gives A_0(u)<=4/(3u) for u<=1; for u>=1, A_0(u)<=4e^(-u/2)/3. Integrating yields

\[
\|1_{(-a,a)}v\|_E^2
\le\left(2ae^{2a}+\frac83+\frac{64a}{3}\right)M_0^2
   +\frac{4a}{3}M_1^2.                                            \tag{L3}
\]

The last coefficient on M_0 is deliberately enlarged by replacing e^(-1/2) with 1. This is a bound for each fixed a, not a bound independent of a.

For a smooth profile v near [-a,a], the cut belongs to V_a. Indeed choose a smooth inward cutoff chi_eta, equal to 1 on [-a+eta,a-eta] and zero outside (-a+eta/2,a-eta/2), with monotone transitions. The error h_eta=1_in v-chi_eta v has support of length at most 2eta, ||h_eta||_infinity<=M_0, ||h_eta||_2^2<=2eta M_0^2, and total variation at most 4M_0+2eta M_1. Therefore

\[
\|U_uh_\eta-h_\eta\|_2^2
\le\min\{2M_0(4M_0+2\eta M_1)u,8\eta M_0^2\}.
\]

Split the Dirichlet integral at eta and 1. For 0<eta<min(a,1) the resulting E-error squared is O_(a,v)(eta(1+|log eta|)), tending to zero. The two jumps are included in total variation. This proves the claimed membership for p and every cut g_{2j}; it also justifies the sharp-cut smooth profiles used below. L3 is the continuity bound needed for analytic parameter differentiation.

## 3. General analytic-kernel completeness lemma

Let g be a nonzero even Schwartz function on the real line that extends holomorphically to a connected strip |Im z|<sigma, sigma>0. Then for every a>0 the cut even derivatives {1_in g^(2j)} span an E-dense subspace of V_a^even.

Proof. Suppose their E-closed span is proper. Hahn–Banach gives a nonzero continuous complex-linear functional L on V_a^even annihilating every cut even derivative. For a compactly supported smooth test psi define

T(psi)=L(1_in psi_even),   psi_even(x)=(psi(x)+psi(-x))/2.

By L3, T is a distribution of order at most one, supported in [-a,a]; it is even. If T=0 then L vanishes on the even compact smooth core and hence on V_a^even, contradiction. Thus T is nonzero. A compactly supported distribution acts on arbitrary smooth profiles through any cutoff equal to 1 near its support.

Set F(z)=T_x[g(x-z)] on |Im z|<sigma. This is holomorphic: on each compact subset of the strip the profile and its first x-derivative depend holomorphically on z in C1([-a,a]); apply the continuous distribution T, equivalently L and L3. Evenness of T and g makes F even. For every j, F^(2j)(0)=T[g^(2j)]=0 by the annihilation assumption; odd derivatives vanish by evenness. Its Taylor series at 0 is zero. The identity theorem on the connected strip gives F identically zero.

On the real axis F=T*g, since g is even. Convolution of a compactly supported distribution with a Schwartz function is Schwartz, and

\[
\widehat F(\xi)=\widehat T(\xi)\widehat g(\xi)=0.                 \tag{L4}
\]

The Fourier transform of a compactly supported distribution is entire. The continuous Fourier transform of the nonzero Schwartz function g is nonzero on some nonempty open real interval. L4 forces the entire function T-hat to vanish on that interval, so T-hat is identically zero. Fourier injectivity gives T=0, a contradiction. This proves the lemma. No assumption that g-hat is everywhere nonzero is used; isolated or other spectral zeros do not obstruct this compact-support argument.

The standard background facts used here are Hahn–Banach separation, uniqueness for holomorphic functions, and the elementary Fourier transform/convolution rules for compactly supported distributions and Schwartz functions. They are invoked as classical analytic facts, not as compiled Lean declarations or newly verified external-paper citations.

## 4. Application to the exact theta source

The series defining Phi is normally convergent on every compact subset of |Im z|<pi/4: Re(e^(2z))=e^(2Re z)cos(2Im z) is bounded below there by a positive constant, so polynomial powers of n are dominated by exp(-c n^2). All complex derivatives are normally convergent there as well. Thus Phi and g_0 are holomorphic in that strip.

Theta inversion gives evenness; the positive real tail and every fixed derivative decay double-exponentially, and evenness gives the negative tail. In particular g_0 is even and Schwartz. Phi is nonzero: every summand at x=0 has coefficient pi n^2(2pi n^2-3)>0. If g_0 were zero then Phi would solve Phi''=Phi/4 on R; the only Schwartz solution Ae^(x/2)+Be^(-x/2) is zero, a contradiction. These checks use the source itself and the same theta-inversion fact as BRIDGE section 1; no statement about zeta-zero locations is used.

The general lemma with g=g_0 proves L1. The projection

P_p f=f-p<p,f>

is continuous in E, since ||p||_2=1 and |<p,f>|<=||f||_2<=||f||_E. It maps V_a^even onto its p-orthogonal subspace. Direct substitution gives P_p(1_in g_{2j})=d_j. Applying this projection to approximants of any z orthogonal to p proves L2.

## 5. Exact consequence and remaining obstacle

For every fixed a, {p-z:z in union_m S_(m,a)} is E-dense in

A_a={f in V_a^even:<p,f>=1}.

BRIDGE B2 gives Q[w_c]=N_a^2 Q[f_c], and B17 defines D_infinity as the infimum of Q[w_c] over all finite shells. B1 gives continuity of the full signed form, with all prime powers, poles and mixed terms retained. Combining these exact identities with L2 yields, in the extended real line,

\[
D_\infty(a)=N_a^2\inf_{f\in A_a}Q[f].                            \tag{L5}
\]

To check both inequalities: each shell trial lies in A_a; conversely approximate any f in A_a by p-z_m and use continuity of Q. If the affine infimum is -infinity, approximate successive trials with arbitrarily negative finite energies. This uses no positivity, invertibility or attainment assumption.

There is a useful budget-preserving existential transfer. Let b(a)>0 be any prescribed budget, and suppose a chosen f_a in A_a satisfies Q[f_a]<=b(a). By L2 choose a finite-shell trial f_(m,a) with E-error e(a)>0 so small that

\[
22e(a)(2\|f_a\|_E+e(a))\le b(a).
\]

Then Q[f_(m,a)]<=2b(a), with the same exact affine normalization. Since m(a) was unrestricted in BRIDGE, pointwise selection for each a is sufficient; no common density rate is needed for this implication. This proves a transfer theorem conditional on the existence of the full-space tests f_a. It does not supply those tests.

Specifically the unpaid upper-rate problem remains

\[
\exists K>0,\mu\ge0,a_0\ge1\quad\forall a\ge a_0:
\left[\inf_{f\in A_a}Q[f]\right]_+
\le K e^{\mu a}T(a)^2.                                          \tag{L6}
\]

By L5 this is exactly BRIDGE's ATOM, now with the independently checked source-family transfer L1–L5. The fixed-test Fourier approximation in DIRECT_WEIL_SOURCE_PROOF section 7 by itself does not establish L1 or L6: it uses another family and its constants depend on the fixed test.

For orientation only: on a window where the full even-space self-adjoint form operator A is strictly positive, the standard constrained minimization would give inf_(A_a)Q=1/<p,A^(-1)p>. This requires the actual full form operator and its positivity/domain hypotheses; none is claimed here. In particular L5 neither grants these hypotheses nor proves a lower-sign supplier.

## 6. Falsifiers, limits and next use

- Do not replace local completeness by global E-density of the uncut radical. Continuity of Q would then force Q to vanish on global E; that is a different and false conclusion. Compact support of the separating distribution is decisive above.
- Do not apply the proof to the unbounded exterior; the Fourier transform of an exterior-supported distribution need not be entire.
- Linear independence alone gives neither L1 nor L6; the proof uses holomorphy, compact support and Fourier uniqueness.
- Finite Gram matrices, small pivots and approximate numerical rank do not verify this density theorem or L6.
- No bounds on coefficients, condition numbers or degree growth are obtained. This is adequate only for BRIDGE's unrestricted existential schedule.
- The global lower-sign problem remains separate. An arbitrarily small upper trial energy does not prove nonnegativity for all tests.

Proposed next use after independent review: ask Proshka to attack L6 by constructing full-space affine trials or a source resolvent/reproducing-kernel estimate, with L1–L5 paying the previously unpaid transfer back to the exact derivative family. The old finite tests are closed: at a=.7,m=6, Q[f_y]/T^2 in [1.069376842,1.069376844], while Q[f_B]/T^2 in [2.268595464 +/-1.90e-10]. No new numerical run is requested by this note.

## 7. Independent check and provenance

Two consecutive read-only passes of the entire derivation found no incorrect assertion. Both returned only WORDING: explicitly cite BRIDGE B2 and B17 in the derivation of L5, in addition to continuity B1. That dependency locator is now explicit in section 5. L1–L5 are accepted as paper lemmas at the stated scope; L6 is an unproved target, and no Lean admission is asserted.

| Pass | Severity | Finding — English term + Russian explanation | Fix applied |
|---|---|---|---|
| 1 | WORDING | Dependency locator — явно назвать тождество энергии и определение инфимума | B2 and B17 added before L5 |
| 2 | WORDING | Dependency locator — повторная проверка, других пробелов нет | Same explicit locator correction |

The parent independently checked the normalization P_p(1_in g_{2j})=d_j, the three integration coefficients 8/3, 64a/3, 4a/3 in L3, and the factor N_a^2 in L5 against BRIDGE B2/B17. No numerical experiment is evidence for density. FIRST_INCORRECT_ASSERTION: NONE_FOUND.

Primary local dependency: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_BRIDGE_2026-09-09.md at commit4ae462655affe4e3511a765a54a04a6510338f72, SHA256 0d2117118585b58acc6f765f3692b5d536e3fb832039c29d9680e12ebbaf0550, sections1–2 and5, especially B1,B2,B17–B18. Its independent check is docs/routeB_bus/BRIDGE_INDEPENDENT_CHECK_2026-09-10.md. No prior verdict is elevated to an axiom.

Discovery preceded this note: ordinary and deep ask.sh searches for 'derivative shell density', plus targeted source search for Hahn–Banach, analytic convolution and derivative-span density. The inspected hits supplied context rather than this exact lemma; no global absence-of-literature assertion is made. No external paper was consulted for this note.
