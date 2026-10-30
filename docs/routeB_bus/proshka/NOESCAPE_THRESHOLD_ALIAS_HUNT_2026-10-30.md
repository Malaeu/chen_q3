# NOESCAPE: threshold binding, higher-order selection, and nonlocal localization

Status: source-verified partial mechanisms; NOESCAPE and RH remain OPEN.
Owner requested semantic alias hunt. Original CCM: N=m, L=log m,
unit even exact bottoms f_m in V_m,E; all prime powers, pole terms,
mixed terms and finite-carrier normalization remain in force.
Target: complete fixed-jet escape implies a same-carrier unit competitor
g_m with k[g_m]<k[f_m]. No automatic jet-mixing gain is available.

## Search and verified shelf coverage

The first shelf searches were INCOMPLETE because the semantic index was stale.
Canonical `orchestrator/spine.py --refresh --reason semantic-index-refresh`
completed successfully: 3743 indexed files, 25871 vectors; receipt PASS.
Three subsequent `ask.sh --deep` queries actually ran vector retrieval:

- eigenvalue absorption binding threshold non spreading repulsive tail;
- higher order Gamma development selection degenerate exact minimizers;
- nonlocal IMS localization jump form binding remainder.

Receipts: /tmp/rh_alias_threshold_ask.txt, /tmp/rh_alias_selection_ask.txt,
/tmp/rh_alias_ims_ask.txt. This is bounded coverage, not literature absence.
Useful returned local anchors were NOESCAPE_ALIAS_RETURN, CONFINE §5.1
(selection is leakage rather than ordinary tail mass), and
NOESCAPE_EXACT_MINIMALITY_TEST (projected unitary curvature with all return terms).
Other historical-sector hits do not supply the current exact consumer.

## 1. Strongest new analogue: binding at threshold

Bellazzini, Frank, Lieb, Seiringer, *Existence of ground states for negative
ions at the binding threshold*, arXiv:1301.5370; Rev. Math. Phys. 26 (2014),
1350021, DOI 10.1142/S0129055X13500219.
Source: https://arxiv.org/pdf/1301.5370
Fetched PDF SHA256: e69b737831f5918c411b3f58ad697259fca7a63b16724b4bd98caacae67d107.
Quote, §2 p.4: “prove that the weak limit of a ground state sequence”.
Root read §2 and the decisive localization proof in §4.

Their Lemma 2.1, (2.3), proves uniformly over its parameter class
(constants depend on the fixed positive delta, theta and cluster count K),
for every sufficiently large radius l,

    H-E >= -(C/l²) 1_{r<l} + (Delta+c/r) 1_{r>=l},  Delta>=0.

Taking expectation in an EXACT ground state gives

    (C/l²) mass(r<l) >= c integral_{r>=l} |psi|²/r.

Lemma 2.2 converts the inequalities for ALL l>=l0 into a uniform positive
mass in a fixed ball. Theorem 2.1 then obtains a nonzero weak limit using
uniform H¹ bounds and local compactness. The binding gap Delta may vanish.
The decisive source property is a repulsive exterior c/r term that survives
localization errors, not a fixed gap above the ground eigenvalue.
In §4 this comes from Coulomb coefficients, a partition adapted to cluster
geometry, and a separate positive gap to a more dissociated cluster.

Proposed mapping: H-E would correspond to A_m-lambda_m; mass in a fixed ball would be an
intermediate localization observable. For CCM, a uniform inequality of this
kind has NOT been derived from the full coefficients. Moreover fixed spatial
mass alone does not imply jet retention: local compactness/frequency control
is an additional unpaid step. An arbitrary pole rank-one form is not a
pointwise repulsive potential. Positive or signed escaping radical trials
must be tested before proposing such a barrier.

Centering guard: their E is an unrestricted ground infimum, while lambda_m
is a carrier-restricted minimum. An ambient H-E estimate would leave the
extra term lambda_m-E even on an exact carrier bottom. Therefore the
following control is CONDITIONAL ON A NEW inequality centered at lambda_m
on V_m,E; it is not a direct consequence of their theorem.
Exactness control under that condition: for a normalized trial q the left energy is
epsilon_m=k[q]-lambda_m, so the necessary inequality becomes

    c integral_out |q|²/r <= epsilon_m+(C/l²) mass_in(q).

Small ||A_m q|| alone does not estimate epsilon_m relative to this barrier,
since lambda_m is also needed. Thus neither zero-residual rhetoric nor
discarding the trial error is legitimate. This explicitly identifies where
exact-bottom energy zero is used. This source proves retention, not our
requested explicit competitor; it is a partial analogue, not a closed route.

## 2. A correction can select without a fixed gap

Braides, *Local minimization, variational evolution and Gamma-convergence*,
2012–13 notes, §1.5 Theorem 1.5.1 and Example 1.5.2, pp.26–27.
https://cvgmt.sns.it/media/doc/paper/2094/Corso2013LN.pdf
SHA256: 4adc1056a5ccdf5f8783f214a31ffda559b5f332adc7dd52cc5c7290c59d0b06.
Quote: “then u minimizes both F and F α”.
Example: F_e(x)=(x²-1)²+e(x-1)² selects +1 while the cost at -1 is 4e.
This is a vanishing signed correction, not a uniform positive gap.
The theorem requires the appropriate compactness and a Gamma-limit of the
rescaled energies; these cannot be assumed for escaping CCM states.

Mapping: seek a source scale rho_m and the first signed correction of the
FULL normalized form. Need a uniform lower bound at that scale for escape
and a less expensive admissible recovery family. Merely renaming this
missing separation a Gamma-limit supplies nothing. Radical quasimodes with
superpolynomial small energy challenge any polynomial-scale separation;
their energy excess above lambda_m must still be accounted for. This route
remains open; no source scale or uniform limiting functional is established.

## 3. Exact nonlocal partition identity: useful algebra, unpaid sign

Duong–Frank–Le–Nam–Nguyen, J. Math. Pures Appl. 190 (2024),
DOI 10.1016/j.matpur.2024.103598, Lemma 18, equation (29), pp.13–14.
https://epub.ub.uni-muenchen.de/125243/1/1-s2.0-S0021782424000965-main.pdf
SHA256: cea9f327fa2daacf95cfdcd10d7c3acd07e8dfd4345af5e7aaba9c6c52870dfe.
Quote: “we have the IMS formula”. Their fractional-kernel remainder is paid
using a Hardy inequality with remainder. That estimate does not transfer
automatically to the CCM arch-plus-atomic jump measure.

For Q_s[f]=||f-T_s f||² and real chi²+eta²=1, direct expansion gives

 Q_s[chi f]+Q_s[eta f]-Q_s[f]
 = integral Re(f(x)conj(f(x+s)))
   *[(chi(x)-chi(x+s))²+(eta(x)-eta(x+s))²] dx.

Integrate with j(s)ds and sum with EVERY Lambda(n)/sqrt(n), 2<=n<=m.
This retains the exact jump localization remainder; signed f gives no
automatic sign. Even cutoffs retain parity but leave the finite carrier.
Pole cross terms, P_m return, nonzero returned norm and renormalization
must all be included before any energy comparison. A binding margin must
strictly exceed those costs; none is proved from escape at present.

Independent bounded PAPER review checked the threshold mechanism, IMS algebra,
and refreshed search receipts; the centering and parameter-uniformity guards
above incorporate its corrections. No CCM transfer was admitted.

## Controls and next bounded test

The rank-one negative control is Dobosevych–Hryniv, arXiv:2006.12241v1,
Lemma 2.3, DOI 10.1016/j.laa.2020.09.027.
https://arxiv.org/abs/2006.12241v1
SHA256: c0a701964185194c3a7079133e73c1d22f9dbee7b3b99910689308fbb81679f0.
Quote: “if and only if a_n b_n = 0”. For self-adjoint J+uu*, a J-eigenmode
orthogonal to u survives exactly. Nonzero coordinates of u in the Fourier
basis do not prove nonzero overlap in the J eigenbasis.

Agmon/weighted-volume search also found Marx–Zhu arXiv:2101.02803v1,
Theorem 2.3, equations (29)–(35). It requires a local scalar potential and
an exterior coercivity parameter; no direct CCM map was found. It is not
being promoted as another supplier.

Preferred bounded continuation: test a source-derived exterior barrier
against the known translated radical packets, retaining the actual excess
k[q]-lambda_m. Determine whether jump, pole and carrier-return terms admit
a positive exterior coefficient with a lower-order localization cost.
If only a physical-space mass bound results, explicitly supply the additional
local compactness/jet-observability bridge before claiming T. In parallel,
the signed correction and other same-carrier competitors remain allowed.
No claim of negative curvature, strict descent, NOESCAPE or RH is made here.

Owner follow-up: Gridnev–Garcia math-ph/0610038v2 was then read at
Theorems2–3, (45)–(47), and AppendixA. See NOESCAPE_GRIDNEV_GARCIA_BRIDGE:
positive Green domination from compact attraction differs from IMS absorption;
finite CCM compression and local compactness remain unpaid. Primary PDF saved.
