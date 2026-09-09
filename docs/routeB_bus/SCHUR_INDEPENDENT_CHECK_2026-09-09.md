# SCHUR verdict — independent mathematical check (2026-09-09)

Target: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCHUR_2026-09-09.md`.

**Result: ACCEPTED as a partial paper derivation. FIRST INCORRECT ASSERTION: NONE FOUND.** The finite construction, tail identities, singular-branch counterexample and S18b survive independent checking. The cofinal \(T^2\) estimates remain unproved.

The actual inventory contains **43 tagged displays**, not 41: S1–S41, S18b and S26b. Every tag is covered below.

This was a fresh, read-only mathematical audit, not automatic approval review. I read all 795 target lines, the complete 89-line request, the complete 268-line DISTANCE independent report, the observer brief and the prescribed §3b. Computations ran through Python standard input; no report, source file, commit or push was created by this checker. Numerical values below are independently calculated diagnostics, not interval certificates or substitutes for the supplied symbolic arguments.

## Scope and byte verification

The checked verdict has:

- SHA-256: `7717cb8106b543339909d734f0128f2e45d3d8df33bf384ff0c2476fa4e38cab`
- Git blob: `84c1ae8791f5124cf676426cfc927898e052d61e`
- 58,293 bytes, 795 lines.

The request was recovered directly from commit `e11338a3a9132c88895b565d74ce189503d1c642`:

- Git blob: `2b3dab1d1eb6cda458bb0d12a96cf8209660f271`
- SHA-256: `4c082be285b9d38df78d8e9ef50771798db1469492ed0ab22602ab7520ab418f`
- 13,296 bytes, 89 lines, final LF present.

For **every** shelf row I ran `git show SOURCE_BASE:path`, calculated its full SHA-256, and independently resolved its Git blob. Here `SOURCE_BASE=e4fa8439f2dd98b3b7192cbb4dbe06d102425be8`.

| Key | Recomputed SHA-256 | Resolved Git blob | Result |
|---|---|---|---|
| B | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | MATCH |
| D | `2ad89fd43395242af8de2ed61383dd481057ae079cbd109aa32443e25edf1c5c` | `11979ce43d5e974080afa6690bb81e07f67f745e` | MATCH |
| I | `a54961ff784e6f1272a4b30cd4140ee320499101187bb7b95ea35c96b3d3f43d` | `168606c055b4839a0cbe1d51256cfae542e6d9e6` | MATCH |
| S | `3db1149291635de9dbca9148c778a8cef904ddac2e930a3b846b117a8bca4393` | `c7220e653535515aab013e63ea25f295cfc2a45c` | MATCH |
| A | `7027bf2b5323f183b2e8af298230d68685c423fb31e4585d571f002626e80f04` | `e456429ba1a55ca04d70d7c3e571979a14aa56aa` | MATCH |
| W | `3807727e0eb78dd7208003753f1c7e97a9f424b7c069a0c45d58dcee972ad123` | `420b11653591629b38fefaa2ba533c19a823154a` | MATCH |
| O | `667899c1bcf620be3c662daad8a1073d3964b16bc15564ed0e7331fc8e7756ca` | `608142948a8e6c7bff506b213c6b49268bd4c97d` | MATCH |
| V | `545b47b24175b6e04b458da1b06bb827f7c52f162a10437d1d866ef647a73f3c` | `ddce881cd1c51c46b397c26633fdba217aae2a26` | MATCH |
| C | `e52f96dff9c04d76963d285ce9055d21f95cc0a340b9c9b3bde67a5bed7db6dc` | `4b62261b2b17416854702e0bd0c178a87844fc20` | MATCH |
| K | `e91899971d56423cea42cfb8ba0c1a1f8a8980b90ac3990f69273a1dfdf1cca5` | `d171a2fb7b6b917a1780656952b1db5458cc9a34` | MATCH |

These checks complete the target verdict’s eight outstanding shelf checks. **They certify bytes, not mathematics.** Hashing a shelf object is not a claim to have mathematically audited every assertion in that object.

## Classification convention

- **VERIFIED** means the displayed definition, identity, estimate or explicitly conditional implication has an independent derivation below or in its table row.
- **PLAUSIBLE** identifies an expressly unpaid quantitative target. It does **not** assign a probability or claim evidence for its universal truth.
- **WRONG** would identify a mathematical error at the scope actually asserted.

Thus a verified equivalence to a determinant test does not verify that the determinant has the required sign.

All line locators in the following table refer to the checked target file identified above.

## Complete per-display check

| Tag | Locator | Status | Independent derivation / reproducible evidence |
|---|---|---|---|
| S1 | §1.1, lines 142–149 | **VERIFIED** | The geometric functional on p.1 of the locally read Suzuki v1 source becomes this form after swapping the linear-first pairing and rewriting the archimedean term as translation differences. The constant shift is \(2\int_0^\infty A_0(t)(1-e^{-t/2})dt=\log2+\pi/2=2.26394350735484192865\). Hence \(c_A=5.37218341922566558223\). Prime coefficient, both pole terms and mass sign agree. |
| S2 | §1.1, lines 159–161 | **VERIFIED** | Weighted Cauchy–Schwarz gives translation factor \(e^{-|t|}\) and moment-square constant \(4/3\). Independently, \(-\zeta'(3/2)=3.93223973743110<6\); even the first-term-plus-integral upper bound is \(4.05374980408187<6\). Thus \(7+12+8/3=65/3<22\), followed by two-component Cauchy–Schwarz. No positivity of \(Q\). |
| S3 | §1.2, lines 176–179 | **VERIFIED** | Substitution \(u=\pi n^2e^{2x}\) gives the two gamma terms. Their difference is \(s(s-1)\Gamma(s/2)/4\), so \(F_\Phi=\xi/2\) in the standard normalization. Direct theta integration at \(z=0,1/2,1,0.3+2i,0.1+14i\) matched \(\xi(1/2+z)/2\), maximum observed error \(2.21\times10^{-47}\) at 45 decimal digits. \(F_\Phi(1/2)=0.25\). |
| S4 | §1.2, lines 188–191 | **VERIFIED** | Suzuki v1 p.13 (3.1), after swapping arguments and setting \(\lambda=i\gamma\), gives \(\overline{F_v(-\bar\lambda)}F_h(\lambda)\). I reconstructed the extension to \(E\times C_c^\infty\): strip evaluation is bounded by \(\sqrt{4/3}\|v\|_E\); three integrations by parts give uniform \(O((1+|\Im\lambda|)^{-3})\) for \(F_h\); the zero-count bound makes the sum absolutely dominated. Details below. |
| S5 | §1.2, lines 195–198 | **VERIFIED** | Integration by parts gives \(F_{\partial^kv}=(-z)^kF_v\); applying \(\partial^2-1/4\) multiplies by \(z^2-1/4\). Values therefore vanish at every centered zero, including repeated zeros without a simplicity assumption. S4 gives radical membership against compact smooth tests; S2 and the independently checked core argument extend it to every second argument in \(E\). |
| S6 | §1.3, lines 204–210 | **VERIFIED** | Write the translation difference as the integral of the piecewise derivative plus two translated jump indicators. Their respective squared norms are bounded by \(t^2D_{\rm tail},t|v(a)|^2,t|v(-a)|^2\); \(\|u_1+u_2+u_3\|^2\le3\sum\|u_i\|^2\) gives exactly S6. The taper error satisfies \(O(\min(t,\delta))\), whose integral against \(2/t\) is \(O(\delta(1+|\log\delta|))\). |
| S7 | §1.4, lines 216–221 | **VERIFIED** | \(\langle p,d_j\rangle=N^{-1}(\int_{-a}^a\Phi g_{2j}-\alpha_jN^2)=0\). Subtraction occurs before cutting, so the radical identity is preserved. Direct source evaluation at \(a=0.7,j=0\): \(N^2=0.07993788809838382927\), \(\alpha_0=-10.45791910319166627\). |
| S8 | §1.4, lines 223–233 | **VERIFIED** | Vanishing on an open interval forces the analytic combination to vanish globally. Its transform is \(F_\Phi(z)[(z^2-1/4)\sum c_jz^{2j}-\sum c_j\alpha_j]\). Since \(F_\Phi(1/2)=1/4\), the constant sum vanishes; then every polynomial coefficient vanishes. The same proof works outside the window and for \(\Phi,g_0,\ldots,g_{2m}\). Actual source check: \(G_{00}=15.61302623897922064>0\) at \(a=0.7\). This proves \(G>0\), not \(C>0\). |
| S9 | §2.1, lines 245–254 | **VERIFIED** | Independent splitting at \(\delta=e^{-2a}\) and \(1\) produces derivative coefficient \(3\delta^2\), trace coefficient \(6\delta\), middle mass coefficient \(8\log(1/\delta)=16a\), and large-\(t\) mass coefficient at most \(16\). These are precisely the printed weights. |
| S10 | §2.1, lines 251–254 | **VERIFIED** | Integrating S6 with \(A_0\le2/t\), then using \(\|\Delta_tw\|^2\le4\|w\|^2\), proves \(\|1_{\rm out}v\|_E^2\le\mathfrak B_a[v]\). S2 proves the factor 22. The exact large-\(t\) coefficient is only \(4\int_1^\infty A_0=4.99448872281692<16\), so the chosen constant has ample margin. |
| S11 | §2.1, lines 258–262 | **VERIFIED** | \(H\) is the Gram matrix of an independently positive tail form. Zero \(H\)-norm implies an analytic source combination is zero on an exterior interval, and the S8 polynomial argument gives zero coefficients. Thus \(H>0\), \(\ell\ne0\), \(Z>0\). In the actual \(a=0.7,m=0\) computation, the determinant of \(e^{2\pi Y}H\) is \(5.9156963984609528\times10^{15}>0\). |
| S12 | §2.1, lines 266–269 | **VERIFIED** | The constrained minimum is attained at \(\theta=H^{-1}\ell/Z\). In the actual source check \(a=0.7,m=0\), \(\theta=(0.972553985464615755,-0.00262442406224082950)\); \(\ell^T\theta=1\). The induced coefficient is \(c_0=-\theta_1/N=0.00928234435565989554\). |
| S13 | §2.1, lines 271–275 | **VERIFIED** | Substitute \(g_{2j}=h_j+\alpha_j\Phi\) into the inside cut and use \(\ell^T\theta=1\): \(f=p-z\). Orthogonality gives \(\langle p,f\rangle=1\), \(\|f\|^2=1+\|z\|^2\). Actual source value: \(\|f\|^2=1.00134524826681632203\). |
| S14 | §2.1, lines 277–285 | **VERIFIED** | Cauchy–Schwarz in the \(H\)-metric gives \(\min_{\ell^*\eta=1}\eta^*H\eta=1/Z\). The radical decomposition gives equal inside/outside \(Q\)-energies, then S10 gives \(Q[f]\le22/(N^2Z)\). For the Rayleigh bound, handle \(Q[f]\le0\) separately; otherwise division by \(\|f\|^2\ge1\) decreases the quotient. No sign assumption is hidden. Actual source bound at \(a=.7,m=0\): \(22/(N^2Z)=7.10350260220143667\times10^{-5}\). |
| S15 | §2.2, lines 291–302 | **PLAUSIBLE — unpaid target** | The implication S15 \(\Rightarrow Q[f]\le Me^{\nu a}T^2\) follows exactly by substituting into S14. Existence of the cofinal schedule satisfying S15 is not proved here. The actual \(a=.7,m=0\) reference bound is about \(1.08\times10^8\) times \(T(.7)^2\) when \(M=1,\nu=0\); this is one finite candidate, not a cofinal refutation. |
| S16 | §2.3, lines 306–321 | **VERIFIED** | Differentiate \(e^{\alpha x}e^{-s}\), with \(s'=2s\): \(P_{r+1}=(\alpha-2s)P_r+2sP'_r\). Independently obtained \(P_1=\alpha-2s\), \(P_2=\alpha^2-(4\alpha+4)s+4s^2\); coefficient recurrence and leading coefficient \((-2)^r\) follow. Orders through \(r=4\) were expanded symbolically. |
| S17 | §2.3, lines 323–329 | **VERIFIED** | Put \(u=ce^{2x}\): \(dx=du/(2u)\), giving exactly \(\frac12c^{-\beta/2}\Gamma(\beta/2,ce^{2a})\). Independent numerical example \(\beta=4.5,c=3,a=.3\) gives \(0.001846230261473439\) on both sides. Fixed-degree theta products converge absolutely, justifying the finite expansion and termwise integration. |
| S18 | §2.4, lines 335–340 | **VERIFIED** | With \(Y=e^{2a}\), the leading squared source is \(4\pi^4y^{9/2}e^{-2\pi y}\). Both tails produce \(L=\|t_a\|^2\sim2\pi^3Y^{7/2}e^{-2\pi Y}\). Squaring \(T=L/I\) gives exponent \(-4\pi Y\). Independent values: \(I=0.07993795299040532128\), \(T(.7)=8.1177987507129910223\times10^{-7}\), \(T(.7)^2=6.5898656557077397760\times10^{-13}\). |
| S18b | §2.4, lines 342–354 | **VERIFIED** | Fully rederived below, including an explicit unconditional constant: **\(C=1\,800\,000\) works for all \(a>0\), all finite \(m\)**. More sharply, \(\mathfrak B_a[\Phi]/(e^{2a}IT)\to1\). Direct numerical ratio at \(a=.7\): **45.320466023056019**. This is a one-\(T\) estimate, not a \(T^2\) estimate. |
| S19 | §2.4, lines 356–367 | **VERIFIED — conditional implication only** | Taking logarithms of \(22Ce^{ca}Te^{-\sigma m}\le Me^{\nu a}T^2\) gives the printed ceiling. For \(C=M=\sigma=1,c=\nu=0,T=e^{-10}\), the rule gives \(m=14\), with budget ratio \(22e^{-4}=0.402944055552152<1\). The hypothesized uniform contraction is not proved. Since \(\log(1/T)=2\pi e^{2a}-7a+O(1)\), the conditional leading degree is \(2\pi e^{2a}/\sigma\). |
| S20 | §2.4, lines 369–373 | **VERIFIED** | Degrees \(0,\ldots,K-1\) contain \(\lceil K/2\rceil\) even Legendre functions. Removing a nonzero projected \(p\) leaves at most \(\lceil K/2\rceil-1\). Thus 17 directions at \(K=36\), 23 at \(K=48\); exceeding this cannot preserve the exact source rank \(m+1\). |
| S21 | §3.1, lines 387–394 | **VERIFIED** | From \(Np+t=\Phi\in\operatorname{rad}Q\), \(Q[p]=Q[t]/N^2\). From \(d_{\rm cut}+d_{\rm out}\in\operatorname{rad}Q\), \(Q(d_{\rm cut},p)=Q(d_{\rm out},t)/N\) and the cut energies agree. The explicit complex six-dimensional model below makes all three radical products exactly zero and reproduces the signs. |
| S22 | §3.1, lines 396–400 | **VERIFIED** | For \(Q(cd,p)=\bar c\,s/N\), completing \(2\Re(\bar c s/N)-u|c|^2\) gives \(c=s/(Nu)\), \(J=|s|^2/(N^2u)\). With \(N=2,u=2,s=1+i,\tau=5\): \(c=(1+i)/4\), \(J=1/4\), \(Q[p-z]=1\). |
| S23 | §3.1, lines 401–405 | **VERIFIED — equivalence only** | Multiply the S22 strong-budget test by \(N^2u>0\): the determinant expression is exactly \(|s|^2-u(\tau-\epsilon N^2)\). In the preceding model with \(\epsilon=1/2\), it is **\(-4\)**, correctly rejecting \(Q[p-z]=1\le1/2\). Its cofinal nonnegative sign for the theta construction remains unproved. |
| S24 | §3.2, lines 409–423 | **VERIFIED** | Direct sesquilinear expansion gives all four lines, including \(1+c^*Gc\). The residual-tail identity follows from the radical vector \(\Phi-N\sum c_jh_j\). In the independently constructed complex model, a nonoptimal rational complex \(c\) gives \(Q[p-z]=9477053/5336100\), \(\|p-z\|^2=1655536/1334025\); both inside and tail expressions agree exactly. |
| S25 | §3.2, lines 425–434 | **VERIFIED** | Completing the finite \(C\)-square and elementary block elimination prove both formulas on \(C>0\). Independent complex model: \(\det C=5\), \(s^*C^{-1}s=2\), \(\tau=5\), \(\delta=3\), bordered determinant \(15\). Symbolic remainder after subtracting the completed-square expression is exactly zero. |
| S26 | §3.2, lines 435–445 | **PLAUSIBLE — unpaid target** | On positive blocks, S25 makes this exactly the strong budget for \(c_Q\). No cofinal source estimate of \(\delta\) was supplied or proved in this check. The model’s \(\delta=3\) and \(N^2=4\) demonstrate the normalization explicitly: its minimized unnormalized energy is \(3/4\). |
| S26b | §3.2, lines 440–445 | **PLAUSIBLE — unpaid target** | The extra square is mandatory. Its algebra is verified by S25. In the complex model, taking the legal comparison coefficient \(c_B=0\) adds \(N^2c_Q^*Cc_Q=2\), changing \(\delta=3\) to \(5\), hence energy \(3/4\) to \(5/4\). No estimate of that extra term for the actual cofinal reference family was established. |
| S27 | §3.3, lines 453–461 | **VERIFIED** | Each translated pairing is bounded by \(n^{-1}\sqrt{\mathcal W[u]\mathcal W[v]}\); the two signs give a factor two. Since \(\log x\,x^{-3/2}\) decreases for \(x\ge2\), the omitted sum is bounded by \(2\int_R^\infty\log x\,x^{-3/2}dx=(4\log R+8)/\sqrt R\). At \(R=100\), coefficient \(2.642068074395237\). |
| S28 | §3.3, lines 463–469 | **VERIFIED** | Expand \((b_A-b_P+b_R)^*C^{-1}(b_A-b_P+b_R)\). All three mixed signs match. The scalar model \(C=1,b_A=b_P=1,b_R=0\) gives full recovery \(0\), prime-only recovery \(1\). |
| S29 | §3.4, lines 490–494 | **VERIFIED — budget equivalence** | Divide S24’s energy by its physical norm \(1+c^*Gc>0\). In the complex model at \(c_Q\), energy \(3/4\), norm \(23/20\), quotient \(15/23\). At \(\epsilon=7/10\), the strong margin is \(-1/20\), while the normalized-budget margin is \(11/200>0\). Thus the distinction is numerically and symbolically real. |
| S30 | §4.1, lines 510–515 | **VERIFIED** | Substitute \(d_j=1_{\rm in}(g_{2j}-\alpha_j\Phi)\) in \(p-\sum c_jd_j\). The coefficient of \(\Phi\) is \(N^{-1}+\sum c_j\alpha_j\), with negative coefficients on the \(g_{2j}\). For \(c_j=-\theta_{j+1}/N\), \(\ell^T\theta=1\) recovers S12 exactly. |
| S31 | §4.1, lines 517–521 | **VERIFIED** | For \(0\le t\le2a\), the two supports intersect on \([t-a,a]\). Translation symmetry gives \(R(-t)=R(t)\); at \(2a\) the intersection has measure zero. For the independent sharp polynomial test \(v=1+x^2\), symbolic integration gives the polynomial displayed below, with \(R(2a)=0\) exactly. |
| S32 | §4.1, lines 523–528 | **VERIFIED** | Leibniz differentiation supplies both the lower-limit trace and the differentiated shifted argument, each with a minus sign. For \(v=1+x^2\), symbolic differentiation minus the printed right side is exactly zero. In particular \(R'(0+)=-\left(1+a^2\right)^2\); dropping the trace would already fail this check. The fixed-interval bound gives absolute continuity. |
| S33 | §4.2, lines 532–539 | **VERIFIED** | Differentiate \(x^{-1/2}R(\log x)\). The chain factor is \(x^{-3/2}\), and the mass coefficient is \(-1/2\). Absolute continuity is preserved under this smooth substitution on \([1,X]\). In the polynomial test \(a=\log2,X=4\), \(k(4)=0\), \(k(1)=1.894328309541319787\). |
| S34 | §4.2, lines 541–547 | **VERIFIED** | Write \(d\psi=dx+dD_\psi\), then integrate the latter term by parts. Both boundary terms are zero. Independent polynomial test with the prime-power endpoint \(X=4\): direct prime sum \(0.7621381631765863943\); \(\int k=1.6749529873680544012\), \(\int D_\psi k'=0.9128148241914680069\). Their difference equals the direct sum; numerical residual \(3.06\times10^{-56}\). |
| S35 | §4.2, lines 549–560 | **VERIFIED** | Substitute S34 into the full prime contribution \(-2\sum\Lambda(n)k(n)\). The sign of the \(D_\psi k'\) term is positive. For the polynomial test, geometric and arithmetic evaluations both give **\(Q[f]=0.21407666318481070994\)**; their numerical difference is \(2.04\times10^{-56}\). Both pole moments are retained. |
| S36 | §4.3, lines 568–575 | **VERIFIED** | Insert S32 into S33 and multiply by \(2D_\psi\). Every displayed sign follows directly; no prime-only substitution occurs. The polynomial test gives \(\mathcal I=2(0.9128148241914680069)=1.8256296483829360139\). |
| S37 | §4.3, lines 577–581 | **PLAUSIBLE — unpaid target** | S35 proves that the strong inequality is equivalent to \(\mathcal I_a\le\epsilon_a-\mathcal M_a\). This does not prove the inequality for a cofinal theta construction. The polynomial identity check verifies the decomposition, not its required \(T^2\) sign or size. |
| S38 | §4.3, lines 582–587 | **PLAUSIBLE — unpaid target** | S13/S24 establish the exact norm factor \(1+c^*Gc\); S35 gives the equivalence. The complex model in S29 independently demonstrates why this bound is weaker. No uniform source estimate establishing S38 was obtained. |
| S39 | §4.3, lines 589–594 | **VERIFIED — conditional sufficient test only** | Under the explicitly stated \(|D_\psi|\le E_\psi\), \(2\int D_\psi k'\le2\int E_\psi|k'|\). Adding the unchanged main term gives the displayed sufficient tests. Neither an adequate envelope nor satisfaction of either test is asserted or proved. |
| S40 | §8, lines 688–694 | **VERIFIED — diagnostic definition** | The strong margin is exactly \(\epsilon-Q[p-z]\), without division by physical norm or by a tiny eigenvalue. In the §3.4 counterexample with \(\epsilon=1/2\), it is **\(-1/2\)** for every coefficient. Actual K36/K48 candidate certification was not rerun by this checker. |
| S41 | §8, lines 696–700 | **VERIFIED** | Put \(h=f-\tilde f\). Sesquilinearity gives \(Q[f]-Q[\tilde f]=2\Re Q(h,\tilde f)+Q[h]\); S2 bounds its absolute value by \(22e(2\|\tilde f\|_E+e)\). Example \(e=.001,\|\tilde f\|_E=2\): \(0.088022\). Componentwise matrix error is independently bounded by \(|w|^TE|w|\). |

Inventory count: **38 VERIFIED at their stated scope, 5 PLAUSIBLE unpaid targets, 0 WRONG.** Verified conditional tests are not counted as proved rate inequalities.

## Independent reconstruction of the foundational extension

This supplies the analytic details needed for S4–S5 without treating the older checker’s conclusion as a theorem.

For \(v\in E\), weighted Cauchy–Schwarz gives
\[
|F_v(\sigma+i\gamma)|
 \le
 \left(\int_{\mathbb R}e^{2\sigma x-2|x|}\,dx\right)^{1/2}
 \mathcal W[v]^{1/2}
 =
 (1-\sigma^2)^{-1/2}\mathcal W[v]^{1/2}.
\]
For \(|\sigma|\le1/2\), this is at most \(\sqrt{4/3}\|v\|_E\).

For compact smooth \(h\), integrate the Fourier transform of \(e^{\sigma x}h(x)\) by parts three times. The \(L^1\)-norms of the required derivatives are uniformly bounded for \(|\sigma|\le1/2\), so
\[
|F_h(\sigma+i\gamma)|\le C_h(1+|\gamma|)^{-3}.
\]
The unconditional zero count \(N(R)=O(R\log(2+R))\) makes this absolutely summable over zeros, including multiplicities. In dyadic shells the summable bound is a constant times
\[
\sum_{k\ge0}(k+1)4^{-k}=16/9.
\]
Consequently the signed zero sum passes to an \(E\)-limit in its first argument.

For the core property, choose smooth cutoffs \(\chi_R\). In the translation difference of \((1-\chi_R)v\), the term containing \(\Delta_tv\) tends to zero by dominated convergence against the defining Dirichlet energy. The remaining term is controlled by
\[
\|v\|_2^2\min(C^2t^2,4),
\]
which is integrable against \(A_0(t)\); it also converges pointwise to zero. Weighted mass convergence is immediate. Mollification of the resulting compact function converges in the Fourier multiplier norm by bounded convergence and in weighted \(L^2\) because the support stays bounded.

Thus compact smooth functions are dense in the **full** \(E\). There is no pole-null restriction and no moment-restoration step. S5’s vanishing pairings extend to all second arguments by continuity. This reasoning does not assert that the zero-series formula converges for every arbitrary pair in \(E\times E\).

## S18b: independent natural-width derivation and explicit constants

Write
\[
Y=e^{2a},\qquad L=\|t_a\|_2^2=IT(a),
\]
and let
\[
W=\mathcal W[t_a],\qquad
D_{\rm tail}=\|1_{|x|>a}\Phi'\|_2^2,\qquad
E_{\rm tr}=|\Phi(a)|^2+|\Phi(-a)|^2.
\]

For \(w=1_{\rm out}v\), integrate S6 only up to \(\delta=Y^{-1}\). Above that scale use the \(L^2\) translation estimate. Independently,
\[
\mathcal D[w]
\le3Y^{-2}D_{\rm tail}+6Y^{-1}E_{\rm tr}
 +(16a+16)L.
\]
After adding \(W\), this is precisely S9.

The leading positive-tail source is
\[
\Phi(x)
 =
 2\pi^2y^{9/4}e^{-\pi y}
 \left(1-\frac3{2\pi y}+O(e^{-3\pi y}\operatorname{poly}(y))\right),
 \qquad y=e^{2x}.
\]
Since both tails give \(2dx=dy/y\),
\[
L\sim2\pi^3Y^{7/2}e^{-2\pi Y}.
\]
Endpoint integration gives the three distinct constants
\[
\frac{W}{YL}\longrightarrow1,\qquad
\frac{D_{\rm tail}}{Y^2L}\longrightarrow4\pi^2,\qquad
\frac{E_{\rm tr}}{YL}\longrightarrow4\pi.
\]
The last constant is **\(4\pi\)** because \(E_{\rm tr}\) contains both endpoints.

It follows that
\[
\frac{\mathfrak B_a[\Phi]}{YL}\longrightarrow1.
\]
More explicitly,
\[
\frac{\mathfrak B_a[\Phi]}L
 =
 Y+16a+16+12\pi^2+24\pi+\frac1{2\pi}+O(Y^{-1}).
\]
The \(1/(2\pi)\) term comes from the next endpoint term in \(W/L\).

The numerical integration used a stabilized coordinate
\[
y=Y+\frac{u}{2\pi}
\]
and divided out \(e^{-2\pi Y}\), so the integrations did not underresolve tiny tail values simply because their unscaled magnitude was small.

| \(a\) | \(L/(2\pi^3Y^{7/2}e^{-2\pi Y})\) | \(W/(YL)\) | \(D_{\rm tail}/(Y^2L)\) | \(E_{\rm tr}/(YL)\) | \(\mathfrak B_a[\Phi]/(YL)\) |
|---:|---:|---:|---:|---:|---:|
| 0.3 | 0.8054800724 | 1.1231706581 | 18.6621669870 | 8.4961735610 | 71.2412893559 |
| 0.7 | 0.9063722866 | 1.0453831729 | 29.1977794702 | 10.7918293492 | **45.3204660231** |
| 1.0 | 0.9474692985 | 1.0232812848 | 33.6870007331 | 11.6044052021 | 28.4540424941 |
| 1.5 | 0.9803650810 | 1.0081493163 | 37.3095830188 | 12.2158848047 | 12.2213948843 |
| 2.0 | 0.9927359089 | 1.0029450458 | 38.6756440368 | 12.4378939719 | 5.3740509495 |
| 3.0 | 0.9990141641 | 1.0003950511 | 39.3694471351 | 12.5490144591 | 1.6384318802 |
| Limit | 1 | 1 | \(4\pi^2\) | \(4\pi\) | 1 |

The asymptotic proof can be replaced by explicit elementary inequalities, giving a concrete universal constant.

For \(y\ge1\) and \(k\le6\),
\[
\sum_{n\ge1}n^ke^{-\pi(n^2-1)y}<2.
\]
Indeed, for \(k=6\), the ratio after the \(n=2\) term is at most
\[
q=(3/2)^6e^{-5\pi}=0.000001716586865249,
\]
and therefore the sum is at most
\[
1+\frac{64e^{-3\pi}}{1-q}
 =1.005164777990290<2.
\]

Define
\[
k_0=2\pi^2-3\pi>0,\qquad
K_0=8\pi^3+30\pi^2+15\pi.
\]
Every theta summand is positive for \(y\ge1\), so
\[
k_0y^{9/4}e^{-\pi y}
 \le\Phi(x)\le4\pi^2y^{9/4}e^{-\pi y},
\qquad
|\Phi'(x)|\le K_0y^{13/4}e^{-\pi y}.
\]
For \(p<2\pi\) and \(Y\ge1\), the elementary estimate
\[
\int_Y^\infty y^pe^{-2\pi y}\,dy
 \le\frac{Y^pe^{-2\pi Y}}{2\pi-p}
\]
follows from \((Y+u)^p\le Y^pe^{pu/Y}\). Also
\[
L\ge\frac{k_0^2}{2\pi}Y^{7/2}e^{-2\pi Y}.
\]
Consequently,
\[
W\le R_WYL,\quad
D_{\rm tail}\le R_DY^2L,\quad
E_{\rm tr}\le R_EYL,
\]
where
\[
R_W=\frac{16\pi^4(2\pi)}{k_0^2(2\pi-9/2)}
 =51.61932583682605,
\]
\[
R_D=\frac{K_0^2(2\pi)}{k_0^2(2\pi-11/2)}
 =26362.40831366784,
\]
\[
R_E=\frac{32\pi^4(2\pi)}{k_0^2}
 =184.0936467974876.
\]
Using \((16a+16)e^{-2a}\le16\) and \(Y^{-1}\le1\),
\[
22\,\mathfrak B_a[\Phi]\le C_QYL,
\]
with
\[
\boxed{
C_Q=22(R_W+16+3R_D+6R_E)
 =1765706.9352477557<1800000.
}
\]

This last strict comparison need not rely on floating arithmetic: replacing \(\pi\) by rational lower and upper bounds \(3.14159<\pi<3.14160\), using the upper value in numerators and lower values in denominators, yields the rational upper bound
\[
\frac{32532996800376904340959978930370637856}
 {18424455101264821896207810275875}
 =1765750.8252791446\ldots<1800000.
\]

Since the feasible coefficient \((1,0,\ldots,0)\) gives \(1/Z_{m,a}\le\mathfrak B_a[\Phi]\), and \(N^2=I(1-T)\), we have independently proved
\[
\boxed{
Q[f_{m,a}],\,\lambda_a
 \le1800000\,e^{2a}\frac{T(a)}{1-T(a)}
 \quad(a>0,\ m\ge0).
}
\]
The constant is deliberately crude. Its purpose is to verify the quantifiers and the exponent in S18b. It supplies no additional factor of \(T\).

## The §3.4 counterexample, reproduced exactly

With the standard physical inner product on \(\mathbb C^3\), take
\[
A=
\begin{pmatrix}
1&0&-1\\
0&0&0\\
-1&0&1
\end{pmatrix},
\qquad Q[x]=x^*Ax=|x_0-x_2|^2.
\]
Set
\[
V=\operatorname{span}(e_0,e_1),\quad
\Phi=e_0+e_2,\quad p=e_0,\quad t=e_2,\quad d=e_1,\quad N=1.
\]

Direct multiplication gives
\[
A\Phi=0,\qquad Ad=0.
\]
Thus \(\Phi\) and \(d\) are genuine global radical vectors, not merely isotropic vectors. The full matrix eigenvalues are \(0,0,2\). On \(V\), the matrix is \(\operatorname{diag}(1,0)\), so
\[
\inf_{0\ne f\in V}\frac{Q[f]}{\|f\|^2}=0.
\]
Here \(r=1,C=0,b=0\), and for every complex \(c\),
\[
J(cd)=0,\qquad Q[p-cd]=1,\qquad \|p-cd\|^2=1+|c|^2.
\]
At \(\epsilon=1/2\), the strong condition would require \(0\ge1/2\), which is false. Its S40 margin is exactly
\[
\boxed{\epsilon-Q[p-cd]=-\tfrac12.}
\]
The normalized quotient \(1/(1+|c|^2)\) can nevertheless be at most \(1/2\). Therefore a zero direction can settle the normalized upper bound while failing to settle the strong affine budget.

The other singular branches also check:

- A negative \(C\)-direction makes the quadratic part of \(J\) grow positively under scaling.
- If \(C\ge0\) is singular and \(b\) couples to its kernel, an appropriate phase makes \(J\) grow linearly.
- If \(b\in\operatorname{ran}C\), completing the square on that range gives \(\sup J=b^*C^\dagger b\); a decoupled null direction does not add recovery.

This counterexample refutes the abstract implication only. It is not a counterexample to the theta-source \(T^2\) law.

## Complex Schur cross-check independent of the source code

To expose conjugation errors, I used a complex rather than purely real test:
\[
C=\begin{pmatrix}2&i\\-i&3\end{pmatrix},\quad
s=\binom{1+i}{2-i},\quad \tau=5,\quad N=2.
\]
Let
\[
B=\begin{pmatrix}\tau&s^*\\s&C\end{pmatrix},\qquad
L=\left[\operatorname{diag}(-1/N,-1,-1)\ \ I_3\right],
\qquad Q=L^*BL.
\]
In \(\mathbb C^6\), choose the inside basis \(p,d_1,d_2\) and outside basis \(t,e_1,e_2\). Then \(Np+t,d_1+e_1,d_2+e_2\) are exact radical vectors.

Symbolic calculation gives
\[
c_Q=\binom{1/5+i/10}{3/10-i/10},\quad
s^*C^{-1}s=2,\quad
\delta=3,\quad
\det C=5,\quad \det B=15.
\]
At this response,
\[
Q[p-z]=3/4,\quad\|p-z\|^2=23/20,\quad
\frac{Q[p-z]}{\|p-z\|^2}=15/23.
\]
At \(\epsilon=7/10\), the normalized budget succeeds and the strong budget fails:
\[
\epsilon\|p-z\|^2-Q[p-z]=11/200,\qquad
\epsilon-Q[p-z]=-1/20.
\]
This independently checks both the tail-conjugation convention and the distinction between S26 and S29.

## Arithmetic and endpoint cross-check

The identities S31–S36 hold for any smooth inside representative. I therefore tested them on a function independent of the theta construction:
\[
v(x)=1+x^2,\qquad f=1_{(-a,a)}v,\qquad a=\log2,\quad X=4.
\]
The prime-power endpoint is intentional.

Direct polynomial integration gives
\[
\begin{aligned}
R(t)={}&\frac{2a^5}{5}-a^4t+\frac{2a^3t^2}{3}
+\frac{4a^3}{3}-2a^2t+2at^2+2a\\
&-\frac{t^5}{30}-\frac{2t^3}{3}-t.
\end{aligned}
\]
Thus \(R(2a)=0\) and \(R'(0+)=-(1+a^2)^2\) exactly. The derivative agrees symbolically with the full Leibniz formula including the moving endpoint.

Using \(\psi=0,\log2,\log2+\log3\) on the three intervals \((1,2),(2,3),(3,4)\), respectively, gives:

| Quantity | Independently calculated value |
|---|---:|
| \(\|f\|^2\) | 1.89432830954131978689 |
| \(\sum_{n\le4}\Lambda(n)k(n)\) | 0.76213816317658639427 |
| \(\int_1^4k(x)\,dx\) | 1.67495298736805440120 |
| \(\int_1^4D_\psi(x)k'(x)\,dx\) | 0.91281482419146800693 |
| \(\mathcal D[f]\) | 6.50766930602876625157 |
| Both-pole contribution | 5.40736281859687960233 |
| \(Q[f]\), direct full source | **0.21407666318481070994** |
| \(Q[f]\), Stieltjes decomposition | **0.21407666318481070994** |

The atom at \(4\) contributes zero because \(k(4)=0\). This verifies endpoint handling and source signs; it does not test a cofinal theta rate.

## Non-displayed claims

The important non-displayed conclusions also survive:

1. **Finite reference inverse existence does not establish S15.** The inverse exists because of independent positive geometry, while its required quantitative growth remains unknown.

2. **Reference and signed coefficients cannot be silently identified.** S26b correctly preserves their nonnegative energy difference.

3. **Cofinal complement positivity would already imply the global sign.** For fixed compact smooth \(f\), the corrected vectors
   \[
   h_j=f-\langle p_{a_j},f\rangle p_{a_j}
   \]
   converge in \(E\) to \(f-\langle \Phi/\|\Phi\|,f\rangle\Phi/\|\Phi\|\). The latter has \(Q\)-energy \(Q[f]\) because \(\Phi\) is radical. Hence eventual complement nonnegativity forces \(Q[f]\ge0\). The premise is not free inverse bookkeeping.

4. **Finite projected stability does not prove a degree law.** In particular, the K36/K48 observations are not proof of cofinal contraction, rank preservation at growing degree or a resolved denominator.

5. **An upper bound tending to zero does not prove the required lower sign.** Neither S18b nor a future \(T^2\) upper bound alone changes that fact.

## Research locators and limitations

| Source | What was independently read / used | Limit |
|---|---|---|
| Authoritative SCHUR request at commit `e11338a3a9132c88895b565d74ce189503d1c642` | All 89 lines; objects, normalization, three quantified obligations, frozen diagnostic scope | The request supplies requirements, not proofs. |
| Target SCHUR verdict | All 795 lines and all 43 tags | This audit concerns the exact SHA above. |
| `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/Codex/BRIEF_2026-09-09_OBSERVER_REVIEW_OF_CODEX_DAY.md` | Entire brief | Used only for audit scope. Observer summaries were not mathematical evidence. |
| `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/CODEX_AS_SECOND_BODY.md`, §3b | Independent-check workflow | Used only for procedure. |
| DISTANCE independent check, pinned shelf I | All 268 lines | Report format and historical context; its numbers were not substituted for fresh calculations. |
| DISTANCE verdict, pinned shelf D, §1.1–1.3 / D2–D8 | Form, domain, theta normalization and cut argument | Reconstructed the parts used here. |
| KERNEL verdict, pinned shelf K, §§2.1–2.3, §3.1–3.2 / K6–K18 | Original form, completion, core and signed transform convention | Reconstructed the continuity/core/extension arguments required for SCHUR. |
| Point-5 supplement, pinned shelf S | Entire relay, especially (2)–(10) | Retained RELAY provenance; finite algebra and arithmetic formulas independently derived. |
| Suzuki, *Weil’s quadratic form via the screw function*, **arXiv:2606.09096v1**, local source p.1, p.3, p.13 (3.1) | Primary geometric functional, its doubled xi normalization, Fourier convention, signed explicit formula | The local document identifies itself as v1, dated June 9, 2026. The target’s **v2** page was not fetched in this audit. No claim of verifying that exact v2 text. |
| DLMF 25.4 and 20.7 citations in target | Standard xi normalization and theta inversion were rederived and numerically checked | The cited DLMF pages/version were not fetched; their exact release metadata remain unverified by this checker. |

The locally consulted primary PDF is :codex-file-citation{path="/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/litreview/pdfs/2606.09096.pdf" purpose="source"}.

No external search was needed. No full K36/K48 source script or interval certificate was rerun. Numerical computations used mpmath 1.2.1 at 45–60 decimal digits, SymPy 1.12 and NumPy 1.26.4. Fixed-order theta checks used finite sums of 8–12 terms on the positive half-line; direct evenness checks used 60 terms when evaluating the negative-half series. These are diagnostic computations. They make no assertion about uniform truncation as the derivative degree tends to infinity.

The explicitly **unproved** requirements are:

- a cofinal degree schedule and uniform inverse-functional estimate S15;
- the signed cofinal remainder S26;
- the additional coefficient-mismatch budget S26b;
- the coupled signed integral estimates S37/S38;
- a useful absolute envelope satisfying S39;
- the all-large-window lower-sign supplier.

None of these was assumed in accepting the finite derivations or S18b.

## Main reproducible number and exact recomputation recipe

The exact counterexample’s decisive margin is **\(-1/2\)**.

The nontrivial independent S18b check yields
\[
C_Q=1765706.9352477557,
\]
with a rigorous rational upper bound below \(1\,800\,000\). This compact recipe independently recomputes the latter without mpmath, source caches or a matrix builder:

```python
from fractions import Fraction as F

lo = F(314159, 100000)
hi = F(314160, 100000)

k = 2 * lo**2 - 3 * lo
K = 8 * hi**3 + 30 * hi**2 + 15 * hi

R_W = 16 * hi**4 * (2 * hi) / (k**2 * (2 * lo - F(9, 2)))
R_D = K**2 * (2 * hi) / (k**2 * (2 * lo - F(11, 2)))
R_E = 32 * hi**4 * (2 * hi) / k**2

upper = 22 * (R_W + 16 + 3 * R_D + 6 * R_E)
assert upper < 1_800_000

print(float(upper))
# 1765750.8252791446
```

The underlying proof is the explicit tail calculation above; the code checks its final rational arithmetic.

**FIRST INCORRECT ASSERTION: NONE FOUND.**

**ACCEPTED — finite derivations and S18b verified; cofinal \(T^2\) supplier and lower sign remain unproved; RH remains unproved.**
## Receiving executor recomputation

The receiving executor independently evaluated the displayed constant in ordinary arithmetic: 1765706.9352477565. A separate exact Fraction calculation reproduced the rational numerator and denominator above and verified its strict bound below 1800000. The exact counterexample gives r=1, b=C=0, J=0 and strong margin -1/2. This receipt adds arithmetic verification, not a cofinal T-squared theorem or lower-sign proof.
