# Referee report, round 2 — "Weil positivity around the canonical test" (15 pp., Sept 2026)

Printed numbering of the revision: Def. 2.1, Def. 3.1, Thm. 3.2, Prop. 3.3, Rem. 3.4, Thm. 4.1, Lem. 4.2,
Cor. 4.3, Lem. 5.1, Lem. 5.2, Thm. 5.3, Cor. 5.4, Cor. 5.5, Rem. 5.6, Ex. 5.7, Rem. 5.8, Prop. 5.9, Rem. 5.10,
eq. (1)–(10). Everything below that can be computed I recomputed from the paper's own definitions
(mpmath 25–40 dps, numpy trapezoid on a super-exponentially decaying integrand, sympy for the polynomial recursion).

## (A) The 24 round-1 findings

| # | resolved? | note |
|---|---|---|
| 1 (Prop. 5.7, no margin) | **YES** | Restated as Prop. 5.9 (no fixed $\mathcal X$-margin on a dense span). Proof is 2 lines and correct: $\mathcal Q$ is a bounded quadratic form on $\mathcal X$ (the $C_\mathcal{X}$ bound), $\mathcal Q(f_0)=0$, $\|f_0\|_\mathcal{X}>0$. The quotient-norm fallacy is gone. |
| 2 (Prop. 5.8, Schur) | **YES** | Demoted to Rem. 5.10 "without a theorem"; ledger item 4 now says "heuristic, not a theorem of this paper". The false $\int_0^\varepsilon b_+\sim\tfrac12\log(1/\varepsilon)$ is replaced by $\int_\varepsilon^{t_0}$ in (6). The $\delta^2/4\int f_0^2|s'|^2$ energy claim checks out. |
| 3 (Lean vs §8 vs App. B) | PARTIAL | The §5/App. B contradiction is gone and the wording is honest about Lem. 5.1 being a hypothesis. But "the finite algebra behind §6 … formalised" still attaches to a section containing **no** numbered statement; see new finding N7. |
| 4 ($\lambda_1\ge-o(\lambda_2)$) | **YES** | Removed from §6 and from ledger item 6; the surviving argument (monotonicity ⇒ cofinal positivity is RH) is the correct one. |
| 5 (eq. (10) "exact") | PARTIAL | §6 now says "we do not prove (10) … numerical observation", and the printed regression $(0.019891,0.00540)$ is exactly what the four printed $a_m$ give (I get $0.0198906,\,0.0053978$). But §1 still says "an exact second-jet formula" (N3), App. A still prints the old $0.005143$ (N4), and "the zeta function cancels identically" is still asserted with no proof or reference. |
| 6 ((EF) off $C_c^\infty$) | PARTIAL | The false parenthetical is replaced by a correct argument: I verified $\mathcal Q(U_qg)=\mathcal Q(g)$ term by term ($A_\pm(U_qg)=e^{\pm q/2}A_\pm(g)$ ⇒ $A_+\overline{A_-}$ invariant), hence $\mathcal B(U_qf_0,v)=\mathcal B(f_0,U_{-q}v)$, and $U_{-q}v\in\mathcal X$ by the stated boundedness of translations. Cutoff strategy is right and non-circular (see below). One real gap remains: N1. |
| 7 (cleveref) | **YES** | `aliascnt` + `\crefname`; the PDF now prints Proposition 3.3, Corollary 5.4/5.5, Example 5.7, Proposition 5.9 correctly. |
| 8 (Thm. 3.2 display) | **YES** | Corrected and now true. Verified: $\Phi(x)=2\Phi_P(x/2)$ to $10^{-41}$; $H_0(z)=\int_0^\infty\Phi_P\cos(zu)=\Xi(z/2)/8$ to $3\cdot10^{-43}$ at $z=1,3$; $\Phi$ even to $5\cdot10^{-31}$; $\widehat\Phi=\Xi$ to $5\cdot10^{-32}$ at $z=1,2,5$; $A=0.565466013092$. Given evenness the two displays are equivalent, so the "hence" is now sound. |
| 9 (positivity vs App. A) | **YES** | Body now reproduces App. A ($h(u)<0$ only for $u<\sqrt{3/2\pi}$); the bogus "$n=1$ can be negative" sentence is gone. |
| 10 ($A_0,A_1$ unvalued) | **NO** | $M_0,M_1,c_\chi$ were added to the table; $A_0,A_1$ — the symbols that actually appear in (8) and in the explicit threshold (9) — are still undefined. See N5. |
| 11 (constant 1.13) | **YES** | Now $1.1513\log_{10}(1/\varepsilon)$; $\ln10/2=1.151293$. |
| 12 (abstract: one inequality) | PARTIAL | Abstract fixed to "three terms: the prime atoms and the short-range positive density against the long-range negative density". §1 still says "one inequality between the primes and a negative density". |
| 13 (space $\mathcal X$, $C_\mathcal{X}$) | PARTIAL | The $C_\mathcal X$ sketch is now complete and I reproduce it: $1+|c_A|+\tfrac83+7.87=|c_A|+11.54$, with $\|e^{\pm x/2-|x|}\|_2=2/\sqrt3$ and $\sup_x e^{-|x|-|x+t|}=e^{-|t|}$ — both correct. Completeness of $\mathcal X$, and density of $C_c^\infty$ in the concrete space, are still asserted in a parenthesis (N8). |
| 14 (Rem. 3.4 radical) | **YES** | "contains the closed span of the $\Xi$-multiples". |
| 15 ($\mathcal J_\infty,\mathcal S_\infty$, $5\cdot10^{-11}$) | **YES** | Paragraph deleted. |
| 16 (Thm. 5.3 general form) | **YES** | Now stated for $(f,\chi_R,\mathcal Q_0,S,W)$ with no Weil input; Cor. 5.4 is the application, Ex. 5.7 the second instance. I checked the proof line by line: pointwise stabilisation $Ss_R(x)=Sr(x)$ for $R\ge|x|+\max|\tau_\ell|$, Fatou, countable union of null sets, Lem. 5.2 with $d_\ell=c_\ell/f(x+\tau_\ell)$. Correct. Measurable (not bounded) cutoffs suffice, as claimed, and $W|Ss_R|^2$ is measurable since $\chi_R,W$ are and $f$ is continuous and positive. |
| 17 (measurable family) | **YES** | Moved into Rem. 5.6 with "we do not use this extension and leave the measure-theoretic details to the reader". Acceptable as a remark. |
| 18 (notation $\rho$) | PARTIAL | $\rho_{\mathrm p}$ now used for the plastic number. Remaining collisions: $A=\|\Phi\|_2$ vs $A_\pm$ vs $A_j$; $S$ (stencil) vs $S$ (Sonin operator, §5 line 1); $b(t)$ vs the fit slope $b$ (§6); $C_g,C_0,C_\mathcal X,C_q,c_A,c_\chi$. |
| 19 ($d\nu(|x-x'|)$) | PARTIAL | Thm. 4.1 now writes $\int_\R dx\int_\R\cdots d\tilde\nu(t)$, correctly. The abstract display still carries only $dx'$ (no $dx$); the §1 display still writes $d\nu(|x-x'|)\,dx\,dx'$. |
| 20 (dead cross-refs) | PARTIAL | `ConnesMoscovici2021` is now cited. Still never `\Cref`'d: Fig. 2 (`fig:f0`), Def. 2.1, Def. 3.1, Lem. 4.2, Open problem 7.1. |
| 21 ($\mathcal Q(f_0)$ numerics) | **YES** | Now $10^{-15}$ and $\mathcal B(f_0,v)=-7.5\cdot10^{-16}$ for a compact bump; the vacuous translation check is gone. |
| 22 (ledger item 1) | **NO** | Still no exhibited test, no $b(L)$ defined, no citation at the place; only a general pointer to [14] at the end of §8. |
| 23 (super-exponential in $\sqrt m$) | **YES** | Now "decays exponentially in $m$", consistent with the three cells ($\log_{10}\lambda_1/m=-4.50,-4.86,-5.11$). See N9 for the dangling forward reference. |
| 24 (six cells, $0.38$) | PARTIAL | "$0.38\,T_m$" and "six cells" are gone; Table 1 is printed. But §6 quotes $a_m$ at $m=83$ and then says "Table 1 records the cells" — there is no $m=83$ row (N11). |

Round-1's positive verifications re-checked and still standing: $N_-=0.083642$, $\sum w_nC_0(\log n)=0.0376$,
$\sup_{(0,1]}ta(t)=0.7014634$, $\min_{[\log1.4,\log1.6]}|b|=0.302847$, $c_A=5.3721834192$,
$\exp(-e^{1/2}(c_A+1))=2.737\cdot10^{-5}$, $\kappa_\Xi=0.0231049931$. Cor. 5.5's bump bound checks step by step
($a(t)\ge e^{-1/2}/(2t)$ on $(0,1]$ because $1-e^{-2t}\le2t$ and $e^{-t/2}\ge e^{-1/2}$; $\|\Delta_tg\|^2=2$ for $t\ge\ell$;
$\mathcal Q(g)\ge e^{-1/2}\log(1/\ell)-c_A\ge1$). Bibliography: I confirmed arXiv:2608.24827 (Zhu),
2606.29555 (Freedman), 2607.02828 (Groskin), 2608.16753 (Tao) exist with the stated titles, authors and dates.

## (B) New findings

| Sev. | Location | Finding | Fix |
|---|---|---|---|
| **HIGH** | Prop. 3.3, zero side | The bound $|\widehat{e_R}(z)|\le\|e_R''\|_{L^1(e^{|x|/2}dx)}|z|^{-2}$ on $|\Im z|\le\frac12$ is itself correct (two integrations by parts give $-z^2\widehat{e_R}=\widehat{e_R''}$, and $|e^{-izx}|\le e^{|x|/2}$ on the strip — the weight is exactly right). What is **not** justified is $\|e_R''\|\to0$: $e_R''=(1-\chi_R)f_0''-2\chi_R'f_0'-\chi_R''f_0$, but Thm. 3.2 states the envelope only for $j=0,1$, and Lem. 5.1 bounds only $|\chi_R'|\le c_\chi$. Nothing in the paper controls $f_0''$ or $\chi_R''$. The same one-line-per-case argument is then also invoked for $f_0*h$ with no norm estimate supplied at all. | State the envelope for $j\le2$ — App. A's recursion delivers it: $P_2=16y^4-112y^3+165y^2-\frac{75}2y$, and the same $M_j$ formula gives $M_2=6011.82$ — and add $|\chi_R''|\le c_\chi'$ to Lem. 5.1. Then $\int_{|x|>R}e^{|x|/2}e^{-a_qe^{2|x|}}\to0$ closes it. Also state the $f_0*h$ estimate. |
| **HIGH** | Thm. 4.1, proof, pole step | "The pole terms give $2\Re A_+(f_0s)\overline{A_-(f_0s)}-2\Re A_+(f_0)\overline{A_-(f_0|s|^2)}$" is **wrong as written**. The polarised pole term of $\Re\mathcal B(f_0,f_0|s|^2)$ is $A_-(f_0)A_+(f_0|s|^2)+A_+(f_0)A_-(f_0|s|^2)$, not $2A_+(f_0)A_-(f_0|s|^2)$; the two differ because $|s|^2$ is not even. With a complex two-bump $s$ on a $2.4\cdot10^4$-point grid: $\text{(paper's expression)}$ misses the claimed $-\int_0^\infty(e^{t/2}+e^{-t/2})E_s$ by $5.63\cdot10^{-3}$, while the symmetric expression matches it to $6.1\cdot10^{-16}$. **The theorem is true** — the symmetrisation $\iint f_0f_0'e^{(x-x')/2}[2\Re s\bar s'-|s|^2-|s'|^2]$ gives exactly $-\int_\R e^{-t/2}E_s(t)dt$ — but the newly added detail is a false display in the proof of the paper's main positive result. | Print the polarised pole term symmetrically, or drop to "$\Re\mathcal B$'s pole part", and keep the two-line symmetrisation. (The $H$-cancellation, the $\mathcal D$-step and the $w_n$-not-$2w_n$ prime step I re-derived independently and they are exact.) |
| **HIGH** | §1, l. 43 vs §6 | §1 still advertises "an exact second-jet formula for the prolate trial of [5]" while §6 says "We do not prove (10) here and present it as a numerical observation with a heuristic derivation". A reader of the introduction is told the opposite of what the section delivers. | Delete "exact"; write "a conjectural second-jet expansion". |
| MEDIUM | App. A table, row $1/(16\pi),13/(256\pi^2)$ | "measured $0.019892,\,0.005143$" contradicts §6's own least-squares $(0.019891,0.00540)$. I confirm §6: the four printed $a_m$ give $(0.0198906,0.0053978)$, and no two-cell fit reaches $0.005143$ (the closest, $m=43,83$, gives $0.005264$). The appendix "measured" value is the theoretical $13/(256\pi^2)=0.0051452$ rounded — round-1 finding 5(c) survived in the appendix. | Replace by $0.019891,\ 0.00540$, or delete the "measured" column entry. |
| MEDIUM | (8), (9), App. A | $A_0,A_1$ are still undefined symbols, and they carry the whole of $C_q^2$ and of the "explicit" threshold in (9). Presumably $A_j=M_j$ (the envelope of $f_0=\Phi/A$), giving $C_q^2=150925/(2a_q)$ — but the paper never says so, so (9) is not evaluable as printed. | Add one sentence "$A_j=M_j$", or write $M_j$ throughout Lem. 5.1. |
| MEDIUM | App. A, "Envelope constants" | Garbled: "Writing $\Phi(x)=4e^{x/2}\sum_np_0(ne^x\cdot ne^x)\ldots$ is cumbersome; instead put $P_0(y)=4y^2-6y$ so that $4e^{x/2}h(\sqrt y)=e^{x/2}P_0(\pi y)e^{-\pi y}/\ldots$" — two literal ellipses and a false identity ($e^{x/2}$ on both sides, a dangling "/"). The correct statement is $4h(\sqrt y)=P_0(\pi y)e^{-\pi y}$, whence $\Phi^{(j)}(x)=\sum_n e^{x/2}P_j(\pi n^2e^{2x})e^{-\pi n^2e^{2x}}$. The recipe itself is sound: I reproduce $P_1=-8y^3+30y^2-15y$, $M_0=23.90998$, $M_1=325.4253$, matching the table. | Rewrite the first sentence; state $y=\pi n^2e^{2x}$ and $e^{x/2}=\pi^{-1/4}y^{1/4}$ (this is where the $r+\tfrac14$ exponent comes from — worth one clause). |
| MEDIUM | §8 + abstract vs §6 + App. B | "The finite algebra behind §6 … [is] formalised in Lean 4" and the abstract's "the finite algebra of the window computations are formalised": §6 contains **no** numbered statement, so nothing in it can be checked against a Lean theorem. The App. B contents also do not line up: the file gives a tail bound $|T|\le L^2/(2\pi^2(N+1)^2)$ whereas §6's $T_m=\frac{L^2}{4\pi^2}\sum_{k>N}k^{-2}\asymp L^2/(4\pi^2N)$ — different order in $N$. | Say that the twelve window files support a companion computation, not a statement of this paper; only `NoFiniteStencilMinorant` covers paper statements (Lem. 5.2 and Thm. 5.3, whose H1/H2 I checked do match the paper's hypotheses exactly). |
| MEDIUM | §2 "Control space" | $\mathcal X$ is still defined as a completion and then identified with a concrete space in a parenthesis; completeness and $C_c^\infty$-density are unproved, yet Prop. 3.3 closes "by density" to all $v\in\mathcal X$. | Nothing downstream needs $v\in\mathcal X$ beyond $U_{-q}v$: state Prop. 3.3 for $v\in C_c^\infty$ and its translates, and note the continuous extension separately. |
| LOW | §3 vs §5 (structure) | Prop. 3.3 borrows "the norm estimate established in the proof of Lem. 5.1", two sections later, while Lem. 5.1's own proof invokes Prop. 3.3. I checked there is **no** circularity — the norm estimate uses only the Thm. 3.2 envelope, as the parenthetical claims — but a reader must verify this by hand. | Split the cutoff norm estimate off as a §3 lemma and let Lem. 5.1 cite it. |
| LOW | §5.1, last sentence | "the finite windows show the same thing quantitatively: $\lambda_1(m,N)$ decays exponentially in $m$ (§6)" — §6 states no decay law in $m$; it states saturation in $N$ and a 20 % agreement with [24]. | Give the three-cell fit, or drop the sentence. |
| LOW | Table 1, row (13,120) | $\delta_m/T_m=-0.003$ flatly contradicts the sentence the table is cited for ("$\delta_m$ … is a stable fraction of the lattice tail"). The wide-window row is a different regime and is not marked as such. | Rule the row off, or say "on the production schedule $N=m$" in the caption. |
| LOW | §6 vs Table 1 | $a_m$ is quoted for $m=13,23,43,83$; Table 1 has $(13,13),(23,23),(43,43),(13,120)$ — no $m=83$ cell. "Table 1 records the cells" is false. | Add the $(83,83)$ row. |
| LOW | Abstract; §1 display | Abstract's Dirichlet display still integrates $\iint\cdots dx'$ with no $dx$; §1's display still writes $d\nu(|x-x'|)\,dx\,dx'$ although Thm. 4.1 and the abstract now use $\tilde\nu$. | Make all three displays the Thm. 4.1 one. |
| LOW | §1, ll. 40–41 | "it holds for any positive integrable function **in the radical** of any functional **with the cutoff property**" — Thm. 5.3 has no radical hypothesis (only the cutoff limit), and "cutoff property" is never defined. | "…for any positive integrable function whose cutoffs have vanishing form value". |
| LOW | §6, "Bottoms" and "wide windows" | "within 20 %", "to 0.03 %", and $\varepsilon_\infty=\|\xi_1-k_\lambda\|/\sqrt{\lambda_1}=1.35,1.33$ are unsupported: no norm is specified for $\varepsilon_\infty$, no table backs either percentage, and [24] is parametrised by $L$ while §6 is parametrised by $m$. | Add the comparison table or delete the percentages. |
| WORDING | §1, l. 30 | "one inequality between the primes and a negative density" — the two-term framing the abstract has already abandoned and (7) contradicts. | Match the abstract. |

## (C) Recommendation

**Major revision** — but a light one: unlike round 1, every defect I found is repairable from material the paper
already contains, and the two unprovable propositions are gone. The positive core is now in good shape: Thm. 3.2
is correct and correctly proved, Thm. 4.1 is true (I re-derived it independently and it matches to $6\cdot10^{-16}$),
Thm. 5.3 is correct in its general form and its proof survives a line-by-line hostile reading, and Prop. 5.9 and
Rem. 5.10 are honestly labelled.

**Biggest remaining risk: the paper's two load-bearing proofs each contain one defective step.** Prop. 3.3 — on which
Thm. 4.1, Lem. 5.1, Thm. 5.3 and Cor. 5.4 all depend — now argues the extension of (EF) off $C_c^\infty$ by cutoffs,
and the architecture of that argument is right, but its decisive estimate calls on a second derivative that the paper
never bounds (N1). Thm. 4.1's newly expanded proof states the pole step in a form that is numerically false (N2),
even though the theorem is true. A referee who checks only these two lines will conclude the revision was not
re-verified after rewriting. Both are half-page fixes; until they are made, nothing in §§4–5 rests on a complete proof.
Secondary risk: the introduction and App. A still carry claims ("exact second-jet formula", "measured $0.005143$",
"the finite algebra behind §6 is formalised") that the body of the same revision explicitly retracts.
