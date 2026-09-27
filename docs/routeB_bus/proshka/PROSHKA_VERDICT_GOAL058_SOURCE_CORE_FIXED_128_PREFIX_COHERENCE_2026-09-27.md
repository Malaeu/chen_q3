# PAPER verdict: `OPEN_SOURCE_FIXED_128_COHERENCE`

**Neither an admitted C128 witness nor exclusion on the entire selected domain has been established.** There is, however, a proved obstruction on a bounded logarithmic subdomain:

\[
\boxed{
C_m<0
\quad\text{for every admitted selected cell with}\quad
128\le \log m\le \Lambda_*,
\qquad
\Lambda_*=272-8\sqrt{254}.
}
\]

This uses the **original two-sign energy and its strictly positive physical exterior**, not a truncated source. It excludes only C128 on that subdomain. It does not assert that the fixed selected tail contains a cell in this bounded interval.

For the remaining domain, I isolate one narrower, falsifiable **complete-source prefix-mass lemma**. Its universal positive outcome would exclude C128; its failure at an actual source cell would **not** establish coherence or a PC violation.

```yaml
REQUEST_ID: REQ-2026-09-27-SOURCE-CORE-FIXED-128-PREFIX-COHERENCE
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_FIXED_128_PREFIX_COHERENCE
SOURCE_COMMIT: aa0a4283e5a3f136c08be1478e40b238805e5209
VERIFIER: PAPER
OUTCOME: OPEN_SOURCE_FIXED_128_COHERENCE
HONESTY_STATE: CHALLENGER_NOT_RH
C128_SOURCE_WITNESS: NOT_ESTABLISHED
C128_FULL_DOMAIN_EXCLUSION: NOT_ESTABLISHED
PROVED_SUBDOMAIN_EXCLUSION: 128_LE_log_m_LE_272_MINUS_8_SQRT_254
NEXT_TEST: TEST_SOURCE_CORE_FIXED_128_PREFIX_MASS_GATE
NEW_DERIVATIONS_INDEPENDENTLY_AUDITED: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Source lock and accepted scope

The authoritative TXT was read completely. Its locally recomputed SHA-256 is

```text
54608557e3d8d380c6c1c029245b47d7042e3774799c2b87213c4ab5f8852cf7
```

I also read the **complete predecessor verdict at the pinned commit**, including its final directive, and the complete named audit section in `docs/Codex/PAPER_CHAIN.md`. The fetched predecessor has Git blob `eb85a8fe408e558a4792f700ae53b3c52b484d2d`. The pinned audit records the requested predecessor SHA-256, `9229428322b1a957662d0e0e0c7c050797dfb3e975e2c5dcefd6f61a468a33cf`. That remote SHA binding is audit-attested here; I did not independently recompute the predecessor’s byte hash.  

The accepted predecessor result remains limited: its fixed-source-cut calculation concerns **truncation error**, and its C128 implication is conditional. Neither its energy upper bound nor its truncation-error lower bound supplies a lower bound for the actual anchor coefficient. The independent reviews did not establish an actual C128 event. 

Fix the same \(P\) and admitted selected
\[
m=J_P+j+2,\qquad
L=\log m\ge128,\qquad b=L/2.
\]
Write \(\mathcal P\) for the specified polynomial, distinguishing it from the fixed selection parameter:
\[
\begin{aligned}
\mathcal P(x)&=-64x^4+448x^3-660x^2+150x,\\
g_\alpha(u)&=e^{u/2}
 \mathcal P(\pi\alpha^2e^{2u})e^{-\pi\alpha^2e^{2u}},
\qquad
g(u)=\sum_{\alpha\ge1}g_\alpha(u),\\
e_n&=\frac{2(-1)^n}{\sqrt L}
       \int_0^b g(u)\cos(2\pi nu/L)\,du,\\
E&=E_O+2\sum_{q\ge1}e_{m+q}^2,
\qquad E_O=2\int_b^\infty |g(u)|^2\,du.
\end{aligned}
\tag{1}
\]

The original \(Q=\sqrt m\), \(5m\) splice, carrier, \(N=\lceil L\rceil\), \(K=N+\lceil L^4\rceil\), and panel remain fixed. In particular, studying the already permitted prefix \(R=128\) does not replace the panel by those even-offset indices. :chatgpt-content-reference{index="3"}

For brevity within this verdict, put
\[
x_\ell=e_{m+2\ell},\qquad a=a_m=x_1,\qquad
\mathcal J=J^{\mathrm{disp}}_m=\sum_{\ell=1}^{128}(x_\ell-a)^2.
\]
Thus \(\mathcal J\) is the dispersion, **not** the separate downstream \(J_m\) whose sign remains open.

## 2. Complete-source kernel and conditional-margin checks

### 2.1. The difference kernel retains both endpoints and every source cross term

Set \(\theta=2\pi u/L\). The elementary identity
\[
\cos((m+2\ell)\theta)-\cos((m+2)\theta)
=-2\sin((\ell-1)\theta)\sin((m+\ell+1)\theta)
\]
gives exactly
\[
\boxed{
x_\ell-a
=-\frac{4(-1)^m}{\sqrt L}
\sum_{\alpha\ge1}\int_0^b
g_\alpha(u)
\sin((\ell-1)\theta)\sin((m+\ell+1)\theta)\,du.
}
\tag{2}
\]

All offsets are even, so their coefficient prefactor is the same \((-1)^m\). At \(u=0\), both cosines equal \(1\); at \(u=b\), both equal \((-1)^m\). Consequently the difference kernel vanishes at both endpoints. For \(\ell=1\), it vanishes identically.

At every fixed cell, the complete source has a summable polynomial-Gaussian majorant on \([0,b]\). This justifies the source interchange in (2). Define
\[
T_{\alpha,\ell}
=\int_0^b g_\alpha(u)
\sin((\ell-1)\theta)\sin((m+\ell+1)\theta)\,du.
\]
Then
\[
\boxed{
\mathcal J
=\frac{16}{L}
\sum_{\ell=1}^{128}
\sum_{\alpha,\beta\ge1}
T_{\alpha,\ell}T_{\beta,\ell}.
}
\tag{3}
\]
The double source sum is absolutely convergent: its absolute value is controlled by the square of \(\sum_\alpha\int_0^b|g_\alpha|\). In particular, the terms with \(\alpha\ne\beta\) are retained.

The endpoint zeros in (2) do **not** establish small relative dispersion. Its second sine still contains the large index \(m\); an absolute real-axis estimate does not supply the required comparison with the actual anchor or \(E\).

### 2.2. The exact unpaid source comparisons

Let
\[
A_m=\sum_{\alpha\ge1}
\int_0^b g_\alpha(u)\cos((m+2)\theta)\,du,
\qquad
T_\ell=\sum_{\alpha\ge1}T_{\alpha,\ell}.
\]
Then
\[
a=\frac{2(-1)^m}{\sqrt L}A_m
\]
and the requested discriminator is exactly
\[
\boxed{
C_m=
\min\left\{
\frac{4A_m^2}{E}-1,\,
\frac{32A_m^2-16\sum_{\ell=1}^{128}T_\ell^2}{LE}
\right\}.
}
\tag{4}
\]

An actual witness therefore still requires the **same cell** to satisfy
\[
4A_m^2\ge E,
\qquad
\sum_{\ell=1}^{128}T_\ell^2\le2A_m^2.
\]

Neither source comparison is supplied by the predecessor’s diagnostic lower bound. The complete source sums must be formed before squaring; an estimate for the error of a fixed source cut cannot replace either \(A_m\) or the \(T_\ell\).

### 2.3. The accepted \(-23\) implication is valid

If \(C_m\ge0\), then \(E\le La^2\) and \(\mathcal J\le8a^2\). Since \(E>0\), necessarily \(a\ne0\). Hence
\[
\begin{aligned}
|S_{m,128}|
&=\left|128a+\sum_{\ell=1}^{128}(x_\ell-a)\right|\\
&\ge128|a|-\sqrt{128\mathcal J}\\
&\ge96|a|.
\end{aligned}
\]
Therefore
\[
\boxed{
\frac{LS_{m,128}^2}{128E}\ge72,
\qquad
D_{\mathrm{pref}}(m,128)\le-23.
}
\tag{5}
\]

This verifies the predecessor’s conditional implication without activating its antecedent. Its scope remains only a violation of the earlier sufficient PC condition at the original pair \((m,128)\). :chatgpt-content-reference{index="4"}

## 3. A proved necessary energy cost for C128

The original energy charges every prefix coefficient twice. That yields an obstruction which the separate anchor and dispersion inequalities obscure.

### 3.1. Exact partition of the original energy

Define the bookkeeping subenergy
\[
B_m=2\sum_{\ell=1}^{128}x_\ell^2
\]
and its full complement
\[
H_m=
E_O+
2\sum_{\substack{q\ge1\\q\notin\{2,4,\ldots,256\}}}
e_{m+q}^2.
\]
Then
\[
\boxed{E=B_m+H_m.}
\tag{6}
\]

This is not a new denominator. The odd positive offsets, even offsets beyond the prefix, and physical exterior all remain in \(H_m\).

For this complete source, the exterior is strictly positive. Indeed, for \(x\ge8\),
\[
\mathcal P(x)
=-64x^3(x-7)-30x(22x-5)<0.
\]
For \(u\ge b\), every source argument satisfies
\(\pi\alpha^2e^{2u}\ge\pi m>8\). Thus every \(g_\alpha(u)\) is negative, and the convergent complete sum is negative. Consequently
\[
\boxed{H_m\ge E_O>0,\qquad B_m<E.}
\tag{7}
\]

Only the actual exterior is used here. No exterior decay estimate has been transported into the interior window.

### 3.2. Completing the square jointly in energy and dispersion

For any \(\mu>0\), put \(r=\mu/(2+\mu)\). For each \(\ell\ge2\),
\[
2x_\ell^2+\mu(x_\ell-a)^2
=(2+\mu)(x_\ell-ra)^2
+\frac{2\mu}{2+\mu}a^2.
\]
Since \(x_1=a\), summing gives
\[
B_m+\mu\mathcal J
=
\left(2+\frac{254\mu}{2+\mu}\right)a^2
+(2+\mu)\sum_{\ell=2}^{128}(x_\ell-ra)^2.
\tag{8}
\]

Choose
\[
\boxed{
\begin{aligned}
\mu_*&=\frac{\sqrt{254}-4}{2}>0,\\
r_*&=1-\frac4{\sqrt{254}},\\
\Lambda_*&=272-8\sqrt{254}>128.
\end{aligned}
}
\tag{9}
\]
This choice maximizes
\[
2+\frac{254\mu}{2+\mu}-8\mu:
\]
its derivative vanishes at \((2+\mu)^2=254/4\).

Define the retained nonnegative square
\[
V_m=(2+\mu_*)
\sum_{\ell=2}^{128}(x_\ell-r_*a)^2\ge0.
\]
Equation (8) becomes
\[
\boxed{
B_m+\mu_*\mathcal J
=(\Lambda_*+8\mu_*)a^2+V_m.
}
\tag{10}
\]

Thus, whenever the dispersion part of C128 holds,
\[
B_m\ge\Lambda_*a^2+V_m\ge\Lambda_*a^2.
\tag{11}
\]

The same energy cost can be seen directly:
\[
\begin{aligned}
\sum_{\ell=2}^{128}x_\ell^2
&\ge\left(\sqrt{127}|a|-\sqrt{\mathcal J}\right)^2\\
&\ge(\sqrt{127}-\sqrt8)^2a^2,
\end{aligned}
\]
and therefore
\[
2\sum_{\ell=1}^{128}x_\ell^2
\ge2\bigl[1+(\sqrt{127}-\sqrt8)^2\bigr]a^2
=\Lambda_*a^2.
\]

This is the algebraic energy cost of the requested dispersion cap. It is not an assertion that the actual theta source realizes an extremizing coefficient profile.

### 3.3. A strict upper envelope for the actual discriminator

Introduce the dimensionless mass discriminator
\[
\boxed{
\mathfrak M_m=\Lambda_*-\frac{LB_m}{E}.
}
\tag{12}
\]

Write the two entries of \(C_m\) as
\[
X_m=\frac{La^2}{E}-1,\qquad
Y_m=\frac{8a^2-\mathcal J}{E}.
\]
Dividing (10) by \(E\) and rearranging yields
\[
\Lambda_*X_m+\mu_*LY_m
=-\mathfrak M_m-\frac{LV_m}{E}.
\]
Since \(C_m=\min\{X_m,Y_m\}\) and both weights are positive,
\[
\boxed{
C_m
\le
-\frac{\mathfrak M_m+LV_m/E}{\Lambda_*+\mu_*L}
\le
-\frac{\mathfrak M_m}{\Lambda_*+\mu_*L}.
}
\tag{13}
\]

No division by \(a\) occurred. This identity and bound remain valid when \(a=0\); independently, that case already has \(C_m\le-1\).

By the exact energy partition,
\[
\mathfrak M_m
=\Lambda_*-L+\frac{LH_m}{E}
\ge\Lambda_*-L+\frac{LE_O}{E}.
\]
Consequently,
\[
\boxed{
C_m\le
\frac{L-\Lambda_*-LE_O/E}{\Lambda_*+\mu_*L}
<0
\quad
\text{whenever }128\le L\le\Lambda_*.
}
\tag{14}
\]

This proves the announced subdomain exclusion, including the endpoint \(L=\Lambda_*\). The strictness at that endpoint comes from the complete physical exterior.

**Quantifier:** for the fixed original \(P\), (14) holds for every \(j\) whose admitted selected \(m=J_P+j+2\) lies in the indicated range. No existence of such a \(j\) is asserted. No conclusion for \(L>\Lambda_*\) follows from the sign of the displayed upper bound alone.

## 4. The remaining source comparison and one narrower lemma

The preceding argument gives a necessary concentration condition:
\[
\boxed{
C_m\ge0
\quad\Longrightarrow\quad
\mathfrak M_m\le0
\quad\Longrightarrow\quad
\frac{B_m}{E}\ge\frac{\Lambda_*}{L}.
}
\tag{15}
\]

This is a genuine reduction, but only in one direction. C128 requires both concentration and alignment with its particular anchor. The mass \(B_m\) does not encode that alignment.

The next test is therefore **one necessary mass gate**, not two unrelated upper estimates for \(E\) and \(\mathcal J\).

### 4.1. Exact complete-source kernel for that gate

Let
\[
c_\ell(u)=\cos((m+2\ell)2\pi u/L)
\]
and define the finite Gram kernel
\[
\mathscr B_m(u,v)
=\sum_{\ell=1}^{128}c_\ell(u)c_\ell(v).
\]
Then
\[
\begin{aligned}
\mathcal I_m
&=\int_0^b\int_0^b
g(u)g(v)\mathscr B_m(u,v)\,du\,dv\\
&=\sum_{\ell=1}^{128}
\left(\int_0^b g(u)c_\ell(u)\,du\right)^2,
\end{aligned}
\]
so
\[
\boxed{
B_m=\frac8L\mathcal I_m,
\qquad
\mathfrak M_m=\Lambda_*-\frac{8\mathcal I_m}{E}.
}
\tag{16}
\]

Every source-index cross term is present:
\[
\mathcal I_m
=
\sum_{\alpha,\beta\ge1}
\int_0^b\int_0^b
g_\alpha(u)g_\beta(v)\mathscr B_m(u,v)\,du\,dv.
\]
Absolute convergence follows from
\(|\mathscr B_m|\le128\) and the same fixed-cell Gaussian majorant. This does not replace the completed square of a source sum by a sum of source squares.

For an explicit phase check, put
\[
F_m(z)=\sum_{\ell=1}^{128}\cos((m+2\ell)z).
\]
Then
\[
F_m(z)=
\frac{\sin(128z)}{\sin z}\cos((m+129)z),
\]
with continuous values
\[
F_m(k\pi)=128(-1)^{mk}.
\]
The Gram kernel is
\[
\boxed{
\mathscr B_m(u,v)=\frac12\left[
F_m\!\left(\frac{2\pi(u-v)}L\right)
+
F_m\!\left(\frac{2\pi(u+v)}L\right)
\right].
}
\tag{17}
\]
All apparent singularities in this display are removable. Both the difference and reflected-sum arguments are retained.

This kernel records the energy of the **already specified prefix**. It is not a new trial mask, panel, carrier, or denominator.

### 4.2. The single proposed PAPER lemma

**`SOURCE_FIXED_128_PREFIX_MASS_GATE` — unproved.**

For the same fixed \(P\), prove that every admitted selected cell with \(L>\Lambda_*\) satisfies
\[
\boxed{
8\int_0^b\int_0^b
g(u)g(v)\mathscr B_m(u,v)\,du\,dv
<
\Lambda_*E.
}
\tag{MG128}
\]

Its exact discriminator is the already defined
\[
\boxed{
\mathfrak M_m=
\Lambda_*-
\frac{
8\displaystyle\int_0^b\int_0^b
g(u)g(v)\mathscr B_m(u,v)\,du\,dv
}{E}.
}
\tag{18}
\]

The two outcome scopes are precise.

**Universal positive source outcome.** If a strictly positive lower envelope for \(\mathfrak M_m\) is proved at **every** remaining admitted cell, then (13), together with (14), gives a strictly negative upper envelope for \(C_m\) on the entire requested domain. This would exclude **only C128**, not every PC violation.

**Actual nonpositive source outcome.** If an explicitly admitted cell, or a rigorously admitted sequence, is proved to have \(\mathfrak M_m\le0\), then the strict mass-exclusion lemma fails there. This establishes only that the necessary mass threshold has been reached. It does **not** establish \(E\le La^2\), small dispersion, \(C_m\ge0\), or a negative original \(D_{\mathrm{pref}}\).

A positive result at just one cell excludes C128 only at that cell. An eventual result alone also leaves any intervening admitted cells unpaid.

### 4.3. Why this is not C128 renamed—and where the proof stops

MG128 contains neither the distinguished anchor nor the signed deviations from it. It asks whether the specified even-prefix block can contain the **necessary fraction \(\Lambda_*/L\)** of the original energy. That threshold was derived jointly from C128’s energy charge and dispersion cap.

The reduction deliberately loses information:
\[
C128\Longrightarrow\text{necessary prefix mass},
\]
but necessary prefix mass does not imply coherence. Thus a counterexample to MG128 is not automatically a counterexample to PC.

The first unpaid complete-source comparison for this narrowed test is exactly the sign of
\[
\boxed{\Lambda_*E-8\mathcal I_m.}
\tag{19}
\]
It is not resolved here.

The generic energy partition supplies only
\[
B_m<E
\quad\Longrightarrow\quad
\mathfrak M_m>\Lambda_*-L.
\]
That is decisive on the bounded subdomain already proved. For \(L>\Lambda_*\), its right-hand side is negative and supplies no sign decision. Likewise, \(\mathcal I_m\ge0\) is not the required relative upper bound. The new lemma still requires an estimate for the **complete source’s actual prefix-mass distribution relative to the same \(E\)**.

## 5. Scope of the verdict

The new proved result is (14): C128 is impossible on the admitted subdomain \(128\le L\le272-8\sqrt{254}\). The remaining full-domain question is open. No actual source cell with \(C_m\ge0\) has been produced, and the conditional margin (5) has not been activated.

The original physical exterior, both Fourier-index signs, low \(\varepsilon\) block, literal diagonal, zero node, final descent, paired logarithmic kernel, and signed \(\beta_m\) correction remain untouched. In particular, the bookkeeping partition (6) does not discard its complement.

The exponent-one prime block, prime/square compensation, opposite-side correlation, integrated symbol deviation, transfer, actual \(J_m\) sign, first \(\tau_j\) sign, Schur-floor, SV, and lag remain open. The constants \(C_0=128\), \(C_{\mathrm{int}}=134\), and \(C_2=146\) remain conditional; \(\Lambda_*\) is only the necessary prefix-energy cost derived above. :chatgpt-content-reference{index="5"}

No coefficient numerics, selected-cell search, mathematical runtime, Lean execution, or repository write was used. The new derivation has not received independent review. No route promotion or RH claim follows.

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_CORE_FIXED_128_PREFIX_MASS_GATE`, on PAPER, for the unchanged complete source and the same admitted selected family.** On the remaining domain \(L>\Lambda_*=272-8\sqrt{254}\), adjudicate the single source inequality **MG128**, with the exact discriminator (18), Gram kernel (17), and original denominator \(E\). A strictly positive source lower envelope for \(\mathfrak M_m\) at every remaining admitted cell, combined with (13)–(14), excludes only C128 on the full requested domain. A rigorously admitted cell with \(\mathfrak M_m\le0\) refutes only this narrower mass-exclusion lemma and must not be reported as a coherence witness or PC violation. If neither outcome is proved, report the unpaid sign (19). Check the factor two in (6), the 127 nontrivial discrepancies in (8), the constants (9), and the source cross terms in (16)–(17). Preserve the original \(N,K\), panel, carrier, \(Q\), \(5m\) splice, low block, both Fourier-index signs, physical exterior, literal diagonal, zero node, final descent, paired logarithmic kernel, and signed \(\beta_m\). No coefficient scan, fitted cutoff, source-index deletion, new mask or panel, mathematical runtime, Lean, repository write, activation of conditional square constants, route promotion, or RH claim is authorized.