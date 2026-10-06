# Proshka growth answer7 — exact inline capture

Chat `6ac54396-d878-83eb-ae29-35d2bdd2262b`, question `ce9f00f6-25c2-4811-ac5b-f2e7fe41150a`.
Answer `03c37d8f-aeec-48b6-8061-2dc545c6594a`, captured 2026-10-06 22:22 UTC. Untruncated read_thread text.
Claims below require audit; RH remains OPEN.

---

Ы — **I proved a source-specific obstruction to sign-blind Cotlar gluing, together with a signed long-range cancellation estimate for the actual arithmetic packets.**

The tested packets retain **both parts of the same \(\Phi\)**: their diagonals and divided differences are not estimated as unrelated data. On every sufficiently late original cell, they satisfy
\[
\sum_\ell C_\ell^2\preceq64(\log m)^5I,
\]
yet every sign-blind Cotlar bound for their sum incurs a cost at least
\[
\Gamma_m:=\frac{\sqrt m\,\log\log m}{1000(\log m)^9}.
\]
The reason is not poor control of the individual packets: **large, negative cross-packet correlations are essential**, and remain essential beyond every fixed polylogarithmic packet-neighborhood.

**This kills the specific gluing mechanism below—not the actual CCM target. The exceptional Schur sign, SP, and RH remain open. No improved bottom floor or common good subsequence is claimed.**

:chatgpt-content-reference{index="3"}[Complete PAPER verdict, including the machine-readable header and dependency ledger](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_NEGATIVE_BOTTOM_GROWTH_Q07.md)

## 1. The attempted estimate uses actual joint prime–pole packets

**[FINITE_CELL | PAPER]**

Use the original carrier in the accepted coordinates:
\[
e_j(t)=L^{-1/2}e^{i\omega_jt},
\qquad \omega_j=\frac{2\pi j}{L},
\qquad -m\le j\le m,\qquad L=\log m.
\]
This is the source identification of CCM Proposition 3.2 with \(\lambda=\sqrt m\); the correlation factors below are those of Lemma 2.3, and the full source remains equation (3.19). :chatgpt-content-reference{index="0"}

In the integer variable, the joint signed measure is
\[
d\mu(x)=
\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\delta_n(dx)
-\left(x^{-1/2}-x^{-3/2}\right)dx.
\tag{3}
\]
Thus its causal operator is precisely
\[
\mathcal P-R_++R=F^{-1}[X,F].
\]
The \(I-R\) factor, both pole pieces and all prime powers remain.

Choose
\[
X=\left\lfloor\frac{m}{L^8}\right\rfloor,
\qquad H=\lceil L^4\rceil,
\]
and partition \([X,2X)\) into consecutive half-open intervals \(I_\ell\) with integer endpoints and length at most \(H\). Define the full-carrier matrices
\[
C_\ell
=
P_m\left[
\int_{I_\ell}(S_{\log x}+S_{\log x}^{*})\,d\mu(x)
\right]P_m.
\tag{4}
\]
These are **arithmetic packets**, not replacement carrier-frequency blocks. The eventual witness lies in a genuine contiguous middle-frequency band.

Writing
\[
\beta(x)=1-\frac{\log x}{L},
\]
their entries are exactly
\[
\begin{aligned}
d_{\ell j}
&=2\int_{I_\ell}\beta(x)\cos(\omega_j\log x)\,d\mu(x),\\
h_{\ell j}
&=-\int_{I_\ell}\sin(\omega_j\log x)\,d\mu(x),\\
(C_\ell)_{jj}&=d_{\ell j},\\
(C_\ell)_{jk}
&=\frac{h_{\ell j}-h_{\ell k}}{\pi(j-k)}
\qquad(j\ne k).
\end{aligned}
\tag{5}
\]
So each \(C_\ell\) retains the **actual coupling between \(d\) and \(h\)**.

Let
\[
\mathcal R_m
=
C_{\rm ar}\sqrt m\,L^3
e^{-.001(L/\log L)^{1/3}}
\]
denote the already accepted primitive envelope. The cumulative primitive of \(\mu|_{[X,2X)}\) is a difference of two values—or left traces—of \(\Phi\). The accepted finite-Hilbert-matrix estimate therefore gives
\[
\boxed{
\left\|\sum_\ell C_\ell\right\|\le8\mathcal R_m,
\qquad
\left|\sum_\ell d_{\ell j}\right|\le4\mathcal R_m.
}
\tag{6}
\]
This is the **coherent reference bound** for the falsification, not a new SP estimate.

Every packet-boundary atom is allocated once. No cutoff atom is discarded, no logarithm is linearized, and every intermediate carrier projection remains present.

## 2. The packet square function really is small

**[COFINAL_FAMILY | PAPER]**

Let \(M_\ell=|\mu|(I_\ell)\). Since \(\Lambda(n)\le\log n\),
\[
M_\ell\le\frac{H(L+1)}{\sqrt X}
\le\frac{2HL}{\sqrt X}.
\]
The zero-frequency case of the accepted \(\Phi\)-bound gives
\[
\sum_{X\le n<2X}\frac{\Lambda(n)}{\sqrt n}
=
2(\sqrt2-1)\sqrt X+O(X^{-1/2}+\mathcal R_m).
\tag{7}
\]
Here \(\mathcal R_m=o(\sqrt X)\). Thus, eventually,
\[
\sum_\ell M_\ell\le4\sqrt X.
\]

Finite shifts and \(P_m\) are contractions, so
\[
\|C_\ell\|\le2M_\ell\le\frac{4HL}{\sqrt X},
\qquad
\sum_\ell\|C_\ell\|\le8\sqrt X.
\]
Consequently,
\[
\boxed{
\sum_\ell C_\ell^2
\preceq
\left(\sum_\ell\|C_\ell\|^2\right)I
\preceq32HL\,I
\preceq64L^5I.
}
\tag{8}
\]

This **square-function estimate** controls the sum of individual packet-output energies in the original norm, on all \(2m+1\) complex directions. The next calculation shows why it cannot be converted into control of the sum by a sign-blind almost-orthogonality argument.

## 3. The original middle band detects large sign-changing packet contributions

**[COFINAL_FAMILY | PAPER]**

Take
\[
\mathcal J_m
=
\{\lceil m/4\rceil,\ldots,\lfloor3m/4\rfloor\},
\qquad N=|\mathcal J_m|\ge m/3.
\]
Eventually, throughout \([X,2X]\),
\[
\log X\ge L/2,
\qquad
\frac{6\log L}{L}
\le\beta(x)\le
\frac{10\log L}{L}.
\tag{9}
\]

Put
\[
A_n=\frac{2\beta(n)\Lambda(n)}{\sqrt n},
\qquad
P_{\ell j}=\sum_{n\in I_\ell}A_n\cos(\omega_j\log n).
\]
The **joint** packet diagonal is
\[
d_{\ell j}=P_{\ell j}-V_{\ell j},
\]
where
\[
V_{\ell j}
=
2\int_{I_\ell}
\beta(x)(x^{-1/2}-x^{-3/2})
\cos(\omega_j\log x)\,dx.
\]

### Squared prime mass

Equation (7) supplies weighted mass at least \(\sqrt X/2\), eventually. Higher prime powers contribute only \(O(L^2)\): there are at most
\[
\sqrt{2X}\,\frac{\log(2X)}{\log2}
\]
such powers, each with weight at most \(L/\sqrt X\). Thus primes alone supply at least \(\sqrt X/4\).

It follows that
\[
\begin{aligned}
\sum_{X\le n<2X}\frac{\Lambda(n)^2}{n}
&\ge
\frac{\log X}{\sqrt{2X}}
\sum_{X\le p<2X}\frac{\log p}{\sqrt p}\\
&\ge\frac L{16},
\end{aligned}
\]
and hence
\[
\boxed{
\sum_{X\le n<2X}A_n^2
\ge9\frac{(\log L)^2}{L}.
}
\tag{10}
\]
Prime powers have only been omitted from a **lower bound for a positive square sum**. They remain in every source matrix.

### Finite-grid mean square, including both aliases

Set \(\theta_n=2\pi\log n/L\). The elementary geometric-sum estimate is
\[
\left|
\frac1N\sum_{j\in\mathcal J_m}e^{ij\theta}
\right|
\le
\min\left(1,\frac1{N|\sin(\theta/2)|}\right).
\]

For \(n\ne k\) in one packet,
\[
|\theta_n-\theta_k|
\ge\frac{\pi|n-k|}{XL}.
\]
The other cosine-product frequency must also be paid: \(\theta_n+\theta_k\) stays a distance comparable to \(\log L/L\) from \(4\pi\). Therefore the averaged cosine Gram matrix satisfies
\[
\left\|G_\ell-\tfrac12I\right\|
\le
\frac{XL}{N}(1+\log H)
+\frac{HL}{2N\log L}
=o(1).
\]
The first term pays difference frequencies; the second pays **all sum frequencies**, including diagonal ones. The bound is uniform in the packet.

Thus
\[
\boxed{
\frac1N\sum_{j\in\mathcal J_m}P_{\ell j}^{\,2}
\ge\frac14\sum_{n\in I_\ell}A_n^2
}
\tag{11}
\]
eventually. No probabilistic model or unproved equidistribution statement is used.

### Continuous pole compensation and both packet endpoints

Let \(\beta_*=10\log L/L\). Integration by parts with the **exact logarithmic phase** gives
\[
\boxed{
|V_{\ell j}|
\le
\frac{10\beta_*\sqrt X}{|\omega_j|}
\le
\frac{20\beta_*\sqrt X\,L}{\pi m}.
}
\tag{12}
\]
Indeed, the boundary amplitude is
\[
2\beta(x)(\sqrt x-x^{-1/2});
\]
its two endpoint values plus the integral of its derivative cost at most \(10\beta_*\sqrt X\).

There are at most \(2X/H\) packets, so
\[
\sum_\ell\sup_{j\in\mathcal J_m}|V_{\ell j}|^2
\le
\frac{800\beta_*^2X^2L^2}{\pi^2m^2H}
\le
\frac{800\beta_*^2}{\pi^2HL^{14}}
=o((\log L)^2/L).
\]
Using
\[
(P-V)^2\ge\tfrac12P^2-V^2
\]
with (10)–(11) proves
\[
\boxed{
\frac1N\sum_{j\in\mathcal J_m}\sum_\ell d_{\ell j}^2
\ge\frac{(\log L)^2}{2L}.
}
\tag{13}
\]

On the other hand, direct counting gives
\[
|d_{\ell j}|
\le
\frac{4\beta_*HL}{\sqrt X}
\le120\frac{L^8\log L}{\sqrt m}.
\]
Therefore
\[
\boxed{
\frac1N\sum_{j\in\mathcal J_m}\sum_\ell|d_{\ell j}|
\ge
\frac{\sqrt m\log L}{240L^9}.
}
\tag{14}
\]

Choose \(j_m\) maximizing the inner sum. This is a **finite, source-defined selection rule**, not a bottom-vector selection. In particular,
\[
\boxed{
\sum_\ell|d_{\ell j_m}|\ge\Gamma_m.
}
\tag{15}
\]

All averaging here is over frequencies of **one original cell**. The conclusion holds on every sufficiently late cell; no good subsequences are intersected.

## 4. The exact Cotlar and positive-envelope obstructions

**[COFINAL_FAMILY | PAPER]**

Choose
\[
\varepsilon_\ell=\operatorname{sgn}(d_{\ell j_m}),
\]
assigning either sign at zero. Then
\[
\left\|\sum_\ell\varepsilon_\ell C_\ell\right\|
\ge
\left\langle e_{j_m},
\sum_\ell\varepsilon_\ell C_\ell e_{j_m}\right\rangle
=
\sum_\ell|d_{\ell j_m}|
\ge\Gamma_m.
\]

For the **Cotlar–Stein test**, the finite self-adjoint family has constant
\[
\mathfrak C_m
=
\max_\ell\sum_k\|C_\ell C_k\|^{1/2}.
\]
Its two adjoint-product bounds agree because the matrices are self-adjoint. Multiplying whole packets by signs leaves these product norms unchanged, so the same Cotlar constant bounds every signed sum. The theorem’s finite bounded-operator hypotheses map directly here. :chatgpt-content-reference{index="1"}

Consequently,
\[
\boxed{\mathfrak C_m\ge\Gamma_m.}
\tag{17}
\]
For every fixed \(A>0\), \(0<\eta<1/2\),
\[
\boxed{
Am^\eta-\mathfrak C_m
\le Am^\eta-\Gamma_m<0
}
\tag{18}
\]
on every sufficiently late original cell.

The sign-modified sum is **not a replacement CCM source**. It is the compulsory control for a sign-invariant theorem applied to the actual packet family. The actual-source signed consequence appears in Section 5 below.

### The failure also reaches one-sided gluing against the actual target

Suppose each packet is replaced by a positive upper envelope:
\[
U_\ell\succeq0,\qquad U_\ell\succeq C_\ell.
\]
Keep everything else unchanged:
\[
\mathsf H_m^{\rm loc}(r)
=
\mathsf H_m(r)+\sum_\ell C_\ell-\sum_\ell U_\ell
\preceq\mathsf H_m(r),
\qquad
\mathsf H_m(r)=\mathsf S(r)-\mathsf T_m.
\tag{19}
\]
This is a valid **sufficient lower envelope** for the requested matrix.

On the selected original mode,
\[
\begin{aligned}
\left\langle e_{j_m},
\sum_\ell(U_\ell-C_\ell)e_{j_m}\right\rangle
&\ge
\sum_\ell\max(-d_{\ell j_m},0)\\
&\ge\tfrac12\Gamma_m-2\mathcal R_m.
\end{aligned}
\tag{20}
\]

The archimedean series gives
\[
a(\omega)\le4+\tfrac12\log(1+4\omega^2),
\qquad
\|\mathsf H_m(0)\|\le L+8+4\mathcal R_m.
\]
Hence, with \(r=Am^\eta\),
\[
\boxed{
\langle e_{j_m},\mathsf H_m^{\rm loc}(r)e_{j_m}\rangle
\le
r+L+8+6\mathcal R_m-\tfrac12\Gamma_m<0
}
\tag{21}
\]
eventually for \(0<\eta<1/2\).

This upper envelope proves that **every independently positive packet-envelope construction of this form fails**, even when its envelopes use all the source data. The original diagonal slack and all remaining source terms were retained.

It does **not** prove that \(\mathsf H_m(r)\) is negative. The killed object is its optional lower certificate.

## 5. What the actual source does: large negative cross-packet compensation

**[COFINAL_FAMILY | PAPER]**

Define
\[
C_+=\sum_{\varepsilon_\ell=+1}C_\ell,
\qquad
C_-=\sum_{\varepsilon_\ell=-1}C_\ell,
\qquad
f_m=e_{j_m}.
\]
The minus-labelled packets are **not negated** in \(C_-\).

The signed test and the coherent source bound give
\[
\|(C_+-C_-)f_m\|^2
-
\|(C_++C_-)f_m\|^2
\ge
\Gamma_m^2-64\mathcal R_m^2.
\]
Thus
\[
\boxed{
\operatorname{Re}\langle C_+f_m,C_-f_m\rangle
\le
-\frac{\Gamma_m^2-64\mathcal R_m^2}{4}
\le-\frac{\Gamma_m^2}{8}.
}
\tag{22}
\]

**This is an actual signed arithmetic estimate.** Each output \(C_\ell f_m\) contains the diagonal and every divided-difference entry:
\[
(C_\ell f_m)_k=
\begin{cases}
d_{\ell j_m},&k=j_m,\\[1mm]
\displaystyle
\frac{h_{\ell k}-h_{\ell j_m}}{\pi(k-j_m)},&k\ne j_m.
\end{cases}
\]
The inner product in (22) sums over **every output mode \(-m\le k\le m\)**. It is not merely a statement about diagonal means.

Moreover, for any integer \(D\ge1\), the square-function bound pays nearby packet pairs:
\[
\begin{aligned}
\sum_{\substack{\ell\in+,\,k\in-\\|\ell-k|\le D}}
|\langle C_\ell f,C_kf\rangle|
&\le D\sum_\ell\|C_\ell f\|^2\\
&\le64DL^5\|f\|^2.
\end{aligned}
\tag{23}
\]
Each packet has at most \(2D\) neighbors; no carrier-dimension factor is suppressed.

Subtracting these nearby pairs from (22) yields
\[
\boxed{
\operatorname{Re}
\sum_{\substack{\ell\in+,\,k\in-\\|\ell-k|>D}}
\langle C_\ell f_m,C_kf_m\rangle
\le
-\frac{\Gamma_m^2}{8}+64DL^5.
}
\tag{24}
\]
For every fixed \(A>0\), taking \(D=\lceil L^A\rceil\) makes the right side at most
\[
-\Gamma_m^2/16
\]
eventually.

Therefore a polylogarithmic neighborhood in **this arithmetic-packet decomposition** cannot account for the necessary cancellation. This is not a claim about every decomposition or about distance between carrier indices.

## 6. The exact arithmetic correlation still needing an upper bound

**[FINITE_CELL | PAPER]**

The remaining correlation has an explicit finite-projection kernel. Define
\[
q_{ab}(x)=
\begin{cases}
2\beta(x)\cos(\omega_a\log x),&a=b,\\[1mm]
\displaystyle
\frac{\sin(\omega_b\log x)-\sin(\omega_a\log x)}
{\pi(a-b)},&a\ne b.
\end{cases}
\tag{25}
\]
For an original coefficient vector \(c\), put \(v_c(x)=q(x)c\). Then
\[
C_\ell c=\int_{I_\ell}v_c(x)\,d\mu(x),
\]
and
\[
\boxed{
\mathfrak A_{\ell k}(c)
=
\int_{I_\ell}\int_{I_k}
\langle v_c(x),v_c(y)\rangle\,d\mu(x)\,d\mu(y).
}
\tag{26}
\]

This contains the actual
\[
\frac{\Lambda(n)\Lambda(q)}{\sqrt{nq}}
\]
terms, **both prime–continuous cross terms**, and the continuous–continuous term, all with the same finite-window factors. The inner product retains the entire finite output sum. In particular, no intermediate \(P_m\) is replaced by the identity.

The unestimated part of this Cotlar branch is
\[
\mathfrak X_m(c)
=
2\operatorname{Re}\sum_{\ell<k}\mathfrak A_{\ell k}(c).
\tag{27}
\]
Exactly,
\[
\left\|\sum_\ell C_\ell c\right\|^2
=
\sum_\ell\|C_\ell c\|^2+\mathfrak X_m(c).
\]
The first term is already bounded by \(64L^5\|c\|^2\). A signed upper bound
\[
\mathfrak X_m(c)\le A_\eta m^{2\eta}\|c\|^2
\tag{28}
\]
on the vectors where this block must be paid would give a subpolynomial norm budget for **this arithmetic block**.

**Equation (28) is not proved here.** It is stronger than a purely one-sided estimate might require, is not asserted necessary for SP, and would not by itself settle the other arithmetic ranges or their relative-form coupling.

For use in the existing exceptional Schur problem, those vectors must be the **actual corrected vectors**
\[
\mathcal J_rv=v-A_r^{-1}B_rv,
\tag{29}
\]
not \(v\) alone. Here \(A_r,B_r\) are the actual regular and regular–exceptional blocks. Their original carrier norm must remain in the budget. No bound on \(\|\mathcal J_r\|\) is supplied, and the correction \(B_r^*A_r^{-1}B_r\) has not been dropped.

## Closeout

The registered prediction that gluing must preserve the sign is confirmed more sharply than by a generic counterexample: **the actual source forces negative far-packet correlations of order \(m/(\log m)^{18}\), up to the displayed logarithmic and constant factors.**

The killed theorem shapes are the subpolynomial sign-blind Cotlar constant and independently positive packet-envelope gluing for the specified decomposition. The witness is an actual complex carrier mode in a contiguous middle band, but is **not asserted to lie in the exceptional space**. Consequently this does not refute a sign-sensitive estimate restricted to the actual Schur-corrected exceptional vectors.

The prior whole-matrix floor, regular-subspace theorem and repaired high-zero budget are unchanged. No jets or auxiliary positive spaces have been reintroduced.

**Next mathematical step:** estimate the signed correlation (26) on the actual corrected vectors (29), keeping the prime–prime and mixed continuous terms combined. Its first source-specific discriminator is the forced far-pair budget (24): any proposed estimate that loses that negative contribution has already failed on the original source, before it reaches the Schur consumer.
