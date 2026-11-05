# Fixed (K_2) leading kernel: whole-line spectral sign

STATUS: INDEPENDENTLY_REVIEWED_PAPER; LEADING-LIMIT SIGN ONLY.  This is a statement
about the first two renewal increments and their (R\to\infty) leading
kernel.  It is not a statement about the terminal (V), a general finite
prefix, or RH.

## Inputs and exact question

The preceding two-step candidate is
`RENEWAL_TWO_STEP_CANDIDATE.md`, SHA256
`8016c6a8a1e449e8a29db56f3421ef6180a7d88cb218f2078e62f151b2d0f848`.
Its source law is the complete theta density (r), with

\[
 \Phi(x)=e^{5x/2}r(e^{2x}),\qquad f=\Phi/A,
 \qquad r(1/t)=t^{5/2}r(t),
\]

and the fixed-offset \(K_2\) asymptotic proved in Section 1 below is

\[
 \frac{K_2(-R+u,-R+v)}{a\log(1/a)}\longrightarrow L(u,v),
 \qquad a=e^{-2R},
\]

where

\[
 L(u,v)=\frac{\mu}{A^2}(b_ub_v)^{5/4}
 \int_0^\infty t^{1/2}r(b_ut)r(b_vt)
       (\log t+u+v)\,dt,
 \qquad b_u=e^{2u}.
 \tag{1}
\]

The question is whether the matrix (L(u_i,u_j)) has a common sign for
every fixed finite family of distinct real offsets.  The answer is strict
negative definiteness when \(\mu>0\), assuming the displayed asymptotic and the standard
Hadamard factorization of completed \(\xi\).

The transform identity used below is source-locked in
`REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, SHA256
`1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282`,
lines 74--80: with
\(\widehat h(z)=\int_{\mathbb R}h(Y)e^{-izY}\,dY\),

\[
 \widehat f(z)=\frac{\xi(1/2-iz)}{A}.
 \tag{2}
\]

## 1. Entrywise leading limit (the new step)

The preceding candidate established the \(q_2/r\) estimate
\[
 0\leq \frac{q_2(t)}{r(t)}\leq C_0(1+\log t),\qquad t\geq1,
 \tag{A1}
\]
and its pointwise limit \( (q_2(t)/r(t))/\log t\to2\).  It explicitly
evaluated only the diagonal.  The fixed-offset entrywise limit used here is
obtained by the following additional change of variables.

For \(x=-R+u,\ y=-R+v\), \(a=e^{-2R}\), \(b_u=e^{2u}\), and
\(b_v=e^{2v}\), insert the exact density form of \(K_2\) from the preceding
candidate and set \(s=at\).
Since \(x+y=\log a+u+v\), this gives

\[
 \frac{K_2(-R+u,-R+v)}{a}
 =\frac{\mu}{2A^2}(b_ub_v)^{5/4}
   \int_a^\infty \sqrt{s}\,r(b_us)r(b_vs)
      \frac{q_2(s/a)}{r(s/a)}(\log s+u+v)\,ds.
 \tag{A2}
\]

For fixed \(s>0\), (A1) gives
\[
 \frac{1}{\log(1/a)}\frac{q_2(s/a)}{r(s/a)}
 \longrightarrow2.
\]
For \(s\geq a\) and \(\log(1/a)\geq1\), the same bound gives a constant
multiple of \(1+|\log s|\) after division by \(\log(1/a)\).  Thus the
integrand in (A2), divided by \(\log(1/a)\), is dominated by

\[
 C_{u,v}\sqrt{s}\,|r(b_us)r(b_vs)|
       (|\log s|+1)(|\log s|+1).
 \tag{A3}
\]

For fixed positive \(b_u,b_v\), this is integrable at infinity by the
source tail and at zero by reciprocity followed by the same tail estimate.
Dominated convergence therefore proves the entrywise formula (1) for every
fixed real pair \(u,v\).  This is a new finite-row input beyond the preceding
diagonal-only calculation; no uniformity in the offsets is claimed.

## 2. The leading integral is a whole-line mixed energy

Put \(t=e^{2Y}\) in (1).  Since
\(r(e^{2(u+Y)})=e^{-5(u+Y)/2}\Phi(u+Y)\), the exact algebra is

\[
 L(u,v)=2\mu\int_{\mathbb R}e^{-2Y}f(u+Y)f(v+Y)
                     (2Y+u+v)\,dY.
 \tag{B1}
\]

Define the weighted profile and a rescaled row

\[
 g(Y)=e^{-Y}f(Y),\qquad d_i=e^{u_i}c_i,
\]

and set

\[
 P(Y)=\sum_i d_i g(Y+u_i),\qquad
 Q(Y)=\sum_i d_i(Y+u_i)g(Y+u_i).
\]

For any finite row (c), (B1) gives, with no omitted factor,

\[
 \sum_{i,j}\overline{c_i}c_jL(u_i,u_j)
   =4\mu\,\operatorname{Re}\int_{\mathbb R}\overline{P(Y)}Q(Y)\,dY.
 \tag{B2}
\]

The integration variable is all of \(\mathbb R\): the \(t\in(0,\infty)\)
leading limit has removed the finite cutoff.  This is separate from the
original \(V\) integral over the physical half-line \(X\geq0\).

## 3. Exact Fourier normalization and multiplier

Let
\[
 C(\omega)=\sum_i d_i e^{i\omega u_i}.
\]

Translation and multiplication differentiation give

\[
 \widehat P(\omega)=\widehat g(\omega)C(\omega),
 \qquad
 \widehat Q(\omega)=i\widehat g'(\omega)C(\omega),
 \tag{C1}
\]

where the prime on \(\widehat g\) is the real-frequency derivative.
Plancherel, with the convention above, therefore yields

\[
\begin{aligned}
 \sum_{i,j}\overline{c_i}c_jL(u_i,u_j)
  &=\frac{2\mu}{\pi}\int_{\mathbb R}|C(\omega)|^2
       \operatorname{Re}\!\left(i\overline{\widehat g(\omega)}
                                    \widehat g'(\omega)\right)d\omega \\
  &=-\frac{2\mu}{\pi}\int_{\mathbb R}|C(\omega)|^2|\widehat g(\omega)|^2
       \operatorname{Im}\!\left(\frac{\widehat g'(\omega)}
                                      {\widehat g(\omega)}\right)d\omega.
\end{aligned}
\tag{C2}
\]

Thus the multiplier in the energy \(2\operatorname{Re}\int\overline P Q\)
is exactly
\(-2|\widehat g|^2\operatorname{Im}(\widehat g'/\widehat g)\); (C2) also
records the outer factor \(2\mu/\pi\) for the kernel (1).

From (2),
\[
 \widehat g(\omega)=\widehat f(\omega-i)
   =\frac{\xi(-1/2-i\omega)}{A},
 \tag{C3}
\]
so this line contains no zero of \(\widehat g\).

## 4. Hadamard sign below the critical strip

The standard completed \(\xi\) facts used here are: it is entire of order one,
even after the change \(z\mapsto \xi(1/2-iz)\), and its zeros correspond to
the nontrivial zeta zeros \(0<\operatorname{Re}\rho<1\).  Hence every zero
\(\zeta=\alpha+i\beta\) of \(\widehat f\) satisfies
\(|\beta|<1/2\).  The strip and functional-equation conventions are recorded
in NIST DLMF §§25.2.E12, 25.4.3--25.4.4 and §25.10(i):
https://dlmf.nist.gov/25.2.E12, https://dlmf.nist.gov/25.4, and
https://dlmf.nist.gov/25.10.

Evenness and order one permit the paired Hadamard product (the nonconstant
exponential factor is absent after pairing \(\zeta,-\zeta\)):

\[
 \widehat f(z)=\widehat f(0)
       \prod_{\{\zeta,-\zeta\}}
       \left(1-\frac{z^2}{\zeta^2}\right).
 \tag{D1}
\]

The order-one zero count gives
\(\sum_{\zeta}|\zeta|^{-2}<\infty\), so this paired product and its
logarithmic derivative converge normally away from the zeros.  No boundedness
of that logarithmic derivative on the real \(\omega\)-axis is needed for the
Fourier integral: \(g\) is Schwartz, hence \(\widehat g\) and
\(\widehat g'\) are Schwartz, and
\[
 |C(\omega)|^2\,|\widehat g(\omega)\widehat g'(\omega)|
\]
is integrable because \(C\) is bounded.  This directly justifies (C2), after
which the ratio form is valid pointwise by (C3).

At \(z=\omega-i\), one paired logarithmic derivative contributes

\[
 \operatorname{Im}\left(\frac1{z-\zeta}+\frac1{z+\zeta}\right)
 =\frac{1+\beta}{(\omega-\alpha)^2+(1+\beta)^2}
  +\frac{1-\beta}{(\omega+\alpha)^2+(1-\beta)^2}>0.
 \tag{D2}
\]

All terms are positive because \(|\beta|<1/2\).  The paired series is the
logarithmic derivative of (D1), and completed \(\xi\) has infinitely many
zeros in the critical strip, so the sum is strictly positive for every real
\(\omega\):

\[
 \operatorname{Im}\frac{\widehat f'(\omega-i)}{\widehat f(\omega-i)}>0.
 \tag{D3}
\]

Since \(\widehat g'(\omega)=\widehat f'(\omega-i)\), (C3) and (D3) make the
integrand weight in the second line of (C2) strictly positive apart from the
factor \(|C|^2\).

## 5. Strict negative definiteness and finite-\(R\) consequence

For distinct real offsets and a nonzero coefficient row, the exponential
polynomial \(C(\omega)=\sum_i d_i e^{i\omega u_i}\) is not identically zero;
its zero set is discrete.  The profile \(g\) is Schwartz by the full-theta
double-exponential tails, so (C2) is finite.  Equations (C2) and (D3) imply

\[
 c^*[L(u_i,u_j)]c<0\qquad(c\ne0).
 \tag{E1}
\]

For a fixed finite offset family, the entrywise \(K_2\) asymptotic proved in
Section 1 then gives

\[
 \frac{c^*[K_2(-R+u_i,-R+u_j)]c}{a\log(1/a)}
   \longrightarrow c^*[L(u_i,u_j)]c<0,
 \tag{E2}
\]

so the actual (K_2) quadratic is negative for all sufficiently large (R).
Those nodes lie in \(J=(-\infty,0)\), generally outside the original
interval \(I=(-\log2/2,0)\).  If one combines this with the already accepted
holomorphic all-row propagation lemma, it yields existence of some finite
complex negative row in (I) whenever universal (K_2\)-positivity on (I)
is assumed.  It supplies no rank bound or explicit in-(I) nodes.

## 6. What the terminal \(V\) does at the same common shift

For fixed offsets \(u,v\), write the original terminal integral at
\(x=-R+u,\ y=-R+v\) with \(s=t-R\):

\[
 V(-R+u,-R+v)
  =\int_{-R}^{\infty}(2s+u+v)f(s+u)f(s+v)\,ds.
 \tag{F1}
\]

The full-line integral of the same integrand is zero.  Indeed, after
\(h=s+(u+v)/2\), the product
\(f(h+(u-v)/2)f(h-(u-v)/2)\) is even in \(h\), while the remaining factor
is \(2h\).  Hence

\[
 V(-R+u,-R+v)
  =-\int_{-\infty}^{-R}(2s+u+v)f(s+u)f(s+v)\,ds.
 \tag{F2}
\]

The full-source tail and all fixed derivatives are bounded by a
superexponential envelope (FULL_SIGN_TRANSFER_AUDIT, source §2, lines 56--62,
same SHA256 as above).  For every fixed finite offset family, (F2) therefore
gives entrywise

\[
 V(-R+u_i,-R+u_j)=o\!\left(a\log(1/a)\right),\qquad a=e^{-2R}.
 \tag{F3}
\]

The shifts in this section eventually lie outside the original interval
\(I\), so the source telescope needs a small global extension before its
remainder may be called a later-term aggregate.  For arbitrary fixed real
\(x,y\), put \(\alpha=e^{2x}\), \(\gamma=e^{2y}\).  From the complete-theta
tail and its positive first-term lower bound, the exact source integrand
\[
 \psi_{xy}(t)=\frac{\mu}{2A^2}(\alpha\gamma)^{5/4}t^{1/2}
   \frac{r(\alpha t)r(\gamma t)}{r(t)}(\log t+x+y)
\]
satisfies, for \(t\geq1\),
\[
 |\psi_{xy}(t)|\leq C_{xy}t^{3/2}(1+\log t)e^{\delta_{xy}t},
 \qquad \delta_{xy}=\pi(1-\alpha-\gamma)<\pi.
 \tag{F4}
\]
Choose \(\lambda\) with \(\max(0,\delta_{xy})<\lambda<\pi\); after enlarging
the constant, (F4) is bounded by \(C_{xy}e^{\lambda t}\).  The renewal sums
\(S_m\uparrow S_\infty\) and the source law \(S_\infty\) has density
\(r^*(t)=tr(t)/\mu\), so \(\mathbb E e^{\lambda S_\infty}<\infty\) for
\(\lambda<\pi\).  Therefore dominated convergence, with the cutoff
\(\mathbf1_{S_m\geq1}\), gives
\[
 K_m(x,y)=\mathbb E[\mathbf1_{\{S_m\geq1\}}\psi_{xy}(S_m)]
 \longrightarrow
 V(x,y)=\mathbb E[\mathbf1_{\{S_\infty\geq1\}}\psi_{xy}(S_\infty)].
 \tag{F5}
\]
The cutoff causes no boundary atom because \(S_\infty\) has a density.
Thus for the shifted pairs the limit of the finite-prefix telescope is
the exact difference \(V_R-K_{2,R}\).  If \(T_{\geq3,R}\) denotes this
later-term remainder, so that \(V_R=K_{2,R}+T_{\geq3,R}\), then (E2) and (F3)
imply, for every fixed nonzero row,

\[
 \frac{c^*[T_{\geq3,R}(u_i,u_j)]c}{a\log(1/a)}
 \longrightarrow -c^*[L(u_i,u_j)]c>0.
 \tag{F6}
\]

This is an aggregate leading compensation forced by the terminal tail.  It
does not make the individual later blocks positive, and it gives no finite
\(R\) sign theorem for the terminal \(V\).

## 7. Scope and remaining gap

This is a new sign result for the fixed two-step leading block.  The earlier
Hankel/Jordan report (SHA256
`c39016a5ba57aaa9e60f56682d11a9eebde9ee3202e4b2294c4e5beb156bc2c3`)
and integrated-sign report (SHA256
`8560b8c70e35fd76dbb2820471440aa802cefe21f9928e957c9f2e0be7dbe8eb`)
analyze the terminal (V), its positive sibling, or the physical half-line;
they do not establish (E1).  The present calculation uses the whole-line
limit after the (K_2) cutoff and should not be relabeled as a full-(V)
Fourier proof.

No general-\(m\) sign or leading-kernel extension, uniformity in offset
families, or terminal positivity theorem is proved here.  The argument assumes the entrywise
\(K_2\) leading asymptotic derived in Section 1 and the standard completed
\(\xi\) Hadamard factorization; either assumption must be checked separately
before using this card as a formal consumer.  The arithmetic input is only
the unconditional exclusion of completed-\(\xi\) zeros outside the critical
strip, together with its functional equation; no RH or stronger
prime-specific lower bound is used.  The negative leading Gram in (E1) and
the opposite aggregate leading Gram in (F6) cancel at scale
\(a\log(1/a)\), leaving the original terminal sign question open.

## Publication and independent acceptance

The complete candidate with SHA256
`c6138f666fb5e1a33831c21190c56d765b42cf5e89cc3054baf47bd6a3ae50e1`
was independently checked by `/root/sibling5_check`; review SHA256
`01931fa74b3598aedcbfad0ba9548d4416fcd47d7fe84730ed4e1ab27404358f`.
The parent independently reconstructed the entrywise limit, Fourier constants,
paired-product sign, fixed-real-pair convergence, and opposite aggregate limit.
The status line and this receipt are the only publication additions.

The staging K2 candidate cited above is publicly preserved, with only its
acceptance status changed, as
`docs/Codex/REPORT_2026-09-16_RENEWAL_TWO_STEP_OBSTRUCTION.md`, SHA256
`7a3e0972ca8e2306de49f048a7b31c4eb10c4f0217c35837105eb3a9d8c55a90`.
The transform source is
`docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`.
This result is an analytic compensation diagnostic, not a new lower bound
for the original V and not canonical or Lean admission.
