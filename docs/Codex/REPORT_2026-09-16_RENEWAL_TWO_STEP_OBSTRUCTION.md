# Two-step renewal block \(K_2\): analytic all-row obstruction

STATUS: INDEPENDENTLY_REVIEWED_PAPER; FINITE-BLOCK POSITIVITY REJECTED AT ALL-ROW
SCOPE, WITH NO CLAIM ABOUT THE TERMINAL \(V\).

The pinned plan selects the first two renewal increments as its first bounded
test (PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES.md, item 1, equations in lines
34--50; local SHA256
f614fa57901954d7fc1716965fe81250e6d8a02f6ad800face52823be8721cc2).
The source response defines the complete field and its cutoff-aware telescope
in equations (4), (8)--(10), (37), and (41)--(44) of
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md
(local SHA256
784e16445c64c1b480cfb0fdc5740182ad59253a775bfc8ab7dc0c44a654eafd).
The source law is fixed by REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md,
L14--L17 (local SHA256
feeb23e50223e5d85b16b8f6f1e83f849a9029f6f9aa8d4f47ad70cd4f5dad21), together
with the SIZEBIASCOMP response §6, equations (22)--(29).  Thus
\(T=\sum_{n\geq1}\operatorname{Gamma}(2,1)/(\pi n^2)\) has density \(r\),
and the multiplier \(H\), distinct from the shape-one density \(h\), has
density
\[
k_H(\lambda)=\lambda^{-1/2}-1,\qquad 0<\lambda<1.
\]
Thus
\[
S_2=T_1+H T_2
\]
with independent \(T_1,T_2,H\).

For \(a=e^{2x}\), \(b=e^{2y}\), the exact projected pair field from the source
equation (44) is
\[
\psi_{xy}(t)=A_{xy}(t)(\log t+x+y),\qquad
A_{xy}(t)=\frac{\mu}{2A^2}(ab)^{5/4}\sqrt t\,
                 \frac{r(at)r(bt)}{r(t)}>0.
\]
The proposed two-step block, including the physical cutoff, is therefore
\[
K_2(x,y)=\mathbb E\!\left[
  \mathbf 1_{\{S_2\geq1\}}\psi_{xy}(S_2)\right].
\tag{1}
\]
This is exactly the first two expected increments of the source telescope;
it does not replace the terminal law by a new source.

Let \(q_2\) be the density of \(S_2\).  The density \(v\) of \(HT_2\) is
\[
v(t)=\int_t^\infty
       \left((tu)^{-1/2}-u^{-1}\right)r(u)\,du,
\qquad q_2=r*v.
\tag{2}
\]
The full source tail estimate already paid in the source report is
\[
r(t)\leq4\pi^2t e^{-\pi t},\qquad
r(t)\sim C t e^{-\pi t},\qquad C=4\pi^2.
\tag{3}
\]
For \(t\geq1\), (2) and \(\sqrt{1+z}-1\leq z/2\) give the global bound
\[
0\leq e^{\pi t}v(t)
 \leq4\pi^2\int_0^\infty
       \left(\sqrt{1+w/t}-1\right)e^{-\pi w}\,dw
 \leq \frac{2}{t}.
\tag{4}
\]
The same change of variables, dominated by \(w e^{-\pi w}/(2t)\), and (3)
give the exact tail limit
\[
t\,e^{\pi t}v(t)\longrightarrow
\frac{C}{2\pi^2}=2.
\tag{5}
\]
Near zero, (2) gives
\[
v(t)\leq t^{-1/2}\mathbb E[T^{-1/2}],
\tag{6}
\]
so the convolution below has no hidden endpoint divergence.

Writing \(\widehat r(t)=e^{\pi t}r(t)\) and
\(\widehat v(t)=e^{\pi t}v(t)\), one has
\[
e^{\pi t}q_2(t)=\int_0^t\widehat r(t-u)\widehat v(u)\,du.
\]
Split this integral into \(u< M\), \(M\leq u\leq t/2\), and
\(t/2<u<t\).  Equations (3)--(6) make the first and last pieces
\(O(t)\), uniformly after \(M\) is fixed.  On the middle piece,
\(\widehat r(t-u)/(t-u)\to C\) and \(u\widehat v(u)\to2\), uniformly after
first taking \(M\) large.  Hence
\[
\frac{q_2(t)}{r(t)}\sim2\log t,\qquad t\to\infty,
\tag{7}
\]
and the same split supplies the usable global bound
\[
0\leq\frac{q_2(t)}{r(t)}\leq C_0(1+\log t),\qquad t\geq1.
\tag{8}
\]
The coefficient \(2\) is source-specific: the \(H\)-density vanishes
linearly at \(\lambda=1\), while the \(T\)-density has the double
\(e^{\pi t}\)-moment pole inherited from its first Gamma(2) factor.

Now take the diagonal \(y=x\), so \(b=a\).  Substituting (1) and then
\(u=at\) gives the exact cutoff-preserving formula
\[
K_2(x,x)
 =\frac{\mu}{2A^2}\,a
   \int_a^\infty \sqrt u\,r(u)^2
     \frac{q_2(u/a)}{r(u/a)}\log u\,du.
\tag{9}
\]
Let \(L=\log(1/a)\).  From (7)--(8), for every fixed \(u>0\),
\[
\frac{1}{L}\frac{q_2(u/a)}{r(u/a)}\longrightarrow2
\qquad(a\downarrow0).
\]
For \(u\geq a\), (8) bounds this ratio divided by \(L\) by a constant
multiple of \(2+|\log u|\).  Therefore dominated convergence applies to
(9), because
\[
\sqrt u\,r(u)^2|\log u|\,(2+|\log u|)
\]
is integrable on \((0,\infty)\): at infinity this follows from (3), and at
zero from the reciprocal full-source identity
\(r(1/u)=u^{5/2}r(u)\) together with (3).  Consequently
\[
\lim_{a\downarrow0}\frac{K_2(x,x)}{a\log(1/a)}
 =\frac{\mu}{A^2}J,
\qquad
J=\int_0^\infty \sqrt u\,r(u)^2\log u\,du.
\tag{10}
\]
The sign of \(J\) is exact, with no numerical evaluation.  Splitting at one
and substituting \(u=1/v\) in \((0,1)\), reciprocity gives
\[
J=\int_1^\infty
      \bigl(u^{1/2}-u^{5/2}\bigr)r(u)^2\log u\,du<0.
\tag{11}
\]
Thus
\[
K_2(x,x)<0
\]
for all sufficiently negative real \(x\) (equivalently, sufficiently small
\(a\)).  This is a genuine diagonal obstruction for the analytically
continued block, and it retains \(S_2\)'s law and the cutoff \(S_2\geq1\).

It remains to bring the obstruction back to the original interval
\(I=(-\log2/2,0)\), where \(a\in(1/2,1)\).  No pointwise claim that the
diagonal is negative inside \(I\) is needed.  Using \(q_2/r\) in (1), write
\[
K_2(z,w)=\frac{\mu}{2A^2}e^{\frac52(z+w)}
 \int_1^\infty \sqrt t\,\frac{q_2(t)}{r(t)}
       r(e^{2z}t)r(e^{2w}t)(\log t+z+w)\,dt.
\tag{12}
\]
On
\[
\Omega=\{z\in\mathbb C:\operatorname{Re}z<0,\ |\operatorname{Im}z|<\pi/8\},
\]
\(\operatorname{Re}(e^{2z})>0\).  The full-source series used in
REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, equations (15)--(23) and
(54)--(58) (local SHA256
1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282), gives
the exact normally convergent expansion
\[
r(\zeta)=\sum_{n\geq1}
 \bigl(4\pi^2n^4\zeta-6\pi n^2\bigr)e^{-\pi n^2\zeta},
\qquad \operatorname{Re}\zeta>0.
\tag{12a}
\]
For every compact \(Q\Subset\Omega\), put
\(\delta_Q=\min_{z\in Q}\operatorname{Re}(e^{2z})>0\).  The expansion gives
\[
\left|r(e^{2z}t)\right|
\leq C_Q(1+t)e^{-\pi\delta_Qt},
\qquad z\in Q,\quad t\geq1.
\tag{12b}
\]
Together with (3) and (8), (12b) gives a compact-uniform integrable
majorant for (12), so \(K_2\) is jointly holomorphic on
\(\Omega\times\Omega\).  On real \(x,y<0\), it is real symmetric and finite.
The denominator \(r(t)\) in (12) stays on the positive real axis; no complex
zero is divided out.

The accepted analytic propagation lemma
docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md,
SHA256
fb83c216aef4687425074732904f9d2f52aac77527a926e7556fb0067335e2bd,
applies to (12) on \(J=(-\infty,0)\).  If every finite complex matrix
\([K_2(x_i,x_j)]\) were positive semidefinite for all \(x_i\in I\), the lemma
would propagate that property to every finite family in \(J\).  Equation
(10)--(11) contradicts it on a one-node family at sufficiently negative
\(x\).  Therefore there exists a finite complex row
\[
x_1,\ldots,x_N\in I,\qquad c\in\mathbb C^N,
\qquad c^* [K_2(x_i,x_j)]_{ij}c<0.
\tag{13}
\]
This is the requested all-row sign obstruction on the original interval.
The argument does not supply a rank bound or a two-node witness inside \(I\);
it only proves that the proposed universal positive-block rule cannot hold
there.

Finally, (13) concerns the first two signed telescope increments only.
It is not a negative witness for the terminal \(V\): later increments may
compensate it, exactly as the source response warns after equations
(41)--(43).  Conversely, a positive diagonal or determinant check for a
particular pair would not establish the all-row rule.  No numerical sweep,
convergence-to-sign argument, or new unproved compensation condition is used.
