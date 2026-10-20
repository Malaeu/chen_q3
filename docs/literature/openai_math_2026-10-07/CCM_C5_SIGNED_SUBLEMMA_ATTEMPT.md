# C5 signed attempt: isolate the unweighted composite core

2026-10-20. Bounded PAPER attempt using the weighted-LCM fee. The exact
weighted-to-signed transfer stalls at the surviving prime sum. C5 remains
OPEN; this is not a counterexample or a status change.

## Fixed source and target

Keep the original source \(N=m\), \(L=\log m\), \(M=\lfloor m^\alpha\rfloor\),
\(R=\lfloor m^\beta\rfloor\), and the same three-constraint sparse-band
projection \(P=P_{m,\alpha}\). For \(2\le n\le m\), put

\[
 H_n=\frac{P Q_M(\log n)P}{\sqrt n},\qquad \|H_n\|\le 2n^{-1/2}.
\]

Thus the target is still the actual composite matrix
\[
 C_{\rm comp}=\sum_{R<n\le m,\ n\ {\text{composite}}} b_R(n)H_n,
\]
with the coefficients and all mixed entries from the source. Proper prime
powers remain among the composites; Pi below is prime-only, not Mangoldt. The exact C5
interface is: for some absolute finite \(c>0\), for every sufficiently small
fixed \(\alpha,\beta>0\),
\[
 \lambda_{\min}(C_{\rm comp})\ge
 -C_{\alpha,\beta}m^{c(\alpha+\beta)}
\]
for all sufficiently large integer \(m\). The parameters are fixed before
\(m\) grows.

I tested the simpler-coefficient, unweighted l=1 core
\[
 B_{m,\alpha,\beta}=
 \sum_{R<n\le m,\ n\ {\text{composite}}}(\log n)H_n.
\]
A bound \(\lambda_{\min}(B_{m,\alpha,\beta})\ge
-C_{\alpha,\beta}m^{c_B(\alpha+\beta)}\), with absolute \(c_B\), would
imply C5 after the paid comparison below. It is a concrete signed estimate,
not an assertion that removing the Selberg weights solves the problem.

## Exact comparison and what W5 pays

Use the exact Q08 expansion \(b_R(n)=\log n\sum_{\ell\mid n}g_R(\ell)\),
\(\sum_\ell g_R(\ell)/\ell=1/C_R\), and the new W1 bound
\(\sum_\ell |g_R(\ell)|/\sqrt\ell\le324R(1+\log R)^2\). Here
\(g_R(1)=u_R(1)^2=1\), and \(b_R(p)=\log p\) for every prime \(p>R\).
Consequently, for \(n>R\), \(b_R(n)-\log n=0\) on primes and is supported
only on composites. Set
\[
 D_{\rm all}=\sum_{2\le n\le m}(b_R(n)-\log n)H_n,\quad
 D_{\rm small}=\sum_{2\le n\le R}(b_R(n)-\log n)H_n.
\]
Then exactly
\[
 C_{\rm comp}=B_{m,\alpha,\beta}+D_{\rm all}-D_{\rm small}.
\]

The W5 source-preserving Abel return and the ordinary l=1 Abel return give
\[
 \sum_{2\le n\le m}b_R(n)H_n=PJP/C_R+E_R,\qquad
 \sum_{2\le n\le m}(\log n)H_n=PJP+E_0,
\]
where \(\|J\|\le8\),
\[
 \|E_R\|\le3888R(1+D_M)(1+\log R)^2(1+2\log R),\quad
 \|E_0\|\le8+4D_M,\quad D_M=(2+8\pi M)/L.
\]
It follows that
\[
 C_{\rm comp}=B_{m,\alpha,\beta}+(C_R^{-1}-1)PJP+E_R-E_0-D_{\rm small}.
\]
The accepted Q08 pointwise bound \(b_R(n)\le\log n\,\tau_9(n)\) pays
\[
 \|D_{\rm small}\|\le
 2\sum_{2\le n\le R}\frac{b_R(n)+\log n}{\sqrt n}
 =O(\sqrt R(1+\log R)^9).
\]
Since \(C_R\ge1\), these estimates yield
\[
 \|C_{\rm comp}-B_{m,\alpha,\beta}\|
 =O_{\alpha,\beta}\!\left(m^{\alpha+\beta}L^2
 +m^\alpha/L+ m^{\beta/2}L^9+1\right).
\]
The l>1 return is therefore paid at the new weighted-LCM cost. This
two-sided norm comparison works in both directions: the parameter-proportional
lower-bound families for B and C_comp are equivalent after enlarging their
absolute exponent constants. It simplifies coefficients, not logical difficulty. For the
sparse receiver, after fixing a hypothetical off-critical exponent
\(\delta>0\), a bound for \(B\) with exponent \(c_B(\alpha+\beta)\) would
leave all costs below the signal by choosing fixed parameters with
\[
 \max\{\alpha+\beta,\ c_B(\alpha+\beta),\ \beta/2\}<\delta.
\]
The original receiver and full source are unchanged; this does not assert the
full-SP floor \(M=m\). The new fee replaces the older larger quadrature price.

## Attempt on the signed core and exact failure

Write the unweighted composite core as all integers minus primes:
\[
 B_{m,\alpha,\beta}
 =\sum_{R<n\le m}(\log n)H_n
   -\Pi_{m,\alpha,\beta},\qquad
 \Pi_{m,\alpha,\beta}=\sum_{R<p\le m}(\log p)H_p.
\]
Applying the l=1 Abel bound and paying the initial segment gives
\[
 \sum_{R<n\le m}(\log n)H_n=PJP+E_0-S_{\le R},\qquad
 \|S_{\le R}\|\le2\sum_{2\le n\le R}\frac{\log n}{\sqrt n}
 =O(\sqrt R\log R).
\]
Thus the attempted lower bound is reduced to the actual prime-only operator:
\[
 \lambda_{\min}(B_{m,\alpha,\beta})
 \ge -\lambda_{\max}(\Pi_{m,\alpha,\beta})
      -8-\|E_0\|-\|S_{\le R}\|.
\]
The coefficient-aware estimate available from \(\|Q_M(s)\|\le2\) is only
\[
 \lambda_{\max}(\Pi_{m,\alpha,\beta})
 \le\|\Pi_{m,\alpha,\beta}\|
 \le2\sum_{p\le m}\frac{\log p}{\sqrt p}
 \le2\sum_{n\le m}\frac{\log n}{\sqrt n}
 =O(\sqrt m\log m).
\]
This cannot give \(m^{c_B(\alpha+\beta)}\) for all sufficiently small fixed
\(\alpha,\beta\), for any fixed \(c_B\). No estimate using cancellation in
the actual prime coefficients was obtained. In particular W1/W5 cannot
attenuate this term: \(g_R(1)=1\), and for a prime \(p>R\), no supported
\(\ell>1\) divides \(p\). The prime deletion is exactly the l=1 term with
coefficient one.

This is a method failure, not a refutation of the sublemma or C5. It does not
reuse the earlier Q08(43) positive/negative-frequency candidate as if that
candidate were proved, and it does not use the fixed-prime Gram defect as a
sign estimate. The separate Q10 representation supplies no new signed estimate here; its
conditional fixed-exponent bound is not substituted for the required bound.

## Provenance and disposition

Read locally: `CCM_COMPOSITE_SIGN_TARGET.md`,
`CCM_FIXED_PRIME_COMPRESSION_TEST.md`, `CCM_WEIGHTED_LCM_RETURN_CONCLUSION.md`,
`CCM_FULL_RAMANUJAN_RETURN.md`, `CCM_MOMENT_Q08_CONCLUSION.md`,
`CCM_SPARSE_BAND_RECEIVER.md`, and the Q10 conclusion, actual-prime-boundary,
and weighted-scale-window reports. The Q10 material was used only to keep its
operator and boundary mechanism separate from this CCM source.

The bounded `ask.sh --defer-external` query returned `ASK_STATUS: INCOMPLETE`
because q3_docs search failed; returned local hits did not supply this signed
estimate. `supplier_preflight.py --query` also returned `INCOMPLETE` because
the configured external Lean registry could not load PyYAML. Neither result
establishes absence. No external or paid search, Lean build, or status update
was made.

Independent read-only mathematical review found no material defects in this
comparison or its stated failure. This is a PAPER audit, not Lean certification.

AUTOPSY: dropped=THEOREM_SHAPE; note=W5 pays the l>1 weighted return, but the exact l=1 prime deletion has no established parameter-proportional signed bound; C5 and the unweighted-core sublemma remain OPEN.
