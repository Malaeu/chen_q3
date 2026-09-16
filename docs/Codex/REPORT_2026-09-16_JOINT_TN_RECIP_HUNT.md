# Joint total positivity and reciprocity: bounded mechanism-hunt intake

Date: 2026-09-16. Base: `a7a67d3853b80dadf20c1a15fa759b35f98e9c74`.
STATUS: INDEPENDENTLY_ACCEPTED_BOUNDED_HUNT; NO_NEW_SIGN_SUPPLIER.
Scope: isolated analytic research; no canonical admission or Lean claim.

## 1. Exact question and preserved return point

For the full source

\[
r(t)=\sum_{n\ge1}(4\pi^2 n^4t-6\pi n^2)e^{-\pi n^2t},\qquad
\mathcal Lr(z)=\left(\frac{\sqrt{\pi z}}{\sinh\sqrt{\pi z}}\right)^2,
\]

the already proved additive TN-infinity property of `r`, extended by zero
on the negative half-line, coexists with the exact identity
`r(1/t)=t^(5/2)r(t)`. The question was whether a published theorem uses these
two properties together to control

\[
M(s)=\int_0^\infty t^{s-1}r(t)\,dt=2\xi(2s-2)
\]

or the original full kernel
`V(x,y)=integral_0^infinity (2X+x+y) f(X+x) f(X+y) dX`,
`Phi(X)=exp(5X/2)r(exp(2X))`, `f=Phi/||Phi||_2`,
for every finite complex family in `I=(-log(2)/2,0)`.

**Result of this bounded hunt:** one primary body was verified, but no new
applicable sign supplier emerged. The theorem returned is a reused
Schoenberg mechanism. The tempting log-PF premise is already refuted,
not merely awaiting proof. A related fractional-pole argument is useful
as a diagnostic, not as a positive representation of `V`.

## 2. Source theorem and exact mapping

Belton, Guillot, Khare and Putinar, *Totally positive kernels, Polya frequency
functions, and their transforms*,
[arXiv:2006.16213v5](https://arxiv.org/pdf/2006.16213v5), 7 December 2021.
Verified PDF SHA256:
`5269524e7ad674f1484655c860f360caad5819c4dfa8658c5e0f4c28cc656259`.
Text extract SHA256:
`5488fef6d2a80eeba6703143df362f56f2175a3acd675e5313493679dcdce867`.
Read scope: printed pp.37-38, Definition 8.1 and Theorem 8.2; pp.40-41,
end of Lemma 8.4 and Theorem 8.5 proof. Printed p.41 was also visually checked.

Theorem 8.2 concerns the **reciprocal of the bilateral Laplace transform**
of an integrable PF function. Its stated entire-function description,
up to an exponential factor, includes the words (p.38):
> the restriction of an entire function of genus zero or one, with purely real zeros.

For `Lambda_0(u)=r(u)1_(u>0)`, this applies to the ordinary additive Laplace
transform above. The reciprocal is the entire function
`(sinh(sqrt(pi*z))/sqrt(pi*z))^2`, with zeros at `-pi*n^2`.
This does not locate zeros of the Mellin transform `M`.

For `Lambda_5(u)=exp(5u/4)r(exp(u))=Phi(u/2)`, direct substitution gives
`B{Lambda_5}(z)=M(5/4-z)`. Reciprocity makes `Lambda_5` even. The input
additive TN property belongs to `r(x-y)`, however, not to
`Lambda_5(x-y)`. The theorem does not supply this nonlinear transfer.

The sharper obstruction is already in
[RH_ROUTE_AUDIT, section 4.1](REPORT_2026-09-15_RH_ROUTE_AUDIT.md):
`q=Phi/integral(Phi)` is **not** PF-infinity. Its bilateral Laplace transform
is entire by the full double-exponential tails. If it were PF-infinity,
Schoenberg would supply an entire Laguerre--Polya reciprocal `Psi`; the
identity `Bq*Psi=1` would make `Psi` zero-free. The precise product form
used here is from Groechenig,
[arXiv:2007.12889v1](https://arxiv.org/pdf/2007.12889v1), Theorem 1(i),
printed p.2, together with the displayed Laguerre--Polya representation.
It reduces the zero-free `Psi` to `C exp(-gamma*z^2+delta*z)`.
Evenness and positive variance force a nondegenerate Gaussian `q`,
contradicting the source tail. Positive dilation transfers this obstruction
to `Lambda_5`. Thus this direct log-PF route is **REUSED / INAPPLICABLE**.

Groechenig PDF, already on the shelf and reread pp.1-3:
`docs/routeB_bus/litreview/pdfs/2007.12889.pdf`, SHA256
`e610f7a0de324a610fd24ee9fafa4356e5005a9af811245f016d6c0d791ed3a2`.
This precise Gaussian-product attribution corrects an imprecision in the
researcher's V2 card; it is not attributed solely to BGKP Theorem 8.2.

## 3. Verified diagnostic analogue, with the operations kept distinct

BGKP Theorem 8.5 classifies scalar maps preserving every PF function under
post-composition. In its proof, printed p.41, the test
`phi(x)=x*exp(-x)1_(x>0)` and the post-composition `F(t)=t^b` yield a
Laplace transform `Gamma(b+1)/(s+b)^(b+1)`. Entire continuation of its
reciprocal forces the exponent `b` to be an integer (in the proof's range).
**This only excludes noninteger powers.** Lemma 8.4 supplies the additional
exclusion of integer powers greater than one, leading to the linear
universal-preserver conclusion. Integer restriction alone does not do so.

This is a published example of detecting loss of total positivity through
a fractional boundary singularity. It acts on `F composed with phi`;
our power tilt multiplies a fixed source by `t^beta`. These are different
operations, so the published preserver theorem is not a direct theorem
about our tilted law.

For our actual source the independent calculation has already been
published in [CRITICAL_TILT_TN4](REPORT_2026-09-16_CRITICAL_TILT_TN4.md),
commit `a7a67d3853b80dadf20c1a15fa759b35f98e9c74`. For every `0<beta<1`,
`k_beta=t^beta*r/E(T^beta)` has a negative ordered additive 4-by-4 minor.
This includes the exact xi-centered probability law `beta=1/4` and the
inverted law `beta=1/2`. The source-level full-tail and finite-minor proof
remains necessary; the literature analogy does not replace it.

## 4. Retrieval and correction record

Saved brief SHA256:
`b39a458e19614210c9d811462e0b730e0450b39ed4535c5604f69f92082c9765`.
Three registered queries were each run once:

1. `Polya frequency Mellin transform weighted inversion`
2. `self reciprocal generalized gamma convolution size bias zeros`
3. `Schoenberg variation diminution logarithmic change theta`

All three shelf receipts are **INCOMPLETE due to index freshness**.
The corresponding lexical KB queries returned no hits for their exact
strings; this does not repair the semantic-index status or prove absence.
One `mgrep --web` attempt failed with HTTP 403 / depleted credits. No paid
retry or index refresh was made. A Schoenberg scan fetch and a separate
BGKP publisher fetch returned HTML instead of PDFs; neither was used as a
verified body. The actual arXiv v5 PDF above is the new verified body.
Existing Groechenig shelf evidence was reused, not counted as a new lead.

Raw researcher card SHA256:
`21201c27b50c79227ab1a8e14a2c7834cadd28857c27514f7840a4f77e080d16`.
The parent rejected its treatment of log-PF as a merely unpaid supplier.
Corrected V2 SHA256:
`75c6ec640b856077c5ca4cf019537ba84fa8597c0026b81649d60a4650982a6b`.
This intake additionally fixes the two source-attribution points in
sections 2-3. Raw cards are provenance, not independently accepted claims.
Machine-readable publication evidence retains all query receipt hashes.

## 5. What remains open, and what the next candidate must do

The **proposed implication** from the already true joint properties of the
unweighted source (additive TN-infinity plus reciprocity) to the required
Mellin/full-`V` conclusion remains open. The premises themselves are known;
neither this hunt nor the negative tilted minor refutes their conjunction.

No new Proshka request is justified merely by renaming the refuted
log-PF or tilted-PF intermediary. A useful next candidate must specify a
different source property, its exact image after the critical tilt and
logarithmic pushforward, and a theorem that reaches the original all-family
consumer. Raw finite EDGE, log-PF, and critical-tilt TN-infinity are rejected
intermediaries; none of these failures is a negative original-`V` witness.

Full `V>=0`, the unresolved joint implication, and RH remain open.
This is a completed bounded hunt and a source-mapping filter, not a
proof that no applicable theorem or different representation exists.

## Independent acceptance

Candidate SHA256: `ca20cc547fe71adf9e4554c5a6ebfe1a1517b74456256b34f3ea0863f74adc23`.
Reviewer `/root/sibling5_check`; review SHA256: `fb5f9a550485b1efc1df76cb2a46aa562b7c21490f827167e1e2a5c061ae6285`.
Verdict: ACCEPT_SCOPED_SOURCE_CLASSIFICATION_AND_OPEN_JOINT_IMPLICATION_ONLY.
The parent read the cited theorem and proof passages, checked the source
mappings and the corrected scope. Only status and this acceptance receipt
were added after independent review.
