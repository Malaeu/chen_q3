# Reciprocal-transform hunt: verified results and rejected source claims

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; ACCEPT_SCOPED_REJECTED_SOURCE_CLAIMS_AND_RH_STRENGTH_FILTER_ONLY.
Base 55c475d55de2c8921c1d9cd142d58a3b69cae2b1. Isolated research only.
The exact target remains the original full V on all finite complex families.
No applicable source-to-sign transfer emerged from this bounded hunt.

## H1. Exact interface, independently checked
For q=Phi/integral Phi, F(z)=xi(1/2+iz)/xi(1/2), the proposed dual is
H(t)=1/F(it)=xi(1/2)/xi(1/2+t). The correct positive-measure candidate uses
E(u)=xi(1/2+sqrt(u))/xi(1/2), an entire function by evenness.
The already reviewed VANDANTZIG_DUAL_FILTER establishes:
- The accepted negative-V control g0=exp(-x^2)-exp(-2x^2)/4 has a dual H0
  which is a Gaussian mixture and infinitely divisible. Its psi0' is
  completely monotone but not Stieltjes. None of those weaker positive-law
  properties automatically pays V.
- A positive Stieltjes representation of actual E'/E is RH-strength, not
  supplied by the known Thorin atoms 2 sum delta_(pi*n^2) of the additive r.
This remains a selected interface for the hunt, not a unique possible route.

## H2. The 2018 GGC paper: independently rejected continuation
Polson, Riemann Hypothesis: a GGC factorisation,
https://arxiv.org/pdf/1806.07964v7 (header 15 October 2018).
PDF SHA256 e4350036340ec9d6fdd5bb2d4e8ee23514a2764f30f5bd658f21dcf4def13214.
Parent read: full six-page text, printed p5 visual check.
The already published POLSON_GGC_CONTINUATION_AUDIT proves that equation38
at alpha2,s0 gives RHS<1 whereas actual xi2/xi(.5)>1. The principal branch
under q=w^2/2 changes on the left half-plane. This is an independently
accepted contradiction to the displayed transfer, not a rejection of RH.

## H3. The revised Wald/Thorin paper: do not import the theorem wholesale
Polson, Riemann, Thorin, van Dantzig Pairs, Wald Couples and Hadamard
Factorisation, https://arxiv.org/pdf/1804.10043v8.
PDF header 29 April 2026; internal date 1 May 2026.
PDF SHA256 aba173364e7df5f849789caf674fd14f17ac91306df79d7cab8200955d3f52df.
Text SHA256 295ba14216d62c1f99d411383587fd08ddedc5f7196f35c389c178e0e90da1dd.
Parent read: printed pp4-5 Theorem14, pp12-13 Theorem23 and Lemma24;
printed p12 visually checked. No whole-paper certification is asserted.

Theorem14(a)-(b) has the familiar zero/GGC equivalence for a real even
entire function of order at most one, centered at alpha with f(alpha)>0
and square-summable reciprocal zero moduli. For f=xi, alpha=1/2, it
requires the unproved central GGC condition; it does not derive it from r.

But Theorem14(ii) further claims that f(alpha+it)/f(alpha) is a
characteristic function of an infinitely divisible law under those
hypotheses. Its wording includes "is the characteristic function of an
infinitely divisible" (printed p5). This clause is false as stated:
f(w)=1+w^2, alpha=0 satisfies the stated entire-order, symmetry and zero
conditions (zeros +/-i, sum of reciprocal squared moduli=2), but
f(it)=1-t^2 has value -3 at t=2. A characteristic function has modulus
at most 1. Thus the whole named theorem and its asserted pair consequences
cannot be imported as an unconditional supplier. The valid zero/GGC
interface is separately justified in our accepted filter.

Theorem23, printed p12, proposes the shifted GGC identity
 xi(3/2)/xi(1/2+sqrt(1+s))=E exp(-sH_star), s>0.
Its proof contains the following false algebraic identity (equation30):
 e^(-sigma*t)=e^(-(y-1)*2t/(y+1))*e^(-(y^2-1)*t),
 y=sqrt(1+sigma)>1.
Since sigma=y^2-1, the right side is the left side times
exp(-2t(y-1)/(y+1))<1 for t>0. This is a direct falsifier of the proof as
written. It does not, by itself, prove the proposed GGC identity false.

## H4. The shifted auxiliary GGC condition already has RH strength
This observation avoids adding an unnecessary later continuation problem.
Let D(z)=E(1+z)/E(1), entire with D(0)=1. If the GGC identity in Theorem23
were independently established on real z>0, its GGC Laplace transform L(z)
would be holomorphic on Omega=C minus (-infinity,0]. The identity
D(z)L(z)=1, first valid on the positive axis, would hold throughout Omega.
Hence D has no zeros there. Every E zero would lie in (-infinity,1].
But E(u)>0 for u>=0 by the exact positive theta moment integral, so all
E zeros would be negative real. This implies RH by the exact xi/E map.
Conversely, RH and the symmetric Hadamard product give
 E(1)/E(1+z)=product_(gamma>0)(1+z/(1+gamma^2))^(-1),
a GGC Laplace transform. Thus this shifted representation is already
RH-equivalent; it is not a cheaper theorem supplied by the right-half-plane
Euler product. No Ramanujan-master-theorem step is needed for this implication.

## H5. Corrections to the raw researcher card
Raw card SHA256 23e0c8fc62406f6463bb004fbc8191f8a4dd53b4006f32904d3fb42583db6259;
manifest SHA256 6bb604379387ab686eb0125183d815c77985a7c13ff0818074c2fe5b6315933b.
The raw card is provenance, not accepted as written. Parent corrections:
1. Theorem14(ii) is false, not a valid automatic corollary of14(a)-(b).
2. Do not label Lemma24's holomorphy implication inherently circular:
   a valid GGC identity would indeed permit the entire-denominator identity
   theorem argument in H4. Also Re(z)>=0 gives Re(sqrt(1+z))>=1, so the
   xi argument has real part at least3/2 and its zero-freeness there is
   already unconditional by the Euler product. The quoted real-asymptotic
   argument is not a complete audit of its stronger uniform growth claim.
3. A negative substituted zeta increment with alpha2 is not itself fatal:
   alpha+increment remains >3/2 for sigma>0, inside absolute convergence.
   We do not retain that claimed domain failure as a falsifier.
4. Neither this selected interface nor either article exhausts other methods.

## H6. Retrieval and stopping condition
Brief SHA256 61a6ee0c846cba824e3acd7f06730fe96cdec787f71ad9b27a9a81d111f627dd.
Three new registered dictionaries were run once; all shelf receipts retain
INCOMPLETE due to semantic-index freshness. The corresponding KB exact-query
no-hits are not evidence of literature absence. The known mgrep credit403
was not retried. Two primary bodies were fetched within the fixed budget.
The source1 and source2 claims were checked against the full source and the
explicit negative control; neither supplies a usable sign theorem.
The already published two filter reports are independently accepted.
Full V sign and RH remain open; no new Proshka proof task or canonical
admission follows automatically from this completed discovery pass.

## Independent acceptance

Candidate SHA256: `5481cb4320ef269a2355a55e6a28391458cd1a9946f5f7772ef01d7cb77d50e5`.
Review SHA256: `5e9a11022f4096a29c784a9a4ca3d92a915791309f6526a2e1812dbd394b0311`.
Reviewer: `/root/sibling5_check`. Verdict: ACCEPT_SCOPED_REJECTED_SOURCE_CLAIMS_AND_RH_STRENGTH_FILTER_ONLY.
The parent read the complete review and checked the source statements,
counterexample and shifted-GGC equivalence. Only status and this receipt
were added after review. This is isolated research, not canonical or Lean
admission, a V sign proof, or an RH proof.
