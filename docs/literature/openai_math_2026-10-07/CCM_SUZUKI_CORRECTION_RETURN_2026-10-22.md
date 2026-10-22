# Suzuki correction: source repair and return to original CCM

Date: 2026-10-22. Status: BOUNDED_PAPER_AUDIT; RH OPEN; no exponent gain.
Source checkout: rh_clean, 943e0fc15e37b171dcc88d6ac99a877472b8acac.
Owner supplied a draft/transcript and requested the actual mathematical consequences.
The underlying author email was read directly in Gmail (dated 2026-09-06),
not inferred from the draft. No email was sent. Private headers are omitted.

## Sources and scope

- Suzuki, arXiv:2301.00421v3, https://arxiv.org/abs/2301.00421v3 .
  Local PDF: `docs/routeB_bus/litreview/pdfs/2301.00421.pdf`, SHA256
  `e4100e529d74cdc4dfa855aa24bcf34a88562d9facebefd70de6e529f9a1ce2e`.
  PDF pp.3,7 visually inspected; relevant subsequent sections read as extracted text.
- Author correction: (3.2) is to define P_t for all real t;
  negative times use P_{-t}(z)=overline{P_t(bar z)} for t>0;
  prefactor i in (1.5) is replaced by -i.
- September parent audit:
  `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SECOND_EXPRESSION_SUZUKI_KERNEL_IDENTITY_2026-09-06.md`, §§3,4,8.
- Further September calculation, not to be rediscovered:
  `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_OPEN_SIGNED_TIME_KERNEL_IDENTITY_2026-09-06.md`, §§4–5, (24)–(31).
- Existing independent algebra review:
  `docs/routeB_bus/AGENT_REPORT_2026-09-06_SECONDEXPR_B_INDEPENDENT_CHECK.md`.
  Its bounded algebra review is not a new certification of all convergence arguments.
- Current consumer: `CCM_SPARSE_BAND_RECEIVER.md`; source definition:
  `paper_weil/sections/setup.tex`.

## 1. The author's continuation equals the proposed signed repair

Let X(z)=xi(1/2-iz). Its zero multiset Gamma is invariant, with multiplicities,
under gamma -> -gamma and gamma -> bar gamma, without RH. For fixed real t,

    P_t(z) = sum_gamma m_gamma (exp(-i gamma t)-1)/(gamma(z-gamma)).

The series is absolutely locally uniformly convergent off Gamma: |Im gamma|<1/2
and sum m_gamma/|gamma|²<infinity control its tail. Reindexing first by -gamma
and then by bar gamma proves the meromorphic identities

    P_{-t}(z) = P_t(-z) = overline{P_t(bar z)}.

Thus the suggestion that Suzuki rejected our reflection continuation is incorrect.
His rule confirms the signed-time repair of September §8. That document's phrase
“not an author-confirmed correction” is historical and is superseded here.
This does NOT identify the correction with the printed even-time rule.

## 2. What changes, and what does not

With the corrected signed P held fixed, i -> -i multiplies every S_t and its
linear integral transform by -1. Squared norms and Gram pairings are unchanged.
Linear expansions must be made phase-consistent. The combined negative-time
repair is NOT merely a global sign change relative to the old EVEN object:
its mixed positive/negative-time products change.

The constant c_A does not come from this prefactor. From the Weil explicit
formula (3.3), with a(t)=exp(t/2)/(exp(t)-exp(-t)),

    integral_0^infinity a(t)(1-exp(-t/2)) dt = (log 2)/2 + pi/4,
    c_A = gamma_E + log(4pi) + 2 integral = gamma_E + log(8pi) + pi/2
        = log pi - digamma(1/4).

The active setup.tex also checks this independently via the digamma multiplier.
Its direct form and the sparse receiver's

    P K_m P = P(A_arch - c_A I - A_prime)P

have no dependence on the S_t phase convention. Every prime power, original
frequency and mixed coefficient remains. This is a bounded dependency audit of
the named files, not an assertion about every historical Suzuki consumer.

Theorem 1.4 remains an RH-equivalent norm identity, not an unconditional proof
of it. The correction repairs a definition; it does not supply the identity.

## 3. The actual shelf already goes beyond the repair

The September OPENSGN note evaluates both signed time integrations and reduces
the full corrected Gram identity to the still-unproved Poisson identity

    (1/pi) integral_R p X(x)^2 / ((p²+x²)(X(x)^2+X'(x)^2)) dx
      = xi(1/2+p)/(xi(1/2+p)+xi'(1/2+p)),  p>1/2.

This is the shelf's stated equivalence, not an independently re-proved theorem
in this audit. Its explicit defects r_p and h_pq determine both Laplace sign
quadrants. Boundary values alone do not justify the required reconstruction:
possible half-plane poles/non-Poisson terms cannot be discarded.
Therefore asking Pro merely to correct time, recompute the same kernel, or
rename this integral would repeat work already recorded in September.

## 4. Concrete original-P budget test

Use the September continuous kernels K_N (corrected norm Gram) and K_A
(arithmetic anchored kernel). Define D=K_N-K_A, and
mathfrak R=partial_t partial_u D, with THIS sign convention. For compact tests,

    Q(psi) = (1/pi)||P_hat_{D psi}||² - mathfrak R[psi tensor bar psi].

Complex conjugation may be placed in the other tensor factor by the real
symmetric kernel convention. The entire tensor is retained; it includes every
mixed Fourier coefficient. A sufficient original-P supplier is an UPPER bound

    mathfrak R[psi tensor bar psi]
      <= C_epsilon m^{eta(epsilon)} ||psi||², eta(epsilon)->0,

on the centered images of the original constrained sparse space. No full
identity on all tests is required for this sufficient receiver. This is an
UNPROVED supplier, not evidence that this representation makes it easier.

Check the existing absolute budget before choosing it as a route. Put L=log m,
T0=L/2, M=floor(m^epsilon), Omega_M=2pi M/L, and center the original zero-endpoint
f on [-L/2,L/2]. September (31) gives

    |mathfrak R[zeta]| <= [N(T0)^2/pi + 4G(2T0)] ||partial_t partial_u zeta||_1.

The explicit g' bound gives G(L)<=C(1+L)exp(L/2) and
N(L/2)^2<=C(1+L)^2 exp(L/2). Further,

    ||partial_t partial_u (psi tensor bar psi)||_1
       = ||psi'||_1² <= L ||psi'||_2² <= L Omega_M² ||psi||_2².

Consequently, for L>=1, the available bound returns only

    |mathfrak R[psi tensor bar psi]| <= C sqrt(m) M² L ||psi||².

Its exponent is 1/2+2epsilon, up to logarithms, and does not tend to zero.
This is a weak upper estimate, NOT a lower bound on the true defect and NOT
an impossibility theorem for the corrected representation.

The endpoint-zero condition matters: zero extension lies in H_0^1, with no
boundary jump in its first weak derivative. The continuous primitive D defines
the tensor pairing by integration against psi'(t)bar psi'(u). Smooth compact
approximations converge in H_0^1; the bounded Bochner construction and anchored
arithmetic kernel give the same extension. Approximation is only for the
identity/domain extension, not a replacement of the original P or its three
constraints. No extra Fourier modes are inserted into the claimed estimate.

## 5. Research decision and concrete next question

Q11 remains audited with no exponent gain. The new radial-energy test
`CCM_Q12_RADIAL_ENERGY_TEST.md` excludes the radial-energy plus absolute-defect
certificate on original P, not the source. Both results motivate a rollback
before absolute values. The corrected Suzuki object is a legitimate candidate
for that rollback, but the crude budget above fails immediately.

Question for Pro, after supplying the September OPENSGN source and this audit:

> Can the explicit signed Gram defect, compressed to the ORIGINAL three-condition
> P with N=m, L=log m and fixed M=floor(m^epsilon), be bounded above with an
> exponent eta(epsilon)->0 without first proving the full Poisson identity?
> Start with the already computed r_p/h_pq defect, preserve both time quadrants
> and all mixed terms, and exhibit a quantitative mechanism plus the full inverse
> transform/window return. The existing absolute return costs sqrt(m)M²log m.
> If projection supplies no gain, locate the exact unpaid signed term and give
> a bounded discriminator; do not repeat the September identity as new progress.

This is a prepared question, NOT a sent request or a claim that a mechanism exists.
The earlier phase-preserving Q12 attachment is held unsent and must not be sent
unchanged after this steering. No author correspondence was sent or copied into
an external research request. No Lean, Arb or numerical proof run occurred.

Validation: root source/math checks plus independent read-only correction and
active-dependency audits; the quantified return is separately checked below.

Independent bounded return review: PASS (suzuki_correction_math). The sign,
sqrt(m)M²L scale, and H_0^1 extension check out. The proposed improved bound must
hold for EVERY vector of original P; it would give its restricted floor, not a
full-carrier floor. Neither root nor reviewer claims a fresh audit/proof of the
entire September Poisson equivalence. No files were changed by reviewers.
