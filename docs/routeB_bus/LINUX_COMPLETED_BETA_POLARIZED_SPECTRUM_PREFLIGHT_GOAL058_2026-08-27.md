---
TASK_ID: GOAL058_SELECTED_FERRERS_COMPLETED_BETA_POLARIZED_SPECTRUM_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
RESPONDS_TO: 3f4c23eb
DISCRIMINATOR: HOLD
RESULT_CODE: COMPLETED_SPECTRAL_IDENTITY_WITHOUT_SOURCE_LOCALIZATION_RATE
LEAN_EDIT: false
NUMERICS: none
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - COMPLETED_BETA_HAS_NO_SINGLE_SPECTRAL_REPRESENTATION
  - ARCHIMEDEAN_TERM_MUST_BE_ESTIMATED_SEPARATELY_FROM_THE_PRIME_SUM
  - CONSUMER_SIDE_NEEDS_A_SEPARATE_FOURIER_TRANSFORM_OBJECT
OPENS:
  - COMPLETED_SPECTRAL_TEST_FUNCTION_REGULARITY_ON_THE_ANGLE_VARIABLE
---

# Completed-beta polarized spectrum: one measure, one test function, one integral

## 0. Result

The exact identity closes, and it closes better than the request asked for: the
three ledgers `W02`, `Arch`, `Prime` are not three objects to be summed, they are
three parts of **one** spectral measure on a single angle variable, and the
consumer meets that measure through **one** explicit test function. No component
norm split occurs anywhere.

The rate does not follow. What blocks it is now a single named property of a
single function of one real variable. Discriminator: HOLD, exactly as the judge's
`P_COMPLETED_SPECTRUM_1` predicted.

## 1. Literal source lock

From `Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean` and
`CCMFiniteWeilSourceCommutator.lean`, read this session:

    ccmL m               = L = log m
    ccmQKernel L n j x   = (sin(2 pi j x / L) - sin(2 pi n x / L)) / (pi (n - j))        for n != j
                         = 2 (L - x)/L * cos(2 pi n x / L)                               for n = j
    ccmW02Entry L n j    = 32 L sinh^2(L/4) (L^2 - 16 pi^2 j n)
                             / ((L^2 + 16 pi^2 j^2)(L^2 + 16 pi^2 n^2))
    ccmPrimeEntryN1 m n j= sum_{k=2..m} Lambda(k) (sqrt k)^{-1} ccmQKernel L n j (log k)
    ccmWRIntegrand L n j x = (e^{x/2} ccmQKernel L n j x - ccmQKernel L n j 0)
                             / (e^x - e^{-x})
    ccmWREntry L n j     = ccmQKernel L n j 0 / 2 * (gamma + log(4 pi (e^L-1)/(e^L+1)))
                             + integral_{(0,L]} ccmWRIntegrand L n j x dx
    ccmWeilTauN1 m n j   = ccmW02Entry - ccmWREntry - ccmPrimeEntryN1
    ccmBetaScalar m n    = n * ccmWeilTauN1 m n 0
    ccmBetaFinite m N i  = (mode i) * ccmWeilMatFinite m N i (center)

Consumer objects, source-locked by the ground-graph decomposition and unchanged
here:

    q_k        selected Ferrers trial row
    a_k        Rayleigh shift
    M_k        literal source matrix on the carrier
    C_k        graph operator, banked as `trialGraphOperator`
    kappa_k(z) P59 pole kernel evaluation vector
    x_k(z)     = C_k^{-1} kappa_k(z), banked as `trialGraphOperator_inv_mulVec_residual`
    H          H_ij = (n_i - n_j)^{-1} for i != j, H_ii = 0, banked as
               `dividedDifferenceHilbert` in `G6N1SelectedFerrersHilbertPairing.lean`

Off-diagonal source law, banked complex form
`ccmWeilMatFinite_commutator_complex`:

    (n_i - n_j) (M_k)_ij = beta_i - beta_j          for i != j,

so the off-diagonal part of `M_k` is literally `[M_beta, H]`, and

    < x, (M_k - a_k I) q >  =  sum_i ((M_k)_ii - a_k) conj(x_i) q_i
                              + < x, [M_beta, H] q >.                        (1)

The diagonal channel is carried explicitly through everything below and is
never absorbed.

## 2. Exact mixed weight and its zero mass

Define, star-first, the polarized Hilbert weight

    omega_i(x,q) = conj(x_i) (H q)_i + conj((H x)_i) q_i.                     (2)

**Identity A (zero mass).** `sum_i omega_i(x,q) = 0`.

Proof. `H` is real and antisymmetric, so `conj((Hx)_i) = (H conj(x))_i`.
Expanding, `sum_i omega_i = sum_{i != j} conj(x_i) q_j H_ij
+ sum_{i != j} conj(x_j) q_i H_ij`. Swapping the names `i, j` in the second sum
turns it into `sum_{i != j} conj(x_i) q_j H_ji = - sum_{i != j} conj(x_i) q_j H_ij`.
The two cancel. QED.

**Identity B (polarized Loewner).** `< x, [M_beta, H] q > = sum_i beta_i omega_i(x,q)`.

Proof. `< x,[M_beta,H]q > = sum_{i != j} conj(x_i)(beta_i - beta_j) H_ij q_j`.
Split; the first half is `sum_i beta_i conj(x_i)(Hq)_i`; the second half is
`- sum_j beta_j (H^T conj(x))_j q_j = + sum_j beta_j (H conj(x))_j q_j`
`= sum_j beta_j conj((Hx)_j) q_j`. Add. QED.

Identity B is the polarized replacement for the quadratic identity of report
`c1e5f00f`, and it is exactly the object the judge specified.

## 3. The completed beta is a single spectral measure

Evaluate the source at the center, `j = 0`, `beta_0 = 0`, `n != 0`. Each ledger
is computed from the definitions above.

**W02.** `ccmW02Entry L n 0 = 32 L sinh^2(L/4) / (L^2 + 16 pi^2 n^2)`, so with
`a := L/(4 pi)`,

    beta^{W02}_n = n * that = (2 L sinh^2(L/4) / pi^2) * n / (a^2 + n^2).

Using `integral_0^infty e^{-a t} sin(n t) dt = n/(a^2+n^2)`:

    beta^{W02}_n = integral_{(0,infty)} sin(n t) dmu_{W02}(t),
    dmu_{W02}(t) = (2 L sinh^2(L/4) / pi^2) e^{- L t /(4 pi)} dt.             (3)

**Prime.** `ccmQKernel L n 0 (log k) = - sin(2 pi n log k / L) / (pi n)`, so the
explicit factor `n` in `ccmBetaScalar` cancels exactly:

    - n * ccmPrimeEntryN1 m n 0 = (1/pi) sum_{k=2..m} (Lambda(k)/sqrt k) sin(n theta_k),
    theta_k = 2 pi log k / L.                                                 (4)

Note the sign: the source gives `+ (1/pi)`. The parent verdict `ab96a4ba` wrote
`- (1/pi)` and the later synergy message wrote `+ (1/pi)`; the source settles it
as `+`. Flagged, not assumed.

**Archimedean.** `ccmQKernel L n 0 0 = 0` for `n != 0`, so the entire
Euler-Mascheroni prefactor of `ccmWREntry` drops out and the subtraction inside
`ccmWRIntegrand` is vacuous. With `e^x - e^{-x} = 2 sinh x`,

    - n * ccmWREntry L n 0 = (1/(2 pi)) integral_{(0,L]} e^{x/2} sin(2 pi n x / L) / sinh(x) dx. (5)

**The crosswalk.** Substituting `theta = 2 pi x / L` in (5) puts the archimedean
term on exactly the same angle axis as the prime atoms in (4). Therefore

    beta_n = integral_{(0,infty)} sin(n t) dmu_beta(t),                       (6)

    dmu_beta = dmu_{W02}                                        on (0, infty)
             + (1/pi) * push_{x -> 2 pi x / L} [ (1/2) e^{x/2} / sinh(x) dx
                                                 + sum_{2 <= k <= m} (Lambda(k)/sqrt k) delta_{log k} ]
                                                                on (0, 2 pi].

This is the object the route has been missing. The archimedean ledger is not a
second thing to estimate beside the prime sum: **it is the absolutely continuous
part of the same measure whose atoms are the prime powers**, on the same axis,
with the same map `x -> 2 pi x / L`. Componentwise splitting is not merely
forbidden here, it is unnatural: the parts are one measure.

## 4. The consumer meets it through one test function

Insert (6) into Identity B and exchange the finite sum with the integral:

    sum_i beta_i omega_i(x,q) = integral_{(0,infty)} G_{x,q}(t) dmu_beta(t),   (7)

    G_{x,q}(t) := sum_i omega_i(x,q) sin(n_i t) = < x, [ S_t , H ] q >,
    S_t := diag( sin(n_i t) ).                                                (8)

The commutator form in (8) follows from Identity B applied with `beta` replaced by
the vector `(sin(n_i t))_i`, which is legitimate because Identity B holds for any
real diagonal, not only for the source `beta`. Equivalently, with
`M_t := diag(e^{i n_i t})`, the Fourier transform of the weight is
`hat omega(t) = < x, [M_t, H] q >` and `G_{x,q} = (hat omega(t) - hat omega(-t))/(2i)`.
Star-first orientation is preserved throughout: `x` always enters conjugated.

Combining with (1), the **entire exact polarized consumer** is

    Psi_k(z) = sum_i ((M_k)_ii - a_k) conj(x_i) q_i
             + integral_{(0,infty)} < x_k(z), [ S_t , H ] q_k > dmu_beta(t).  (9)

One diagonal sum, one integral, one measure, one test function of one real
variable. This is the mandated `COMPLETED_BETA_POLARIZED_SPECTRAL_PAIRING`.

## 5. Endpoints are removable, and the top prime power contributes nothing

Both endpoints of the arithmetic band are exactly harmless, for structural
reasons rather than by estimate.

At `t = 0`: `S_0 = 0`, so `G(0) = 0`. This is Identity A seen at a point.
Moreover `G(t) = t * sum_i omega_i n_i + O(t^3)`, so `G` vanishes to first order.
The archimedean density behaves like `1/(2x)` as `x -> 0` because
`sinh x ~ x`; the first-order vanishing of `G` cancels it exactly, and the
integral in (9) converges at the origin with no principal value and no cutoff.

At `t = 2 pi`: the modes `n_i` are integers, so `S_{2 pi} = 0` and `G(2 pi) = 0`.
The angle `theta_k = 2 pi` corresponds to `log k = L`, that is `k = m`. Hence
**the largest prime power in the truncation contributes exactly zero** to the
consumer. The same mechanism identifies the conjugate collision noted by the
judge: `theta_{k_1} + theta_{k_2} = 2 pi` is exactly `k_1 k_2 = m`, and it is the
reflection `t -> 2 pi - t` of the test function that pairs those atoms.

## 6. Where the rate stops

Absolute majorization fails, and it fails for a reason worth recording, because
it shows the cancellation is not incidental.

Total masses, at `L = log m`:

- prime atoms: `sum_{k <= m} Lambda(k)/sqrt k ~ 2 sqrt m`;
- W02 continuous part: `(2 L sinh^2(L/4)/pi^2) * (4 pi / L) = 8 sinh^2(L/4)/pi ~ 2 sqrt m / pi`;
- archimedean continuous part: `O(1)`, since `e^{x/2}/(2 sinh x) ~ e^{-x/2}` for large `x`.

So the two large pieces are of the **same order** `sqrt m` and enter with the
same sign convention in (6). `|mu_beta|` has mass of order `sqrt m`, while the
downstream budget is `o(1/sqrt(log m))` on the axis. Any bound of the form
`|integral G dmu_beta| <= ||G||_infty * |mu_beta|` is therefore off by a power of
`m`, which is the same overshoot recorded at the eighth and ninth preflights.

The route survives only through cancellation *inside* the integral. And that
cancellation now has a name that does not mention our matrix at all: the measure
`mu_beta` is, by construction, the finite explicit formula, so it annihilates
smooth test functions to the accuracy of the unconditional prime-counting error.
Consequently the rate is controlled by **one** property:

    COMPLETED_SPECTRAL_TEST_FUNCTION_REGULARITY:
    the modulus of continuity of  t -> < x_k(z), [S_t, H] q_k >  on (0, 2 pi],
    uniformly along the selected schedule.

If that function is smooth on the scale at which `mu_beta` cancels, the pairing
inherits the cancellation and the wall is bypassed. If it oscillates on the
scale of the atom spacing near `t = 2 pi` — where the spacing is about twice the
window resolution, per report `6d647f05` — then the atoms are resolved
individually, no cancellation is available, and the wall is confirmed at the
level of the exact consumer.

I do not have that regularity, and no supplier in the catalogue provides it.

## 7. Supplier inventory for the exact left vector

Asked of the shelf this session for `x_k(z) = C_k^{-1} kappa_k(z)`:

- `trialGraphOperator`, `trialGraphOperator_posDef`,
  `trialGraphOperator_inverse_residual_identity`,
  `trialGraphOperator_inv_mulVec_residual`,
  `trialGraphOperator_inverse_residual_unique` — the inverse exists, is
  characterized, and the residual identity is kernel-green
  (`G6N1SelectedFerrersFiniteAssetBank.lean`, ratified `c998edbd`).
- `penalty_lower_envelope`, `penalty_quadratic_split`, `penalty_lower_envelope_gram`
  — two-metric envelopes and the Schur mechanism.
- `centering_factor_bound`, `proposition59PoleKernel_diagonal_resolvent`,
  `movedAction_entire_formula` — the `kappa` side.
- `SELECTED_FERRERS_CENTER_COEFFICIENT_INVERSE_LOG_FLOOR` and
  `SOURCE_SCALE_INVERSE_BOUNDED_AS_SEPARATE_INPUT` — the only quantitative
  handles the catalogue returns.

**Not supplied by anything in the catalogue:** any statement about the behaviour
of `x_k(z)` as a function on the *mode index*, which is what a modulus-of-continuity
statement for `G` requires. Every banked supplier bounds `x` in norm. The judge's
plant P1 says precisely that norm control does not give band localization, and I
confirm it applies to our entire banked inventory. This is the load-bearing hole,
and it is now a hole in one clearly named place instead of being spread over the
route.

## 8. Comparison with the earlier walls

- **Retained-prime oscillation wall** (`49c3b916`, corridor FATAL `a843c458`).
  That wall was reached by estimating a prime-side quantity against
  Korobov-Vinogradov. Representation (9) does not reproduce it: the prime atoms
  are never estimated apart from the continuous parts, so the sub-power versus
  power mismatch does not arise in this form. What replaces it is a regularity
  demand on the consumer side. That is a genuinely different demand, and it is
  the first time in this corridor the open question does not name primes.
- **Compact log-commutator wall.** There the object was an operator norm over all
  vectors. Here the pairing is fixed to the literal pair `(x_k(z), q_k)`, so the
  extra quantifier that inflated Track A is absent.
- **Dressed IIKS generator wall.** That route needed a dressing transform. None
  appears in (9); the identity chain uses only Identities A and B, the source
  evaluations of section 3, and Fubini on a finite sum against a finite measure.
- **Annihilator range obstruction** (`6d647f05`). Not reintroduced: nothing here
  asks the consumer weight to lie in the range of anything.

## 9. Mandatory plants

- **P1, norm does not give spectrum.** Accepted and confirmed against the
  inventory in section 7. No claim of band localization is made from any norm
  bound.
- **P2, zero mass does not give band decay.** Accepted. `G(0) = 0` is used only
  for convergence at the origin in section 5, never as control on `(pi, 2 pi)`.
- **P3, component split.** Structurally impossible in (6)-(9): `W02`, `Arch` and
  `Prime` are parts of one measure and are never separated. Section 6 quotes
  their individual masses only to prove that the absolute majorant fails, which
  is an argument *against* splitting, not a use of it.
- **P4, diagonal channel.** Carried explicitly as the first term of (1) and (9)
  and never determined by the Hilbert identity. It remains open under its own
  name, `LITERAL_CCM_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND`.
- **P5, exact ground sanity.** Passes by construction. Equations (1), (7) and (8)
  are algebraic identities, not estimates, so (9) equals `< x, (M_k - a_k I) q_k >`
  identically. If `q_k` is an exact eigenvector then `(M_k - a_k I) q_k = 0` and
  the right-hand side of (9) vanishes identically, both terms together. No
  intermediate quantity was bounded separately, which is exactly what the
  correction-2 test demands.

## 10. Verification handoff

Nothing in this report is Lean, numerical or Aristotle work. Everything is
paper, derived from the source definitions quoted in section 1 and from banked
kernel-green declarations named in section 7. Two items are Lean-formalizable
immediately if authorized, both finite and elementary: Identity A and Identity B
in the polarized complex form, which generalize the already-green
`hilbert_weight_total_mass_zero_complex` and
`loewner_form_eq_two_mul_hilbert_pairing_complex` from the quadratic to the
mixed case. No such edit was made.

## 11. Next load-bearing gap

    COMPLETED_SPECTRAL_TEST_FUNCTION_REGULARITY_ON_THE_ANGLE_VARIABLE

stated for the literal pair `(x_k(z) = C_k^{-1} kappa_k(z), q_k)`, on `(0, 2 pi]`,
uniformly along the selected schedule, with the diagonal channel carried
separately.
