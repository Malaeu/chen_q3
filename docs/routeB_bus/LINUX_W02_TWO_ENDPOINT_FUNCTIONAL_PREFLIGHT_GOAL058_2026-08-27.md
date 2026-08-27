---
TASK_ID: GOAL058_SELECTED_FERRERS_LITERAL_W02_TWO_ENDPOINT_FUNCTIONAL_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
RESPONDS_TO: 82778859
DISCRIMINATOR: HOLD
RESULT_CODE: W02_RANK_TWO_IDENTITY_WITHOUT_ENDPOINT_RATE
LEAN_EDIT: false
NUMERICS: none
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - W02_ENDPOINT_FUNCTIONALS_AS_TWO_UNRELATED_OBJECTS
OPENS:
  - EVEN_ENDPOINT_MOMENT_RATE_AGAINST_THE_KAPPA_L_PREFACTOR
---

# The two W02 endpoints are one complex Cauchy value

## 0. Result

The rank-two repair is confirmed and simplifies: the two endpoint functionals are
the real and imaginary parts of **one** complex number, the discrete Cauchy
transform of the vector evaluated at the single point `i beta`, `beta = L/(4 pi)`.
So `W02` sees the trial through one evaluation, not two independent moments.

Both endpoints then get bounded, and neither reaches consumer strength against
the prefactor `kappa_L = 32 L sinh^2(L/4) ~ 8 L sqrt m`. The odd endpoint has a
banked supplier and still loses; the even endpoint has no supplier beyond `l^2`
normalization. Discriminator: HOLD, the judge's `P_W02_ENDPOINT_1` branch.

## 1. The rank-two identity, checked

With `d_n = L^2 + 16 pi^2 n^2`, `u_n = L/d_n`, `v_n = 4 pi n / d_n`,
`kappa_L = 32 L sinh^2(L/4)`:

    kappa_L (u_n u_m - v_n v_m) = kappa_L (L^2 - 16 pi^2 n m)/(d_n d_m)
                                = ccmW02Entry L n m,

by the literal definition in `CCMFiniteWeilSourceMatrixN1.lean:49`. Exact, no
approximation. Hence for arbitrary complex `x, q` on the carrier

    x* W02 q = kappa_L ( conj(U(x)) U(q) - conj(V(x)) V(q) ),
    U(w) = sum_n w_n u_n,   V(w) = sum_n w_n v_n.                        (1)

`u` is even in `n`, `v` is odd. The form has signature `(1,1)`: it is a J-Gram
block, which is why one linear condition cannot annihilate it.

## 2. The two endpoints are one Cauchy value

With `beta = L/(4 pi)` we have `n^2 + beta^2 = d_n/(16 pi^2)`, so

    1/(n - i beta) = (n + i beta) * 16 pi^2 / d_n
                   = 4 pi * (4 pi n / d_n) + 4 pi i * (L / d_n)
                   = 4 pi ( v_n + i u_n ).

Therefore, writing `Cauchy_w(zeta) = sum_n w_n/(n_n - zeta)` for the discrete
Cauchy transform on the mode lattice,

    Cauchy_q(i beta) = 4 pi ( V(q) + i U(q) ).                            (2)

So `V` and `U` are `(1/4 pi)` times the real and imaginary parts of a **single**
complex evaluation, and the "two endpoints" `+- i beta` are its conjugate pair.
Full annihilation of the `W02` action on `q` is exactly `Cauchy_q(i beta) = 0`,
one complex equation, two real conditions — the judge's `U(q) = V(q) = 0`.

This is worth naming because the corridor already runs on this object. The Phase-1
reduction expresses the consumer error as the discrete Cauchy transform of the
residual at a spectral argument `zeta(z)`. The `W02` channel is the *same*
transform, of a different vector, at the fixed argument `i beta`. One object, two
uses. The evaluation point sits at lattice height `beta = L/(4 pi) ~ log m/12.57`,
deep inside the lattice `[-m, m]`, not near its ends.

## 3. What the catalogue supplies, endpoint by endpoint

**Odd endpoint `V`.** `v` is odd, so only the reflection-odd part of `q`
contributes: `V(q) = sum_n q^{odd}_n v_n`, hence
`|V(q)| <= sqrt(oddMass(q)) * ||v||_2`. Two inputs are banked:

- `selectedFerrersFiniteCCMOddMass` is `sum_j |oddPart_j|^2`
  (`G6N1SelectedFerrersH2aSourceQuantities.lean:289`);
- `selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates`
  and `..._tendsto_zero_of_modeAndChiRates`
  (`G6N1SelectedFerrersOddMassDecay.lean:995, 1169`) give
  `oddMass <~ log(lambda)/sqrt(lambda)`, `lambda = sqrt m`, so
  `oddMass <~ L/(2 m^{1/4})`.

And `||v||_2` is elementary: `(4 pi n)^2/d_n^2 <= (4 pi n)^2/(16 pi^2 n^2)^2 = 1/(16 pi^2 n^2)`,
so `||v||_2^2 <= 2 sum_{n>=1} 1/(16 pi^2 n^2) = 1/48`, i.e. `||v||_2 <= 1/(4 sqrt 3)`.

Hence `|V(q)| <~ (1/(4 sqrt 3)) sqrt(L/2) m^{-1/8}`.

**Even endpoint `U`.** `u` is even, so the whole of `q` contributes and only
normalization is available: `|U(q)| <= ||q||_2 ||u||_2 = ||u||_2`. By AM-GM,
`d_n^2 = (L^2 + 16 pi^2 n^2)^2 >= 32 pi^2 L^2 n^2`, so

    ||u||_2^2 = sum_n L^2/d_n^2 <= 1/L^2 + 2 L^2 sum_{n>=1} 1/(32 pi^2 L^2 n^2)
              = 1/L^2 + 1/96.

So `|U(q)| = O(1)` and nothing better. **No supplier in the catalogue bounds the
even endpoint moment**; asked this session, none returned.

## 4. Why neither reaches consumer strength

Insert both into (1) with the prefactor `kappa_L = 32 L sinh^2(L/4)`. Since
`sinh(L/4) = (m^{1/4} - m^{-1/4})/2`, `kappa_L ~ 8 L sqrt m`.

- even channel: `kappa_L |U(x)| |U(q)| <~ 8 L sqrt m * ||x||_2 * (1/96)^{1/2}`,
  which is of order `L sqrt m` and does not decay;
- odd channel: `kappa_L |V(x)| |V(q)| <~ 8 L sqrt m * ||x||_2 * (1/48) * sqrt(L/2) m^{-1/8}`,
  of order `L^{3/2} m^{3/8}`, which also does not decay.

So the banked odd-mass supplier buys `m^{-1/8}` against a prefactor of size
`m^{1/2}` and loses by `m^{3/8}`. That answers the open question of the previous
preflight in the negative: the odd-mass ledger does **not** rescue the `W02`
channel.

**Guard, stated because it decides how to read the above.** Both displays are
absolute majorants of a single ledger. Bounding the `W02` channel by itself is
the component split this route has been killed for repeatedly, and the two
displays are therefore *not* evidence that the consumer is large — only that no
separate control of `W02` at consumer strength exists. That is precisely the
argument for the judge's `R3`: do not remove `W02`, keep it inside the one
completed signed measure where it cancels against the prime ledger, and attack
the polarized Volterra test function instead.

## 5. Corrections carried

Three claims of `d2c044f7` are withdrawn in correction 7 (`docs/routeB_bus/
LINUX_CORRECTION_7_TWO_C04_SLIPS_IN_THE_POLE_CROSSWALK_GOAL058_2026-08-27.md`):
rank-one pole removal, transport of the function's zero integral to the
coefficient row, and exact evenness of the finite row. Nothing above uses any of
them. In particular section 3 uses reflection-**odd mass**, the row-level object,
never exact evenness.

## 6. Next load-bearing gap

    EVEN_ENDPOINT_MOMENT_RATE_AGAINST_THE_KAPPA_L_PREFACTOR

stated as: a supplier for `|U(q)| = |sum_n q_n L/(L^2 + 16 pi^2 n^2)|` along the
selected schedule, at strength `o(1/(L sqrt m))` after pairing, or a same-family
theorem that forbids it and forces the completed-measure route `R3` outright.

Given section 4, my own reading is that `R3` is the live line and the endpoint
route is a diagnostic that has now returned its answer. I do not select; that is
the judge's call.
