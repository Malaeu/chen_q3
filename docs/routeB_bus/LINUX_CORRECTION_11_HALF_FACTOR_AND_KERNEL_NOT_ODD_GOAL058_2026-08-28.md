---
TASK_ID: LINUX_SELF_CORRECTION_11
MODE: PAPER_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
CORRECTS: 6c5f307f and ad621220 (four claims)
ACCEPTS_VERDICT: cc0effc7
RH_CLAIM: false
---

# Correction 11 — the missing one half, and three overstatements

## 1. The factor `1/2`

The reflection identity reads `integral G d mu = (1/2) Phi(G)`, `Phi(G) =
integral G d nu`, `nu = mu - R_* mu`. Carrying it into the consumer gives

    Psi_k(z) = D_k(z) + (1/2) * Phi_k(G_{k,z}),
    D_k(z) = sum_i ((M_k)_ii - a_k) conj(x_k(z)_i) q_{k,i}.

My reports named `Phi` as the legal object and then wrote the consumer without
the `1/2`. Arithmetic slip with a real consequence for any rate ledger.

## 2. The full Volterra kernel is not reflection-odd

Withdrawn. The antisymmetry belongs to the **off-diagonal test**
`G(t) = sum_k omega_k sin(n_k t)`, which is `2 pi`-periodic and odd, hence
`G(2 pi - t) = G(-t) = -G(t)`. The full kernel
`K(w) = sum_k (alpha_k + beta_k w) e^{2 pi i k w}` contains the term
`w * sum_k beta_k e^{2 pi i k w}`, whose prefactor `w` is not periodic. So `K` is
not `2 pi`-periodic and the reflection argument does not reach it. Any sentence
of mine that applied "the test function is antisymmetric" to the full kernel is
withdrawn.

## 3. The residue does not by itself produce the primitive

Withdrawn. I wrote that the existence of

    F^comp(t) = lim_{eps->0} [ nu([eps,t]) - (1/(2 pi)) log(1/eps) ]

"is exactly the statement that the residue is `1/(2 pi)`". It is not. Cancelling
the logarithm removes the divergent term; existence of the limit additionally
needs integrability of the remainder after that subtraction, near each endpoint.
That statement is unproved and is now carried as
`COMPENSATED_ENDPOINT_REMAINDER_PRIMITIVE`.

## 4. The graph envelope is not the only binding gap

Withdrawn. I called `GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE` "the binding one".
The two-channel form of section 1 shows the diagonal channel `D_k(z)` needs its
own compact budget, carried as
`LITERAL_CCM_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND`, and the finite normalized row
needs an adapter, carried as `SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER`. Naming
one gap as binding while three others are open is the kind of narrowing this
route has been punished for.

## 5. Ledger

Sixteenth forbidden move: **when an identity is rewritten, carry its constant.**
The `1/2` was in the reflection identity I wrote correctly two reports earlier and
absent when I used it.
