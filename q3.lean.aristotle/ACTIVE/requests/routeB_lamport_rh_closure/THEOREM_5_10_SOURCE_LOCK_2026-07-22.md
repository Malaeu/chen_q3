# Theorem 5.10 source lock — 2026-07-22

Status: `PRIMARY_SOURCE_PINNED / H2B_TRANSFORM_LAYER_OPEN / NOT_RH`

## Source

- Alain Connes, Caterina Consani, Henri Moscovici, *Zeta Spectral Triples*.
- arXiv: `2511.22755v1`.
- Primary PDF: <https://arxiv.org/pdf/2511.22755>
- PDF page: `23`, Section `5.6`.
- Downloaded PDF SHA-256:
  `c98d89f7fc999d038e15e80a9aaaee2af797c17711c4329ca7ce48ad49cb336b`.
- Existing local transcription:
  `literature/zotero/H8ULBMAL/fulltext.md:1063`.

Short source excerpt:

> Let εN be the smallest eigenvalue of QWλN assumed simple and ξ the corresponding eigenvector assumed even.

The complete source statement is already present verbatim at
`fulltext.md:1063-1079`; that location, rather than a second transcription, is
the canonical textual pointer.

## Exact mathematical payload

Inputs:

```text
ε_N = smallest eigenvalue of QW^N_λ
ε_N simple
ξ = corresponding eigenvector
ξ even
δ_N(ξ) = 1
```

Outputs:

1. `D_log^(λ,N)` is self-adjoint on `E'_N ⊕ E_N^⊥`; on
   `E'_N = E_N / Cξ`, the metric is the restriction of
   `QW^N_λ - ε_N ⟨·,·⟩`.
2. The regularized determinant satisfies the exact all-variable identity

   ```text
   det_reg(D_log^(λ,N) - z) = -i λ^(-iz) ξ_hat(z).
   ```

3. `ξ_hat` is entire; every zero of `ξ_hat` is real and equals a spectral
   point of `D_log^(λ,N)`.

## Contract boundary for `H2bTransformLayer`

The theorem does not derive the simple-even hypothesis.  The Route-B contract
must therefore consume the same canonical vector supplied by H2a and provide:

```text
same Pstar / same (m,N) vector ξ
simple + even + δ_N(ξ)=1
source quotient E'_N = E_N/Cξ
positive quotient metric from QW^N_λ - ε_N⟨·,·⟩
self-adjoint D_log^(λ,N)
nonvanishing phase -i λ^(-iz)
all-z determinant identity
transform identification Hfam(Pstar,j)=nonzero_unit*ξ_hat
```

Only after these fields are instantiated may `realZeroTheorem` and
`RoofGateA` be retyped as honest theorems.  The current exact stop remains
`H2B_EXACT_THEOREM510_FACTORIZATION_MISSING`.
