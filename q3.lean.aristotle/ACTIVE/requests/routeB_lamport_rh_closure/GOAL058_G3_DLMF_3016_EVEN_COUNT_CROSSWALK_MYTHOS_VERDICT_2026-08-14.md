# Goal 058 G3 DLMF 30.16 even-count crosswalk — Mythos verdict

Date: `2026-08-14`

Transport: fresh Mythos chat, completed naturally; browser-visible response
extracted from the final response article.

Captured response body: `20705` UTF-8 bytes.

Captured response body SHA-256:
`e40dffc45ed2d41c67d6aad918eb2e17da85f5448ec73c7e621803ee1016585a`

Evidence boundary: external source/architecture audit, not a Lean proof, source
supplier, endpoint-count theorem, G1/G3 closure, Route B promotion, or RH claim.

## Verbatim visible response

GOAL058/G3 — HOSTILE SOURCE AUDIT: DLMF 30.16 EVEN-COUNT CROSSWALK

Дата: 2026-08-14 · Boundary: source audit + import-contract synthesis only. No Lean code, no G1/G3 closure, no endpoint counts, no Aristotle authorization, no RH claim.

0 · Access & integrity report (Lawyer)

All five rh_clean files read in full: Proshka verdict, classical-spectrum source packet, PSWF index pin packet, D0_3F external source lock, and the accepted leaf D0Mode4FiniteToLiteralNegativeCount.lean (theorem head, hypotheses hm/hK/hsep/hΛ/hdet, ∀ᶠ d in atTop conclusion — all verified as Proshka described).

Primary source verified live, not from memory: DLMF version 1.2.7, release 2026-06-15 — §30.2, §30.3, §30.4, §30.16 fetched as rendered pages; §30.8.E1–E7 and §30.16.E1a–E9 fetched as official TeX endpoints. All nine SHA-256 pins in the existing source packet re-verified byte-identical against the live 30.16.E*.tex files (5ded…f22, 146c…06a, d194…b5e, c0e5…cbd, 35b0…e4d, 76e0…524, c0f3…1a5, 9457…05c, 87b5…383). The packet's lock is sound.

Not accessible / not audited: the Lean definition files for mode4ActualFiniteJacobiTruncation, mode4HermitianSchurMatrix, mode4BackwardTailSchurApprox, mode4JacobiIndex (not among the five URLs). Every claim below about the project matrix's internal layout — reversal, diagonal, entry normalization — is therefore REPO_INTERNAL_UNVERIFIED and must be discharged by a proved entrywise Lean lemma, never asserted in a packet.

1 · Exact pin of DLMF 30.16.1–30.16.4 (Architect + Lawyer)

30.16.1 (even sector, prose: "Let n−m be even… construct the d×d tridiagonal matrix 𝐀 = [A_{j,k}]", rows j = 1…d):

A_{j,j} = (m+2j−2)(m+2j−1) − 2γ²·[(m+2j−2)(m+2j−1)−1+m²] / [(2m+4j−5)(2m+4j−1)]
A_{j,j+1} = −γ²·(2m+2j−1)(2m+2j) / [(2m+4j−1)(2m+4j+1)]
A_{j,j−1} = −γ²·(2j−3)(2j−2) / [(2m+4j−7)(2m+4j−5)]

I independently verified symbolically that these are exactly the 30.8.3 recurrence coefficients (A_k, B_k, C_k) — equivalently 30.3.7's (γ_k, β_k, α_k) — evaluated on the even Legendre ladder ℓ = m+2(j−1), so for m=0 the rows are degrees ℓ = 0, 2, 4, …. The packet's central identification claim is source-true. Also verified at source level: the numerator of A_{1,0} is (2·1−3)(2·1−2) = 0 — the left edge closes itself at degree 0; no coupling to an omitted lower mode exists. That is the source-level half of the offset-zero reason (a).

Finding N1 — the DLMF matrix is nonsymmetric. For m=0: A_{j,j+1} and A_{j+1,j} share the numerator (2j−1)(2j) but have denominators (4j−1)(4j+1) vs (4j−3)(4j−1). For m>0 even the numerators differ. Since both off-diagonals are strictly negative for γ² > 0, the product A_{j,j+1}A_{j+1,j} > 0, so 𝐀 is symmetrizable (similar to a real symmetric Jacobi matrix via a strictly positive diagonal D, with d_{j+1}/d_j = √(A_{j+1,j}/A_{j,j+1})). Consequence: reality and simplicity of the α's are provable finite linear algebra, not something to import from DLMF's bare assertion "real eigenvalues."

Finding N2 — ordering prose is ambiguous. DLMF's exact wording: eigenvalues "arranged in ascending order of magnitude." Read literally as |·|-ordering, this breaks the whole count architecture whenever eigenvalues go negative (which happens: λ = χ − γ² < 0 once γ² > χ₀). The contract must define α_{j,d} as the j-th smallest by value and record why this is the only source-coherent reading: (i) at γ²=0 the matrix is diagonal with entries m(m+1) < (m+2)(m+3) < … all positive, both orderings coincide, and 30.16.3 then reproduces 30.3.3, λ_n^m(0) = n(n+1), exactly at p = (n−m)/2+1; (ii) 30.16.2's monotonicity α_{j,d+1} ≤ α_{j,d} is precisely Cauchy interlacing (eigenvalues of a bordered Hermitian matrix interleave those of its principal submatrix) for value-ordering of the symmetrized leading principal truncations — |·|-ordering satisfies no such law; (iii) 30.3(ii) analyticity in γ² makes value-ordering the continuous labeling. Interpretation note goes in the packet, never silent.

30.16.2: α_{j,d+1} ≤ α_{j,d}. Direction: monotone from above — combined with 30.16.3, α_{p,d} ≥ λ for all valid d, so finite counts below a threshold never overcount, they climb to the classical count. Hostile fine print: the enclosing prose carries a "for d sufficiently large" qualifier; if E2 is imported at all, import it as eventual-in-d, not universal.

30.16.3: λ_n^m(γ²) = lim_{d→∞} α_{p,d}, with the selector p = ⌊(n−m)/2⌋ + 1 attached to the equation. This is the sole load-bearing analytic statement. Direction: finite approximants → classical eigenvalue; never the reverse.

30.16.4: α_{p,d} − λ_n^m(γ²) = O(γ^{4d} / (4^{2d+1}((m+2d−1)!(m+2d+1)!)²)), d→∞. This is a constant-free big-O (asymptotic order symbol with no effective constant) — unusable for certification and unnecessary for the eventual-count argument. Excluded from the import contract. Its only audit value: its sign orientation (α − λ, nonnegative) reconfirms from-above.

Adjacent traps pinned: 30.16.6 is the odd-sector matrix with different entries — an E1↔E6 swap is a live mutation surface; 30.16.5 is numerics (never imported); 30.16.7–30.16.9 belong to the eigenvector route only (see §6).

2 · Selector check (Lawyer)

p = ⌊(n−m)/2⌋+1 verified three ways: (a) verbatim in the E3 TeX; (b) (m,n)=(0,4) ⇒ p = ⌊2⌋+1 = 3; (m,n)=(0,0) ⇒ p = ⌊0⌋+1 = 1 — locked; (c) γ²=0 anchor: the p-th smallest diagonal entry is (m+2(p−1))(m+2(p−1)+1) = n(n+1) = λ_n^m(0) per 30.3.3, forcing n = m+2(p−1), i.e., the selector. In the even sector the floor is decorative ((n−m)/2 is an integer) — but the contract keeps the floor form so an odd-sector reuse cannot silently misfire. Classical-index ledger: DLMF p ↔ classical even index r = p−1 (α_{p,d} → the eigenvalue of χ_{2(p−1)}); p is 1-based, r is 0-based. This ±1 is falsifier territory (F2).

3 · Shift, orientation, reversal, similarity vs congruence (Architect + Critic)

Unit ledger (source-exact). 30.2.1 with μ=m=0 reads (1−x²)w″ − 2xw′ + (λ + γ² − γ²x²)w = 0. The project's stored Ferrers equation −(1−x²)S″ + 2xS′ + Gx²S = (Λ+G)S is the same equation with λ = Λ, γ² = G — no residual shift, no factor. 30.8.4 confirms the matrix's spectral parameter is λ. Therefore:

λ-units (the DLMF matrix's own units): shift is −Λ·I. negCount(sym(𝐀_d) − Λ·I) = #{p ≤ d : α_{p,d} < Λ}.
χ-units: the threshold is Λ + G, i.e., #{r : χ_{2r}(√G) < Λ + G}, because χ = λ + γ² (30.2.1 vs Osipov's ODE, both pinned).

Finding U1 (the wall's predicted bug, found in the existing packet). The classical-spectrum packet's route step says "the finite d×d even DLMF Jacobi matrix after the existing Hermitian diagonal similarity and the shift by Λ + G." Read literally against the λ-unit DLMF matrix, that shift is wrong by exactly G: negCount(𝐀_d − (Λ+G)I) counts λ's below Λ+G, i.e., χ's below Λ+2G. The sentence is salvageable only under an unstated prior rewrite of the matrix into χ-units (adding G·I first). The crosswalk packet must carry the explicit two-line unit ledger above and state the shift once, in one unit system. This becomes falsifier F3.

Index base and orientation. DLMF rows j = 1…d ↔ ℓ = 2(j−1); growing d appends rows at the high-degree end, i.e., 𝐀_d is the leading principal d×d block of the semi-infinite even recurrence operator. E2's interlacing direction is consistent with exactly this bordering and with nothing else. Project side: mode4JacobiIndex q with q ≥ 0 suggests 0-based rows (map j = q+1); whether "backward tail / left continuant" storage involves an actual index reversal is repo-internal-unverified. A reversal is an orthogonal permutation P = Pᵀ = P⁻¹ — simultaneously a similarity and a congruence, so it is harmless once its exact form is written down and proved entrywise. It may not be waved through.

Similarity vs congruence — stop conflating them. The packet's phrase "positive diagonal similarity/congruence" fuses two different animals: similarity D⁻¹MD (preserves eigenvalues; used to symmetrize the nonsymmetric 𝐀_d and to transport the α-count) vs congruence ẼSẼᵀ (preserves inertia of a Hermitian matrix by Sylvester's law, changes eigenvalues; used in block Gaussian elimination / Schur inertia additivity via Haynsworth). Both appear in the chain and the contract must label each use.

Trap T1 — congruence does not commute with shifting. Ẽ(S − ΛI)Ẽᵀ ≠ ẼSẼᵀ − ΛI unless Ẽ = I. If mode4ActualFiniteJacobiTruncation happens to be a positive-diagonal congruence of the symmetrized DLMF matrix (plausible if the project uses a differently normalized Legendre/Ferrers basis — the symmetrized DLMF off-diagonals carry square roots, and I could not inspect the definition), then the shift must sit inside the congruence: negCount(Ẽ(sym(𝐀_d) − ΛI)Ẽᵀ) = #{α < Λ} is correct; negCount(ẼSẼᵀ − ΛI) is garbage. The entrywise leaf must fix the factorization order, not just the factors. This is the sharpest silent-failure mode I found and the packet does not currently name it.

4 · Exact separator/nonsingularity premises for the eventual count (Architect)

Target statement (the source theorem the wall demands), with M_d := the project truncation proved entrywise equal to P·Ẽ(sym(𝐀_d(G)) − Λ·I)Ẽᵀ·Pᵀ for explicit P, Ẽ:

Eventually in d: negCount(M_d) = #{r ≥ 0 : χ_{2r}(√G) − G < Λ} = #{r : χ_{2r}(√G) < Λ + mode4JacobiG mProject}.

Premises, exhaustively:

P1 (analytic import): ∀ p ≥ 1: α_{p,d} → χ_{2(p−1)}(√G) − G as d→∞ [30.16.3 + the identification of §5].
P2 (definitional/finite LA): α_{p,d} := p-th smallest by value of sym(𝐀_d); requires d ≥ p; ordering nondecreasing in p is then definitional.
P3 (already pinned): χ_0 < χ_1 < ⋯ strictly increasing, unbounded (Osipov TR-1450 Th. 3) — gives finiteness of the count and strict increase of the limit sequence over p.
P4 (separator): Λ + G ∉ {χ_{2r} : r ≥ 0}, equivalently Λ ≠ χ_{2r} − G for every r. This is logically independent of hdet (nonsingularity of the K×K literal Schur matrix); no equivalence lemma exists in the tree yet, so the composed production theorem must carry both until one is proved. Conflating them is a killed shortcut.
P5 (finite LA per d, uniform): tail block of M_d (rows q ≥ K) positive definite, from the existing hsep inequality + Λ ≤ 20 by diagonal dominance — feeding Haynsworth inertia additivity so negCount(M_d) = negCount(finite Schur head). Already the accepted transport's territory.
P6 (bookkeeping): d large enough that d ≥ K+1 and d ≥ N+1 where N is the classical count; absorbed by ∀ᶠ.

Proof shape from P1–P4 alone (finite reasoning over limits, fully Lean-provable once P1 exists): let N = #{r : χ_{2r} < Λ+G}. For p ≤ N the limit sits strictly below Λ, so eventually α_{p,d} < Λ; for p = N+1 the limit χ_{2N} − G > Λ strictly (separator), so eventually α_{N+1,d} > Λ; ordering in p pushes all higher positions above. Note: 30.16.2 is not needed for eventual equality — convergence at finitely many positions suffices. Importing E2 anyway buys the one-sided canary "finite count ≤ classical count for all large d" (never-overcount), which is a cheap D-series tripwire. Recommended as optional, excluded from the minimal carrier.

5 · The index-4 identification, fully sourced (Lawyer)

The identification λ_n⁰(γ²) = χ_n(√γ²) − γ² for the same n is the actual content of "INDEX4_IDENTIFICATION". Two source-faithful sub-routes, both now fully pinned:

ID-A (ordering route, recommended — no zero counts needed): 30.3(i) defines the DLMF eigenvalues by solutions of 30.2.1 bounded on (−1,1), equivalently of the form (1−x²)^{m/2}·g(x) with g entire — for m=0 the eigenfunction is the restriction of an entire function, hence continuous on the closed window, i.e., regular in exactly Osipov's sense. So after χ = λ + γ², the DLMF spectrum {λ_n⁰ + γ²} and Osipov's {χ_n} are the same set. 30.3.1 gives strict increase λ_m^m < λ_{m+1}^m < ⋯; Osipov Th. 3 gives strict increase of χ_n. Two strictly increasing enumerations of one set coincide termwise. Done — termwise, all n, evenness included for free (even n ⇔ even DLMF matrix sector ⇔ even ψ by Osipov parity / 30.4.3).

ID-B (zero-count route, belt-and-braces / row-route asset): 30.4(ii) states verbatim-level that Ps_n^m has exactly n−m zeros in (−1,1); with Osipov Th. 1 (ψ_n has exactly n zeros) and Th. 3 (uniqueness of the regular solution at χ_n), the zero count forces the index. Now page-pinned; hold in reserve.

Either way the identification consumes only already-locked papers plus DLMF 30.2/30.3(/30.4) — no new analytic hypothesis is invented, matching the PSWF pin packet's claim.

6 · Classification: pinned / finite-Lean / new import (Synthesizer)

Directly source-pinned (cite, hash, done): 30.16.1 entries (= 30.8.3 on the even ladder, symbolically re-verified); 30.16.2 direction (from above, eventual-in-d); 30.16.3 + selector; 30.16.4's existence-as-excluded; 30.2.1 (⇒ χ = λ+γ², c² = γ²); 30.3(i) regularity-equivalence, 30.3.1 strict order, 30.3.3 anchor; 30.4(ii) zero count; 30.8.1's (−1)^k sign convention and 30.8.5's 1/(2n+1) normalization (= 1/9 at n=4, coherent with 30.16.7); Osipov Th. 1/3, Bonami–Karoui, Katsnelson locks as already recorded.

Provable by finite linear algebra already inside Lean (no import allowed for these): the Lean-side definition of the m=0 even matrix from 30.16.1 (pure arithmetic); symmetrizability, reality, and simplicity of its spectrum (irreducible symmetric tridiagonal ⇒ simple); sorted-eigenvalue machinery; the entrywise identity project-truncation ↔ P·Ẽ(sym(𝐀_d)−ΛI)Ẽᵀ·Pᵀ with explicit P, Ẽ, and shift placement (leaf 1); tail positive-definiteness from hsep (P5); Haynsworth/Sylvester inertia additivity; the eventual-count derivation from P1–P4; the already-accepted finite-to-literal transport.

Genuinely new analytic import (the only one): the carrier below. Nothing else. Explicitly not imported: 30.16.4 (constant-free big-O), any finite-d eigenvector statement, eigenvector simplicity from prose, 30.16.7–30.16.9 for this wall.

7 · Do-not-assume compliance (Critic)

The contract as drafted assumes: no indexed coefficient row (E8 is a route-B object, deferred); no endpoint counts 2/3 (they remain downstream theorems via Bonami–Karoui separators, χ_4 − c² ≤ 20 already pinned); no zero offset (it remains the three-part theorem: left edge closed at degree 0 — source-verified via the vanishing A_{1,0} numerator — plus proved reversal/diagonal inertia preservation, plus proved tail positivity); no numerical truncation result (E4 and E5 excluded; the DLMF 30.16.5 numeric column is never evidence). Additionally the row route's E8 is sign-ambiguous at finite d (E7 normalizes e² only) and presupposes simplicity DLMF never states — two extra premises the count route simply doesn't have. Repo-side mutation surface worth one line in the packet: argument-order inconsistency mode4HermitianSchurMatrix mProject Λ K vs …_isHermitian mProject K Λ — every new leaf head must pin per-symbol argument order verbatim.

8 · Planted falsifiers (Critic)

F1 — monotone-direction reversal (required): plant the mutated import α_{j,d+1} ≥ α_{j,d} ("convergence from below") together with the derived claim "finite counts may exceed the classical count and decrease to it." Kill mechanism: contradicts the hashed 30.16.E2 text and breaks the never-overcount canary; under the true carrier the mutated inequality plus 30.16.3 would force α_{p,d} ≤ λ, refuted at γ²=0⁺ by continuity of the interlacing chain. Any reviewer or D-canary accepting F1 fails.

F2 — index-base/offset mutation (required): plant p = ⌊(n−m)/2⌋ (dropping +1) and, separately, r = p (dropping the −1). Kill anchors: (0,0) must select p=1 → χ₀ (the mutation claims χ₂ or selects position 0, which doesn't exist in 1-based DLMF indexing); (0,4) must select p=3, third smallest, not second; γ²=0 diagonal anchor 30.3.3 detects both instantly.

F3 — unit/shift mutation (the audit's finding, weaponized): plant "negCount(sym(𝐀_d) − (Λ+G)·I) eventually = #{r : χ_{2r} < Λ+G}" — the literal reading of the current packet's route sentence. Kill mechanism: the unit ledger of §3 shows the left side eventually counts χ's below Λ+2G; any G with χ-modes in (Λ+G, Λ+2G) separates the two. The accepted contract must provably reject this statement, making U1 a permanent tripwire.

Free extras worth planting alongside: E1↔E6 sector swap (odd matrix on even claim); congruence-shift order swap per trap T1; dropping the (−1)^{j−p} sign in any future E9 use.

FINAL BLOCK

PRIMARY_ROUTE: ROUTE_INERTIA_FINITE_LIMIT — it is the wall Proshka named, it consumes (not strands) the accepted mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix transport, and its analytic surface is a single limit family. ROUTE_DLMF_INDEXED_ROW_LIMIT stays alive as the secondary root-existence spur only, with its honestly larger import bill now itemized: E7 normalization, E8 with an explicit sign-selection premise, E9 function identity, the 30.8.1 (−1)^k bridge, and finite-d simplicity.

MINIMAL_NEW_CARRIER: one source-prop family (Osipov-object-first): given the Lean object for the ordered classical family χ_{2r}(√G) (strictly increasing, unbounded, regular-solvability characterization; Osipov Th. 3 + Katsnelson realization), the sole analytic import is — for every p ≥ 1, the p-th smallest-by-value eigenvalue of the Lean-defined d×d matrix with the literal 30.16.1 entries at m=0, γ² = G, tends to χ_{2(p−1)}(√G) − G as d→∞. Justification chain, each link page/hash-pinned: 30.16.3 (+ selector) ∘ [30.2.1, 30.3(i), 30.3.1, Osipov Th. 3] (ID-A). Optional non-carrier import: 30.16.2 as eventual-in-d, canary-only. Everything else in §4's premise list is finite linear algebra.

EXACT_NEXT_LEAN_HEAD: NOT_READY. Proshka's binding leaf is the read-only packet GOAL058_G3_DLMF_3016_EVEN_COUNT_CROSSWALK_SOURCE_PACKET_2026-08-14.md at the required path, and she has ruled the tree lacks the source-locked χ_{2r} object. Queued post-acceptance heads (names only, in order): (1) the χ-even-family source object; (2) mode4DLMFEvenFiniteMatrix_eq_reversed_diag_similarity_actualTruncation — the entrywise identity with explicit P, Ẽ, and shift placement per trap T1; (3) the carrier prop; then the §4 count theorem.

SOURCE_PINS: DLMF 1.2.7 (2026-06-15): 30.16.E1a/E1b/E1c, E2, E3 (+selector), E4 (pinned-as-excluded), E6 (pinned-as-trap), E7/E8/E9 (route-B reserve); 30.2.E1; 30.3.E1, 30.3.E3, 30.3(i) prose (bounded ⇔ (1−x²)^{m/2}·entire); 30.4(ii) zero-count prose, 30.4.E3; 30.8.E1 (sign), E3a–c, E4 (λ-units), E5 (1/(2n+1)); all nine 30.16 TeX hashes re-verified this run. Two prose ambiguities pinned with resolutions: "ascending order of magnitude" → by-value (three-argument justification, §1/N2); "for d sufficiently large" → E2 imported eventually-in-d if at all. Osipov TR-1450 Th. 1/3, Bonami–Karoui 1405.3676v2, Katsnelson lock 6822e3…b919: unchanged.

KILLED_SHORTCUTS: (1) "shift by Λ+G" applied to the λ-unit DLMF matrix — replaced by the explicit unit ledger, shift −Λ·I in λ-units ⇔ threshold Λ+G in χ-units; (2) importing 30.16.4 in any form; (3) |·|-ordering of α; (4) conflating hdet with the separator premise P4 — independent until an equivalence lemma exists; (5) conflating diagonal similarity with congruence, and shifting outside a congruence (T1); (6) importing eigenvector statements, simplicity, or a finite-d indexed row for the count wall; (7) E1↔E6 sector swap; (8) any use of 30.16.5 or 30.8.7 asymptotics as count evidence; (9) endpoint counts 2/3 and offset zero as assumptions anywhere — theorems only.

ARISTOTLE_BOUNDARY: NOT_AUTHORIZED, unchanged, and nothing in this audit moves it. First Aristotle-eligible object after packet acceptance and χ-object creation is leaf (2) above — pure finite linear algebra, zero analytic content, hence maximally safe to outsource. The carrier prop itself is a source-prop and never an Aristotle task.

STOP_CODE: DLMF_3016_SEMANTICS_VERIFIED_HASHES_MATCH_UNIT_SHIFT_AMBIGUITY_KILLED_COUNT_CONTRACT_DRAFTED_LEAN_HEAD_NOT_READY
