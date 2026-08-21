# TASK 2026-08-21 — W13.7B source interface and W13.7E selected theta equality

```yaml
task_id: 2026-08-21-w13-7b-7e
authorized_by: PROSHKA_VERDICT_REQ_2026_08_21_N_BOOK_EXHAUSTIVENESS_AND_W13_7D_AUTHORIZATION_2026-08-21.md
verdict_commit: d7e6f06009da7b2d0b9f09e220caf391df90caed
verdict_blob: 603ae33abcde46b22f5db2e266788e85a1b48b33
written_by: LINUX_CLAUDE_UNDER_NIGHT_GRANT_2026-08-20
pointer_moved: false      # docs/Codex/CURRENT.md is the owner's; he flips it
```

> **Сокращай пространство решений, а не расширяй.** Нашёл два пути — убей один
> измерением, а не оставляй оба. Проверяй варианты сам: у тебя есть ядро,
> `./ask.sh` и вся полка. К судье идёшь **только** когда упёрся в стену,
> которую не можешь ни пройти, ни обойти, ни убить. Запрос к судье — признак
> стены, а не способ подумать вслух.

## Where the front stands

W13.7D is kernel-green (`G6N1OrderedEnumerationLock.lean`, blob `ce6c9d2e`
after the audit repair). It is deliberately abstract: two strictly increasing
sequences whose parts below a shared cutoff enumerate the same set agree term by
term while both stay below. It mentions no spheroidal function and no
eigenvalue, so it selects nothing on its own.

Two nodes remain between it and the packet.

## W13.7B — the source interface, two inclusions kept apart

For each precommitted production `k`, with `G_k = gamma_k^2 > 0` and the
source-locked even split `s_k`, the interface must state the set equality

```text
{Lambda | Lambda < 20 and mode4DLMF3035EvenCharacteristicEquation G_k Lambda s_k}
  = {Lambda | Lambda < 20 and exists r, lambda_(2*r)^0(G_k) = Lambda}
```

**The two directions have different provenance and must stay visibly separate.**
Collapsing them into one citation hides an object mismatch: the book classifies
solutions of the differential equation, while our object starts life as a root
of a continued-fraction characteristic equation. Those are different categories,
and C04 fires exactly there.

```text
right -> left   DLMF 30.3.5, one-way membership. PAPER_PROVED / PORT_OPEN.
left  -> right  project bridge + Meixner-Schaefke Satz 1.
```

The reverse direction is **already built on our side** and must be reused, not
rewritten:

```text
mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero
  Q3/Proofs/RouteB/D0Mode4DLMF3035EvenCharacteristicSource.lean:80

exists_mode4FerrersRegularEvenProlateSolution_of_root
  Q3/Proofs/RouteB/D0Mode4FerrersRegularEvenProlateSolution.lean:96
  -> Nonempty (Mode4FerrersRegularEvenProlateSolution mProject K Λ)
     even, ContinuousOn on Icc (-1) 1, prolate ODE inside, zero flux at ends

center_ne_zero_of_even_of_nontrivial
  Q3/Proofs/RouteB/G6N1EvenSolutionCenterNonvanishing.lean:70
```

What the book supplies, and what therefore has to become a **typed hole** rather
than an axiom: the regular endpoint spectrum is exhausted by the branches
`lambda_n^m`, all eigenvalues are real and simple, and parity follows the parity
of `n - m`. Simplicity is load-bearing — without it one eigenvalue could carry
both an even and an odd solution, and the parity step would not close.

**Do not encode Meixner-Schaefke as a Lean axiom.** Model it the way
`Satz9SourceData` is modelled in `G6N1Satz9SourcePackageInterface.lean`: a
structure whose fields are facts about a supplied function, inhabited only by
exhibiting one. Note the audit correction already applied there — continuity is
`ContinuousOn ... (Icc (-lambda) lambda)`, never global `Continuous`, because our
production modes are `Icc.indicator` zero extensions with a nonzero endpoint
value, which makes the global form unsatisfiable and the endpoint extension
vacuous.

Suggested file: `Q3/Proofs/RouteB/G6N1BookRegularSpectrumSourceInterface.lean`.

## W13.7E — selected theta equality for degrees 0 and 4

Compose W13.7B's set equality with W13.7D's ordered enumeration at rank two:

```text
project ordinal  j = 0, 1, 2
source degree    n = 2*j = 0, 2, 4
```

The intermediate ordinal `j = 1` is load-bearing even though the packet consumes
only `j = 0` and `j = 2`. Dropping it breaks the order argument that makes the
third element of the two ordered spectra agree.

Suggested file: `Q3/Proofs/RouteB/G6N1SelectedThetaEqualityDegreeZeroFour.lean`.

## Rejected in advance — the judge killed these before they were written

```text
inferring r <= 2 from Lambda < 20 alone
  The cutoff admits the selected branches; it does not isolate them. Higher
  even branches enter below 20 as G grows: at k=0 the n=6 branch already sits
  at +5, at k=5 the n=8 branch at -1187. The numerical table is a falsifier,
  never a proof premise. Selection comes from fixed-G strict order.

DLMF 30.4 completeness route          not required, do not build it
project analytic branch from G = 0    not required, do not build it
defining the book branch as our carrier   C10 surrogate kill
one citation covering both inclusions     C04 same-coordinates-two-laws kill
```

## Control v9 is now active — this changes what closing a node means

Landed 2026-08-21 in `d92960a0`, after this task was written. Three consequences
here, none optional:

```
SOURCE_WRITTEN -> KERNEL_GREEN -> SEMANTICALLY_ADMITTED
MAX_KERNEL_GREEN_AWAITING_SEMANTIC_REVIEW = 1
```

A green kernel no longer closes a node. It reaches `KERNEL_GREEN` and stays
quarantined until the independent Linux auditor issues a
`q3_semantic_attestation.v1` receipt, which you cannot issue yourself. Until it
lands: no second theorem on the first, no gap marked closed, no next node.

So **W13.7B and W13.7E go one at a time**, not as a pair.

Every new load-bearing hypothesis needs a `HYPOTHESIS_PROVENANCE` row, and
`production_inhabitant_or_plant` is a closed object — `kind`, `path`, `blob`,
`declaration`, `exact_type`, `verifier`, `scope`. Free text is refused. That
rule is in your own transaction because the first plant accepted an entry whose
provenance said the hypothesis was uninhabited.

The book's exhaustiveness enters as `NEW_OPEN_OBLIGATION` and must appear
verbatim in `OPENS`. `EXACT_FIT_SUPPLIER` rows go through the existing
`scripts/supplier_preflight.py`.

## Gate

Standard: `lake env lean` on the file, `lake build`, `scripts/q3_check.sh`,
axiom profile exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
Receipts (blob, sha256) into the commit message. Text agreement is not a kernel
check — run the kernel here yourself and read `${PIPESTATUS[0]}`.

## Ledger

```text
CLOSES: [W13_7B_BOOK_REGULAR_SPECTRUM_TO_DLMF3035_CHARACTERISTIC_RANGE,
         W13_7E_SELECTED_THETA_EQUALITY_DEGREE_ZERO_FOUR]
OPENS:  [MEIXNER_SCHAEFKE_SATZ_1_TYPED_SUPPLIER]
```

The single opened entry is honest and unavoidable: the book's exhaustiveness
enters as a typed hole, and something must eventually inhabit it. It is the same
shape as the Satz 9 hole and is expected to be discharged the same way, by a
source-only witness. Naming it here is the point — an interface that opened a
supplier silently would read as if the paper had been formalized.

## If you hit a wall

Write `docs/routeB_bus/CODEX_REQ_2026-08-21_<slug>.md` with a non-empty `TRIED`
field and push it. Do not address the judge directly — the browser lives on the
Linux body, and the answer comes back as
`docs/Codex/CODEX_ANSWER_<same-slug>.md` carrying `ANSWERS_REQ: <your id>`.
