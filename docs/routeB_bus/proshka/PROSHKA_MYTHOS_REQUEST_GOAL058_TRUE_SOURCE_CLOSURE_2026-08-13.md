# Goal 058 true source-closure joint request

Date: 2026-08-13

Addressees: Proshka (judge) and Mythos (independent attacker)

## Source lock

```yaml
REPOSITORY: Malaeu/chen_q3
BRANCH: rh_clean
REQUEST_BASE_HEAD: f557dfe2621982b48d51389b20e43b46eb681776
ROUTE: CHALLENGER_NOT_RH
GOAL_058: OPEN
G1: OPEN
G3: OPEN
G2B_P59: PROVED
BUS_010: VOID
RH_CLAIM: false
```

The request is written after strict startup and `routeb_status.py --check`
both passed at the named head.

Pinned source files:

| Object | Path | SHA-256 |
|---|---|---|
| literal finite CCM matrix | `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean` | `282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89` |
| literal complex source trial and residual | `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteSourceResidual.lean` | `c11fe72d9df1e7a81d73cdcb1beebfc016be82cb1d0bcc8ffc371fc748cfb497` |
| kernel-checked complex P59 connector | `q3.lean.aristotle/Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean` | `dc5e858863647224c17256b3cf629efc000ca81cbea4fb9cfd02fef28a6bc4eb` |
| prior full-source architecture verdict | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SOURCE_ARCHITECTURE_RATIFICATION_2026-08-13.md` | `0a8e2e0a1b9423003d3d62ed7964cc22e17fc43c2642f43c164ca71c634aaa68` |
| primary CCM paper | arXiv `2511.22755v1` | `96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a` (source e-print lock used by production) |

Correction: the local rendered PDF is
`tmp/pdfs/2511.22755.pdf`, SHA-256
`c98d89f7fc999d038e15e80a9aaaee2af797c17711c4329ca7ce48ad49cb336b`.

## Knowledge preflight

The exact query

```text
Goal 058 literal CCM complement floor source residual decay fixed schedule Feshbach prolate transfer smallest missing theorem
```

returned exit code `0` and `no hits`. Existing catalog results provide
receivers and finite identities, not the two source estimates below.

## Current exact finite object

For one literal pair index `i`, set

```text
q_i = D0Pstar.sourceCCMComplexRow S i
K_i = D0Pstar.sourceCCMFiniteMatrix i
a_i = <q_i, K_i q_i>
r_i = K_i q_i - a_i q_i
P_i = |q_i><q_i|
Q_i = I - P_i
C_i = Q_i (K_i - a_i I) Q_i.
```

The current Aristotle project
`0bf0fd63-4122-4627-8920-66dba6a7b98e` is already proving only the exact
finite decomposition

```text
K_i - a_i I = |q_i><r_i| + |r_i><q_i| + C_i.
```

Do not duplicate or count that identity as source closure. It contains no
inequality and no limit.

## What the primary source actually says

Section 8, page 32 of arXiv `2511.22755v1` explicitly calls the following the
two essential missing steps of the tentative strategy:

1. prove that the smallest eigenvalue of the Weil quadratic form is simple
   and its eigenvector is even;
2. prove that the proposed source trial is a sufficiently accurate
   approximation to that eigenvector.

Theorem 1.1 and Theorem 5.10 assume the finite lowest eigenvalue is simple and
the eigenvector even. Proposition 3.4 supplies lower-bound convergence but not
simplicity, a positive complement floor, or trial tracking. The paper proves
the simple-even statement for the prolate-wave operator, not for the literal
full CCM Weil matrix.

This request therefore asks for new mathematics, not repository plumbing.

## Previously killed shortcuts

The following are unavailable and must not reappear under new names:

- the rank-two CCM commutator does not imply a positive gap; a kernel-checked
  3-by-3 plant has the exact commutator identity and a nonsimple ground space;
- a scalar commutator expectation is identically zero for symmetric matrices;
- `PairCofinal` means only `m -> infinity` and `N -> infinity`; the previously
  kernel-checked schedule `m_k = 2^((k+1)^2)`, `N_k = k+1` makes
  `N_k / log(m_k) -> 0`, so physical-bandwidth cofinality does not follow;
- one finite `(13,120)` projective defect near `4.69188255e-9` is a control
  cell, not a cofinal estimate;
- `WeightedRayleighProjectiveDefect`, Temple, perturbative-gap, ambient-
  residual, and penalty/coercivity declarations are receivers. A theorem
  that binds the desired floor, residual rate, tracking, or gap is not a
  source supplier;
- a free `xi_j` called “the bottom eigenvector” is not a selected object.
  Without existence and simplicity, different vectors in one bottom
  eigenspace can have different trial-line errors. G3 cannot silently select
  its own ground family before G1.

## The one joint mathematical problem

Choose and name one source-defined schedule

```text
sigma : Nat -> PairIndex
```

with every coupling condition it genuinely needs written explicitly (for
example a relation between `N_j` and `log m_j`). The schedule may not be
introduced after observing favorable spectra.

On the literal family `(K_j,q_j,a_j,r_j,Q_j,C_j)` above, the intended source
package must prove rather than assume:

```text
SOURCE FLOOR:
  exists delta_j > 0 such that
  delta_j * ||w||^2 <= Re <w, C_j w>
  for every w in range(Q_j), eventually in j;

SOURCE COUPLING DECAY:
  ||r_j|| / delta_j -> 0;

PARITY/NORMALIZATION EXIT:
  the isolated low eigenspace produced by the same package has the exact
  nonzero eta-normalization needed by CCMFiniteWeilParity, so simplicity plus
  reflection commutation selects the even branch rather than merely an
  unspecified parity branch.
```

It is acceptable to replace these displayed heads by a strictly stronger
same-family theorem, such as a norm-resolvent or exact prolate-to-Weil
comparison, only if every connector to `ccmWeilMatFinite` and
`sourceCCMComplexRow` is explicit and source-derived.

If the prolate operator is used, give the exact operator/form identity and an
error norm small relative to a proved prolate gap. “Landau-Widom class”,
numerical resemblance, or equality of one scalar eigenvalue is not an
operator comparison.

## Required joint response contract

Return exactly one `PRIMARY`:

```text
SOURCE_PACKAGE_SURVIVES
SOURCE_OBJECT_OR_SCHEDULE_REPAIR_REQUIRED
NO_SOURCE_PACKAGE_FROM_CURRENT_INPUTS
```

Then provide:

1. `FIRST_LOAD_BEARING_SOURCE_LEMMA`: the smallest theorem not already on
   disk. Give an exact mathematical statement and a Lean-shaped head.
2. `INPUT_PROVENANCE`: for every premise, name the exact primary-source
   theorem/equation or current Lean declaration that supplies it. Mark an
   unsupplied premise `OPEN`; do not relabel it.
3. `G1_G3_EFFECT`: show the finite spectral argument from the proposed source
   lemma to a unique simple even low eigenspace and projective tracking.
4. `SCHEDULE`: define the schedule and prove every required cofinal/coupling
   property, or return the smallest missing schedule lemma.
5. `ARISTOTLE_TASK`: only if there is a bounded theorem that is strictly
   source progress. Include owned file, allowed import, exact binders, exact
   theorem head, mandatory plants, axiom gate, success and typed-stop codes.
   Otherwise return `NO_SOUND_ARISTOTLE_TASK_AT_THIS_BOUNDARY`.
6. `ATTACK_YOUR_OWN_PROPOSAL`: give at least three concrete counterexamples or
   binder/object mutations and explain why they fail.

## Acceptance gate

A response is rejected if it does any of the following:

- puts `hgap`, `hfloor`, residual decay, ground tracking, simplicity, RH, or
  global Weil positivity into a claimed source supplier;
- changes `ccmWeilMatFinite`, `sourceCCMComplexRow`, or the P59 coordinate;
- selects the ground vector by an unproved definite description;
- promotes a finite cell or a numerical ladder to a cofinal theorem;
- uses a second favorable schedule/diagonal;
- supplies another algebraic decomposition while leaving both source
  estimates open;
- closes G1, G3, Route B, or RH without the complete kernel-checkable chain.

Current authorized effect is architecture/judge output only. G1 and G3 remain
open until the source package is proved and integrated.
