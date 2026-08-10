# D0.7e.5a — Mythos source-acquisition verdict

```yaml
STATUS: REVIEWED_REPAIR_REQUIRED
PRIMARY: SOURCE_PARTIAL_B_ORIENTATION_OPEN
PROVENANCE: USER_RELAYED_MYTHOS_RESPONSE
DATE: 2026-08-03
PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 6af9170d15a38e451a76f8dbf2ad8725d62b6f5f
ACTIVE_ADDRESS: RB-LAMPORT-D0 / D0.7e.5a
STOP_RETAINED: D0_7E_WPRIME_CONSUMER_MISSING
ROUTE_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
LEAN_EDITS: false
ROUTE_STATE_EDITS: false
MAP: maps/2026-08-03_d0_7e_5a_mythos_source_acquisition_verdict.svg
PROSHKA_REVIEW: D0_7E_5A_PROSHKA_SOURCE_AUDIT_VERDICT.md
SYNTHESIS: D0_7E_5A_MYTHOS_PROSHKA_SYNTHESIS.md
```

This file records the owner-relayed Mythos result. Independent Proshka review
confirmed the recovered CCM operator/determinant package but rejected the
claim that only the `b` orientation remains. This remains evidence, not a
route-state transition.

## Verdict

`SOURCE_PARTIAL_B_ORIENTATION_OPEN`

The pin was reported as checked: `6af9170d` exists at `HEAD`; the journal is
caught up; Müntz 4/4 is reported by the committed `lake build` ledger at 8055
jobs. The search was reported across the full requested surface. No Lean or
route-state change was made and no bus goal was created.

## A. Approximant — recovered verbatim (DEFINITION + THEOREM)

Source: CCM, arXiv:2511.22755v1, file `mc2arXiv.tex`.

- Lines 997–1001, Proposition `pertscal`: the unique operator
  `D_tilde = D_log^(lambda,N)` with the same domain as
  `D_log^(lambda)`, agreeing with it on `ker delta_N` and satisfying
  `D_tilde(xi) = 0`.
- Reported explicit formula at source page 298:

  \[
  \widetilde D
    = D_{\log}^{(\lambda)}
      - |D_{\log}^{(\lambda)}\xi\rangle\langle\delta_N|.
  \]

- Line 984:

  \[
  \delta_N := L^{-1/2}\sum_{n=-N}^{N}V_n,
  \qquad \langle\delta_N|f\rangle \to f(\lambda),
  \]

  with the Dirichlet kernel acting as a boundary delta.
- Source page 298(i): `D_tilde` is self-adjoint on
  `E'_N \oplus E_N^perp`; on `E'_N = E_N / C xi` the form is reported as
  `QW_lambda^N - epsilon_N <.,.>`. Mythos flags this as the analogue of the
  project L-M2 factor, while also flagging the difference: CCM subtracts
  `epsilon_N`, whereas CvS uses the radical.

## B. Verbatim WPrime — not found

No object named `WPrime`, nor a scalar object with the requested role, was
reported in:

- CCM;
- CvS `Araki-final-oct25.tex` (reported zero hits for `Fhat(0)`,
  `zeta(1/2)`, `Xi(0)`, and `central value`);
- zeta-cycles arXiv:2106.01715, where
  `W_{0,2}(F) = integral_1^infinity F(x)(x^(1/2)+x^(-1/2)) d*x` is a
  functional, not the required scalar consumer.

The historical expression
`|b| * sqrt(lambda) * sqrt(alpha / DeltaE)` was reported only in project
target/sketch material. It was therefore rejected as a definition source and
was not used.

## C. Independent semantic theorem — recovered

Source page 299, Theorem `finmain` (ii):

\[
\det_{\mathrm{reg}}(\widetilde D-z)
  = -i\,\lambda^{-iz}\,\widehat\xi(z).
\]

Reported semantics: the regularized characteristic determinant of the
rank-one-perturbed scaling operator; its zero set is the zero set of
`xi-hat`. This has independent content and does not mention `alpha`,
`DeltaE`, or the 5c right-hand side.

## D. b argument — open

The source reportedly fixes a boundary normalization:

- `delta_N(xi) = 1` at source pages 297/1085;
- in the `N -> infinity` outlook, `normalized by xi(lambda) = 1` at source
  page 1223.

This is a third scalar orientation. No theorem was found crosswalking it to

\[
bCal = \widehat F(0)/\Xi(0).
\]

The reported convergence to `Xi` uses only “multiplied by suitable constants”
at source page 1224 and is classified as Outlook/CONJECTURE. No occurrence of
`zeta(1/2)`, `Xi(0)`, or another explicit central constant was reported.

## E. Legal domain

The reported source domain is

\[
L^2([\lambda^{-1},\lambda],d^*u),
\qquad E_N = \operatorname{span}\{V_n:|n|\le N\},
\]

with `2N+1` modes and eigenvalue magnitude bounded by
`N*pi/log(lambda)`. The two source parameters `(lambda,N)` remain free.
The project relation `lambda = sqrt(m)` is a transfer assumption, not a
source definition.

## F. Reported locators and hashes

- arXiv:2511.22755v1, reported as the only version, submitted 27 November
  2025 and headed to EMS Press 2026; reported e-print SHA-256 prefix/suffix:
  `96c88486…81f3bf4a`.
- arXiv:2511.23257: `d78c6f23…d65d5f7`.
- arXiv:2106.01715: `bbe3bff3…9c9a2e63`.

Reported negative search surfaces: no arXiv ancillary beyond the single TeX
listed by `00README`; no author GitHub repository; no Zenodo artifact; no CMP
supplement; the CCM numerical Mathematica thread at source page 1295 was not
published; third-party reproduction repositories were not treated as
provenance.

## Acceptance-test report

1. PASS — no `alpha`, `DeltaE`, or 5c RHS in the recovered source object.
2. PASS — changing `alpha`/`DeltaE` leaves the source object unchanged.
3. PASS — 5c is not definitionally forced by the source.
4. PASS for the determinant identity as THEOREM; FAIL for Xi normalization,
   which appears only in Outlook.
5. OPEN — no project crosswalk.
6. OPEN — the source boundary normalization is not identified with either
   `bCal` or `bCal^(-1)`.
7. N/A / respected — no illegal inverse-domain use was reported.
8. PASS — no H3c/H4, RH, Xi-convergence theorem, kappa, or `N(lambda)` was
   imported.
9. PASS — both source coordinates remain free.

## Reported consequence

The stop `D0_7E_WPRIME_CONSUMER_MISSING` remains. The approximant and its
determinant theorem were recovered, but an independently source-defined
`WPrime` consumer was not. Under the current no-new-definition/source-lock
constraints, D0.7e.5a does not open without an owner-approved mint or contract
revision.

The reported smallest missing statement is one orientation/crosswalk line

\[
c_{\lambda,N}:\quad
\delta_N(\xi)=1
\longmapsto
\widehat F(0)/\Xi(0)
\]

on the legally typed nonzero locus. CCM reportedly leaves this only as
“suitable constants.”

The independent challenger fronts G2/G3/G5/G6 are not changed by this verdict.

## K6 scoring reported by Mythos

- P-A: PASS — no ancillary artifact.
- P-B: FAIL — the prior prediction assigned 50% to a v2, but only v1 exists.
- P-C: FAIL — the prior prediction assigned 75% to NO and 20% to PARTIAL;
  the returned outcome was PARTIAL because the approximant was recoverable
  verbatim.
