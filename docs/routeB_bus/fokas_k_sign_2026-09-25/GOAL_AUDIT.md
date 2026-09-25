# Completion audit against the original Fokas research objective

Date: 2026-09-25. Evidence baseline: e4e5bc3b.
This audit distinguishes completion of the requested mechanism investigation
from completion of Goal058 or a new proof of cellwise ground tracking.

Original objective:
«Для выбранной Ferrers-семьи Goal058 проверить механизм Фокаса после действия
исходной матрицы K: получить source-matched формулу полного дефекта,
установить, даёт ли сокращение необходимый знак/оценку для ground tracking,
и довести до проверенного доказательства применимого звена либо точного
обоснованного препятствия; сохранить результат и инсайты в репозитории,
не дублируя ожидающий запрос Прошке.»

| Explicit requirement | Current evidence | Scope of result |
|---|---|---|
| Same selected Ferrers source and original K | Recovered response (1)-(8); recovery crosswalk audit; literal matrix entry definitions used by REPORT | Full action of K-aI with original modes, normalization and boundaries; not replacement by the Jacobi operator |
| Source-matched full defect formula | D=(K-aI)[V(U)+B0*1-B1*sigma], r=(A/Z)D; independently checked correspondence with denominator-cleared local candidates | PAPER identity on the source's stated port; candidate Lean files remain untracked and unadmitted |
| Determine what cancellation supplies for ground tracking | Recovered equations (9)-(11): Z cancels exactly; the kernel, central coordinate and floor remain | Exact original tracking-envelope rewrite; no rate or sign follows merely from boundary rank two |
| Verified applicable link OR exact justified obstacle | Audited constant-floor counterexample on this literal selected family; separately audited all-m Robin enclosure proof | The current constant-beta consumer cannot be supplied: unit y_j perpendicular to q_j satisfy y_j*(K_j-a_j I)y_j <= U_j with U_j -> 0, contradicting every fixed beta>0. This is a family obstruction, not a finite numerical miss |
| Preserve results and insights in repo | REPORT/REVIEW, recovered source and recovery note, Progress_Log, insight document, reproducible certificate scripts | Commits pushed and read back; packet hashes checked |
| Do not duplicate pending Proshka request | Root actions consist of local work and read-only observations of the exact existing chats; queue keeps request #8 separate | No new mathematical send; no interruption or duplicate watcher |

## Why the obstacle is exact

For any proposed beta>0, eventually U_j<beta. Its unit witness is in the
SAME q_j-complement required by the consumer, so the claimed lower bound
beta is contradicted there. The source-family and matrix crosswalk, radical
identity, source hmode input and two-case Hermitian argument were checked in
../proshka/PROSHKA_GOAL058_FLOOR_KILL_INDEPENDENT_AUDIT_2026-09-25.md.
This is stronger than the statement that a bound has not been found.
The Fokas identity survives; the fixed-floor supplier required by its old
cofinal consumer does not. It cannot be restored by cancelling Z or by
proving the scalar Mellin remainder small.

The additional RAW_R6 family obstruction in REPORT concerns only a named
sufficient implementation and is bypassable. The m2 Arb result and density
counterexample concern only a finite reference cell. Neither is used here
as evidence for a cofinal sign or a general impossibility of the method.

## Work that is NOT established

Positive cellwise delta_j, the compatible same-family consumer, weighted
full-residual decay, the complete central scalar sign, Schur positivity and
Goal058/RH remain open. Request #8 investigates that subsequent analytic
front. An outcome of this audit must not be described as ground tracking
proved or the entire Fokas route killed.

This audit uses the original objective's explicit proof-or-obstacle outcome;
it does not replace it by success of the finite m2 certificate. The reviewed
source-family obstruction is the decisive evidence for the obstacle branch.

## Independent completion-evidence check

Native read-only reviewer /root/sign_algebra_review independently inspected
the evidence at e4e5bc3b against the original objective. Its conclusion was
that the explicit exact-obstacle alternative is met, under the accepted
source/hmode inputs, for the fixed-beta consumer only. It expressly excluded
Lean admission, source-rate closure, cellwise sign and general tracking.
The root separately verified ordinary Git remote readback, packet hashes and
the absence of its own sends; this is not a provider transport attestation.
