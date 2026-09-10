# Instruction issues

## 2026-09-09 — autonomous Proshka dispatch versus exact push approval

- Sources: current owner's explicit delegation (Codex decides when/what to send to Proshka); AGENTS.md, `ADVISORY v1 ship rule`; `docs/CODEX_AS_SECOND_BODY.md` sections 1, 4, 5.
- Concrete effect: `bind_request.py --no-push --commit-prefix '[Codex][rh_clean][SCHUR]'` created request e11338a3a9132c88895b565d74ce189503d1c642 and binding 22a3b598d31d0b0cc7af0ad16ee80465de65aa09. Automatic approval review rejected `git push origin rh_clean`, interpreting the delegation as insufficient exact-payload push approval.
- Status: exact two-commit approval requested; no alternate transport used to bypass the rejection. Other authorized work continues.
- Proposed resolution: obtain explicit approval for this exact push; separately reconcile the owner-delegated dispatch rule and exact-payload push rule when the owner reviews instruction issues. No policy file changed by this task.

- Resolution 2026-09-09: after the owner explicitly requested repair of the publication problem and continuation, the exact three-commit push to `993ae9cdbbae6576692a9f71eb71a969ff67036a` passed automatic approval review and completed. SCHUR attachment and locator were delivered in canonical chat `6a8c3e2a-df50-83eb-b53d-dd4cc46f646f`; natural reasoning start observed. No approval policy was changed or bypassed.

## 2026-09-10 — standing authorization for the Proshka work loop

- Sources: owner's direct request to rewrite GOAL so work with Proshka proceeds automatically without repeated go; docs/Codex/GOAL.md section 5 and queue previously required a separate go for BRIDGE.
- Resolution: explicit task-scoped standing authorization is recorded in GOAL section 1.1 and the current queue entry. It covers preparation, verified commits/non-force pushes, project request attachments/messages to Proshka, watch and intake. Historical pinned requests remain unchanged. The existing phase transport, proof verification and owner-only final claim remain in force.
- Platform boundary: previous push attempts were rejected by automatic approval review even after a standing grant. The later exact owner approval allowed the ordinary push check; remote c7271cae was verified. A goal edit cannot guarantee platform approval or authorize evasion of a future rejection.
