# Instruction issues

## 2026-09-09 — autonomous Proshka dispatch versus exact push approval

- Sources: current owner's explicit delegation (Codex decides when/what to send to Proshka); AGENTS.md, `ADVISORY v1 ship rule`; `docs/CODEX_AS_SECOND_BODY.md` sections 1, 4, 5.
- Concrete effect: `bind_request.py --no-push --commit-prefix '[Codex][rh_clean][SCHUR]'` created request e11338a3a9132c88895b565d74ce189503d1c642 and binding 22a3b598d31d0b0cc7af0ad16ee80465de65aa09. Automatic approval review rejected `git push origin rh_clean`, interpreting the delegation as insufficient exact-payload push approval.
- Status: exact two-commit approval requested; no alternate transport used to bypass the rejection. Other authorized work continues.
- Proposed resolution: obtain explicit approval for this exact push; separately reconcile the owner-delegated dispatch rule and exact-payload push rule when the owner reviews instruction issues. No policy file changed by this task.
