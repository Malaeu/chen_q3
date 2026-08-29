# WORKFLOW REFACTOR — BLOCK B

```yaml
status: DONE
block: B
closes: [SESSION_CLOSE_MISSING]
opens: [WORKFLOW_BLOCK_C_PHASE_CLOSE]
```

`specs_docs/session_close.py` is the missing close half. It consumes Block A,
repairs only stale repairable artifacts when explicitly run with `--repair`,
requires the kernel gate for owned Lean paths, writes an atomic session-protocol
skeleton, and splits dirty paths into owned and foreign sets. Foreign paths are
preserved and are not reported as our failure.

It never stages, commits, pushes, publishes, or changes mathematical status.
Residual stale/manual states return nonzero. Two consecutive fresh runs execute
no generators and create no repository diff.

Validation: four dependency/session-close plants PASS; real clean-worktree close
reported all three derived artifacts FRESH and emitted a protocol skeleton.
