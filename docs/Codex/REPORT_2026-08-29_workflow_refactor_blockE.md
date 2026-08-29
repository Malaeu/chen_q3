# WORKFLOW REFACTOR — BLOCK E

```yaml
status: DONE
block: E
closes: [WORKFLOW_BLOCK_E_ROUTEB_BUILD_COVERAGE]
opens: [WORKFLOW_BLOCK_F_UNIFIED_RUNTIME]
```

The combined build graph was measured before changing `lakefile.toml`.
At commit `c0316cb8`, the explicit union of target `Q3` and all 367 tracked
`Q3.Proofs.RouteB.*` modules completed successfully:

```text
Build completed successfully (8181 jobs).
real 882.37
build_status=0
```

For comparison, the default `Q3` target alone completed 7814 jobs. The union is
therefore 367 jobs larger in this checkout; the graph is not treated as an
additive sum. The measurement used the canonical cached checkout. Its working
tree contained pre-existing foreign Lean edits, while the target list itself was
derived from committed `HEAD`; this is recorded rather than promoted into a
clean-tree proof claim.

After the measurement, the `Q3` library globs were changed from bare `Q3` to:

```toml
globs = ["Q3", "Q3.Proofs.RouteB.+"]
```

Thus the existing default target now includes the entire RouteB subtree without
creating a second library or selector. A regression plant checks both an
existing RouteB module and a hypothetical future nested module, and separately
proves that bare `Q3` is not accepted as subtree coverage.
