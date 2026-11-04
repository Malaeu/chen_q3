# Verbatim Appendix A replay

DIAG_NOT_INTERVAL. The executable appendix was extracted and executed **without modification**. No formulas, seeds, precision settings, epsilon values or thresholds were changed. No source matrices or eigensystems were read or saved.

Input: `INPUT_VERDICT.md`, pinned verdict at f96a9072.

- Input Git blob: `7cf72ea5ae3f3370eee05b9cc688887e10c37852`.
- Input SHA256: `9c31d9f713255ff90a2e813fee1f55a3e3f3ffca612ca55d4bfe1d2e57a9d9f2`.
- Extracted executable SHA256: `0ce6fd6483229146c0af0fcff282ba472ea2aa3ccbfcd5939e5a0128cec6e5c5`.
- Published raw receipt SHA256: `2affe81bd46f6b18addc0fba026426d0fdf55367adc5223e0db95f44195339e7`.

Extraction used exactly the verdict's algorithm: locate `<!-- BEGIN_EXECUTABLE_DIAG -->`, locate the following Python fence, take all text through the next closing fence, and append one final newline. `appendix_a.py` and the executed copy in the isolated runtime directory have identical bytes; this equality was checked again immediately before the published replay.

The replay command was `python appendix_a.py`, with working directory `/workspace/source_cayley/appendix_runtime`. The script itself writes `diag_results.json` adjacent to its executable. That file was copied byte-for-byte to `APPENDIX_REPLAY.json`; the raw JSON was not wrapped, reformatted or supplemented.

Execution environment: Python3.12.14, mpmath1.3.0. The code's own decimal precisions45 and70 and epsilon values0.001 and0.0001 were retained. Published replay initiation:2026-11-04T18:01:03.117859+00:00; raw receipt copied:2026-11-04T18:01:17.192567+00:00. The script reports elapsed6.6621150499995565 seconds. Process exit code0; all ten progress records completed; raw status is `DIAG_NOT_INTERVAL` with ten records.

## Chronology and unused initial execution

Registration a1919fbf165da30b9cc4cbd2575a6f43be5fb6ed preceded the numerical work. An initial parallel appendix execution occurred prematurely relative to the intended **independent-implementation-before-appendix** ordering. Its receipt was quarantined as unused local provenance at `appendix_runtime/unused_initial_diag_results.json`; it is not the published receipt and no numerical values from it were sent to the independent implementer or used to choose formulas, gates or design. An initially copied output receipt was removed immediately when the ordering issue was identified.

The parent then explicitly confirmed that its independent implementation was frozen and its numerical execution had completed before authorizing a second verbatim appendix execution. The published raw receipt is exclusively this subsequent replay. The initial run is not counted as an independent confirmation or used as mathematical evidence. The executable was unchanged between runs.

The appendix contains point diagnostics rather than interval certificates and does not itself assert the parent's separate fixed audit gates. This artifact records faithful extraction and execution; comparison with the independently frozen implementation and application of those gates are separate parent-owned steps. No repair, route-state change or RH export is made here.
