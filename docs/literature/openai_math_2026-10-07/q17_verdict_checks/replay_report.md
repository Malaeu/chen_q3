# Q17 verdict replay report

Date: 2026-10-25

## Inputs and extraction

The downloaded original at `/Users/emalam/Downloads/PROSHKA_CCM_ZERO_SELECTIVE_PAIR_Q17_VERDICT_2026-10-25.md` is byte-identical to the repository copy: 89,445 bytes, SHA-256 `5d6616bd696887491170b847d09f1afd4d84f8581498264929c505732e73b35b`.

Six supplied Appendix A/B files were extracted by their `FILE_BEGIN` / `FILE_END` markers into `embedded/`, retaining the body bytes, including the terminal LF. The literal Appendix C JSON replay summary is also saved as `embedded/markdown_check.json`. The S1 artifact is 6,850 bytes and SHA-256 `f2911c38717dd5cf711ea422d232abf9c4dabcd2bc92428946412c3d16f00a06`.

The request packet is 126,407 bytes, 1,919 LF, SHA-256 `b26a7672a0aeb4049f4e42e157014a4c318f788ed299d52f0ee728623de51245`. The embedded seven-body manifest passed, and each of the seven packet bodies matched its named repository source file byte-for-byte.

## Commands and results

Interpreter: `/Users/emalam/GitHub/riemannn/riemann_env/bin/python`; Python `3.13.17`; SymPy `1.14.0`.

1. `/Users/emalam/GitHub/riemannn/riemann_env/bin/python replay/verify_sources.py /Users/emalam/GitHub/rh_lean_01_2026/docs/literature/openai_math_2026-10-07/PROSHKA_CCM_ZERO_SELECTIVE_PAIR_Q17_2026-10-25.txt`
   - Exit 0.
   - `PASS_BYTE_EXACT_PACKET_AND_SEVEN_BODIES`; 7/7 embedded bodies validated.
   - Generated `replay/source_verification.json` is byte-identical to `embedded/source_verification.json` (2,284 bytes; SHA-256 `dcf3419cd758d037509127b707c235db4212aac5abb13bc43f701a0e14d33b2c`). Captured stdout is byte-identical to the generated JSON.

2. `/Users/emalam/GitHub/riemannn/riemann_env/bin/python replay/check_q17.py`
   - Exit 0.
   - `PASS_EXACT_LOCAL_ALGEBRA_NOT_RH_OR_ASYMPTOTIC_CERTIFICATE`; SymPy reports 354 exact control cases.
   - Generated `replay/results.json` is byte-identical to `embedded/results.json` (1,209 bytes; SHA-256 `1bb32fd44d072c13a08a7279592d81e31067e37ae431a25aeb459a44ab7a1406`). Captured stdout is byte-identical to the generated JSON.

The 354 controls use no hypothetical zero numerical values; compute no actual CCM spectrum; and run neither Lean nor Arb. These checks validate the supplied finite algebra and source bytes. They do not certify the asymptotic analytic claims, a CCM spectral lower bound, or RH.

## Replay records

- `extraction_manifest.json`: source identities, original/repository comparison, and extracted artifact hashes.
- `replay_verification.json`: exact output comparisons and all seven packet-body/source-file comparisons.
- `embedded/`: literal supplied files and expected JSON outputs.
- `replay/`: byte-identical runnable scripts, captured stdout, and generated JSON outputs.
