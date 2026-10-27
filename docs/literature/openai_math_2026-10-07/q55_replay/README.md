# Q55 local replay

## Reproduction

Independent q55_replay executed the inspected four-asset replayer: exit0,
semantic_replay=true, all4 asset hashes and9 source frames match.
115 rational matrix entries, exact complex pairing/constant shift/polynomial
return,5 binary64 diagnostic cases and5 planted violations passed.
json_byte_identical=false:25 binary64 strings differ, maximum absolute
difference1.7763568394002505e-15 (comparison tolerance5e-11). Exact sections
and source manifests match. Original JSON6481bytes; local output6477bytes.
No interval or cofinal certificate follows from those diagnostics.
Assets and generated output preserved in q55_replay/.

Command: python3 q55_replay/replay_q55.py PROSHKA_CCM_Q55_DIRECT_HILBERT_PERRON_VERDICT_2026-10-27.md PROSHKA_CCM_Q55_FRESH_CHAT_CONTINUATION_2026-10-27.txt q55_replay
