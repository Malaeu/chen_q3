# Aristotle April project inventory — 2026-07-22

Scope: read-only inventory through `aristotlelib` 2.1.0 using the API key of the
local Codex environment.  No project was submitted, modified, or cancelled.

## Counts

| Creation date | Projects |
| --- | ---: |
| 2026-04-02 | 296 |
| 2026-04-11 | 1 |
| 2026-04-13 | 1 |
| 2026-04-19 | 1 |
| **Total** | **299** |

All 299 projects currently report `IDLE`.  Of these, 288 report both
`has_input = true` and `has_files = true`; 11 April-2 records report both flags
false and have UUID-only descriptions, consistent with empty/reference
records rather than downloadable proof outputs.  `IDLE` is an API lifecycle
state, not a hole scan, a Lean build, or a proof certificate.

The complete mechanical export is
`ARISTOTLE_APRIL_PROJECT_INVENTORY_2026-07-22.csv`.

## Later-April targets

- `67d09804-a379-4bcd-9535-3ed1c44068ec` —
  `Formalize d2g25_fejer_shrinking_target_2026_04_11.md`.
- `2f8d588f-bba6-42aa-adc5-7cf1f73837bb` —
  `Formalize po3a_4_outer_invariance_minimal_2026_04_13.md`.
- `d34c1795-0f57-40d4-b4b1-a457a81068e8` —
  `Formalize po3a_a0_double_telescoping_2026_04_19.md`.

## Account boundary

The recovered browser project
`16535289-f016-4f62-bfbd-be83d826b4da` is not readable with the local API key:
`Project.from_id` returns HTTP 403.  Therefore the browser session and the
local Aristotle API key must be treated as distinct authority channels until
their account identity is explicitly reconciled.

## Fail-closed interpretation

This inventory establishes only project IDs, dates, lifecycle state, and file
availability.  Any candidate result must still be downloaded, scanned for
`sorry`/`admit`/`exact?`, and checked locally with the pinned Lean project
before integration.
