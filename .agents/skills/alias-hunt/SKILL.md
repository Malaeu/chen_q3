---
name: alias-hunt
description: 'Find proofs or usable partial mechanisms for one mathematical obstruction under other names or in other fields. Use for semantic hunt, cross-domain siblings, missing properties, and return to blocking objects after a bounded failed attempt. Return source-verified mappings, hypotheses and the exact remaining gap.'
---

# alias-hunt

Use this skill for one exact object, not for a broad topic or a novelty claim. The
object may be an identity, inequality, operator, kernel, construction, missing
property, sufficient hypothesis, geometric structure, or theorem mechanism.
Answer an already understood explanatory question directly; do not start a
search merely to restate known mathematics. Plain mode (owner order 2026-09-25):
no `plan`, RESUME, owner/epoch or receipt steps; start from `docs/Codex/NEXT.md`.

## 1. Brief (first step, written by this skill)

Write it at the top of the answer, not as a precondition:

1. the obstruction in two to four plain sentences;
2. the exact formula in project notation, with normalization, domain,
   quantifiers and a source locator;
3. facts already proved, with theorem or formula locators;
4. an explicit negative control outside the intended class, and the hypothesis
   on which the naive mechanism should fail;
5. one or two own rewrites, marked `UNVERIFIED`, used only as search hints.

Locate a worked proof or an explicitly proved part of one: what step rules
out the bad outcome, and which hypothesis makes that step valid? A method name
or a list of papers is not an application argument.

## 2. Semantic return after a failed attempt

After a bounded mathematical attempt yields no new basis or exposes an
obstruction, return BEFORE selecting the next approach:

1. Preserve the return point: exact blocking objects, their joint action,
   the required invariant and the established failure.
2. Describe what the objects do independently of their current names.
   Search alternative representations of the interaction as well as its parts.
   Weight, truncation and conditional expectation, for example, may obstruct
   transfer jointly even when each operation is familiar separately.
3. Mark alternative spaces, dimensions, physical models and hypotheses
   `UNVERIFIED`; name the map back, retained properties and unknown corrections.
4. Use these structural descriptions as new search dictionaries. A new name
   for the same unproved inequality is not new evidence.
5. Select one bounded bridge or research question only after checking the
   source correspondence and identifying what new evidence would change it.

Waiting, a tool error, an unfinished proof, delivery and a build are not failed
mathematical attempts. The owner's mechanism-node plan
(`docs/Codex/PLAN_2026-09-13_REQUIRED_MECHANISM_NODE.md` §2.1–2.2) gives worked detail.

## 3. Partial bridges and exact compensation

Retain a source-verified partial theorem when a concrete completion could help.
Record the proved part, the missing hypothesis or lemma, the exact map to our
source, and one bounded test of that map. A published conjecture remains a
conjecture. When combining methods, prove that each output satisfies the next input.

For a proposed "vortex" or compensation, specify the operation that preserves
the target. In Q=A+B, inserting +C and -C preserves Q but supplies no sign by
itself. A total derivative requires the actual boundary terms and full-domain
integrability. A correction with zero integral need not vanish pointwise.
Never assume an arbitrary constant or an unconstructed positive square root
can pay an unrestricted signed remainder.

For repeated square extraction, separate the entrance from the invariant:
construct the initial positive representation independently, prove preservation
under each elimination, and account for zero pivots. Pairwise positivity or
entrywise Gram domination does not supply that entrance. A stronger sufficient
property may fail without refuting the original target. Worked conditional
example: `docs/Codex/REPORT_2026-09-14_SCHUR_REPEATABILITY.md`.

## 4. Dictionaries and search order

Translate the object into at least three dictionaries of object names, not three
synonyms for a topic: operator language (Gram, Hankel, Toeplitz, moment,
translate-space), special-function language (total positivity, Pólya-frequency,
Turán, Jensen), and a probability/physics or domain-specific language
(reflection positivity, covariance, complete monotonicity, frames). Replace these
with object-specific dictionaries when appropriate.

Search in this order; reuse earlier results for an unchanged query:

1. **Shelf first:** `./ask.sh "<name>"` for three to five object names, then the
   DOI/PDF shelf and `docs/literature/`. On 2026-09-11 three of eight proposed
   findings were already on the shelf. `ASK_STATUS: INCOMPLETE` means the search
   was unfinished, not that nothing exists.
2. **Literature, when the shelf is insufficient** (say why and what you expect):
   - scite MCP `search_literature` (full-text excerpts, citation contexts, retractions);
   - Consensus MCP `search` (claims across papers);
   - `scripts/literature_discovery.py "<query>"` (arXiv + Crossref metadata);
   - web search tools the agent actually has.
3. **Community signal, never evidence:** X via xapi MCP `search_posts_all` /
   `search_news`, or `xurl "/2/tweets/search/recent?query=..."`. Use it to find
   names, preprints and people; fetch the actual paper before citing anything.

Use as many parallel researchers as the task needs; keep one independent
reviewer for any candidate that is claimed to close a gap.

## 5. Candidate evidence contract

Every candidate that enters a report must have:

- a source actually fetched or present locally, its URL/identifier, and a
  SHA-256 hash of the fetched file;
- a verbatim quote with a precise locator (section, theorem, page, or line);
- an explicit mapping of variables, domains, normalization, and quantifiers;
- the theorem strength: exact fit, conditional result, partial analogue, or
  diagnostic only, with what the source does not establish;
- the candidate's hypotheses mapped against the explicit negative control.

A candidate with a missing field is an excluded lead, stated with the reason.
Only after independently rereading the quoted source and checking the mapping
may a candidate be labelled `VERIFIED`; this means verified discovery evidence,
not accepted mathematics. A confidence score is a search heuristic, never
acceptance. Numerical checks are `DIAGNOSTIC`: they can expose a mismatch but
never prove a universal identity. If sources conflict, audit their exact
hypotheses, domains, normalizations and versions; prefer a certified relevant
counterexample to averaging the claims.

## 6. Output

One compact section: plain problem; worked example; decisive mechanism;
hypothesis mapping with PROVED/OPEN/FALSE/INAPPLICABLE status; negative-control
discrimination; rejected branches; one next step with a stopping condition.
Emit `CLOSES/OPENS` only for a source-verified exact fit to a named consumer
(see the roof and open premises in `docs/Codex/NEXT.md`); otherwise state the
unresolved or diagnostic status. Save useful sources to `docs/literature/` and
the finding into the phase's `docs/Progress_Log.md` entry. A proposed CLOSES is
a proposal until independent review and the Lean check confirm it.
