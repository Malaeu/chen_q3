---
name: alias-hunt
description: 'Find published proofs of one exact mathematical mechanism under other names or in other fields. Return source-verified candidates with quotes, locators, mappings, and an honest CLOSES/OPENS decision. Triggers: /alias-hunt, «пробей под другими именами», «кто-то это уже доказывал», "search the literature for this mechanism", "same object under another name".'
---

# alias-hunt

Use this skill for one exact object, not for a broad topic or a novelty claim. The
object may be an identity, inequality, operator, kernel, construction, or theorem
mechanism.

## Startup and reconciliation

First run the canonical read-only plan:
`python3 orchestrator/workflow_runtime.py plan`.
Read its owner, operation, search-receipt/output, and source-pin observations.
Until the team continuation card is activated, obtain the missing observations
from `docs/Codex/RESUME.md` and the owning task's ledger; do not invent them.
Establish the current owner and current operation before creating
anything. Reconcile any existing `BRIEF.md`, report, receipt, query, or no-hit
and error result; never create a replacement brief before that check. The
durable assigned report area is an existing project area such as
`docs/routeB_bus/` or a named protocol. Worker-local evidence is only a staging
area: the root owner must copy it into the assigned area and hash-check it.

## Intake gate

This is a read-only discovery route. Require an already saved, source-pinned
brief in the assigned report area or protocol; an existing report section may
serve as that brief. If it is missing or incomplete, return `BRIEF_REQUIRED`
with the missing fields. The owning task prepares it as a separate authorized
source-writing action before invoking discovery. This skill never creates,
updates or copies a shared brief or report. The input brief contains:

1. the formula in the project's notation, including normalization and a source
   locator;
2. facts already proved, with theorem or formula locators;
3. an explicit negative control outside the intended class, plus the hypothesis
   on which the naive mechanism should fail;
4. one or two own rewrites, marked `UNVERIFIED`, used only as search hints.

Do the registered `ask.sh` shelf query for three to five object names first,
unless the reconciled receipt already proves that exact query was run. Reuse
the existing source, query, and result when the input is unchanged; do not
repeat an unchanged query without new evidence or a new dictionary. Preserve
the recorded error or no-hits status. Read the DOI/PDF shelf and other local
evidence before any external search.
`INCOMPLETE` means that this workflow or evidence is unfinished; it does not
mean that there were no hits. A missing source, hash, quote, or locator is
`UNVERIFIED`, never an absence claim.

## Object dictionaries and routing

Translate the object into at least three dictionaries of object names, not three
synonyms for a topic. For example, use operator language (Gram, Hankel,
Toeplitz, moment, or translate-space terms), special-function language (total
positivity, Pólya-frequency, Turán, or Jensen terms), and a probability/physics
or domain-specific language (reflection positivity, covariance, complete
monotonicity, or frames). Replace these with object-specific dictionaries when
appropriate. Run the dictionary passes sequentially or in a bounded batch.
Dictionary count and worker count are separate: three dictionaries do not
require three workers.

Capacity comes from the canonical plan and `GOAL`. Before team activation keep
at most two live children, normally one researcher plus the reserved reviewer
when review is needed. After activation, at most three live children are
permitted: two researchers plus the reserved reviewer, with no descendants. A
native `gpt-5.6-luna/max` worker may be used only after actual capacity is
observed; a requested model or chat wakeup is not evidence of activation.

Supplier mode requires all of the following before dispatch: the exact target,
the exact downstream consumer, the weakest interface that consumer can spend,
and a registered supplier-preflight route. Actually run that registered
supplier-preflight and retain its receipt before dispatch; having a route is not
enough. If the object is source-pinned but the target or consumer is not bound,
exploratory discovery may proceed within the existing bounded owner grant. Return
`INCOMPLETE_NO_CONSUMABLE_TARGET`, name the missing denominator (target, consumer,
edge, or registry field), and report source-verified candidates with that limit.
There is no `CLOSES/OPENS` line, semantic admission, proof admission, or new goal.

Inspect the current tool manifest and capabilities before choosing a search
tool; never assume `WebSearch` exists. Reserve the independent reviewer slot;
researchers have no descendants.

Return an intake manifest to the root owner for any shared writes, shelf downloads,
source registration or index refresh. Those are separate owner actions, outside
this read-only invocation, using the existing authorized writer routes/epoch and
exact preimage checks. Destinations are existing usage cards, `REFERENCES`,
`docs/CHAT_DIGESTS`, and the issue queue when needed.
Researchers are read-only and may save only explicitly assigned local evidence.
They must not edit project state, registrations, shared ledgers, or reports.

## Candidate evidence contract

Every candidate that enters a report must have:

- a source actually fetched or present locally, its URL/identifier, and a
  recorded SHA-256 hash;
- a verbatim quote with a precise locator (section, theorem, page, or line);
- an explicit mapping of variables, domains, normalization, and quantifiers;
- the theorem strength: exact fit, conditional result, partial analogue, or
  diagnostic only, with what the source does not establish;
- the candidate's hypotheses mapped against the explicit negative control.

Reject a candidate with any missing field. Unverified discoveries are excluded
leads with an explicit reason; they are never `VERIFIED` candidates. Only the
orchestrator may label a candidate `VERIFIED`, after independently rereading
the local quoted source and checking the variable/domain/normalization/
quantifier mapping. A confidence score is a search heuristic, never acceptance.
Numerical checks are separately labelled `DIAGNOSTIC`; they can expose a
mismatch but cannot substitute for the source theorem or identity proof and
never prove a universal identity. If sources conflict, audit their exact
hypotheses, domains, normalizations, and source versions; use a certified
relevant counterexample when one is available rather than averaging the claims.

## Search, continuity, and writes

Autonomous external search is allowed only when the mechanism remains genuinely
unresolved after the shelf review. Record why the shelf is insufficient, what
new information is expected, and the bounded stopping condition. Reuse the same
assignment/run after compaction or restart. A missing receipt is not a reason
for an automatic retry.

Include observed workflow defects in the returned manifest for the existing
issue cycle. This skill never admits a proof or creates a goal. The manifest
proposes one batched refresh through the registered route only if the later
owner intake changes indexed source bytes. This invocation never runs refresh
or performs direct `paper.sh` writes.

The report lists candidates, exact mappings, checks, rejected branches, and the
next bounded test. Emit `CLOSES/OPENS` only for a source-verified exact consumer
fit; otherwise state the unresolved or diagnostic status and preserve the
missing evidence.
`VERIFIED` here means verified discovery evidence, not accepted mathematics.
Any proposed CLOSES remains a proposal until the existing independent review,
parent check and canonical acceptance gates are completed on the exact sources.

In reported 2026-09-11 search, three of eight proposed findings were already on
shelf; inspect shelf first. This is a dated reported lesson, not a current
mathematical choice or a prevalence claim.

The skill does not dispatch Proshka, edit `TOOLS.yaml`, commit, or push.
