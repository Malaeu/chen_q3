# Tao 2026, "Mathematics in the age of AI" — usage cards

Terence Tao, arXiv:2608.16753v1 [math.HO], 17 August 2026. Essay based on a
public lecture at the 2026 International Congress of Mathematicians, 13 pages.
PDF: `pdfs/tao_mathematics_age_of_ai_2026_annotated.pdf` — **the owner's own
copy, carrying his annotations**; the file went through `docs/_inbox` on
2026-08-20 and was dispersed here on 2026-08-21.

⚠️ The annotations could not be extracted separately: the file was rewritten by
`pdf-lib`, and no PDF library is installed here to read annotation objects. The
owner's marks are visible in the rendered pages and are **not** reproduced in
this card. If they matter, they must be read from the pages.

This is not a Route B mathematical source. It carries no theorem we consume.
It is carded because it bears directly on `docs/PUBLICATION_PLAN.md` and on how
this project must present itself.

---

## §7 "Proof scarcity and proof abundance" — printed p. 9

VERBATIM (the core of the section):
"If the Working Hypothesis holds, then in the absence of suitable policy and
cultural changes, significant 'impedance mismatches' — or, to use a less
flattering metaphor, proof indigestion — will emerge all along the pipeline …
AI-generated proofs will accumulate faster than they can be verified; verified
AI-generated proofs will accumulate faster than they can be given a readable
write-up; AI-generated proofs, even those required to be both correct and well
written, will overwhelm a traditional peer review system that depends on
volunteer expert labor; and even the published proofs will be too numerous for
the community to work into definitive form."

"In short, we will transition from an era of proof scarcity to an era of proof
abundance. Most of our institutions — journals, priority conventions, hiring
and promotion criteria, prizes, the very notion of a research program — were
designed under the assumption of scarcity, and it should not surprise us if
they behave poorly under abundance."

K7-TAG: ESSAY / POSITION (an argued position, not a theorem)

WHAT IT MEANS FOR US: our own pipeline is the one he describes, run at small
scale. The kernel gives verification for free, so the first mismatch does not
bite us — but the second does. Ten kernel-green nodes exist in this repository
and exactly one has a human-readable write-up. `PUBLICATION_PLAN.md` calls that
the second layer; this essay says the second layer is where the whole community
will jam.

---

## §8 "From goals to recommendations" — the Leiden Declaration, four recommendations

The essay does not propose its own program. It points to the **Leiden
Declaration on Artificial Intelligence and Mathematics** (June 2, 2026,
endorsed by the International Mathematical Union, 23 recommendations, arising
from a 2025 Lorentz Center workshop) and quotes four addressed to individual
mathematicians. Three of the four apply to us directly.

### 1. Disclose tool use

VERBATIM: "Transparently disclose the use of automated tools, including large
language models, machine learning systems, proof assistants, and other
mathematical software. Include a 'Tool and computational resource disclosure'
section in your papers … When acting as a reviewer, abide by publisher
guidelines."

And the sharp line: "The scenario to be avoided at all costs is one in which
authors use AI tools covertly to aid their work, but conceal that usage in
order to avoid criticism from their peers."

**ACTIONABLE FOR US, and it is not optional.** Our paper needs a *Tool and
computational resource disclosure* section naming: Lean 4 and Mathlib, the
kernel gate, the agent bodies that wrote sources and verdicts, and the fact
that a substantial part of the formalization was machine-authored under human
direction. Recorded into `PUBLICATION_PLAN.md` by this dispersal.

### 2. Support the needs of reviewing

VERBATIM: "Make it easier for your peers to review your work by disclosing tool
use, giving precise and complete references to previous results, and providing
**formal proofs where feasible and appropriate**."

This one we already satisfy by construction — the artifact *is* the formal
proof. It is worth saying plainly in the paper that the reviewer can run the
kernel rather than trust the prose.

### 3. Affirm the humanity of authorship

VERBATIM: "Credit and responsibility continue to belong to humans within the
mathematical community and should not be given to automated systems.
Artificial intelligence may obscure, but does not replace, the collective human
labor behind a result."

**This is independently the owner's own standing rule** (memory:
`author-is-ylsha-not-the-machine`, 2026-08-19): the author is the owner, the
body that typed is irrelevant. The declaration and the owner arrived at the
same position separately. Our commit messages, which never carry AI attribution
or co-author lines, already implement it.

---

## The essay's broader claim, recorded because it cuts against our instincts

VERBATIM: "we need to decrease the emphasis that our culture places on proof
generation, and in particular on being the 'first' to solve a problem, and
correspondingly increase the emphasis we place on proof digestion: exposition,
refereeing, publication, and canonicalization."

For a project whose owner has said plainly that he wants the Clay prize, this
is the uncomfortable half. It does not argue against wanting it. It argues that
the scarce resource is shifting, and that a formalized result nobody can read
is not yet a contribution. `PUBLICATION_PLAN.md`'s three-layer model — machine
skeleton, human prose, full LaTeX — is exactly the digestion work he means, and
this essay is the reason not to postpone layer two indefinitely.

---

## NOT READ / NOT VERIFIED
- §§1–6 were skimmed for structure only; the case study on problem solving
  (§6, the longest section) was not read.
- The Leiden Declaration itself [11] was not fetched; only the four
  recommendations Tao quotes are known here. **The remaining nineteen are
  unread**, and at least the ones addressed to organizations may bear on the
  Clay submission route.
- Bessis, "The fall of the theorem economy" [2], cited approvingly, unread.
- Avigad, "Mathematics and the formal turn", Bull. AMS 61 (2024) [1], cited as
  the pointer for recent formalization developments, unread — this one is
  probably worth having.
- The owner's own annotations in the PDF, as noted at the top.
