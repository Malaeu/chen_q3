# Style pass — change log

Source (untouched): `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/paper_weil/sections/`
Edited copies: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/paper_weil/style_pass/sections/`

Method: `humanizer-academic` (AI-pattern removal) first, then `sciwrite`
(`manuscript-writing-review`, five passes), per `~/.claude/docs/antislop_routing.md`.
No mathematics, number, symbol, citation key, `\label`/`\ref`, or environment was
altered. Verified mechanically: brace balance, `$` parity, environment stack,
and the full sets of `\cite`/`\label`/`\Cref`/`\eqref` arguments are identical to
the originals in every file; a trial `pdflatex` + `bibtex` + 2×`pdflatex` run over
the copies (in `/tmp`, main.tex untouched) completes with 0 undefined references.

**Totals: 15 changes — 1 `[humanizer-academic]`, 14 `[sciwrite]`.**

| File | Changes | humanizer-academic | sciwrite |
|---|---|---|---|
| abstract.tex | 1 | 0 | 1 |
| intro.tex | 3 | 0 | 3 |
| setup.tex | 2 | 0 | 2 |
| canonical.tex | 0 | 0 | 0 |
| groundstate.tex | 3 | 0 | 3 |
| obstruction.tex | 2 | 0 | 2 |
| windows.tex | 1 | 0 | 1 |
| ledger.tex | 2 | 1 | 1 |
| disclosure.tex | 1 | 0 | 1 |
| app_constants.tex | 0 | 0 | 0 |
| app_lean.tex | 0 | 0 | 0 |

The manuscript arrived already clean of the usual markers: zero em dashes, zero
`-ize`/`-ization` spellings, no formulaic openers, no empty significance claims,
no "it is worth noting", no promotional self-citation, and exactly one word from
the Kobak excess-vocabulary list ("corroborate"). The AI-pattern pass therefore
produced one change; the rest is clarity work.

---

## abstract.tex

1. **old:** `... are formalised in Lean~4 against Mathlib; the use of automated reasoning tools is disclosed.`
   **new:** `... are formalised in Lean~4 against Mathlib; we disclose how automated reasoning tools were used.`
   — passive with a known actor; the section it points to (`sec:disclosure`) is written in the first person. `[sciwrite]` Pass 2

---

## intro.tex

2. **old:** `... and the finite window matrices of Connes, Consani and Moscovici \cite{CCM-ZST-2025}, whose bottoms ...`
   **new:** `... and the finite window matrices of Connes, Consani and Moscovici (CCM) \cite{CCM-ZST-2025}, whose bottoms ...`
   — the abbreviation "CCM" is used unintroduced in `canonical.tex` (definition title), `canonical.tex` body and `windows.tex`; defined here at first mention of the authors. `[sciwrite]` Pass 4 (acronym austerity)

3. **old:** `The signed kernel itself is not new: Suzuki writes the Weil form as ...`
   **new:** `The signed distributional kernel itself is not new: Suzuki writes the Weil form as ...`
   — one object, three names in the manuscript: "signed jump kernel" (the paper's own, §GS), "signed distributional kernel" (the abstract's name for Suzuki's), "signed kernel" (here). Aligned with the abstract, which is the name used for the attributed object. `[sciwrite]` Pass 4 (Banana Rule)

4. **old:** `The remaining sections record what the finite windows do and do not show (\Cref{sec:windows}), including an exact second-jet formula for the prolate trial of \cite{CCM-ZST-2025} and the agreement of certified window bottoms with the decay law of \cite{XUEFENGZHU-2026}; a ledger of excluded proof shapes with the theorem that excludes each (\Cref{sec:ledger}); the precise open problem and the two representations it leaves open; and the provenance of every statement, including which statements are machine-checked in Lean~4 (the core of the obstruction theorem is) and how automated reasoning tools were used (\Cref{sec:disclosure}).`
   **new:** `The remaining sections record what the finite windows do and do not show (\Cref{sec:windows}), including an exact second-jet formula for the prolate trial of \cite{CCM-ZST-2025} and the agreement of certified window bottoms with the decay law of \cite{XUEFENGZHU-2026}. They also record a ledger of excluded proof shapes with the theorem that excludes each (\Cref{sec:ledger}), the precise open problem and the two representations it leaves open, and the provenance of every statement: which statements are machine-checked in Lean~4 (the core of the obstruction theorem is) and how automated reasoning tools were used (\Cref{sec:disclosure}).`
   — one 78-word sentence carrying a four-item semicolon list whose last item itself branches; split at the first item, semicolons demoted to commas, `including which statements` turned into a colon. No item added, dropped or reordered. `[sciwrite]` Pass 3

---

## setup.tex

5. **old:** `The normalisation of \eqref{eq:Q} was checked against \eqref{eq:EF} numerically on the canonical test of \Cref{sec:canonical} (\Cref{app:constants}).`
   **new:** `We checked the normalisation of \eqref{eq:Q} against \eqref{eq:EF} numerically on the canonical test of \Cref{sec:canonical} (\Cref{app:constants}).`
   — passive with a known actor; the parallel numerical checks in §GS and §canonical already read "we verified". `[sciwrite]` Pass 2

6. **old:** `Restricting $\Q$ to tests supported in $[\dots]$ and expanding in the prolate basis of Connes--Consani--Moscovici \cite{CCM-ZST-2025} (the prolate operator and its relation to the zeros is the subject of \cite{ConnesMoscovici2021}) produces the finite matrices $K(m,N)$ studied there (and, in additive coordinates, in \cite{XUEFENGZHU-2026}).`
   **new:** `Restricting $\Q$ to tests supported in $[\dots]$ and expanding in the prolate basis of Connes--Consani--Moscovici \cite{CCM-ZST-2025} produces the finite matrices $K(m,N)$ studied there, and, in additive coordinates, in \cite{XUEFENGZHU-2026}; the prolate operator and its relation to the zeros is the subject of \cite{ConnesMoscovici2021}.`
   — buried predicate (35 words between subject and `produces`) caused by a parenthetical wedged in front of the verb, plus a second parenthetical at the tail. The `ConnesMoscovici2021` aside moves out to a trailing clause; the predicate gap drops to 22 words. `[sciwrite]` Pass 3

---

## canonical.tex

No changes. (The only candidates — the `\cite`-dense provenance sentence at "…is \cite[Lemma 7.1]{CCM-ZST-2025} in the logarithmic variable" and the numerical remark — are citation-heavy by genre and precise as written.)

---

## groundstate.tex

7. **old:** `... an archimedean density with a $\tfrac12\mathrm{Pf}(1/|t|)$ singularity; the following identity is the ground-state version of that kernel ...`
   **new:** `... an archimedean density with a $\tfrac12\mathrm{Pf}(1/|t|)$ singularity. The following identity is the ground-state version of that kernel ...`
   — 71-word sentence carrying a semicolon and then a colon; split at the semicolon, where the subject changes from Suzuki's kernel to this paper's identity. `[sciwrite]` Pass 3

8. **old:** `We also verified \eqref{eq:GS} numerically on a non-trivial $s$`
   **new:** `We also verified \eqref{eq:GS} numerically on a nontrivial $s$`
   — the manuscript's dominant form is the closed prefix (`nonnegative` ×8, `nonzero` ×3, `nonlocal` ×3, `noncompact`). `[sciwrite]` Pass 4

9. **old:** `... so no sign of $\sigma$ follows without RH; and non-negativity of $\sigma$ would in any case be a statement about the diagonal ...`
   **new:** `... so no sign of $\sigma$ follows without RH. Nonnegativity of $\sigma$ would in any case be a statement about the diagonal ...`
   — `; and` joining two independent clauses; and `non-negativity` clashes directly with the eight unhyphenated `nonnegative` in the same paper. `[sciwrite]` Pass 3 + Pass 4

---

## obstruction.tex

10. **old:** `The noncompact ratio $r_q$ is never inserted into the hypothesis; only the compact $s_{q,R}$ are, and the limit is taken on the certificate side.`
    **new:** `We never insert the noncompact ratio $r_q$ into the hypothesis; only the compact $s_{q,R}$ enter, and the limit is taken on the certificate side.`
    — passive hiding the actor in a sentence whose whole point is what the authors do and do not do; the elliptical `only the compact $s_{q,R}$ are` also had to borrow its verb from the passive. The third clause stays passive on purpose (the limit is a fact about the argument, not an act). `[sciwrite]` Pass 2

11. **old:** `The consequence for proof design is that positivity of $\Q$ cannot be established by proving a fixed $\Xf$-margin on a dense family of tests and passing to the limit: ...`
    **new:** `For proof design this means that positivity of $\Q$ cannot be established by proving a fixed $\Xf$-margin on a dense family of tests and passing to the limit: ...`
    — `The consequence ... is that` is a smothered verb; the frame "for proof design" is kept because it marks the sentence as guidance rather than theorem. `[sciwrite]` Pass 1

---

## windows.tex

12. **old:** `Every premise of this kind is the conclusion in disguise, and the numbers of this section are diagnostics for the location of the difficulty, not steps toward its removal.`
    **new:** `Every premise of this kind is the conclusion in disguise. The numbers of this section are diagnostics for the location of the difficulty, not steps toward its removal.`
    — two unrelated assertions joined by `and`; the second is the section's closing claim and reads harder for being subordinated. `[sciwrite]` Pass 3

---

## ledger.tex

13. **old:** `Two external facts corroborate the zero-margin picture from outside our construction: ...`
    **new:** `Two external facts support the zero-margin picture from outside our construction: ...`
    — the only word in the manuscript from the excess-vocabulary list; "support" carries the same strength without the inflation. (The skill's default swap, "is consistent with", would have weakened the claim, so it was not used.) `[humanizer-academic]` A3

14. **old:** `Two representations are not excluded by the results above.`
    **new:** `The results above do not exclude two representations.`
    — passive with the actor named in the same sentence. `[sciwrite]` Pass 2

---

## disclosure.tex

15. **old:** `Several of the proofs in \Cref{sec:obstruction}, in particular \Cref{lem:budget,thm:nominorant}, were first written by such a reviewer in response to a formally specified request and were then independently re-derived from the definitions by a second, blind agent and checked numerically by the author.`
    **new:** `Such a reviewer first wrote several of the proofs in \Cref{sec:obstruction}, in particular \Cref{lem:budget,thm:nominorant}, in response to a formally specified request. A second, blind agent then re-derived them independently from the definitions, and the author checked them numerically.`
    — a 47-word chain of three passives with three different actors, in the paragraph where the actor is precisely what is being disclosed. Split into two sentences, each actor now the subject; the order of events and the qualifiers ("first", "then", "independently", "blind", "numerically") are unchanged. `[sciwrite]` Pass 2 + Pass 3

---

## Glossary — object names and the form settled on

| Object | Form settled on | Note |
|---|---|---|
| Riemann's function, unnormalised | **$\Phi$** | "Riemann's function $\Phi$"; already consistent |
| its $L^2$-normalisation $\Phi/\|\Phi\|_2$ | **canonical test $f_0$** | "canonical test" throughout; no competing name found |
| the paper's own signed measure $\nu$ | **signed jump kernel** | used in intro and §GS; the *measure* is $\nu$, the *kernel* is how it acts |
| Suzuki's $-g''$ | **signed distributional kernel** | abstract's name; intro's bare "signed kernel" aligned to it (change 3) |
| Connes–Consani–Moscovici | **CCM** | now defined at first mention (change 2); spelled out in the abstract |
| eigenvalue $\lambda_1(m,N)$ | **bottom** | "bottom", "bottom eigenvalue", "saturated bottom"; already consistent |
| eigenvector $\xi_1$ | **bottom vector** | never "ground vector"; already consistent |
| CCM's prolate packet $k_\lambda$ | **prolate trial** | full form at paragraph head, "the trial" thereafter; already consistent |
| support interval indexed by $m$ | **window** | "window", "finite window", "wide window"; already consistent |
| one evaluated $(m,N)$ instance | **cell** | distinct from "window", but never defined — see flag F4 |
| a nonnegative lower bound built from stencils | **finite-stencil minorant** (theorem), **local certificate** (prose) | hierarchy already consistent: certificate ⊃ local certificate ⊃ finite-stencil minorant |
| prefix `non-` | **closed**: nonnegative, nonnegativity, nonzero, nonlocal, noncompact, nontrivial | two outliers closed (changes 8, 9); three left — see flag F8 |

---

## Flagged but NOT changed

**F1 — numerical inconsistency between `windows.tex` and `app_constants.tex` (Pass 5, would be CRITICAL).**
`windows.tex`: the least-squares fit gives `(0.019891, 0.00540)` against `(0.019894, 0.005145)`, "the second coefficient to $5\%$".
`app_constants.tex`: `1/(16\pi), 13/(256\pi^2)` = `0.0198944, 0.0051452`, "measured `0.019892, 0.005143`".
The two *measured* pairs disagree (`0.00540` vs `0.005143`), and so do the implied errors (5 % vs 0.04 %). One of the two is stale. Numbers are out of scope for this pass; the author must decide which is current and reconcile the "$5\%$" wording with it.

**F2 — "exact second-jet formula" (intro) vs "we do not prove it" (§windows) (Pass 5 / hedge integrity, HIGH).**
The Introduction advertises "an exact second-jet formula for the prolate trial", while `windows.tex` says of the same equation: "We do not prove \eqref{eq:trialjet} here and present it as a numerical observation with a heuristic derivation." The Introduction reads stronger than the body allows. Dropping "exact" would change claim strength, which this pass is forbidden to do — flagged for the author.

**F3 — abstract: "all its convolutions".**
`prop:radical` proves $f_0*h\in\operatorname{rad}\B$ for $h\in C_c^\infty$; the abstract says "all its convolutions" without the qualifier. A content question, not a style one.

**F4 — "cell" is used five times and never defined (Pass 4).**
`windows.tex`: "certified cells", "our production cells", "the computed cells", "\Cref{tab:jet} records the cells", plus `app_constants` context. It is genuinely a different object from "window" (a window is an $m$; a cell is one evaluated $(m,N)$ pair), so the Banana Rule does not apply — but the reader is never told. Defining it would introduce a proposition, so it is left to the author.

**F5 — `app_lean.tex`: the fourth theorem is missing.**
The table row reads `NoFiniteStencilMinorant … 5 thms`; the paragraph names three (`independence_of_translates`, `stencil_energy_limit_eq_zero`, `no_positive_finite_stencil_minorant`), then jumps to "A fifth theorem exhibits a model …" and closes with "All five declarations report axioms". The fourth is never described.

**F6 — `app_constants.tex`, envelope-constants paragraph: two formulas end in `\ldots` placeholders.**
"Writing $\Phi(x)=4e^{x/2}\sum_n p_0(ne^x\cdot ne^x)\ldots$ is cumbersome; instead put $P_0(y)=4y^2-6y$ so that $4e^{x/2}h(\sqrt y)=e^{x/2}P_0(\pi y)e^{-\pi y}/\ldots$". The sentence says the direct route is cumbersome and then leaves both intermediate displays unfinished. Mathematics — untouched.

**F7 — `groundstate.tex`, display `eq:masses` ends in a comma.**
The last line of the `aligned` block ends `\qquad(\eps\downarrow0),` and the next word starts a new sentence ("The prime atoms weigh less than half …"). The display punctuation should be a full stop. It sits inside the equation environment, so it was left alone.

**F8 — remaining `non-` hyphenation outliers.**
`non-real` (groundstate), `non-degenerate` (canonical), `non-degeneracy` (intro), against the paper's closed `nonnegative`/`nonzero`/`nonlocal`/`noncompact`. Only the two with a direct in-paper clash were closed (`non-negativity` → `nonnegativity`, `non-trivial` → `nontrivial`); the remaining three are standard hyphenated in mathematical usage and closing them ("nonreal") would read worse. Author's call whether to unify.

**F9 — abstract: "We also note that no uniform margin … can exist".**
`prop:trade` is a proved proposition, so "we note" understates it. Strengthening a claim is outside this pass's mandate; flagged only.

**Kept deliberately (WHAT NOT TO CHANGE / Constraints):**

- *Passive where the actor is genuinely irrelevant or the register is methodological:* "All finite-window quantities were computed in interval arithmetic (`arb`, 220–300 decimal digits)"; "Statements that use \eqref{eq:EF} are marked as such"; "Predictions about the outcome of each such round were registered before the round"; "are formalised in Lean~4 against Mathlib".
- *Every hedge:* "We do not prove \eqref{eq:trialjet} here"; "present it as a numerical observation with a heuristic derivation"; "appear to be new"; "To our knowledge … have not appeared before; we would be grateful for references"; "We do not use this extension and leave the measure-theoretic details to the reader"; "We record, without a theorem, why we do not expect this to work"; "A precise impossibility statement would have to specify the class of majorants, and we do not pursue it here"; "this entry is a heuristic, not a theorem of this paper"; "It is tempting to read the saturation as a mechanism"; "Nothing in this paper is a step toward RH in the sense of a new inequality".
- *First person and present tense* throughout (discipline convention).
- *Three-part enumerations that are substantive, not rhythmic:* "the archimedean part …, the pole part, and the prime part"; "the closed form of the density, its sign change …, and the differences $|s(x)-s(x')|^2$"; "as adversarial reviewers …, as drafters of Lean code …, and as literature scouts …".
- *Abstract/introduction overlap* (genre-permitted).
- *All mathematics*, including the informal-looking `(\text{valid; the sum of the four bounds is }|c_A|+11.54)` inside the display in `setup.tex`.
