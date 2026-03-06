# Philosophy of Proof: Q3 Lean Formalization

**Author:** Eugen Malamutmann
**Project:** Q3 - Formal Verification of Riemann Hypothesis Proof Structure
**Last Updated:** 2026-03-06

---

## Executive Summary

This document explains our formalization philosophy for the Q3 project. We follow the "explicit reduction" approach recommended by Talia Ringer and the Lean community: **we do NOT claim that Lean "proved RH"**. Instead, we demonstrate that **RH formally follows from a small, explicit set of mathematical statements** that are proven in the Q3 paper.

This approach is:
- **Honest**: We clearly separate what Lean verifies from what requires mathematical trust
- **Transparent**: All dependencies are explicit and traceable
- **Future-proof**: As theorems get added to Mathlib, our axioms can be replaced with proofs
- **Valuable**: It proves the logical structure is correct, even if base lemmas aren't formalized

---

## The Problem with Axioms (Why We Care)

As discussed in the Lean community (David Budden's thread, 2024):

> "Using many axioms makes it hard to verify or take the proof seriously."
> — Jason Rute

> "The ideal is a Lean proof with no extra axioms—that's the point of formal verification."
> — Ben Spitz

> "Prove an explicit reduction or implication to the cited theorem, rather than axiomatizing it."
> — Talia Ringer

The risk: If we just `axiom` everything, critics can say "you just assumed the answer."

---

## Our Approach: Explicit Reduction

### What We Claim

```
┌─────────────────────────────────────────────────────────────────────┐
│  IF these 5 mathematical statements are true (1 classical + 1 project + 3 standard)  │
│  THEN RH is true.                                                  │
│                                                                    │
│  Lean verifies: the logical implication is CORRECT.                │
│  Human verifies: the nonstandard statements match the paper route. │
└─────────────────────────────────────────────────────────────────────┘
```

### What We Do NOT Claim

- ❌ "Lean proved RH"
- ❌ "RH is now machine-verified"
- ❌ "No trust required"

### What We DO Claim

- ✅ "The Q3 proof structure is formally verified"
- ✅ "If the paper's theorems are correct, RH follows"
- ✅ "All logical steps from axioms to RH are machine-checked"

---

## Axiom Classification

As of **2026-03-06**, `#print axioms Q3.Main.RH_of_Weil_and_Q3` reports **5 axioms** total:
3 kernel/standard + 2 project.

Important honesty note:
- the active top-level route is now the shifted-atom paper route, not the old `τ=0` branch;
- the remaining project placeholder is
  `Q3.prime_term_le_at_t_critical_axiom`;
- local repo notes already mark the full `τ`-uniform scalar claim behind that
  placeholder as false-for-now, so the current theorem chain is structurally useful
  but not yet the final credible closed proof object.

### Level 0a: Standard Lean/Mathlib (3) — UNIVERSALLY ACCEPTED
- `propext` — propositional extensionality
- `Classical.choice` — axiom of choice
- `Quot.sound` — quotient soundness

These are part of Lean's foundation. Most Mathlib proofs use them.

### Level 0b: Computation Trust (0) — CLOSED

We eliminated `native_decide` from the PrimeCert table checks, so
`Lean.ofReduceBool` / `Lean.trustCompiler` no longer appear in the main chain.

### Level 1: Classical Results from Literature (1) — ESTABLISHED MATHEMATICS
- `Weil_criterion` — Weil criterion on the full `Weil_cone`: `Q ≥ 0` on `Weil_cone` ⟺ RH

These are well-known results. Citations:
- Weil, A. (1952). "Sur les 'formules explicites' de la théorie des nombres premiers"

**Note:** The following are now THEOREMS (proven from Mathlib/Aristotle):
- `digamma_one_fourth_neg` — Re(ψ(1/4)) < 0 (DLMF 5.4.14, proven via reflection formula)
- `a_star_pos`, `a_star_bdd_on_compact`, `a_star_continuous`, `a_star_even`
- `A1_density_WK_axiom` → closed (A1_density_WK_thm)
- `Q_nonneg_on_atoms_of_A3_Fourier_RKHS` → closed via Q_nonneg_atoms_closure

### Level 2: Active Project Placeholder (1) — TEMPORARY AND MATHEMATICALLY UNSTABLE
- `Q3.prime_term_le_at_t_critical_axiom` — scalar placeholder in
  `Q3/Proofs/Q_nonneg_t_critical.lean` asserting
  `prime_term (phi_shift_critical B τ) ≤ arch_term (phi_shift_critical B τ)`
  for all admissible `(B, τ)`.

This is the only remaining project-specific nonclassical placeholder in the active
shifted-atom RH chain. It currently feeds:
- `Q_phi_shift_nonneg_t_critical`,
- `Q_phi_shift_pair_nonneg_t_critical`,
- `Q_Fejer_heat_atom_nonneg_t_critical`,
- `CompatibilityReduction`,
- `PaperMainlineAtomRoute`,
- `Q3.Main.RH_of_Weil_and_Q3`.

**Important:** theorem names above exist, but they are not yet independent of the
placeholder. So theorem-level packaging is not the same as closure.

### Level 3: Technical Bridge Lemmas (0) — CLOSED

arch/prime Lipschitz bridges are now proven in Lean (no longer axioms).

### Off‑Chain / Legacy Axioms (0 in active main chain)
- `Weil_criterion_tau0`, `prime_cert_margin_from_pathB`, `prime_cert_margin_from_rkhs`
  and the PrimeCert data axioms remain in the tree for legacy `τ=0` and certificate
  branches, but are **not** in the current `Q3.Main` axiom print.
- `Schur_test` remains defined as an axiom in the codebase, but is also off-chain.

---

## Verification Commands

Anyone can verify our axiom dependencies:

```bash
# Clone and build
git clone https://github.com/Malaeu/chen_q3.git
cd chen_q3/full/q3.lean.aristotle
lake build Q3.Main

# Check axioms
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'
```

Expected output:
```
'Q3.Main.RH_of_Weil_and_Q3' depends on axioms: [
  propext,                        -- Level 0a: Standard Lean
  Classical.choice,               -- Level 0a: Standard Lean
  Quot.sound,                     -- Level 0a: Standard Lean
  Q3.Weil_criterion,               -- Level 1: full Weil criterion
  Q3.prime_term_le_at_t_critical_axiom
]
```

---

## Proof Structure Diagram

```
                           RH (Riemann Hypothesis)
                                    ▲
                                    │
                        ┌───────────┴───────────┐
                        │   Weil_criterion      │ ← Level 1 (full Weil cone)
                        │  Q≥0 on Weil_cone ⟺ RH│
                        └───────────┬───────────┘
                                    │
                        ┌───────────┴───────────┐
                        │ PaperMainlineAtomRoute│ ← THEOREM
                        │  Weil_cone → W_K      │
                        └───────────┬───────────┘
                                    │
                        ┌───────────┴───────────┐
                        │ CompatibilityReduction│ ← THEOREM
                        │ shifted atoms → W_K   │
                        └───────────┬───────────┘
                                    │
                        ┌───────────┴───────────┐
                        │ Q_Fejer_heat_atom_    │ ← theorem name
                        │ nonneg_t_critical     │    but still inherits
                        └───────────┬───────────┘    scalar placeholder
                                    │
                        ┌───────────┴───────────┐
                        │ prime_term_le_at_     │ ← Level 2 project placeholder
                        │ t_critical_axiom      │
                        └───────────────────────┘
```

**Key insight:** The boxes marked "THEOREM" are fully machine-checked. The boxes marked "Level X" are our explicit assumptions.

---

## Why This Approach Is Valid

### Per Talia Ringer's Recommendation

> "Prove an explicit reduction or implication to the cited theorem, rather than axiomatizing it, to make dependencies clear until the theorem itself is formalized in Lean."

We do exactly this:
1. Each axiom is **explicitly declared** with its mathematical content
2. Each axiom has a **citation** to where it's proven (paper section or literature)
3. The **logical structure** from axioms to RH is machine-verified
4. There are **no hidden dependencies** — `#print axioms` shows everything

### Per Ben Spitz's Observation

> "It's still valuable to formalize a reduction to existing theorems (e.g., showing your result follows from them), even if those theorems aren't yet in Mathlib."

Our formalization shows: **IF** the Q3 paper's theorems are correct, **THEN** RH follows. This is valuable because:
1. It validates the proof structure
2. It identifies exactly what needs to be trusted
3. It can be extended as Mathlib grows

---

## Roadmap to Full Formalization

Our axioms can be eliminated one by one:

| Axiom | How to Eliminate | Difficulty |
|-------|------------------|------------|
| `Weil_criterion` | Major project (full Weil explicit formula / full cone normalization) | Very High |
| `prime_term_le_at_t_critical_axiom` | Replace false strong scalar contract by an honest weaker theorem on the paper generator | High |

Each elimination makes the proof stronger. Current state: **5 axioms total (3 standard + 2 project)**.

**Recently closed (now theorems):**
- `digamma_one_fourth_neg` — proven via Aristotle (reflection/duplication formulas)
- `a_star_pos` — proven from `digamma_one_fourth_neg`
- `a_star_bdd_on_compact` — proven via Mathlib continuity
- `a_star_continuous` — proven via Mathlib
- `a_star_even` — proven via `Gamma_conj`

---

## Pre-Commit Checklist

Before committing any changes, verify:

### 1. Axiom Audit
```bash
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'
```
- [ ] No NEW axioms introduced (unless documented)
- [ ] All axioms are in our classification (Level 0-3)
- [ ] No circular dependencies

### 2. Philosophy Compliance
- [ ] New theorems use `theorem`, not `axiom` where possible
- [ ] If new axiom needed: documented with citation and justification
- [ ] Bridge axioms are for well-understood math (not hiding complexity)

### 3. Documentation
- [ ] PROJECT_ASCII.md updated if axiom status changed
- [ ] This file (PHILOSOPHY_OF_PROOF.md) updated if philosophy changes

---

## FAQ

### Q: "Isn't using axioms just cheating?"

**A:** No. We're explicit about what we assume. This is like a mathematical paper saying "By Theorem X [citation], we have..." The difference is Lean checks all the logic between our axioms and RH.

### Q: "Why not formalize everything?"

**A:** Time and resources. Fully formalizing Weil's explicit formula alone could take years. Our approach validates the proof structure NOW, while allowing incremental improvement.

### Q: "How do I know your axioms match the paper?"

**A:** Each axiom is stated in Lean with its exact mathematical content. Compare it to the corresponding section in the Q3 paper. The statements are direct translations.

### Q: "What if one of your axioms is wrong?"

**A:** Then RH wouldn't follow. But that would mean an error in the Q3 paper itself, not in the formalization. Our job is to verify "paper correct → RH", not to verify the paper.

---

## Contact & Verification

- **Repository:** https://github.com/Malaeu/chen_q3
- **Paper:** [Q3 Paper Link]
- **Lean Version:** Lean 4 with Mathlib
- **Verification:** Clone, build, run `#print axioms`

We welcome scrutiny. The whole point of this formalization is transparency.

---

## Acknowledgments

This philosophy is informed by discussions in the Lean community, particularly:
- Talia Ringer's work on proof engineering
- The Mathlib community's standards
- David Budden's thread on axiom usage

---

*"The goal is not to hide our assumptions, but to make them so clear that anyone can verify them."*
