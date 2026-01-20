# Philosophy of Proof: Q3 Lean Formalization

**Author:** Eugen Malamutmann
**Project:** Q3 - Formal Verification of Riemann Hypothesis Proof Structure
**Last Updated:** 2026-01-20

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
│  IF these 7 mathematical statements are true (6 classical + 1 Q3)  │
│  THEN RH is true.                                                  │
│                                                                    │
│  Lean verifies: the logical implication is CORRECT.                │
│  Human verifies: the 7 statements match what's in the paper.       │
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

Our formalization depends on exactly **4 axioms** (beyond Standard Lean):

### Level 0: Standard Lean/Mathlib (3) — UNIVERSALLY ACCEPTED
```
propext          — Propositional extensionality
Classical.choice — Axiom of choice
Quot.sound       — Quotient soundness
```
These are part of Lean's foundation. Every Mathlib proof uses them.

### Level 1: Classical Results from Literature (2) — ESTABLISHED MATHEMATICS
```
Weil_criterion        — Weil 1952: Q ≥ 0 on Weil cone ⟺ RH
Schur_test            — Schur test for operator norm bounds
```
These are well-known results. Citations:
- Weil, A. (1952). "Sur les 'formules explicites' de la théorie des nombres premiers"

**Note:** The following are now THEOREMS (proven from Mathlib/Aristotle):
- `digamma_one_fourth_neg` — Re(ψ(1/4)) < 0 (DLMF 5.4.14, proven via reflection formula)
- `a_star_pos`, `a_star_bdd_on_compact`, `a_star_continuous`, `a_star_even`

### Level 2: Q3 Paper Contributions (2) — OUR MATHEMATICAL CONTENT
```
A1_density_WK_axiom                  — Fejér×heat atoms dense in W_K
Q_nonneg_on_atoms_of_A3_Fourier_RKHS — Q ≥ 0 on atoms (Theorem 5.3, Fourier A3)
```
These are the novel contributions proven in the Q3 paper.

### Level 3: Technical Bridge Lemmas (0) — CLOSED

arch/prime Lipschitz bridges are now proven in Lean (no longer axioms).

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
  propext,                              -- Standard Lean
  Classical.choice,                     -- Standard Lean
  Quot.sound,                           -- Standard Lean
  Q3.Weil_criterion,                    -- Level 1: Weil 1952
  Q3.Schur_test,                        -- Level 1: Analysis
  Q3.A1_density_WK_axiom,               -- Level 2: Q3 paper
  Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom -- Level 2: Q3 paper
]
```

---

## Proof Structure Diagram

```
                           RH (Riemann Hypothesis)
                                    ▲
                                    │
                        ┌───────────┴───────────┐
                        │    Weil_criterion     │ ← Level 1 (Weil 1952)
                        │  Q≥0 on Weil ⟺ RH     │
                        └───────────┬───────────┘
                                    │
                        ┌───────────┴───────────┐
                        │  Q_nonneg_on_Weil_cone │ ← THEOREM (proven in Lean!)
                        └───────────┬───────────┘
                                    │
                        ┌───────────┴───────────┐
                        │    T5_transfer        │ ← THEOREM (proven in Lean!)
                        │  Q≥0 on atoms → W_K   │
                        └───────────┬───────────┘
                                    │
              ┌─────────────────────┼─────────────────────┐
              │                     │                     │
    ┌─────────┴─────────┐ ┌────────┴────────┐ ┌─────────┴─────────┐
    │  A1_density_WK    │ │  Q_Lipschitz    │ │ Q_nonneg_on_atoms │
    │  (Level 2: Q3)    │ │  (THEOREM!)     │ │ (Level 2: Q3)     │
    └───────────────────┘ └────────┬────────┘ └─────────┬─────────┘
                                   │                    │
                          ┌────────┴────────┐    ┌─────┴─────┐
                          │  arch + prime   │    │ A3 + RKHS │
                          │  Lipschitz      │    │ (A3 L2 +  │
                          │  (THEOREM)      │    │  RKHS Thm)│
                          └─────────────────┘    └───────────┘
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
| `Schur_test` | Formalize from Mathlib Analysis.InnerProductSpace | Medium |
| `Weil_criterion` | Major project (Weil explicit formula) | Very High |
| `A1_density_WK_axiom` | Prove density via Fejér×heat approximation | Medium |
| `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` | Follows from A3 floor + RKHS contraction | Medium |

Each elimination makes the proof stronger. Current state: **7 axioms total (3 standard + 4 project)**.

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
