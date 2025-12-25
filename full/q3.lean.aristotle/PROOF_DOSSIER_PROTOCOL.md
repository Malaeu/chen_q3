# PROOF DOSSIER PROTOCOL

## Purpose

This document defines the **mandatory structure** for all mathematical proofs in this project. Every proof must be **audit-resistant**, with explicit axioms, quantified statements, and justified steps.

**CRITICAL RULES:**
1. Never start with a conclusion — context, definitions, and reasoning come FIRST
2. Every object must be defined before use
3. Every inference must be justified
4. No hidden assumptions

---

## PROOF DOSSIER STRUCTURE

### 0. Theorem Title and Status

- **Exact statement:** State the theorem in one precise sentence, using explicit quantifiers.
- **Status:** Indicate whether the proof is:
  - Within standard mathematics (ZFC + standard analysis)
  - Conditional on specific hypotheses (list them)

### 1. Formal Statement (with Quantifiers)

Express the statement formally and fully, making explicit:
- What objects are considered and their "universe of discourse"
- What limitations or hypotheses apply
- Whether the property is universal (∀), existential (∃), or unique (∃!)
- Which parameters are fixed, which are arbitrary

**Template:**
```
For all [objects] in [domain],
if [conditions],
then [conclusion].
```

### 2. Definitions and Notation

List every term, object, operation, or property used:
- Clear definitions OR standard references
- Nonstandard conventions stated explicitly
- **Rule:** No term without definition or reference

### 3. Dependencies (Dependency List)

Enumerate all supporting facts:

| Fact | Source | Status |
|------|--------|--------|
| Lemma A | Proven in this document | §5.1 |
| Theorem B | Author, Title, Thm X.Y | Classical |
| Fact C | Well-known | State it anyway |

### 4. Proof Plan (Roadmap)

2–6 lines outlining the main steps:
```
Step 1: Establish X
Step 2: Apply Y to get Z
Step 3: Combine to conclude
```

### 5. Lemmas

For each nontrivial intermediate step:

**Lemma N.** [Precise formulation with quantifiers and domain]

**Proof of Lemma N.**
1. Starting assumptions: [list them]
2. Introduce object X defined as...
3. By [reference], we have...
4. Therefore...
5. Conclusion: [restate what was proved]
∎

### 6. Main Proof

Construct as chain of justified steps:
1. By Lemma 1, we have...
2. Applying Definition 2.3 to...
3. From Dependency 3.2, it follows...
4. Combining steps 1-3...
5. Therefore, the theorem is proved.
∎

### 7. Audit–Edge Check

Explicitly address potential errors:

| Potential Issue | Location | Verification |
|-----------------|----------|--------------|
| Hidden quantifiers | § | All explicit |
| Limit/integral swap | § | Dominated convergence: condition X |
| Division by zero | § | Denominator ≠ 0 because... |
| Boundary cases | § | Checked: case θ = 0 handled |
| Circular reference | § | Linear chain verified |
| Branch cuts | § | Re(z) > 0 satisfied |
| Numerical → general | § | Rigorous bounds via... |

### 8. Appendix

List major known theorems used:
- Reference: Author, Title, Theorem N
- Why applicable: conditions X, Y, Z satisfied

---

## AUDITOR'S KILL LIST

These issues typically break "great proofs" — address each explicitly:

1. **Hidden quantifiers**: "let small ε" — how small? depends on what?
2. **Limit/sum/integral swaps** without justification (uniform convergence, dominated convergence)
3. **∃ ↔ ∀ confusion**: mixing "exists" and "for all"
4. **Boundary cases lost**: zero, degeneracy, multiple roots, singular points
5. **Unchecked invertibility**: division by potentially zero
6. **Implicit compactness/completeness**
7. **Circular reference**: lemma depends on corollary
8. **Implicit function properties**: analyticity, branch selection
9. **Numerical experiments → general claim** without bridge

---

## OUTPUT FORMAT

- Use markdown with headers and LaTeX math
- Each section must use bold or header style
- Each reasoning step articulated BEFORE conclusion
- Proofs structured step-by-step, not as single blocks
- **NEVER** present conclusion before reasoning

---

## EXAMPLE (Template)

### 0. Theorem Title and Status
- **Statement:** If matrices \(A,B \in M_n(\mathbb{C})\) are similar, then their characteristic polynomials are equal.
- **Status:** Standard linear algebra, proof below.

### 1. Formal Statement
For all \(A, B \in M_n(\mathbb{C})\), if there exists invertible \(S \in M_n(\mathbb{C})\) such that \(B = S^{-1}AS\), then \(\det(tI - A) = \det(tI - B)\) for every \(t \in \mathbb{C}\).

### 2. Definitions and Notation
- \(M_n(\mathbb{C})\): set of \(n \times n\) complex matrices
- Similarity: \(B = S^{-1}AS\) for invertible \(S\)
- Characteristic polynomial: \(p_A(t) = \det(tI - A)\)

### 3. Dependencies
- Multiplicativity of determinant: \(\det(PQR) = \det(P)\det(Q)\det(R)\)
- \(\det(S^{-1})\det(S) = 1\)

### 4. Proof Plan
1. Show \(tI - B = S^{-1}(tI - A)S\)
2. Apply determinant multiplicativity
3. Conclude equality

### 5. Lemmas
**Lemma 1.** For any invertible \(S\) and square \(M\): \(\det(S^{-1}MS) = \det(M)\).

**Proof.**
1. By multiplicativity: \(\det(S^{-1}MS) = \det(S^{-1})\det(M)\det(S)\)
2. Since \(\det(S^{-1})\det(S) = 1\): result follows
∎

### 6. Main Proof
1. Given \(B = S^{-1}AS\), compute \(p_B(t) = \det(tI - B)\)
2. Note \(tI = S^{-1}(tI)S\), so \(tI - S^{-1}AS = S^{-1}(tI - A)S\)
3. Therefore \(\det(tI - B) = \det(S^{-1}(tI - A)S)\)
4. By Lemma 1: \(= \det(tI - A)\)
5. Thus \(p_B(t) = p_A(t)\)
∎

### 7. Audit–Edge Check
- **Hidden quantifiers:** All explicit
- **Lemma use:** Justified
- **Exceptions:** Invertibility required, checked
- **Known facts:** Determinant multiplicativity standard

### 8. Appendix
- Horn & Johnson, *Matrix Analysis*, Ch. 1

∎

---

## MANDATORY CHECKLIST BEFORE SUBMISSION

- [ ] Every object defined before use
- [ ] Every inference justified with reference
- [ ] No conclusion before reasoning
- [ ] All quantifiers explicit
- [ ] Dependencies listed with sources
- [ ] Audit-edge check completed
- [ ] No items from "kill list" present

---

## FOR ARISTOTLE SUBMISSIONS

When preparing `.md` files for Aristotle:

1. Follow this protocol exactly
2. Include Lean 4 code blocks for definitions
3. Mark `sorry` for steps Aristotle should prove
4. List axioms explicitly with `axiom` keyword
5. Provide numerical bounds where applicable

**Template for Aristotle:**

```markdown
# [Theorem Name]

## 0. Status
- **Statement:** [one sentence]
- **Status:** [standard/conditional]

## 1. Formal Statement
```lean
theorem my_theorem : ∀ x, P x → Q x := by sorry
```

## 2. Definitions
```lean
def my_object : Type := ...
```

## 3. Dependencies
```lean
axiom known_fact : ...
```

## 4-6. Proof Outline
**Step 1:** ...
**Step 2:** ...

## 7. Audit Check
[table]

## 8. Appendix
[references]
```

---

**END OF PROTOCOL**
