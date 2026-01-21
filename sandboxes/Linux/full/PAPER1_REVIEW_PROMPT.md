# Scientific Writer Task: Paper 1 Review

## Task: Review and Update "Fejér–heat generators and Lipschitz control"

**CRITICAL RULES**:
1. Paper 1 is ALREADY WRITTEN
2. Only make MINOR edits for trilogy consistency
3. DO NOT rewrite the paper

---

## Location

PDF: `/Users/emalam/Documents/GitHub/chen_q3/full/Fejér–heat generators and Lipschitz control for the Weil quadratic functional/main.pdf`

**Note**: You CAN read this PDF as it's only 15 pages.

---

## Review Checklist

### 1. Abstract
- [ ] Add mention of "first in a series of three papers"
- [ ] Reference companion papers in Discussion section

### 2. Introduction
- [ ] Add paragraph about paper series:
  ```
  This is the first in a series of three papers developing an
  operator-theoretic proof of the Riemann Hypothesis via Weil's
  positivity criterion. The present paper establishes density and
  Lipschitz tools. The Toeplitz barrier and RKHS contraction are
  developed in [Part II]. The synthesis and main theorem appear
  in [Part III].
  ```

### 3. Discussion Section
- [ ] Add forward references to Papers 2-3
- [ ] Clarify how density/Lipschitz feed into A3 bridge

### 4. Notation Consistency
Verify these match the planned Papers 2-3:
- [ ] ξ_n = log(n)/(2π) for prime nodes
- [ ] w_Q(n) = 2Λ(n)/√n for Weil weights
- [ ] W_K = [-K,K] notation
- [ ] G_K for Fejér-heat cone
- [ ] c* for Archimedean floor (mentioned but not defined here)

### 5. Bibliography
- [ ] Add placeholder citations for [Part II] and [Part III]
- [ ] Ensure Szegő, Böttcher, Aronszajn citations present

---

## Minimal Edits Required

If the paper is mostly correct, only these edits are needed:

### In Abstract:
Add at end: "This note is the first of three developing an operator-theoretic approach to the Weil positivity criterion."

### In Introduction (end of "Context and motivation"):
Add: "The present paper develops the density (A1') and continuity (A2) modules. The Toeplitz barrier (A3) and RKHS prime cap are established in a companion paper [Part II], and the synthesis yielding the main theorem appears in [Part III]."

### In Discussion (new paragraph):
Add: "**Series context.** This paper provides the density and Lipschitz foundations. In [Part II], we develop the Toeplitz–symbol bridge using Szegő–Böttcher asymptotics and establish a uniform RKHS cap for the prime operator. In [Part III], we combine these modules with the Guinand–Weil normalization to prove Q ≥ 0 on the full Weil cone, and apply Weil's criterion to deduce the Riemann Hypothesis."

---

## Output

If edits are needed, provide:
1. A diff-style list of changes
2. The specific LaTeX text to insert/modify

If the paper is fine as-is, just confirm consistency with Papers 2-3.

---

*This prompt file: /Users/emalam/Documents/GitHub/chen_q3/full/PAPER1_REVIEW_PROMPT.md*
