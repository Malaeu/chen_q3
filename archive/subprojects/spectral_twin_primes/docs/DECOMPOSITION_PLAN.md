# 📋 Paper Decomposition for Aristotle Verification

## Project: A Spectral Criterion for Twin Primes via Cone–Kernel Separation

---

## 🎯 PRIORITY 1: Core Lemmas (MUST VERIFY)

These are the foundation of our paper. If Aristotle verifies these, the paper is rock solid.

| # | Lemma/Theorem | File | Status | Priority |
|---|---------------|------|--------|----------|
| 1 | **Cone-Kernel Separation** | hypothesis_B1_prime.tex:16 | ✅ DONE | P0 |
| 2 | **Cone Positivity (B₁-strong)** | hypothesis_B1_prime.tex:67 | TODO | P0 |
| 3 | **Spectral Equivalence** | target_theorem.tex:14 | TODO | P0 |
| 4 | **Universal Energy Scaling** | target_theorem.tex:51 | TODO | P0 |
| 5 | **Finite Stabilization (SC2)** | SC2_arithmetic.tex | TODO | P0 |

---

## 🎯 PRIORITY 2: Supporting Lemmas

| # | Lemma/Theorem | File | Status |
|---|---------------|------|--------|
| 6 | Boundary Row Lower Bound | target_theorem.tex:68 | TODO |
| 7 | Abstract SC1 | abstract_SC1.tex:35 | TODO |
| 8 | Phase difference for twins | twin_coherence.tex:17 | TODO |
| 9 | Anti-diagonal coherence | twin_coherence.tex:25 | TODO |

---

## 🎯 PRIORITY 3: Advanced Theorems (if time permits)

| # | Lemma/Theorem | File | Status |
|---|---------------|------|--------|
| 10 | Weil's positivity criterion | Weil_linkage.tex:30 | TODO |
| 11 | Weil positivity on compacts | Weil_linkage.tex:68 | TODO |
| 12 | RKHS strict contraction | RKHS_contraction.tex:127 | TODO |
| 13 | A3 bridge inequality | A3_operator_bridge.tex:58 | TODO |

---

## 📁 Input File Format

Each lemma gets its own markdown file in `lean_aristotle/input/`:

```
lean_aristotle/input/
├── 01_cone_kernel_separation.md       ✅ DONE
├── 02_cone_positivity_B1.md           TODO
├── 03_spectral_equivalence.md         TODO
├── 04_universal_scaling.md            TODO
├── 05_finite_stabilization.md         TODO
└── ...
```

---

## 📁 Output Files

Aristotle outputs go to `lean_aristotle/output/`:

```
lean_aristotle/output/
├── 01_cone_kernel_separation_aristotle.md   ✅ DONE
├── 02_cone_positivity_B1_aristotle.md       TODO
└── ...
```

---

## 🔄 Workflow

1. **Extract** lemma from paper (LaTeX → Markdown)
2. **Create** input file in `lean_aristotle/input/`
3. **Run** Aristotle:
   ```bash
   aristotle prove-from-file --informal --no-validate-lean-project input/XX_lemma.md
   ```
4. **Move** output to `lean_aristotle/output/`
5. **Verify** Lean code compiles (optional: install Lean4 + Mathlib)
6. **Update** this document with status

---

## 📊 Statistics

| Category | Count |
|----------|-------|
| Total lemmas in paper | ~60+ |
| Core lemmas (P0) | 5 |
| Verified by Aristotle | 1 |
| In progress | 0 |
| Failed | 0 |

---

## 🏆 Success Criteria

- [ ] All P0 lemmas verified
- [ ] Lean code compiles with Mathlib
- [ ] Can add "Formally verified" badge to paper

---

## 📝 Notes

### Cone-Kernel Separation (Completed)
- Input: `lean_test/cone_kernel.md`
- Output: `lean_test/cone_kernel_aristotle.md`
- Time: ~20 minutes
- Result: Full Lean4 proof with Mathlib

### Tips from Experience
1. **Include proof sketch** - Aristotle needs hints for complex proofs
2. **Be explicit about hypotheses** - Don't assume anything
3. **Use standard notation** - ξ, K, A, etc.
4. **Parallel runs** - Can run multiple at once

---

*Last updated: December 2025*
