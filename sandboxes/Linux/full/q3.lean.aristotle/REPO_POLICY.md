# Repository Policy v1.0

> **Q3 RH Lean Formalization — Governance Rules**
> Last updated: 2025-12-22

---

## 1. Single Source of Truth

**`PROJECT_STATUS.md`** is the ONLY authoritative document for:
- Current progress and verification status
- What's broken / what's "verified clean"
- Plans and roadmap

All other status files are considered **legacy/deprecated** and MUST NOT be used for decisions.

---

## 2. Definitions Are Law

**`Q3/Basic/Defs.lean`** is the SOLE anchor for all formulations.

Any change to definitions (coordinates, windows, weights, δK, etc.) is a **BREAKING CHANGE** requiring:
- [ ] Explicit migration plan
- [ ] Update ALL bridges and aggregators
- [ ] Verify `#print axioms` on final theorem

**Rationale:** The entire architecture depends on definition alignment across bridges.

---

## 3. Tier Discipline

| Tier | Description | Requirements |
|------|-------------|--------------|
| **Tier-1** | Classical/External | Mathlib import OR axiom with source (book/paper/exact citation) |
| **Tier-2** | Our Contribution (Q3 pipeline) | MUST be replaced by theorems via standalone proofs + bridges |

Tier-2 axioms are **temporary placeholders**, not permanent.

---

## 4. No Circular Closures

**BANNED:** Any file/lemma that "closes" an axiom through itself or imports what it proves.

- `*_integrated.lean` files are **banned by default**
- Exception: Only after explicit non-circularity audit (documented in PROJECT_STATUS)

---

## 5. Bridge-First Approach

When formulations don't match:

```
PREFERRED:  Standalone proof (unchanged) → *_bridge.lean → Target formulation
FORBIDDEN:  Rewrite standalone proof to match
```

Rewriting standalone proofs is allowed ONLY when bridge is **provably impossible** (must be documented in PROJECT_STATUS).

---

## 6. Honest Minimal Axioms

Every axiom in `Q3/Axioms.lean` MUST have:

- [ ] **Tier tag** (Tier-1 or Tier-2)
- [ ] **Source/Reference** (book, paper, or explicit justification)
- [ ] **"Why not Mathlib"** explanation
- [ ] **Correct parameter dependencies** (no magic constants)

**Bad Example:** `W_sum_finite_axiom` with fixed constant when bound depends on K
**Rule:** If it grows with K, the axiom MUST reflect that dependency.

---

## 7. Axiom Audit (PR Requirement)

Every PR MUST include:

```bash
# Check axiom dependencies
lake env lean --run Q3/CheckAxioms.lean

# Or manually on key theorems
#print axioms RH_proven
#print axioms <bridge_theorem>
#print axioms <standalone_theorem>

# Check for sorry
grep -rn "sorry" Q3/
```

Any remaining `sorry` requires explicit justification in PR description.

---

## 8. Import Hygiene

**No cycles. No "kitchen sink" imports.**

```
Hierarchy (arrows = "imports"):

┌─────────────────┐     ┌──────────────────┐
│  Q3/Axioms.lean │     │ Standalone proofs│
└────────┬────────┘     └────────┬─────────┘
         │                       │
         v                       v
┌────────────────┐      ┌────────────────┐
│   Main.lean    │      │   *_bridge.lean │
│ (axiom-based)  │      └────────┬────────┘
└────────────────┘               │
                                 v
                    ┌────────────────────────┐
                    │ AxiomsTheorems.lean    │
                    │ (imports bridges)      │
                    └────────────┬───────────┘
                                 │
                                 v
                    ┌────────────────────────┐
                    │ MainTheorems.lean      │
                    │ (theorem-based RH)     │
                    └────────────────────────┘
```

---

## 9. Canonical Coordinates

**Project canonical form:**
- ξ = log n / (2π)
- Nodes: ξₙ = log n / (2π) with ±ξₙ symmetry where needed

**If standalone proof uses different coordinates** (e.g., α = log n):
1. Do NOT declare it "wrong"
2. Create `*_rescaling.lean` with explicit parameter conversion lemmas
3. Then create `*_bridge.lean` using rescaling

Example: `RKHS_rescaling.lean` → `RKHS_contraction_bridge.lean`

---

## 10. Documentation vs Computation

| Category | Role | Example |
|----------|------|---------|
| **Core Proof** | Lean files + Tier-1 axiom list | `Q3/*.lean` |
| **Reproducibility Aid** | Certificates, JSON, scripts, ATP logs | `scripts/`, `*.json` |

**Deprecated files** MUST have header:
```
-- DEPRECATED / LEGACY
-- See: <current_file.lean> or PROJECT_STATUS.md
```

Example: `ACCEPTANCE_GATE.md` is marked as archive, use only for historical context.

---

## PR Checklist

Before merging any PR:

- [ ] `lake build` succeeds
- [ ] `#print axioms RH_proven` shows only expected axioms
- [ ] `grep -rn "sorry" Q3/` explained or zero
- [ ] No circular imports
- [ ] PROJECT_STATUS.md updated if status changed
- [ ] New axioms have tier/source/justification

---

## Reference Documents

- **PROJECT_STATUS.md** — Current verification status
- **Q3/Basic/Defs.lean** — Canonical definitions
- **Q3/Axioms.lean** — Axiom registry with tiers and sources

---

*Policy version: 1.0 | Created: 2025-12-22*
