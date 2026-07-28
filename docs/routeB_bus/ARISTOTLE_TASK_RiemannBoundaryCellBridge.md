TASK:
RiemannBoundaryCellBridge_Standalone

CONTEXT (one line):
Self-contained: Mathlib only, no project files. A finished run returned the
code RIEMANN_SUM_BOUNDARY_CELL_GAP and named one exact missing packaged
lemma (finite right-endpoint mesh estimate with a boundary cell). Prove
exactly that lemma and its two small corollaries in a fresh file. Nothing
else. Integration happens elsewhere, offline.

SETUP (define inside the file):
  variables (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (K : NNReal)
  (hsupp : ∀ v, v ∉ Set.Icc (0:ℝ) b → h v = 0)
  (hlip : LipschitzOnWith K h (Set.Ico (0:ℝ) b))
  (hmeas : Measurable h)

  noncomputable def Estar (h : ℝ → ℂ) (u : ℝ) : ℂ :=
    Real.sqrt u * ∑' n : ℕ+, h (n * u)

TARGETS (no sorry):

T0 (finite reduction): for 0 < u, the family n ↦ h (n*u) over ℕ+ has
   support inside {n | (n:ℝ) * u ≤ b}; hence the tsum equals the finite sum
   over n ∈ Finset.Icc 1 (Nat.ceil (b/u)) (values with n*u > b vanish by
   hsupp; the possible exact hit n*u = b is kept in the sum).

T1 (MAIN — the named missing lemma, verbatim constant):
   for all u with 0 < u,
   ‖(u:ℂ) * ∑' n : ℕ+, h (n * u) - ∫ x in Set.Ioi (0:ℝ), h x‖
     ≤ u * (K * b + (‖h 0‖ + K * b) + ‖h b‖).
   Proof skeleton to follow literally:
   (a) let N := Nat.ceil (b / u); by T0 replace the tsum by the finite sum
       over Finset.Icc 1 N;
   (b) write ∫_{Ioi 0} h = ∑_{n=1}^{N} ∫_{Ioc ((n-1)*u) (min b (n*u))} h
       (cells beyond b contribute 0 by hsupp; the cells partition (0, min b (N*u)]
       and h vanishes on (b, ∞));
   (c) interior cells with (n:ℝ)*u < b: the whole cell lies in [0, b), so
       ‖(u:ℂ) * h (n*u) - ∫_{cell} h‖ = ‖∫_{cell} (h (n*u) - h x)‖
         ≤ u * (K * u) ≤ u * K * u,
       and summing ≤ (N*u) * K * u ≤ (b + u) * K * u; absorb the +u case by
       using N*u ≤ b + u and keeping the generous global constant of (e)
       below — or simply bound the interior total by K * b * u + K * u * u
       and then by u * (K*b) after dividing forms; any clean bookkeeping
       reaching the stated constant is acceptable;
   (d) the unique terminal cell with (n-1)*u < b ≤ n*u: bound its integral
       by u * (‖h 0‖ + K*b), since ‖h x‖ ≤ ‖h 0‖ + K*b on Ico 0 b, and its
       sum term by ‖h b‖ when n*u = b exactly, else that term is 0;
   (e) combine to the stated right-hand side. If the tight combination
       misses by a benign additive u * (K*u) ≤ u * (K*b) style slack, prove
       the statement with the SAME displayed constant by absorbing slack
       into K*b (u ≤ b may be assumed only if you add the easy complementary
       case u > b, where the sum has at most one term and the bound is
       immediate).

T2 (zero-mass corollary): if additionally
   (hmass : ∫ v in Set.Ioi (0:ℝ), h v = 0), then for 0 < u,
   ‖∑' n : ℕ+, h (n * u)‖ ≤ K * b + (‖h 0‖ + K * b) + ‖h b‖.

T3 (Estar corollary): under hmass, for u ∈ Set.Ioo (0:ℝ) 1,
   ‖Estar h u‖ ≤ (K * b + (‖h 0‖ + K * b) + ‖h b‖) * Real.sqrt u.

FORBIDDEN:
- no new axioms, no native_decide, no sorry/admit;
- import Mathlib only; no external project names;
- do not weaken to Lipschitz on the closed [0, b] (the intended h jumps at b);
- do not replace the explicit constant by an unnamed ∃ C (the packaged
  constant is the point).

VALIDATION:
- lake build succeeds; #print axioms for T0–T3:
  exactly [propext, Classical.choice, Quot.sound];
- grep sorry/admit/axiom/native_decide: clean;
- report which Mathlib lemmas supplied (i) the Ioc-partition of the integral,
  (ii) the tsum-to-finite-sum reduction, (iii) the Lipschitz cell estimate.

RETURN EXACTLY ONE PRIMARY STATUS:
RIEMANN_BOUNDARY_CELL_BRIDGE_PROVED
IOC_PARTITION_API_GAP (name the exact missing Mathlib statement)
TSUM_FINITE_REDUCTION_GAP (name it)
