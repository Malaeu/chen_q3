GOAL 054 — SectorCell13N2 Phase-0: Enclosure-Receiver Inventory (RULE_INVENTORY_FIRST)

**Context (self-contained).** The Arb certificate for cell (13,2) is committed: commit 8dad5aaf0b78552a1bfeb8efd6f3a2844aaf7acf; artifacts by content-SHA: script 01464c9b47b415fb85480b6aaea18b469c0cd659f18417ead3768e79c71aba72, JSON f71d48a93db91d70d03be6fbc3fc65bece2acde31fdc1bdd057965beb92be94f. Proshka's assigned Lean receiver Q3/Proofs/RouteB/CCMFiniteWeilSectorCell13N2.lean requires the theorem shape ccmCell13N2_entry_enclosures: rational lower/upper sandwiches for every entry of ccmWeilMatFinite 13 2. This goal is **read-only**, so no parent pin is needed (artifacts are SHA-addressed; HEAD drift is irrelevant). PRE-COMMIT (K6): no auxiliary objects. Arsenal scan: no card applies (inventory node); add ARSENAL_USED: Cxx only if one actually fires.

**Task — three zones, in this order.**

**(1) Named candidate first — mainline hbox-import machinery:** the file family Q3/Proofs/PSD_CenteredCoeff*HboxImport.lean, plus ACTIVE/requests/step32f_boundary_gram_hbox_receiver/report.md, ACTIVE/requests/step32f_penalty_matrix_hbox_factor_receiver/report.md, ACTIVE/PSD_STEP33_MONITOR.md. Determine exactly: what an hbox import proves (external interval certificate → Lean inequality on a transcendental entry?), and its **trust chain** — a #print axioms profile is mandatory; if native_decide / a declared axiom / opaque appears inside, the mechanism is FORBIDDEN for this route (per Proshka's SectorCell directive) — record it as unusable, with the reason. The node-5 mainline is frozen as a route; its mechanisms are a legal read-only library (modify nothing).

**(2) Mathlib:** Real.exp_one_lt_d9 / exp_one_gt_d9, Real.exp_bound, log bounds via exp monotonicity, Analysis.SpecialFunctions.Log.Deriv, norm_num extensions.

**(3) Community precedents** for interval tactics over Mathlib.

**Mandatory per-component classification** of the entry formula τ = W02 − WR − Prime: (a) log component (log p for p ≤ 13, incl. log 13) — likely zone 2; (b) archimedean WR integral — the real question; (c) rational q_kernel combinatorics — trivially norm_num. Mark each: COVERED(mechanism, axiom profile) or GAP.

**Output — exactly one of three:** RECEIVER_FOUND (all components covered, standard axiom triple, minimal working example included); RECEIVER_PARTIAL (covered/gap table + the missing theorem stated ONLY for the uncovered component, endpoints taken from the 512-bit section of the certificate JSON); G2_CCM_SECTOR_CELL_13_2_ARB_TO_LEAN_ENCLOSURE_GAP (nothing usable + full statement of ccmCell13N2_entry_enclosures). On any stop: one AUTOPSY: line (K8).

**Boundaries:** read-only; no new Lean files, no Aristotle submission, no edits to frozen files; commit only the answer file, canon + mirror in one commit. Answer file: 054_sectorcell13n2_phase0_inventory.answer.md with handoff + ACTIONS LOG (else REJECTED). Route stays CHALLENGER / NOT_RH; Bus 010 VOID; no promotion. After answering, resume the standing goal.

**Files:** q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/054_sectorcell13n2_phase0_inventory.goal.md + mirror in docs/routeB_bus/.

