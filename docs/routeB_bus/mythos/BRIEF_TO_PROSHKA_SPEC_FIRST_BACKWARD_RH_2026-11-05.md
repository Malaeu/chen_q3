PROSHKA REQUEST — SPEC FIRST, THEN BUILD, BACKWARD FROM RH (2026-11-05, v2)

Firmware: docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md, blob 32a5337b8b3bd431126084f250baf73f86e8f749 (v3 text).
Branches:
- rh_clean @ 39c788f2d8cb80f8b870688c5c1693e559d6b9d3
- proshka_inbox_2026-10-31 @ 616619f2 (write your verdict here)

GOAL
Prove the Riemann Hypothesis. The bottom line of your answer is RH.

DIRECTION
Your last runs went forward, from what is provable upward, until the proof stopped:
- 62f78231 (PROVE_RH edition, blob 2b5e02a0): stopped at (7.4)/(10).
- 616619f2 (blob 3d122971): stopped at (18).
Now reverse the direction, in the way Viazovska worked: first specify the imaginary object, then build it.

STEP 1 — SPECIFY THE IMAGINARY OBJECT (before any construction)
Write down an object X that does not exist yet: a function, a family, an operator or a factorization (your choice). Give its exact list of properties S such that "X with S exists => RH" is a strictly proved theorem.
- Fix S in your verdict BEFORE Step 2. S may not be edited after construction starts.
- S must be checkable without assuming RH or any statement equivalent to it.
- If S is just a rewording of RH, state that and pick a different S.

STEP 2 — BUILD X FROM OUR OWN MATERIAL
Build X from what this project has and nobody else has. Inventory of our assets (status in brackets):

  window / geometry
  - Literal CCM window A_m; quiet space J_m [PAPER+A, rh_clean 2176dab, e724ae6]
  - Index formula n_-(J_T + Delta_m) [PAPER, f6c9cd8]
  - Dichotomy: floor <=> RH [PAPER, d142486]
  - Pole-null core p_perp [PAPER, 44aaf90d, e586ebba]

  corner and operators
  - Corner A00 = 2 Psi(log m)/log m [PAPER + DIAG, 2ad7342c]
  - Loewner formula [PAPER, 7021db85]
  - zeta-operator Z = prod (I - e_p)^-1, prime part = Z^-1 Y Z - Y [PAPER, 8e584bb8]

  prime structure
  - Prime-only core [PAPER, 115714b7]
  - Adjacent prime-shell cancellation [PAPER, 603b24e1]

  judges and transforms
  - Source quotient; Cayley address judge [PAPER, d558268a; Codex replay 9aa2a426]
  - Phase u_m; projection difference = Sonin + compact K [PAPER, f96a9072]
  - DMV obstruction; integer-lattice candidate floor(x) [PAPER, 3f0d43a9]

  response and increment
  - Gaussian response identity; growth m^(Theta/2) [PAPER, 62f78231]; normalization confirmed [DIAG, rh_clean 39c788f2, task_a_rerun/RESULT.md blob 74601eb1]
  - Coupled one-prime increment, remainder <= 10/p [PAPER, 616619f2]

You may also modify zeta, add structure Riemann did not know, or build your own object unlike zeta. The construction may not use RH or anything equivalent to it.

STEP 3 — THE CHAIN DOWN
  RH <= N_1 = "X with S exists" <= N_2 <= ... <= N_K
- Every arrow must be strictly proved.
- N_K must be a theorem: an asset above, the literature, or proved by you here.
- For each step, name the asset it uses.

ACCEPTANCE (fixed before you start)
1. S is stated first and never changed afterwards.
2. The chain as a table. For each N_k give:
   - the statement;
   - the proof of the arrow;
   - the asset used;
   - its status: THEOREM / CONDITIONAL / CONJECTURE / FALSE;
   - whether it is equivalent to RH or strictly stronger.
3. False-world check for every N_k (k >= 1):
   - It must be false in Davenport–Heilbronn and in a Diamond–Montgomery–Vorhauer Beurling system.
   - Name the excluding property for each world and the exact step where it is used.
4. Every N_k strictly stronger than RH gets its cheapest falsification test, written for Codex if numerics decide it.
5. The bottom of the chain is one of:
   (a) N_K is a theorem. Then RH is proved; give the full proof.
   (b) The lowest N_K reached, plus the exact missing arrow, plus why our assets do not supply it.
   (c) A proof that X with S cannot be built from this class of material (a kill).
   All three are results. A chain that only restates RH is NO_PROGRESS.
