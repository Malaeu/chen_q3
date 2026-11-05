CODEX TASK — LIFT THE Q3 NYMAN–BEURLING–BÁEZ-DUARTE ANALYSIS (2026-11-05)

Repo: github.com/Malaeu/chen_q3
- Base: rh_clean (this file lives here; commit given in the owner's message). Commit your result to rh_clean.
- Read-only: proshka_inbox_2026-10-31 @ 3d3ba2e60785408063c9aee70657ee0a0cf0e1dc.

GOAL
In the Q3 era the project analysed whether the Nyman–Beurling / Báez-Duarte criterion (NB–BD) can be transferred into our framework. We remember the result as "4 transfer nodes, 3 failed structurally"; that memory is unconfirmed.
Bring that analysis back, verbatim and sourced, and set it against today's Route B objects. The owner and Mythos will use it to decide whether NB–BD is a live door.
How you search and how you lay out the file is your call.

1. FIND THE ORIGINAL
Search by content, not only by file name:
- all branches of chen_q3;
- the local Q3 repo rh_lean_01_2026, if it is on your machine;
- any older Q3 doc trees you know of.
Suggested terms: Nyman, Beurling, Báez / Baez, Burnol, Bettin, d_N, "fractional part", {θ/x}, rho_theta, "transfer node".
For every hit, report path + branch + commit + blob.
If the original analysis does not exist in any repo you can reach, write exactly that. Do not rebuild it from memory or invent nodes.

2. IF FOUND: THE NODES
For each node give, quoted from source:
- what was being transferred;
- the verdict;
- the exact reason it failed (or why it passed).

3. CROSS WITH ROUTE B
For each failed node, check whether one of these objects removes the stated reason. Answer YES / NO / UNCLEAR, each with a one-paragraph justification that cites equation numbers.

  a) Zeta-operator algebra — proshka_inbox_2026-10-31, docs/routeB_bus/proshka/PROSHKA_VERDICT_CCM_ARITHMETIC_COMPENSATION_2026-11-04.md (commit 8e584bb8422073d077d80d4f88a2c8416973f49a, blob 7e9bc641140a8e3b4b9d7b199416957bb1051a4b):
     - Z_L, M_L, C_L in (3.1)–(3.3); C_L = M_L[Y_d, Z_L].
     - Square factorization A_m = R*R + E in (3.5)–(3.6).
     - Theorem 1 (4.1): lambda_min E_m(t,d) <= -c L m^{1/4} for all t, d.
     - Key question: do NB–BD's L² squares fall inside the class killed by Theorem 1, or outside it? State which.

  b) Integer lattice floor(x) — proshka_inbox_2026-10-31, docs/routeB_bus/proshka/PROSHKA_VERDICT_SD_JUDGE_BEURLING_2026-11-05.md (commit 3f0d43a921b5d76ac04b2c7012291e937dace231, blob 215d24203d783d6f1229230832bee31a513bf9a9):
     - zeta(s) = s/(s-1) - s ∫{x}x^{-s-1} dx as the separator against DMV.

Literature already in the repo (rh_clean), docs/routeB_bus/litreview/pdfs/survey_2026-09-03_sources/:
- baez_duarte_2003.txt — blob 85be01a5
- baez_duarte_2_0202166.txt — blob b9109169
- burnol_2002.txt — blob 8bf50b0d

4. DELIVERY
- One markdown file under docs/routeB_bus/ (path of your choice), plus anything else you find useful.
- Commit and push to rh_clean.
- Report the commit hash and the blob of the main file.
- Do not edit the Proshka verdicts or any route-state file.
