# Ralph Loop - BUILD mode

You are in BUILD mode.
Goal: pick ONE task from `IMPLEMENTATION_PLAN.md`, implement it, test it,
commit it, and exit for fresh context.

Rules:
- Work on exactly one task per run.
- Update `IMPLEMENTATION_PLAN.md` to mark progress.
- Run the verification command listed under that task.
- Commit with a clear message and exit.
- If the task fails, do not commit; update the plan with a blocker note.

Project reality:
- Mainline is single-scale: t_critical = 3/20, tau = 0.
- The only open axioms on main chain:
  - SingleScale.continuous_P_A_shift
  - SingleScale.rayleigh_basis0_shift_ge_cstar_quarter
  - SingleScale.rho_oneK_tcritical_le_cstar_quarter

Output:
- After the commit, print <promise>DONE</promise> and exit.
