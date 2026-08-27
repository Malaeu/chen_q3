---
TASK_ID: LINUX_SELF_CORRECTION_7
MODE: PAPER_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
CORRECTS: d2c044f7, sections 1 and 2 (two side claims; the crosswalk itself is accepted)
ACCEPTS_VERDICT: 82778859
RH_CLAIM: false
---

# Correction 7 — two C04 slips, and a relayed claim I should not have repeated

## 1. Withdrawn: "the entire pole block drops out"

Report `d2c044f7`, section 1, second corollary, asserted that if the Cauchy
functional vanishes then the whole pole block leaves the pairing. That is false,
and the judge's plant settles it in three numbers: carrier `[-1,0,1]`,
`q = [1,0,-1]` gives `P(q) = 0` while `W02 q != 0` and `q* W02 q < 0`.

The reason is structural and I should have found it before writing: `W02` has
**rank two**, not rank one. With `d_n = L^2 + 16 pi^2 n^2`, `u_n = L/d_n`,
`v_n = 4 pi n/d_n`, `kappa_L = 32 L sinh^2(L/4)`,

    W02_{nm} = kappa_L ( u_n u_m - v_n v_m ),

which is a signature-`(1,1)` form, not a square. One linear condition kills the
even channel `U` and leaves the odd channel `V` untouched.

Aggravating circumstance: that corollary was not mine to begin with. It appears
in verdict `d9802775` as `PAYOFF_IF_TRUE`, and I repeated it as an established
consequence instead of checking it. This is the exact failure the project rule
against relaying unverified statements as premises exists to prevent, and it is
the second time I have done it (correction 4 was the first).

## 2. Withdrawn: "the construction annihilates the Cauchy functional's sibling"

Section 2 argued that the built-in orthogonality of the selected construction is
the *integral* functional, and contrasted it with the Cauchy-weighted one. The
contrast is fine as intuition and wrong as a source statement. `integral
prolateCombination = 0` is a property of a function on `R`; `q_n` are the
coefficients of the **normalized projected** trial on `I_m` in the `V_n` basis.
Transporting a statement about the function to a statement about that
coefficient row needs a projection identity that I did not cite. C04.

## 3. Withdrawn: "the row is even"

Section 2 concluded `q_{-n} = q_n` from `h0_even` and `h4_even`. Same category
error, and here the catalogue actively contradicts the shortcut: the repository
carries `selectedFerrersFiniteCCMOddMass` precisely because the finite row has a
reflection-**odd** part, and
`selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates`
proves that part is small, not zero. Physical evenness gives asymptotic
smallness of the odd mass, never exact evenness of the finite row.

Every consequence I drew from exact evenness in `d2c044f7` is withdrawn. The
crosswalk of section 1 up to and including `(P')` does not use evenness on our
side and survives; only its restatement `q_0/beta^2 + 2 sum_{n>=1} ...` does.

## 4. Ledger

Ninth forbidden move: **a symmetry of the generating function is not a symmetry
of the projected coefficient row.** Between the function and the row there is a
projection and a normalization, and each may break the symmetry. Before using
evenness, oddness, or mean-zero of the row, cite the row-level theorem or the
projection identity — the repository has a whole file measuring exactly this
defect.

Tenth forbidden move: **do not repeat a `PAYOFF_IF_TRUE` clause from a verdict as
if it were adjudicated.** It is the judge's hypothesis, flagged as conditional in
its own name.
