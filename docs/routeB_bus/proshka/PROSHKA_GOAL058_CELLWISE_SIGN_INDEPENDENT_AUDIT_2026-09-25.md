# Goal058 cellwise complement sign: independent PAPER audit

Status: `OPEN_FIRST_SIGN`, not a proof or disproof of eventual `d_j > 0`.
Request: `REQ-2026-09-25-CELLWISE-COMPLEMENT-SIGN`, SHA-256
`7349cae1277d96576aaf26c2bc69d271b532766747e57c3e42530213c23c9602`.
Source: [project chat](https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ab6827b-387c-83eb-a71d-865f68d835d5), completed answer message
`c1910ff1-2d30-46ed-9c42-d4ad89a7f2c1`. The browser answer-copy Markdown is preserved byte-for-byte in
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CELLWISE_COMPLEMENT_SIGN_2026-09-25.md`
(13,151 bytes, no final LF, SHA-256
`970c8b37a7e70c7c2ce94c35779bd8f360dc8085cef4d88f03004e1db6f6b556`).
The answer displayed no attached file tile; its only visible link was the CCM arXiv source.

## Independently checked step

The orthonormal approximate-null plane `U_j=span_C{u_j,v_j}` and the overlap
`|q_j*u_j|² -> 1` are imported from the previously audited PAPER argument,
not reproved here. With `alpha=q*u` and `gamma=q*v`, the verdict's
`z=(alpha v-gamma u)/sqrt(|alpha|²+|gamma|²)` is a unit vector in `U_j ∩ q_j^perp`.
No conjugation of `alpha` or `gamma` belongs in that numerator. Therefore
`||K_j z|| <= epsilon_j`, `d_j <= tau_j := z*K_j z-a_j`, and
`|z*K_j z| <= epsilon_j`. These inequalities give no sign for `tau_j`.

The exact source matrix is `W02-WR-Prime`: `ccmQKernel` has the separate
diagonal branch (`CCMFiniteWeilSourceMatrixN1.lean:40-46`), the prime entry
sums every integer `2 <= k <= m_j` with von Mangoldt weight (`:56-60`),
and `ccmWREntry` includes the full archimedean integral and constant
(`:90-100`). The W02 integral pairing and its equality to the source entry
are in `D0PstarSourceW02ModePairing.lean:12,640`; the finite-form lift and
three-part crosswalk are in `D0PstarSourceW02FiniteFormCCMW02Crosswalk.lean:14`
and `D0PstarSourceWeilFiniteFormCCMWeilCrosswalk.lean:17`.
For unit `z_j,q_j`, their `Q_L` difference is zero at `x=0`, so the WR
constant and its subtractive numerator value cancel. W02 contributes the
`2 cosh(x/2)` term, WR the negative kernel term, and Prime the full negative
sum in verdict (7). Both branches of `Q_L` vanish at `x=L`; their right
derivative at zero is `-2/L`, yielding verdict (8). The diagonal for `x>0`,
all prime powers, and both window edges remain in (7).

The finite-dimensional Schur identity (9)-(11) is exact on the full complex
`q_j^perp = C z_j ⊕ {q_j,z_j}^perp`. Thus `d_j>0` is equivalent to both
`tau_j>0` and positivity of `D_j-eta_j eta_j*/tau_j` on the remaining
complement. This is an equivalence, not a supplier of either sign.
Verdict (13) is precisely `tau_j <= 0` written in the full source form;
if proved on unbounded selected indices it would kill eventual positivity.
No such signed estimate is supplied. An `o(1)` upper bound cannot decide it.

For verdict (5), the case `|alpha|=1` makes `w=u-alpha q=0`, but then
`u=alpha q`, so `a=u*K_j u` and `|a|<=epsilon_j`; the hypothesis
`a<-6 epsilon_j` is impossible. Equivalently, the verdict's strict negative
quadratic estimate already excludes `w=0`. There is no remaining gap in (5),
and eventual `a_j -> 0` is a consequence *if* `d_j>0`, not a premise.

## Review disposition

| Pass | Original label | Finding and disposition |
| --- | --- | --- |
| 1 | none | On-target check of (1)-(13) found no material issue. |
| 2 | WORDING | The exact-alignment `w=0` edge case was challenged and resolved above; no mathematical correction to the verbatim source is needed. The full-source equality and test direction remained clean. |

Two consecutive on-target native review passes found no unresolved
CRITICAL, HIGH, MEDIUM, or LOW findings. A separate Luna source read confirmed
the CCM definitions and full-form crosswalk. Neither review ran Lean or the
project workflow runtime. Browser provenance was checked by the current owner
from the live chat; reviewers audited the preserved bytes, not the UI action.

Next PAPER target: a genuinely signed estimate for `tau_j` in (7) on the same
selected family, followed (if positive) by the Schur inequality in (12).
The response's (13) names the obstruction but does not prove it.

## Independent follow-on: leakage-energy identity

This is our calculation after the verdict, not a claim made by Proshka.
Let `p_j=Pi_{U_j} q_j` and `ell_j=q_j-p_j`; `ell_j` denotes leakage of the
trial row out of the approximate-null plane and must not be confused with
the already named spectral residual `(K_j-a_j I)q_j`. Then
`||p_j||²+||ell_j||²=1` and `||ell_j||² <= 1-|q_j*u_j|² -> 0`.
Expansion of `q_j=p_j+ell_j` gives the exact identity

`tau_j = -ell_j* K_j ell_j + E_j`,

`E_j = z_j* K_j z_j - p_j* K_j p_j - 2 Re(ell_j* K_j p_j)`.

The action bound on `U_j` implies
`|E_j| <= epsilon_j(1+||p_j||²+2||p_j||||ell_j||) <= 3 epsilon_j`.
Thus `ell_j* K_j ell_j > 3 epsilon_j` would give `tau_j<0` and a
cellwise nonpositive witness; `ell_j* K_j ell_j < -3 epsilon_j` would give
`tau_j>0` but still not the Schur sign. Neither signed inequality has been
proved for the selected CCM coefficients. The current sources bound `K_j`
on `U_j`, not its quadratic energy on the leakage component.

The hypotheses alone allow both signs of `tau`: in `C³`, take
`U=span(e1,e2)`, `q=sqrt(1-delta)e1+sqrt(delta)e3`, `z=e2`,
`delta=epsilon²`, and `K_±=diag(0,0,±1)`. Then `K_± U=0`, the overlap tends
to one, and `tau_±=∓delta`. These are abstract countermodels to a sign
deduced solely from the plane and overlap bounds; they are not CCM
counterexamples and do not assert opposite signs for the full `d_j`.
The identity, `3 epsilon_j` bound, and this scope distinction received an
independent native review with no findings.
