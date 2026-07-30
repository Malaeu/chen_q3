# 034 SESSION REGISTRATION — PRE-RUN PREDICTIONS (executor cell, 2026-07-29)

Scope of this session: transaction `034_COFINAL_SCALED_EDGE_SLIVER_MOMENT`,
STEP 0 (object lock), STEP 1 (abstract reduction), STEP 3 (m=257 regression),
plus exact statements of the STEP 2 suppliers. No repo access in this cell:
source hashes are imported-declared, not re-verified; Lean validation is
emitted as a standalone Aristotle task, not run here.

Judge: `check_034_edge_sliver_reduction.py` — exact rational arithmetic
(fractions) + exact symbolics (sympy); no floats in verdict-bearing checks;
contains planted violations that MUST be detected (C5, C9).

Registered BEFORE the checker run; wording may not drift afterwards.

```text
R034-1  The abstract reduction (034-edge) admits a complete proof from
        (H0) measurability, (H1) bridge |E| <= B*sqrt(u) on (0,1),
        (H2) a.e. sign on [A/lambda, lambda] ALONE; no certificate
        parameter (q=700, tau_response, box radii, Bernstein policy)
        enters any hypothesis or step.

R034-2  m=257 regression, exact numbers: conservativity margin
        4/3 - 257/195 = 1/65; crossing band of a = 4/3 is r = 192
        (257/193 < 4/3 < 257/192); planted A_edge = 5/4 FAILS the
        regression and the judge fires.

R034-3  The runnable plant subset {P2, P3, P4, P6, P8, P9-abstract,
        P10, P11} passes; P3 star identity equals (r+1)/(6r) exactly;
        P1, P5, P7-backend remain repo-emitted (cannot run here).

R034-4  Sharpness: the witness E0(u) = B*sqrt(u) on u < A/lambda, 0
        otherwise, satisfies all hypotheses and attains (034-edge) WITH
        EQUALITY at every sigma — the constant is optimal, no hidden slack.

R034-5  Uniform-in-sigma constant of the simple corollary:
        sup over sigma in [0,1/2) of ((4/3)^(1/2-sigma)-1)/(1/2-sigma)
        = 2*(2/sqrt(3)-1) = 0.3094011..., attained at sigma = 0;
        the sigma -> 1/2- limit is ln(4/3) = 0.2876821...

R034-6  Assembly of the m=257 instance: imports 033 (bands r=16..194 have
        epsilon_r = 0, i.e. certified S >= 0 on a in [257/195, sqrt(257)])
        + 027 (E_star <= 0 on u in [1, lambda], i.e. a in [sqrt(257), 257])
        cover [4/3, 257] a.e. => hypothesis (S) holds at (m=257, A=4/3)
        and the m=257 edge bound is unconditional GIVEN those two imports.
```

Most likely failure point (registered): normalization drift between the
033-contract crosswalk form E_star(h_lambda, lambda*z) = -(I0*I4/D)*sqrt(z/lambda)*S_lambda(z)
and the 034 scaled form E_star = -C_m*sqrt(a)/lambda^(3/2)*S_m(a).
Pre-planned response: the reduction consumes only the SIGN of the prefactor
(C_m > 0, source-locked) plus (H1)/(H2) as abstract hypotheses, so a
normalization error cannot corrupt the reduction; it would surface at
supplier-consumption time as SCALED_EDGE_OBJECT_MISMATCH.
