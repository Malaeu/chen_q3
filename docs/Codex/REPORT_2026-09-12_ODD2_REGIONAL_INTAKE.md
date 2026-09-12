# Regional ODD2 intake — min4/gap4 accepted, full goal open

Status: ACCEPT_REGIONAL_ODD2_MIN4_GAP4_ONLY.
Response kind: owner-direct same-chat continuation of REQ-2026-09-12-ODDCURV.
No new canonical request ID was assigned. Local observation label:
MANUAL-ODDCURV-FULL-SIGN-20260912.
Parent and sole independent checker completed the PAPER audit.
No Lean certification, canonical writer admission or RH claim is made.

## Receipt and exact source

The owner manually sent the continuation in the existing mathematical chat
https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13-rh-marz-2026/c/6aa52001-4094-83eb-9520-01a09f54eff2
and confirmed that send in this Codex task. The visible message is recorded in
`docs/routeB_bus/proshka/PROSHKA_MANUAL_FOLLOWUP_GOAL058_ODDCURV_2026-09-12.txt`.
Codex did not send a duplicate. The natural response displays `31m 16s nachgedacht`.
Completion was first observed near 2026-09-12T12:03Z; its exact instant was not
continuously measured. The complete download was copied unchanged to
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_ODDCURV_OWNER_CONTINUATION_2026-09-12.md`.
Its 39236 bytes, 651 LF, final LF and SHA256
`2281280161631905987633e895c34e980470bbeda517e3bc4c1df2ce2d0e9833`
match the producer receipt. Parent read all 651 lines. The response retains
the original ODDCURV request, boundary, six provenance fields and source base
7653a3503d20be4dba91a333ff96e5eea30c738c, explicitly marking manual continuation.

## Accepted theorem and exact remaining domain

With the unchanged normalized theta f, odd kernel K and alpha_z=pi exp(2z),
for every pair satisfying min(x,y)>=4 and |x-y|>=4:

`K(x,x)K(y,y)-K(x,y)^2 >= xy f(x)^2 f(y)^2/(128 alpha_x alpha_y) > 0`.

For every pair of complex coefficients, its two-node form is at least

`xy [f(x)^2|c1|^2+f(y)^2|c2|^2] / [192(x alpha_y+y alpha_x)]`.

The exact odd four-node V form is twice this two-node form, so the same
regional family of original consumer tests is proved with a factor2 floor.
This is a real regional sign-family theorem, not merely positive entries,
a finite grid, or the previous fixed-compact curvature statement.

After symmetry x>=y>0, the still-unpaid off-diagonal ODD2 domain is
`{x>y>0: y<4} union {x>y>=4: 0<x-y<4}`.
The diagonal has the exact equality Delta(x,x)=0.
The unpaid domain is noncompact. The new theorem supplies no IC sign,
even on its own domain; IC is sufficient for ODD2, with no converse proved.

## Parent decisive checks

1. The accepted full theta tail 0<=E(q)<=q^-4 yields
   `197/200<=H(q)=1-3/(2q)+E(q)<=1` for q>=100.
   For z>=2 and h>=0, the exact ratio f(z+h)/f(z) is bounded on both sides
   by the factors197/200 and200/197 times
   `exp(9h/2-alpha_z(exp(2h)-1))`.
   The upper ratio is at most `(200/197)exp(-lambda_z h)`, where
   `lambda_z=2alpha_z-9/2>=3alpha_z/2`.
   All higher theta modes remain in H. The square of200/197 is below21/20.

2. For 0<=v<=1/4, exp(2v)-1<=4v. The lower ratio squared and integration
   of the nonnegative diagonal term on that subinterval give
   `V(z,z)>=z f(z)^2 (197/200)^2(1-exp(-2alpha))/(4alpha)`.
   Using alpha>=100 and 1-exp(-2alpha)>=99/100 leaves a strict margin
   `642091/16000000` above z f(z)^2/(5alpha).
   The discarded part is positive, so the lower-bound direction is valid.

3. The entire reflected diagonal term is split at v=z/2. For 0<=v<=z/2,
   both z+v,z-v>=2. The exact two-sided source ratios cancel their linear
   exponents; `exp(2v)+exp(-2v)-2>=4v^2` bounds the product by
   `(21/20)f(z)^2 exp(-4alpha v^2)`. Its full comparison integral is
   `21 f(z)^2/(80alpha)`.
   For v>=z/2, evenness and the accepted concavity of log f(sqrt(u)) give
   `f(z+v)f(z-v)<=f(sqrt(z^2+v^2))^2`, including negative z-v.
   Substitution w=sqrt(z^2+v^2), with 2v dv=2w dw, and the full upper
   ratio give exactly the integral bound (17) starting at w0=sqrt(5)z/2.
   Since w0-z>=z/10 and w0<=3z/2, its dimensionless factor is at most
   `(21/20)(2z)exp(-20z)<=21/(2000z)<=21/8000`.
   Here exp(20z)>=(20z)^2/2. Summing the two pieces gives
   `V(z,-z)<3 f(z)^2/(10alpha)`, with rational margin279/8000.
   No reflected interval or infinite tail is omitted.

4. Subtracting that upper bound from the positive diagonal lower bound gives
   `K(z,z)>=z f(z)^2/(8alpha_z)` for z>=4: the last scalar comparison is
   exactly `3(z-4)/40>=0`.
   Integrating the full upper source ratio also gives
   `K(z,z)<=V(z,z)<=3z f(z)^2/(2alpha_z)`.

5. For x>=y>=4, V(x,-y)>=0 because its linear weight x-y+2v>=0.
   Inherited OD1 gives K(x,y)>0, so K(x,y)<=V(x,y) bounds the mixed term
   in the correct direction. The two source ratios give
   `K/(f(x)f(y)) <= (21/20)[(x+y)/lambda_x+2/lambda_x^2]`.
   Using x+y<=2x, lambda_x>=3alpha_x/2 and alpha_x x>=400 yields
   `K/(f(x)f(y))<=3x/(2alpha_x)` with rational margin293/3000.

6. For d=x-y>=4 and y>=4, x/y<=1+d/4. The function
   exp(2d)/(1+d/4) is increasing. At d=4, exp(8)/2>(8/3)^8/2>288,
   with exact last margin6499040/6561.
   Thus alpha_x/alpha_y>288x/y. The diagonal product minus the squared
   mixed upper bound is at least
   `xy/(64alpha_x alpha_y)-9x^2/(4alpha_x^2)` after removing f factors.
   Exactly the factor288 makes the subtraction at most half the first term,
   proving the stated128 denominator, uniformly throughout the region.

7. Divide each K_ij by f(x_i)f(x_j) via a positive invertible diagonal
   congruence. The normalized matrix has positive diagonal and determinant;
   its trace is at most `(3/2)(x/alpha_x+y/alpha_y)`.
   For its positive eigenvalues, lambda_min=det/lambda_max>=det/trace.
   This yields the coefficient floor with denominator192. Substituting
   `(f(x)c1,f(y)c2)` returns the original form for all complex coefficients.
   The accepted odd reflection identity supplies the factor2 on four nodes.

## Independent receipt, limits and owner-counter adjudication

The sole read-only checker `/root/sibling5_check` returned
`ACCEPT_REGIONAL_ODD2_MIN4_GAP4_ONLY` for the exact response SHA above.
It independently checked the full reflection split, diagonal and mixed bounds,
gap factor288, determinant floor and all-complex coercivity. It explicitly
inherited OD1, the full theta E bound and the Csordas concavity input.
The parent checks above agree. The uncertified diagnostic cell (1/5,4/5)
was neither used by the proof nor rerun by the reviewers.

Global IC and unrestricted ODD2 remain unproved and unrefuted. No negative
witness for either was supplied. The response records conservative full-target
count2->3 and a separate REGIONAL_PROOF_PROGRESS flag. These are different
facts: three cycles did not close the full target; the last cycle nevertheless
proved a real region of the actual consumer. It must not be described as a
tautological theorem or as proof of the whole target.

Parent adjudication: the owner's stop condition concerns three repetitions of
the same mathematical dead end without new progress, rather than any three
responses short of global completion. The verified theorem R supplies actual
two-node consumer forms for all complex coefficients on a nonempty unbounded
domain. It therefore counts as mathematical progress under that instruction.
Preserve the producer's full-target-incomplete count3 as historical bookkeeping;
reset consecutive same-obstacle no-new-result cycles from2 to0 only upon this
parent/independent acceptance. This does not reset killed classes, mark global
ODD2 complete, or treat the preceding curvature-only theorem as consumer closure.
The producer's requested pause is advisory, not new owner authority.

Continue with the precisely stated unpaid domain (28), retaining the diagonal
equality and the entire reflected integral. A new notation, an increased cutoff
or reproof of theorem R alone will not be new progress. The broad RH goal stays
active; owner escalation remains required upon the next actual sequence of
three same-obstacle no-progress cycles or a checked full RH candidate.

PX_RH_CLAIM: NOT_MADE.
