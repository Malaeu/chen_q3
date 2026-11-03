# Bounded read-only final review of arithmetic-section integration

DIAGNOSTIC_NEVER_A_PROOF. Reviewed-file hashes are in final_review_inputs.json.
The reviewer authored the separate uniform component, but did not author the
reviewed root prose or arithmetic-section implementation. This is a bounded
code/conventions review, not an independent proof or interval certification.
The later all-n q4/q8 profile output is outside this read epoch.

Verdict: no calculation/sign/old-history-retention blocker found in
sections.py and validate_fine_scalar.py. Two wording corrections are requested
in the reviewed root RESULT.md:

1. The quantity with a sign and zero crossing is **1-lambda_max(Theta)**,
   not the planted matrix Theta itself. The former and the section margin
   have the same PSD boundary on identical combined node sets with all stated
   positive-block/baseline guards. Theta itself is positive semidefinite and
   its largest eigenvalue crosses one, not zero.
2. The comparison mu_q>=mu_full assumes the **full fresh form is positive**
   on its stated completion. Positivity of the finite F_q alone does not
   establish that assumption. Qualify the general comparison accordingly.
   The decisive section16 test lies below1/16 and therefore inside the
   source's proved short-form coercivity range; the rejection of the .1
   floor is unaffected. The code labels sections outside that proved range.

Checks of the arithmetic-section implementation:

- Old uniform increments cover (0,p*Delta), and the appended partial
  increment covers (p*Delta,log n). Thus the exact section anchor is retained;
  it is not silently rounded to a grid point. Partial increments also retain
  both endpoint contributions through the full stationary increment Gram.
- gram(g,left,right,fl,fr) computes
  g(right-fr)-g(right-fl)-g(left-fr)+g(left-fl), the correct mixed difference
  of K. This includes all old/new interactions and both source pole terms
  inherited from float_source. The fresh support is the actual arithmetic
  section length log((n+1)/n).
- The stored old Cholesky is used only on a leading positive prefix. The
  partial-old scalar pivot is checked before division. A nonpositive or
  unresolved partial pivot is labelled invalid/unresolved, not clipped or
  replaced with a pseudoinverse. Indefinite old uniform prefixes are rejected.
- After conditioning on the old uniform increments, v is the residual
  partial-old/fresh coupling. The total old-explained fresh Gram is
  Y_fresh^T Y_fresh + v^T v/pivot. This is precisely the Schur augmentation
  for the additional old partial increment. No old direction is dropped.
- Fresh Gram F is checked by Cholesky. The two triangular solves form
  L_F^(-1) G L_F^(-T), so 1-its largest eigenvalue has the intended
  generalized-eigenvalue normalization.
- The MP scalar checker uses the same full old grid plus exact partial
  endpoint, but an independent arbitrary-precision innovation whitening
  rather than float Cholesky. Its B columns have the correct mixed-difference
  signs. The final partial-old pivot and fresh variance D11 are both retained
  in 1-[G11+(D01-G01)^2/pivot]/D11. A separate dense32 check validates the
  innovation-whitening assembly without discarding old coefficients.

Scope of conclusions is appropriate after the wording corrections: a
validated finite upper approximant below.1 rejects that quantitative full
margin floor in the coercive section16 regime; it does not show a negative
zeta margin, collapse of the actual maximal step, or a new source sign law.
The numerical nesting across old grids and fresh subspaces is generic, so
four resolutions do not by themselves establish a zeta-specific power law.
The root cards preserve these limits, the planted/DH guards and the distinction
between a censored finite search and the full infinite-dimensional object.
