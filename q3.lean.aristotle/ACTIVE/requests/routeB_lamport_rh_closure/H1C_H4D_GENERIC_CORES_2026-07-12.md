# Route B H1c/H4d generic cores — revision 16

Status: `TWO_UNCONDITIONAL_LEAN_CORES_PROVED / EXACT_CROSSWALKS_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS`

This worker transaction does not change the unique canonical ACTIVE leaf
`D0.7e.5a`, select `RAW_GLOBAL` or `COMPLETED_STRIP`, define the master family
`F_j`, close an exact SAFE leaf, create Bus 010, or prove RH.

## 1. H1c source formula: removable poles are now Lean objects

H8 Proposition 5.9 gives, for `L>0` and a finite coefficient vector,

```text
L^(-1/2) * 2 sin(zL/2) * sum_k xi_k/(z-2pi k/L).
```

The displayed quotient is misleading at the lattice points.  The source says
that every apparent pole cancels.  The Lean file
`Q3/Proofs/RouteB/Proposition59EntireTransform.lean` encodes each summand as

```text
dslope (2 sin(L * . / 2)) (2pi k/L).
```

This is the canonical removable extension.  Lean proves:

- the numerator vanishes at every source lattice point;
- off the lattice, the kernel is exactly the Proposition-5.9 quotient;
- on its own lattice point, the kernel is the finite derivative value
  `L*cos(pi*k)`;
- every kernel and every finite coefficient sum are globally complex
  differentiable;
- off the finite lattice, the finite sum equals the printed common-numerator
  formula.

Verdict: `PROPOSITION59_RHS_ENTIRE`.

This is not yet `EXACT_RAW_TRANSFORM_LOCKED`.  The remaining mathematical
crosswalk must prove that the exact phase-centered integral built from
`finiteLogFourierTrial` equals this removable formula also at the lattice.
After that, a separate D0.8/owner decision must identify the master `F_j` with
the raw ground transform rather than the completed trial tracker.

Exact residual stops:

- `H1C_RAW_INTEGRAL_RHS_CROSSWALK_MISSING`;
- `H1_EXACT_APPROXIMANT_SOURCE_UNPINNED`;
- `H1_MASTER_ARCHITECTURE_CHOICE_REQUIRED`.

## 2. H4d generic cofinal square core

The old H4d1 theorem handled only the natural scale `n`.  The exact Route B
must eventually use one joint `(m,N)` filter.  The new Lean theorem
`safe_rate_cofinal_square_core` proves the filter-correct statement.

For an arbitrary non-bottom filter `l`, if

```text
scale -> +infinity,
r_Delta-r_alpha > 2q_b+1,
0 <= W eventually,
W^2 <= (C scale^(q_b+(1+r_alpha-r_Delta)/2))^2 eventually,
```

then `W -> 0` along `l`.  The `[NeBot l]` hypothesis is essential: without it,
the bottom filter would certify a vacuous witness.  The companion assembly
theorem also exports the strict negativity of the polynomial exponent.

Verdict: `LEAN_SAFE_RATE_COFINAL_SQUARE_CORE` and
`LEAN_SAFE_RATE_GENERIC_PACKAGE`.

The exact H4d2 leaf remains OPEN.  It must derive the squared envelope, with
the correct constant `C_b*sqrt(C_alpha/c_Delta)`, from the exact WPrime
identity, SafeAlphaUpper, SafeGapLower, SafeSignAndB, and one selected joint
filter.  No such constants, filter, or exact bounds are inferred here.

Exact residual stops:

- `H4D_FILTER_BOT_VACUITY` (now guarded generically);
- `H4D_COFINAL_SCALE_MISSING`;
- `H4D_WPRIME_SQUARE_ENVELOPE_MISSING`;
- `H4_LIMIT_FILTER_UNSELECTED`;
- `H4D_EXACT_CONSTANTS_MISSING`.

## 3. Honesty boundary

The source-entire theorem quantifies over every finite vector, so it is usable
for a future ground vector or a trial vector.  It does not prove that those are
the same vector.  The rate theorem quantifies over every valid cofinal filter,
but it does not supply one.  Thus both results remove generic mathematics
without consuming either missing exact object.

The canonical stop remains `D0_7E_WPRIME_CONSUMER_MISSING`; Route B remains
`CHALLENGER / NOT_RH`.
