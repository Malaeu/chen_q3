# Goal 058 G3 — actual-mode final source Mythos verdict

Date: 2026-08-15
Role: Mythos proof/source architecture only
Request commit: `c8c31368b8f0eae514c339999f192e5bc16d237e`
Request SHA-256: `d24b2830e8face3d431583778a2f0d0f8c7a51e4ff06aa777bc9141c32488220`
Transport: in-app browser, living Mythos chat `6a7e2bb9-dfd4-83ed-9ac5-b93536281fc6`
Natural reasoning: completed without using `Answer now` or interrupting generation.
Boundary: external architecture verdict, not Lean proof and not judge acceptance.

## Browser-extracted Mythos response

The text below preserves the browser response content; trailing spaces were
removed mechanically to satisfy repository whitespace checks.

STATUS: OPEN — DECISION B; TWO SOURCE CARRIERS REQUIRED BEFORE LOCAL ACTUAL-MODE ASSEMBLY
YAML
DECISION: TWO_MINIMAL_SOURCE_CARRIERS_THEN_LOCAL_ASSEMBLY


REQUEST:
  COMMIT: c8c31368b8f0eae514c339999f192e5bc16d237e
  SHA256_EXPECTED: d24b2830e8face3d431583778a2f0d0f8c7a51e4ff06aa777bc9141c32488220
  SHA256_VERIFIED: true


EVIDENCE_HEAD: efbf549894a825404911995b45003d3c65e8840a


SOURCE_STATE:
  PAPER_CHAIN_COMPLETE: true
  LEAN_SOURCE_CARRIERS_MATERIALIZED: false
  LOCAL_TRANSPORT_ARCHITECTURE_BOUNDED: true
  FINAL_ACTUAL_MODE_ASSEMBLY_PROVED: false


SOURCE_CARRIERS:
  - SELECTED_FERRERS_DLMF_ZERO_COUNT_SOURCE
  - SELECTED_FERRERS_SLEPIAN_PHASE_ORDER_SOURCE


REJECTED_DECISIONS:
  A_LOCAL_PROOF_FROM_EXISTING_SOURCE_OBJECTS: NO_LEAN_SOURCE_DECLARATIONS
  C_ONE_COMBINED_SELECTED_MODE_SOURCE_CARRIER: HIDES_TWO_INDEPENDENT_SOURCE_LAWS
  D_SOURCE_CHAIN_STILL_INCOMPLETE: PRIMARY_STATEMENTS_ARE_PINNED


ARISTOTLE_READY: NOT_READY
ARISTOTLE_OWNED_FILE_AND_TARGETS: NONE
CODEX_EXECUTION_AUTHORIZED: false
REPO_WRITE_AUTHORIZED: false


NEW_STOP_CODE: GOAL058_G3_DLMF_ZEROCOUNT_AND_SLEPIAN_PHASEORDER_CARRIERS_PENDING


G1_CLOSED: false
G3_CLOSED: false
ROUTE_B_PROMOTED: false
RH_CLAIMED: false
ROUTE_STATE: CHALLENGER_NOT_RH
DECISION:
B. TWO_MINIMAL_SOURCE_CARRIERS_THEN_LOCAL_ASSEMBLY
	​


The zero-count law and the finite-Fourier phase/order law must remain separate.

They come from different operators and preserve different data:

the DLMF/Sturm law identifies the differential degree through interior zeros and is invariant under nonzero rescaling;

the Slepian–Pollak law identifies the finite-Fourier scalar through the kernel sign, physical scale, phase i
n
, and the ordered concentration spectrum.

Combining them into one carrier would conceal exactly the sign, scale, and index mutations that the request requires us to detect. This is a C04 same-coordinates/two-laws and C10 functional-not-surrogate issue. [ABSTRACT][PAPER]

Decision A is rejected because the repository currently contains the selected solutions, production pair, nonzero real Fourier scalars, and orthogonality, but no Lean declaration proving the classical zero law or positive-phase concentration law. The remaining four fields are explicit in IsActualProlateModePair.
GitHub
+2
GitHub
+2
 [ABSTRACT][LEAN]

Decision D is rejected because the necessary primary statements are located: DLMF gives the exact zero count, and Slepian–Pollak gives the Fourier phase, positive concentration eigenvalues, and their strict order.
Mathematik UCDavis
+4
DLMF
+4
Mathematik UCDavis
+4
 [ABSTRACT][PAPER]

SMALLEST_SOURCE_OBJECTS:

The carriers must state source laws before physical zero extension. They must not contain:

IsActualProlateModePair P
0 < P.chi2
P.chi2 < P.chi0
physical production zero counts

as imported fields.

1. Zero-count carrier

Use the exact selected Ferrers solution and the general degree formula 2j. Do not import the two final physical counts separately.

lean
def selectedFerrersInteriorZeros
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) : Set ℝ :=
  {t | t ∈ Set.Ioo (-1 : ℝ) 1 ∧
    mode4FerrersSeries S.coefficients t = 0}


theorem selectedFerrersDLMFZeroCountSource
    (mProject K j : ℕ)
    (hj : j = 0 ∨ j = 2)
    (S : Mode4FerrersRegularEvenProlateSolution mProject K
      (mode4ClassicalEvenEigenvalue
        (mode4JacobiG mProject) j)) :
    (selectedFerrersInteriorZeros S).Finite ∧
    (selectedFerrersInteriorZeros S).ncard = 2 * j

This is the smallest honest DLMF source theorem:

j is the zero-based even carrier index;

the full spheroidal degree is n=2j;

DLMF m
sph
	​

=0 gives n−m
sph
	​

=2j interior zeros.

It is not a physical ProlatePair conclusion. [ABSTRACT][PAPER]

DLMF states that Ps
n
m
	​

 has exactly n−m zeros in (−1,1). The project has already materialized the strict selected-carrier identification, including the unique index j=2 corresponding to degree four.
DLMF
+1
 [ABSTRACT][PAPER]

2. Phase/order carrier

First use a separate dimensionless action:

lean
noncomputable def mode4SlepianC (mProject : ℕ) : ℝ :=
  2 * Real.pi * (mProject : ℝ)


noncomputable def selectedFerrersDimensionlessFourierAction
    (c : ℝ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∫ s in Set.Icc (-1 : ℝ) 1,
    Complex.exp
      (Complex.I * ((c * t * s : ℝ) : ℂ)) *
        (mode4FerrersSeries a s : ℂ)

The source theorem must then be:

lean
theorem selectedFerrersSlepianPhaseOrderSource
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (S0 : Mode4FerrersRegularEvenProlateSolution mProject K
      (mode4ClassicalEvenEigenvalue
        (mode4JacobiG mProject) 0))
    (S4 : Mode4FerrersRegularEvenProlateSolution mProject K
      (mode4ClassicalEvenEigenvalue
        (mode4JacobiG mProject) 2)) :
    ∃ kappa0 kappa4 : ℝ,
      0 < kappa4 ∧
      kappa4 < kappa0 ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1,
        selectedFerrersDimensionlessFourierAction
            (mode4SlepianC mProject) S0.coefficients t =
          (Complex.I ^ (0 : ℕ)) *
            (((Real.sqrt
                (2 * Real.pi / mode4SlepianC mProject) *
              Real.sqrt kappa0 : ℝ) : ℂ)) *
            (mode4FerrersSeries S0.coefficients t : ℂ)) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1,
        selectedFerrersDimensionlessFourierAction
            (mode4SlepianC mProject) S4.coefficients t =
          (Complex.I ^ (4 : ℕ)) *
            (((Real.sqrt
                (2 * Real.pi / mode4SlepianC mProject) *
              Real.sqrt kappa4 : ℝ) : ℂ)) *
            (mode4FerrersSeries S4.coefficients t : ℂ))

Here kappa0 and kappa4 are the positive concentration eigenvalues. This name avoids collision with:

Slepian’s differential eigenvalues χ
n
	​

(c);

the project’s Fourier scalars P.chi0 and P.chi2;

the physical window parameter λ.

The carrier imports an exact operator identity and strict source ordering. It does not import the final project inequalities. [ABSTRACT][PAPER]

Slepian–Pollak equation (25) supplies the factor 2i
n
R
0n
(1)
	​

(c,1). Equation (27) gives the square-magnitude relation with a strictly positive concentration eigenvalue, and the paper orders those eigenvalues strictly as κ
0
	​

>κ
1
	​

>⋯.
Mathematik UCDavis
+3
Mathematik UCDavis
+3
Mathematik UCDavis
+3
 [ABSTRACT][PAPER]

Hostile guard: equation (27) alone is insufficient. It is unchanged by

R
0n
(1)
	​

(c,1)↦−R
0n
(1)
	​

(c,1).

Therefore the judge packet must pin the source normalization equivalent to

μ
n
	​

=i
n
∣μ
n
	​

∣.

Without that sign pin, the carrier proves magnitude and nonvanishing only, not positive phase. The project dossier records exactly this convention and warns that the kernel sign must match.
GitHub
+1
 [ABSTRACT][PAPER]

EXACT_SOURCE_PINS:
Zero count and degree

DLMF §30.4(ii):

Ps
n
m
	​

(x,γ
2
) has exactly n−m zeros in (−1,1).

At m=0, degrees n=0,4 give counts 0,4. DLMF §30.4.3 also fixes parity (−1)
n−m
.
DLMF
 [ABSTRACT][PAPER]

DLMF selector already materialized:

p
DLMF
	​

=⌊
2
n−m
	​

⌋+1.

Hence

(m,n)=(0,0)⇒p=1,(m,n)=(0,4)⇒p=3.

The corresponding zero-based even index is

j=p−1=0,2.

This index work is finished and must not be reopened.
GitHub
+2
GitHub
+2
 [ABSTRACT][LEAN]

Bonami–Karoui, arXiv:1405.3676, independently records that ψ
n
	​

 has exactly n interior zeros, parity matching n, and strictly increasing differential eigenvalues. It is corroborating, not the minimal carrier pin.
arXiv
+1
 [ABSTRACT][PAPER]

Fourier phase and order

Slepian–Pollak (1961), equation (25):

∫
−1
1
	​

e
icts
S
0n
	​

(c,s)ds=2i
n
R
0n
(1)
	​

(c,1)S
0n
	​

(c,t).

This fixes the plus-kernel phase before physical scaling.
Mathematik UCDavis
 [ABSTRACT][PAPER]

Equations (26)–(27) define the positive concentration operator and

κ
n
	​

(c)=
π
2c
	​

[R
0n
(1)
	​

(c,1)]
2
.

The kernel is positive definite, so every κ
n
	​

(c) is strictly positive.
Mathematik UCDavis
 [ABSTRACT][PAPER]

Section VI/order theorem:

κ
0
	​

(c)>κ
1
	​

(c)>κ
2
	​

(c)>⋯.

In particular,

0<κ
4
	​

(c)<κ
0
	​

(c).

Mathematik UCDavis
+1
 [ABSTRACT][PAPER]

Exact sign-normalization pin still required in the judge packet:

μ
n
	​

=i
n
c
2π
	​

	​

κ
n
	​

	​

.

The equations above determine the magnitude; the positive radial/source convention determines the sign. [ABSTRACT][PAPER]

PROJECT_DLMF_SLEPIAN_CROSSWALK:

Let

ℓ:=
mProject
	​

>0.
Scale and ODE dictionary
x=ℓt,y=ℓs.

The project’s physical window is

[−ℓ,ℓ].

The exact Slepian bandwidth is

c=2πℓ
2
=2πmProject.
	​


The project’s dimensionless ODE parameter is

G=mode4JacobiGmProject=(2πmProject)
2
=c
2
.
	​


The project physical-scaling file states this identity explicitly, and the project ODE uses the physical potential (2πℓu)
2
.
GitHub
 [ABSTRACT][LEAN]

Notation must remain separated:

DLMF γ²:
  G = c².


DLMF differential eigenvalue λ_n^0(γ²):
  project mode4ClassicalEvenEigenvalue G j.


Slepian differential χ_n(c):
  project physical theta_j
  = mode4ClassicalEvenEigenvalue G j + G.


Slepian concentration eigenvalue:
  renamed kappa_n in this packet.


Project P.chi0 / P.chi2:
  finite-Fourier scalars, not differential eigenvalues.
Kernel dictionary

The project kernel is literally

e
+2πixy
.

After x=ℓt and y=ℓs,

e
2πixy
=e
2πiℓ
2
ts
=e
icts
.

Thus the project uses the same plus-phase convention as Slepian equation (25).
GitHub
+1
 [ABSTRACT][LEAN]

Index dictionary
DLMF spheroidal order:
  m_sph = 0.


DLMF one-based even selector:
  p = 1, 3.


Zero-based even carrier:
  j = p - 1 = 0, 2.


Full physical degree:
  n = 2j = 0, 4.


Production names:
  n = 0 ↔ S0 ↔ P.h0 ↔ P.chi0
  n = 4 ↔ S4 ↔ P.h4 ↔ P.chi2

The field P.chi2 names the scalar attached to zero-based even carrier j=2, which is full degree n=4. It must never be renamed chi4, and it must never be interpreted as the scalar of full degree 2. The repository source lock explicitly records h4 ↔ chi2, never h4 ↔ chi4.
GitHub
 [ABSTRACT][LEAN]

Fourier scalar scaling

If the dimensionless source satisfies

F
c
	​

ψ
n
	​

=μ
n
	​

ψ
n
	​

,

then the physical source satisfies

F
ℓ
project
	​

h
n
	​

=ℓμ
n
	​

h
n
	​

.

Using

μ
n
	​

=i
n
c
2π
	​

	​

κ
n
	​

	​


and c=2πℓ
2
,

ℓ
c
2π
	​

	​

=1.

Therefore

P.chi0=i
0
κ
0
	​

	​

=
κ
0
	​

	​

,
P.chi2=i
4
κ
4
	​

	​

=
κ
4
	​

	​

.

Hence, locally,

0<P.chi2<P.chi0.

The inequalities are consequences of the exact source identity, Real.sqrt_pos, and strict monotonicity of square root. They are not imported as source fields. [ABSTRACT][CONDITIONAL]

EXACT_FIRST_LEAN_HEAD:

After the two source declarations are ratified and materialized, the first bounded local theorem should be:

lean
theorem selectedFerrersProduction_remainingActualFields
    {mProject K : ℕ}
    (hm : 2 ≤ mProject)
    (S0 : Mode4FerrersRegularEvenProlateSolution mProject K
      (mode4ClassicalEvenEigenvalue
        (mode4JacobiG mProject) 0))
    (S4 : Mode4FerrersRegularEvenProlateSolution mProject K
      (mode4ClassicalEvenEigenvalue
        (mode4JacobiG mProject) 2))
    (P : D0Pstar.ProlatePair)
    (hlambda : P.pw.lambda = Real.sqrt mProject)
    (hP0 : P.h0 = S0.normalizedPhysicalMode)
    (hP4 : P.h4 = S4.normalizedPhysicalMode)
    (hFourier0 :
      ∀ x ∈ Set.Icc (-P.pw.lambda) P.pw.lambda,
        D0Pstar.finiteFourierAction
            P.pw.lambda P.h0 x =
          (P.chi0 : ℂ) * P.h0 x)
    (hFourier4 :
      ∀ x ∈ Set.Icc (-P.pw.lambda) P.pw.lambda,
        D0Pstar.finiteFourierAction
            P.pw.lambda P.h4 x =
          (P.chi2 : ℂ) * P.h4 x) :
    0 < P.chi2 ∧
    P.chi2 < P.chi0 ∧
    (D0Pstar.prolateInteriorZeros
      P.pw.lambda P.h0).Finite ∧
    (D0Pstar.prolateInteriorZeros
      P.pw.lambda P.h0).ncard = 0 ∧
    (D0Pstar.prolateInteriorZeros
      P.pw.lambda P.h4).Finite ∧
    (D0Pstar.prolateInteriorZeros
      P.pw.lambda P.h4).ncard = 4

This head contains no requested conclusion as a binder. Its inputs are only:

exact production witness identities;

exact production Fourier relations already proved;

the physical scale identity already proved.

The proof calls the two named source declarations. The production theorem already supplies these local inputs for one exact P.
GitHub
 [ABSTRACT][CONDITIONAL]

The head is mathematically bounded but not currently compilable because the two source declarations are not on disk. It is therefore not yet an Aristotle task.

LOCAL_PROOF_CHAIN:

ROUTE MAP

selected j = 0,2 Ferrers witnesses
        │
        ├── DLMF source:
        │     dimensionless ncard = 2j
        │
        ├── Slepian source:
        │     exact plus-phase scalar
        │     + positive ordered concentration values
        │
        ▼
local physical scaling and zero-set transport
        │
        ▼
remaining four IsActual fields
        │
        ▼
same-witness production assembly
        │
        ▼
IsActualProlateModePair P
Zero transport

For each selected solution S, prove:

prolateInteriorZeros(ℓ,S.normalizedPhysicalMode)={ℓt:t∈Z
S
	​

},
	​


where

Z
S
	​

={t∈(−1,1):mode4FerrersSeries(S.coefficients,t)=0}.

The current definitions suffice:

x∈(−ℓ,ℓ) implies the closed-window indicator equals 1;

the physical mode is the dimensionless series at x/ℓ;

the normalization is strictly positive;

t↦ℓt is injective because ℓ>0.

The zero extension does create zeros outside the window, and it may create endpoint zeros. Those zeros are intentionally excluded by prolateInteriorZeros, which uses Ioo, not Icc.
GitHub
+2
GitHub
+2
 [ABSTRACT][LEAN]

Then transport finiteness and ncard through the injective scale map:

2⋅0=0,2⋅2=4.
Scalar transport

Rescale the exact dimensionless Slepian relations.

Obtain physical restricted-Fourier relations with scalars

κ
0
	​

	​

,
κ
4
	​

	​

.

Compare these with the already stored relations using the nonzero normalized modes.

Conclude

P.chi0=
κ
0
	​

	​

,P.chi2=
κ
4
	​

	​

.

Apply positivity and strict monotonicity of Real.sqrt.

The current local theorem proves only that the stored scalars are real and nonzero; it explicitly does not prove their signs or order.
GitHub
+1
 [ABSTRACT][LEAN]

Final same-witness assembly

Do not splice one existential witness from

lean
exists_modeZero_modeFour_selectedFerrersProductionProlatePair

with an independently unpacked witness from

lean
exists_modeZero_modeFour_selectedFerrersProductionProlatePair_orthogonal.

Lean does not identify two separately chosen existential triples.

The final assembly must either:

construct one S0, S4, P from the production theorem and rerun the already-proved generic orthogonality lemma on those same objects; or

strengthen the orthogonality wrapper to retain all production fields, including P.pw.lambda = sqrt mProject.

The generic orthogonality lemma and the production construction are already on disk.
GitHub
+1
 [ABSTRACT][LEAN]

K1_K6_DISPOSITIONS:

K1 — source object:
Two carriers are mandatory. Splitting is not cosmetic: zero count belongs to the singular Sturm–Liouville source, while phase/order belongs to the finite-Fourier/concentration source. [ABSTRACT][PAPER]

K2 — conventions:
The exact dictionary is:

ℓ=
mProject
	​

,c=2πℓ
2
,G=c
2
,γ
2
=G,
p
DLMF
	​

=1,3,j=0,2,n=0,4,

with plus kernel e
+2πixy
. P.chi2 belongs to degree 4. [ABSTRACT][LEAN]

K3 — zero transport:
Yes, purely local. The required equality is the image identity above. Positive normalization and the indicator definition suffice on the open physical window. Whole-line zero-set equality is false and must not be attempted. [ABSTRACT][LEAN]

K4 — phase/order:
Yes, after importing the exact phase identity and concentration order. The minimal scalar source data are:

0<κ
4
	​

<κ
0
	​

,
μ
0
	​

=i
0
2π/c
	​

κ
0
	​

	​

,μ
4
	​

=i
4
2π/c
	​

κ
4
	​

	​

.

Equation (27) without the phase convention is insufficient. [ABSTRACT][PAPER]

K5 — Lean eligibility:
The local transport is bounded and ordinary Lean analysis. The source theorems are not Aristotle obligations. No execution is ready until Proshka ratifies and materializes the two source declarations. [ABSTRACT][CONDITIONAL]

K6 — falsifiers:
All requested mutations are covered below. [ABSTRACT][CONDITIONAL]

STRONGEST ATTACK

The strongest reviewer objection is:

Equation (27) only determines the square of the Fourier eigenvalue. Your claimed positive phase is a sign choice disguised as a theorem.

That objection is valid unless the packet contains the exact normalization pin

μ
n
	​

=i
n
∣μ
n
	​

∣.

Therefore the Slepian carrier must include the exact operator identity with phase, not merely positive concentration eigenvalues. [ABSTRACT][PAPER]

PLANTED_FALSIFIERS:
G3_ACTUAL_F1_SECOND_EVEN_IS_NOT_DEGREE_FOUR

Mutation:

p = 2
j = 1
n = 2

while labeling it “mode four”.

Expected failure:

zero count=2

=4,i
2
=−1

=+1.

The correct mode four is the third even mode:

p = 3
j = 2
n = 4

[ABSTRACT][PAPER]

G3_ACTUAL_F2_PLUS_MINUS_KERNEL_SIGN

Mutation:

e
+icts
↦e
−icts
.

Important discriminator: for the target degrees 0 and 4,

i
n
=(−i)
n
=1.

Therefore an even-mode-only phase test cannot detect the kernel-sign mutation.

Required plant:

check the exponent crosswalk symbolically before specializing the degree; and

include an odd control degree n=1, where +i mutates to −i.

Any packet claiming that n=0,4 alone distinguishes the kernel sign fails. [ABSTRACT][CONDITIONAL]

G3_ACTUAL_F3_SCALE_MISSING_2PI

Mutations:

c = lambda²
c = 2*pi*lambda
G = c

instead of

c = 2*pi*lambda²
G = c²

Expected failure:

2πxy

=cts

after x=λt, y=λs, or the physical ODE potential no longer matches mode4JacobiG. [ABSTRACT][LEAN]

G3_ACTUAL_F4_CHI2_CHI4_NAME_SWAP

Mutation:

h4 ↔ P.chi4

or:

P.chi2 ↔ full degree n=2.

Expected failure: the production record has chi2, and its source meaning is the scalar of zero-based even carrier j=2, hence full degree 4. [ABSTRACT][LEAN]

G3_ACTUAL_F5_WHOLE_LINE_ZEROSET_TRANSPORT

Mutation:

Z(zero extension)=λZ(dimensionless mode)

as whole-line sets.

Expected failure: the zero extension vanishes at every exterior point. The correct theorem restricts both sides to the interior open window. Endpoint and exterior zeros are not counted. [ABSTRACT][LEAN]

G3_ACTUAL_F6_NONZERO_IS_NOT_POSITIVE

Mutation:

chi2 = -1

This satisfies chi2 ≠ 0 and must fail the positive-phase source carrier.

The current local nonvanishing theorem alone must not discharge 0 < chi2. [ABSTRACT][LEAN]

G3_ACTUAL_F7_POSITIVE_MAGNITUDES_DO_NOT_GIVE_ORDER

Mutation:

kappa0 = 1
kappa4 = 1

or the reversed pair:

kappa0 = 1
kappa4 = 4

Both magnitudes are positive, but neither supplies

κ
4
	​

<κ
0
	​

.

Strict concentration order is a separate source field. [ABSTRACT][PAPER]

G3_ACTUAL_F8_EQ27_SIGN_BLINDNESS

Mutation:

R
0n
(1)
	​

(c,1)↦−R
0n
(1)
	​

(c,1).

Equation (27) survives unchanged; equation (25) changes the finite-Fourier scalar sign. This plant forces the exact phase-normalization pin into the source packet. [ABSTRACT][PAPER]

ARISTOTLE_READY:
NOT_READY

Reason:

The two mathematical source declarations do not exist in Lean.

The exact positive-phase normalization excerpt must be attached and ratified.

Aristotle may prove local scaling and set transport, but it may not manufacture the external DLMF or Slepian source theorem.

This verdict is architecture only and grants no execution authority.

[ABSTRACT][CONDITIONAL]

ARISTOTLE_OWNED_FILE_AND_TARGETS:
NONE

No file, job, repository patch, or submission is authorized.

PROSHKA_JUDGE_PACKET_DELTA:

The judge must receive one packet containing exactly:

Hash receipt

request SHA-256:
d24b2830e8face3d431583778a2f0d0f8c7a51e4ff06aa777bc9141c32488220
evidence HEAD:
efbf549894a825404911995b45003d3c65e8840a

Two source declarations

selectedFerrersDLMFZeroCountSource
selectedFerrersSlepianPhaseOrderSource

Exact primary pins

DLMF 30.4(ii), 30.4.3
existing 30.16 selector crosswalk p=1,3 ↔ j=0,2
Slepian–Pollak (25), (26), (27), (28)
strict concentration order from Section VI
exact mu_n = i^n |mu_n| normalization pin

Notation firewall

Slepian differential chi_n
≠ project Fourier P.chi0/P.chi2


Slepian concentration lambda_n
is renamed kappa_n


project P.chi2 corresponds to full degree n=4

Exact scale proof

lambda = sqrt(mProject)
c = 2*pi*lambda² = 2*pi*mProject
G = c²
project physical Fourier scalar = lambda * source scalar

The exact bounded Lean head

selectedFerrersProduction_remainingActualFields

Same-witness assembly guard

no composition of unrelated existential witnesses

All eight falsifiers above.

Explicit nonclaims

G1 OPEN
G3 OPEN
no Aristotle authorization
no Route B promotion
no RH claim

META CLOSEOUT

What became smaller:
  four final fields
  → two source theorems
  → one local transport leaf.


What was killed:
  one opaque combined carrier;
  Eq.(27)-only positivity;
  whole-line zero-set equality;
  second-even = degree-four;
  chi2 = full-degree-two interpretation.


Current smallest named gap:
  DLMF_ZEROCOUNT_AND_SLEPIAN_PHASEORDER_SOURCE_CARRIERS.


Next cheapest decisive test:
  verify the exact positive-phase normalization line
  and reject the R -> -R mutation before any Lean work.


Prior predictions:
  the selected indices 0 and 2 correspond to degrees 0 and 4:
    CONFIRMED and materialized.
  zero count and Fourier phase remain external source laws:
    CONFIRMED.
NEW_STOP_CODE:
GOAL058_G3_DLMF_ZEROCOUNT_AND_SLEPIAN_PHASEORDER_CARRIERS_PENDING
STATUS:
G1 OPEN; G3 OPEN; CHALLENGER_NOT_RH; NO_RH
