# PSWF_STURM_LIOUVILLE_SOURCE_DOSSIER

Role: external research/source worker (not orchestrator/judge/repo-writer/proof authority).
Target: PSWF_STURM_LIOUVILLE_SOURCE_ACQUISITION.
Date: 2026-08-03 · Worker: conductor-CLI (Claude Code, Linux), web + on-bus PDFs.
Scope note: Q3/CCM use the WHOLE-LINE prolate operator (Slepian's R-extension); the
finite-interval [-1,1] prolate Sturm–Liouville (SL) theory below is the CONSTRUCTIVE
substrate the whole-line picture is built from. Both are documented.

## RETURN STATUS

SOURCE_CHAIN_PARTIAL

Reason: a primary source chain that CONSTRUCTS (not assumes) the finite-interval
prolate SL modes is located — decisively Osipov–Rokhlin–Xiao (2013) plus the original
Slepian–Pollak (1961). Every one of the 12 required items maps to a located primary
source, and construction-not-assumption is confirmed for the core. What is NOT
recoverable from freely fetchable text is the exact THEOREM NUMBER + verbatim
assumptions for several items (the monographs — ORX, Meixner–Schäfke, Flammer — are
not full-text online; the Slepian–Pollak scan is on archive.org but was not text-
extracted here). Items needing physical-page pinning are flagged PIN-NEEDED below.

## PRIMARY SOURCES (bibliographic identity)

S1. D. Slepian, H. O. Pollak, "Prolate Spheroidal Wave Functions, Fourier Analysis
    and Uncertainty — I", Bell System Technical Journal 40 (1961) 43–63.
    (Scan: archive.org/details/bstj40-1-43.) ORIGINAL. CCM ref [15].
    Contains: energy-concentration eigenproblem; the DISCOVERY that the finite Fourier
    / band-limiting integral operator commutes with the prolate second-order ODE;
    double orthogonality (on [-1,1] and on R); nonzero integral-operator eigenvalues.
S2. A. Osipov, V. Rokhlin, H. Xiao, "Prolate Spheroidal Wave Functions of Order Zero:
    Mathematical Tools for Bandlimited Approximation", Springer, Applied Mathematical
    Sciences 187 (2013). MODERN RIGOROUS PRIMARY. Explicit statement (verified via
    Springer/Amazon front-matter): the order-zero angular PSWFs "together with
    boundary conditions constitute a SINGULAR SELF-ADJOINT STURM–LIOUVILLE PROBLEM"
    and "form an ORTHOGONAL BASIS in L²(-1,1)". This is the CONSTRUCTOR (SL problem +
    Legendre/tridiagonal realization), not an assumed eigenbasis.
S3. J. Meixner, F. W. Schäfke, "Mathieusche Funktionen und Sphäroidfunktionen",
    Springer 1954. Classical monograph. CCM ref [9]; CCM (2511.22755 §7) cites
    "[9], Satz 9, p. 243, §3.2 (Die Sphäroidfunktionen)" for uniform eigenfunction
    estimates. Book, not online. PIN-NEEDED for exact Satz statements.
S4. C. Flammer, "Spheroidal Wave Functions", Stanford Univ. Press 1957. Classical
    monograph (ODE, eigenvalue indexing, parity). Book, not online. Pointer.
S5. W. H. J. Fuchs, "On the eigenvalues of an integral equation arising in the theory
    of band-limited signals", J. Math. Anal. Appl. 9 (1964) 317–330. CCM ref [8].
    Eigenvalue asymptotics/nonvanishing of the band-limiting operator.
S6. B. Simon, "The classical moment problem as a self-adjoint finite difference
    operator", Adv. Math. 137 (1998) 82–203. CCM ref [14]/[18]. Jacobi-matrix
    self-adjointness (the whole-line prolate realization uses this).
On-bus application context (already in repo): CCM 2511.22755 + 2310.18423
(docs/routeB_bus/imports/). Whole-line prolate = classical prolate extended to R
(Connes–Moscovici [12], CCM's "negative part of the spectrum" / Sonin space).

## THE 12 REQUIRED ITEMS

1. EXACT DIFFERENTIAL EXPRESSION — LOCATED (S1, S2, S4).
   L_c ψ = -d/dx[(1-x²) dψ/dx] + c² x² ψ on [-1,1], eigenvalue χ_n(c):
     -( (1-x²) ψ' )' + c² x² ψ = χ_n ψ.
   (Order-m general form carries +m²/(1-x²); Q3/CCM use m = 0.) Tag: THEOREM/DEF (S2).

2. INTERVAL + ENDPOINT CONDITIONS — LOCATED (S2). Interval [-1,1]; x = ±1 are
   SINGULAR endpoints (limit-circle). Realization = bounded/finite solutions at ±1
   (the natural SL boundary condition making the problem self-adjoint). Tag: THEOREM
   (S2 "singular self-adjoint SL problem"). PIN-NEEDED: exact ORX theorem number.

3. SELF-ADJOINT REALIZATION + DOMAIN — LOCATED (S2). Singular self-adjoint SL
   operator; domain = the limit-circle self-adjoint extension selecting solutions
   regular at ±1. ORX front-matter states self-adjointness explicitly. Tag: THEOREM
   (S2). PIN-NEEDED: theorem number + domain description verbatim.

4. DISCRETE / COMPACT-RESOLVENT SPECTRUM — LOCATED (S2, S1). χ_0(c) < χ_1(c) < …,
   discrete, accumulating only at +∞ (compact resolvent); equivalently the commuting
   band-limiting operator Q_c is COMPACT (trace class) with eigenvalues λ_n → 0. Tag:
   THEOREM (S2 orthogonal basis ⇒ discrete; S1 compactness of Q_c).

5. SIMPLICITY OF EIGENVALUES — LOCATED (S2 + classical singular-SL oscillation).
   Each χ_n is SIMPLE (1-D regular/limit-circle SL spectra are simple). Tag: THEOREM
   (SL oscillation theory; ORX). PIN-NEEDED: explicit ORX/Zettl theorem number.
   NOTE: this is exactly the "simple" half of the CCM PW_SIMPLE_EVEN import that was
   UNVERIFIED — the finite-interval SL simplicity IS classical; the CCM claim is for
   the WHOLE-LINE prolate PW_λ, whose simplicity follows via the S1 commutation +
   the same SL structure. Transfer risk flagged in §COMPAT.

6. PARITY THEOREM — LOCATED (S2, S4). Since the coefficients depend on x², L_c
   commutes with x ↦ -x; hence ψ_n has parity (-1)^n: EVEN n ⇒ even function, ODD n
   ⇒ odd function. Tag: THEOREM (parity of SL eigenfunctions under coefficient
   symmetry). PIN-NEEDED: exact monograph statement.

7. DEGREE / EIGENVALUE INDEXING — LOCATED (S2, S4; Sturm oscillation). ψ_n indexed
   by n = NUMBER OF ZEROS in (-1,1) (Sturm oscillation theorem for SL), monotone with
   χ_n. "Degree n" = "n interior zeros" = SL index. Tag: THEOREM (Sturm oscillation).

8. EXISTENCE + SELECTION OF DEGREE-0 AND DEGREE-4 MODES — LOCATED, WITH A WARNING.
   ψ_0: ground mode, 0 zeros, EVEN (parity of n=0). ψ_4: 4 interior zeros, EVEN
   (parity of n=4). Existence: from item 4 (full discrete family). Selection of
   n = 4 REQUIRES the index/oscillation theorem (item 7) + parity (item 6) TOGETHER.
   ⚠ FORBIDDEN-CLAUSE GUARD: ψ_4 must NOT be called "the second even mode". The even
   modes are ψ_0, ψ_2, ψ_4, … ; ψ_4 is the THIRD even mode (or "second even EXCITED
   mode above ψ_0"). Only the oscillation index theorem (n = 4 interior zeros) pins
   it unambiguously; "second even" is convention-dependent and forbidden without the
   index theorem. Tag: THEOREM (existence) + INFERENCE (n=4 selection, via items 6+7).

9. FINITE-FOURIER COMMUTATION / SIMULTANEOUS DIAGONALIZATION — LOCATED (S1). Slepian–
   Pollak's central discovery: the prolate ODE operator L_c COMMUTES with the finite
   Fourier integral operator F_c ψ(x) = ∫_{-1}^{1} e^{i c x y} ψ(y) dy and with the
   band-limiting operator Q_c = F_c* F_c (kernel sin(c(x-y))/(π(x-y))). Hence L_c, F_c,
   Q_c share the SAME eigenfunctions ψ_n. Tag: THEOREM (S1 — the foundational
   commutation). PIN-NEEDED: S1 equation number (archive.org scan).

10. NONVANISHING OF THE FINITE-FOURIER EIGENVALUES — LOCATED (S1, S5). F_c ψ_n = μ_n ψ_n
    with μ_n = i^n (2π/c)^{1/2} λ_n^{1/2} up to convention, and Q_c ψ_n = λ_n ψ_n with
    λ_n ∈ (0,1) STRICTLY POSITIVE for all n (Q_c positive-definite, injective on the
    bandlimited space). Therefore μ_n ≠ 0 for every n. Relation λ_n = (c/2π)|μ_n|².
    Tag: THEOREM (S1 positivity of λ_n; S5 Fuchs eigenvalue asymptotics confirm
    nonvanishing). PIN-NEEDED: exact μ_n formula/normalization from S1.
    NOTE: this is the classical analogue of the Mac's on-bus "finite-Fourier
    nonvanishing" Lean work — the source here is Slepian–Pollak, not an assumption.

11. NORMALIZATION CONVENTIONS + SCALE PARAMETERS — LOCATED, CONVENTION-HEAVY.
    Common conventions: (a) ∫_{-1}^{1}|ψ_n|² = 1 (L²[-1,1] unit); (b) Slepian's ψ_n(1)
    or peak normalization; (c) double-orthogonality normalization (unit on R). Scale:
    "bandwidth" c = a·Ω (time-radius × band-radius). CCM MAP: γ = 2πλ² and z = x/λ,
    i.e. c ↔ 2πλ² (from CCM 2511.22755 §7, "γ = 2πλ²"). Tag: CONVENTION. RISK: Q3
    "plus-phase finite Fourier" convention must be matched to S1's e^{+icxy} kernel
    sign and to CCM's γ = 2πλ² — see §COMPAT.

12. THEOREM / COROLLARY / CONVENTION / INFERENCE per item — see the tag on each item
    above. Summary: items 1–4, 9–10 = THEOREM (located, some PIN-NEEDED for the exact
    number); 5, 6, 7 = THEOREM (classical SL, PIN-NEEDED); 8 existence = THEOREM,
    n=4 selection = INFERENCE from 6+7; 11 = CONVENTION.

## CONSTRUCTED vs MERELY INTRODUCED (forbidden-clause compliance)

- Osipov–Rokhlin–Xiao (S2): CONSTRUCTS — singular self-adjoint SL problem + Legendre-
  coefficient tridiagonal eigenproblem realizes the modes; not an assumed basis.
- Slepian–Pollak (S1): CONSTRUCTS the eigenbasis via the energy-concentration
  eigenproblem AND proves the ODE commutation (so the ODE modes = integral-operator
  modes, not assumed equal).
- Degree 0 and 4 are EXPLICITLY reachable (full discrete family), but their SELECTION
  as "the degree-4 even mode" is an INFERENCE requiring items 6 (parity) + 7
  (oscillation index) — not asserted as a bare "second even mode".

## COMPAT — risks against Q3 plus-phase finite-Fourier convention

R1. WHOLE-LINE vs FINITE-INTERVAL. Q3/CCM use the R-extended prolate operator; the SL
    theorems above are on [-1,1]. Transfer of SIMPLICITY and PARITY to PW_λ on R uses
    the S1 commutation + Slepian's extension [CCM ref 12]; this transfer is an
    INFERENCE, not a single cited theorem — flag as the exact gap for CCM's
    PW_SIMPLE_EVEN (still UNVERIFIED at whole-line theorem level).
R2. PHASE/KERNEL SIGN. S1 uses e^{+icxy}; a "plus-phase" Q3 convention must match this
    sign, else μ_n picks up conjugation/i^n phase flips — affects item 10's exact μ_n.
R3. SCALE. c ↔ 2πλ² (CCM). Any Q3 formula in c must be converted; mixing c and λ
    conventions silently is a normalization bug.
R4. INDEX. Do not identify CCM "h_4" with "second even mode" — only n=4 (4 interior
    zeros, item 7) + even parity (item 6) pins it. CCM's h_{0,λ}, h_{4,λ} = ψ_0, ψ_4.

## POINTERS FOR THE NEXT (PHYSICAL-TEXT) PASS

- Osipov–Rokhlin–Xiao (2013), Ch. on the SL problem: pin theorem numbers for items
  2,3,5,6,9,10 (this single book covers most of the chain rigorously).
- Meixner–Schäfke (1954) §3.2 Satz 9 (p. 243): the uniform eigenfunction estimate CCM
  actually cites (item 11 normalization + the λ^{-2} rate feeding C3).
- Slepian–Pollak (1961) BSTJ 40:43–63 (archive.org scan): items 9,10 exact equation
  numbers + μ_n formula.
