# Prime-Comb Structure Track B

Date: 2026-06-12

Purpose: organize the research track behind question 1:

```text
What modular or special structure plays for the prime comb the role that
modular forms played for the E8 lattice?
```

This is Track B research, not the trick atlas itself.  It may use atlas tricks,
but it should not be recorded as proof progress until a theorem-shaped result
feeds a checked Q3 receiver.  It does not mutate Step33, H1/PO3, `Q3.Main`, or
the current PSD route.

## Core Distinction

The atlas contains moves.  Track B searches for an object.

- Atlas move:
  "Use Fourier-side rewrite instead of prime-side scalar replay."
- Track B object question:
  "What is the right Fourier/trace/automorphic object in which the prime comb
  becomes structured rather than arbitrary?"

## Prime-Comb Object

Working prime comb:

```text
mu_P = sum_n 2 Lambda(n) / sqrt(n) * delta_{log n / 2pi}
```

The route-local versions may use one-sided, truncated, smoothed, centered, or
windowed variants.  A candidate structure is useful only if it preserves the
normalization required by the active receiver.

## Candidate Structure Families

### 1. Guinand-Weil / explicit-formula distribution

The prime comb is not isolated data; it is one side of the explicit formula,
paired with zeros and the archimedean gamma term.

- Atlas tricks:
  Fourier-side rewrite; dual certificate; margin ledger.
- What it must give:
  A checked identity or inequality that returns to the exact Q3 prime/arch
  object with all gamma, cap, boundary, and sign terms named.
- First falsification:
  It proves a cleaner transformed model but loses the active Q3 normalization.

### 2. Hecke / Dirichlet / automorphic twisting

Twists by characters and Hecke data expose arithmetic structure hidden in the
untwisted prime comb.

- Atlas tricks:
  positivity cone compression; large-values stratification; dual certificate.
- What it must give:
  A structured coefficient family or cone estimate compatible with the Q3
  prime weights.
- First falsification:
  The useful identity exists only after a shifted convolution or deformation
  that has no Euler product or no return map to the active object.

### 3. Adelic harmonic analysis / Tate-style local factors

The zeta prime comb may be a shadow of multiplicative harmonic analysis on
local fields and ideles, where self-duality and local functional equations are
the real symmetry.

- Atlas tricks:
  Fourier-side rewrite; interpolation; dual certificate.
- What it must give:
  A local-to-global identity that produces the exact archimedean and prime
  terms in one normalization.
- First falsification:
  The adelic object is elegant but too global or categorical to produce finite
  Q3 receivers, hboxes, or certificates.

### 4. Trace formula / closed-orbit model

Prime powers can behave like lengths of closed orbits on the geometric side of
a trace formula; zeros sit on the spectral side.

- Atlas tricks:
  explicit-formula transfer; positivity cone; ratchet.
- What it must give:
  A trace-formula-like positivity or cancellation mechanism for the finite
  prime-edge defect.
- First falsification:
  The analogy predicts the right shape but no actual operator, measure, or
  finite certificate exists for Q3.

### 5. de Branges / canonical-system inverse spectral model

Zeros may be treated as spectral data of a canonical system; the prime comb
would then be encoded in a Hamiltonian or phase function.

- Atlas tricks:
  interpolation; dual certificate; positivity cone compression.
- What it must give:
  A reconstruction theorem or monotonicity certificate that turns zero/prime
  data into a finite positive object.
- First falsification:
  The inverse spectral theorem is equivalent in strength to RH or does not
  preserve the test-function class used by Q3.

## Track B Workflow

1. Pick exactly one candidate family.

   Do not run a broad survey.  Start with the candidate that can most directly
   produce a finite receiver or a falsifiable identity.

2. Write a one-page structure note.

   Include:

   - candidate object;
   - exact Q3 object it should replace or compress;
   - atlas tricks used;
   - preserved normalization;
   - danger;
   - minimal experiment.

3. Test one finite window.

   The first experiment should answer:

   ```text
   Does this structure explain one finite prime/arch window better than
   scalar replay, while preserving the exact receiver object?
   ```

4. Classify the result.

   - `kill`: structure cannot return to Q3 normalization;
   - `heuristic`: explains numerics but gives no theorem shape;
   - `probe-ready`: gives a route-local experiment card;
   - `receiver-ready`: gives a theorem-shaped input for Lean/Aristotle.

5. Promote only through the trick workflow.

   If Track B yields a concrete move against a current wall, create an
   experiment card under `docs/RH_TRICK_WORKFLOW.md` discipline.  Do not add the
   research question itself to the atlas.

## First Track B Probe

Probe name:
`PC-001 explicit-formula structure scan`.

Question:
Can the Guinand-Weil distribution be organized so the prime comb is a structured
dual object, not a row-by-row source of hbox pain?

Minimal output:

- one finite-window identity or inequality candidate;
- all normalization terms listed;
- one sentence saying which atlas trick it instantiates;
- one failure check showing how it could prove only a nearby object.

Preferred outcome:
Find a theorem-shaped compression that can become an experiment card, not a
new global route claim.

Current proof note:
`docs/PRIME_COMB_STRUCTURE_PROOF.md`.

Full review card:
`docs/PRIME_COMB_MODULARITY_ATLAS_CARD_01.md`.

Current answer:
The first candidate structure is the Guinand-Weil explicit-formula
distribution, viewed through Tate-Iwasawa adelic harmonic analysis.  The prime
comb is the non-archimedean local term of a global Fourier/trace identity, not
an arbitrary scalar table.

Deep-review update:
The base structural layer is still Guinand-Weil/Tate.  Among concrete
post-2020 candidate mechanisms, the preferred operational line is now:

1. Connes-Consani-Moscovici prolate/Sonin/Toeplitz-Caratheodory-Fejer
   structure as the primary finite experiment target.
2. Carneiro-Littmann-Vaaler extremal majorants/minorants as the parallel
   unconditional edge-defect bounding tool.
3. Bondarenko-Radchenko-Seip zero-side interpolation as dual bookkeeping, not
   as the prime-side certificate generator.
4. Fourier-quasicrystal/Lee-Yang analogies only as obstruction/falsification
   probes, because the explicit-formula prime comb is not a Fourier
   quasicrystal.
5. Direct automorphic/Eisenstein inputs only after a concrete transfer map to
   the Q3 prime weights is found.
