# CODEX ANALYTIC NOTE 001 — O2 canonical-source crosswalk

Status: `AGENT_ANALYTIC_NOTE_MATERIALIZED / V1_ADJUDICATED / SOURCE_INJECTIVITY_LOCKED / O2_OBJECT_CROSSWALK_BLOCKED / PL1_PL4_NOT_RUN / NOT_RH`

Scope: analytic/type audit of O2 in
`SOFT_L2_EVEN_REAL_SOURCE_DETERMINATION_CLAIM_V2.md`.  This note neither
selects a ground vector nor executes PL1--PL4.  It records no numerical or RH
claim.

## 1. Typed object ledger

Fix `m>=2`, `lambda=sqrt(m)`, and `L=2 log(lambda)=log(m)`.

```text
H_m                    := L2([lambda^-1,lambda],du/u);
E_m_N                  := finite Fourier carrier in H_m;
Inv_m : H_m -> H_m     := multiplicative inversion, (Inv_m f)(u)=f(u^-1);
Eplus_m_N              := E_m_N intersection ker(Inv_m-I);
Mfin_m_N : E_m_N->E_m_N;
GroundSpace_m_N        := ker(Mfin_m_N-groundValue_m_N*I);
GroundUnit_m_N         := {xi in GroundSpace_m_N : ||xi||=1};
q_ground               := a future selected member of GroundUnit_m_N,
                          presently NOT DEFINED;
kTrial_m_N             := gTrial_m_N/||gTrial_m_N|| on TrialNonzero only;
J : L2([-L/2,L/2],dy) -> L2([-L/2,L/2],dy),
                          (Jh)(y)=h(-y).
```

The type firewall is exact: `GroundUnit_m_N` is a set, not a selected vector;
`kTrial_m_N` is a conditional normalized trial vector, not a ground selector.
D0.5 explicitly leaves both `GroundSpace_m_N subset Eplus_m_N` and a canonical
phase open, and claims no `kTrial_m_N in GroundSpace_m_N` membership.

## 2. O2 crosswalk — the two requested source lines

### D0.4 parity line, with exact half-shift centering

D0.4 fixes the uncentered window coordinate

```text
x=log(lambda*u) in [0,L],               Inv: x -> L-x,
Eplus_m_N=E_m_N intersection ker(Inv_m-I).
```

Define the unitary log-coordinate map and its re-centering by

```text
Jlog_m : H_m -> L2([0,L],dx),
          (Jlog_m f)(x)=f(exp(x)/lambda);
C_L    : L2([0,L],dx) -> L2([-L/2,L/2],dy),
          (C_L g)(y)=g(y+L/2);
W_m    := C_L o Jlog_m,
          (W_m f)(y)=f(exp(y)).
```

Because `du/u=dx=dy`, all three displayed maps are unitary on their stated
carriers.  With the additive convention `(U_a g)(y)=g(y-a)`, the re-centering
is exactly `C_L=U_(-L/2)` after interval relabelling.  Direct substitution gives

```text
C_L (x -> L-x) C_L^(-1) = (y -> -y),
W_m Inv_m W_m^(-1)=J.
```

Therefore the source-locked parity statement is the conditional line

```text
f in Eplus_m_N  ==>  (W_m f)(-y)=(W_m f)(y) a.e.
```

The half-shift does not consume parity.  What is absent is the premise
`q_ground in Eplus_m_N`: D0.4 expressly makes no simple-even-ground claim,
and D0.5 lists `GroundSpace_m_N subset Eplus_m_N` as open.

### Symmetry-audit reality line

The symmetry audit proves, for `(m,N) in TrialNonzero`, exactly

```text
kTrial_m_N is real almost everywhere.
```

It does not prove that an element of `GroundUnit_m_N` is real, and D0.5 forbids
the substitution `q_ground := kTrial_m_N`.  Thus no source-locked reality line
for the canonical ground is presently available from that audit.

## 3. O2 verdict

```text
O2_HALF_SHIFT_INTERTWINER               LOCKED;
O2_EVENNESS_OF_CANONICAL_GROUND         NOT_SOURCE_LOCKED;
O2_REALITY_OF_CANONICAL_GROUND          NOT_SOURCE_LOCKED;
O2_OBJECT_IDENTITY_GROUND_EQ_KTRIAL      FORBIDDEN;
O2_OBJECT_CROSSWALK                     BLOCKED.
```

This is consistent with Round 12: the abstract real-even source-injectivity
theorem survives, but its project instantiation requires independent upstream
provenance for a real-even canonical ground.  No smallness, simplicity, sector
winner, or ground/trial approximation is inferred.

## 4. Plants and execution state

The claim's executable plants are registered without execution:

| plant | registered role | execution state |
|---|---|---|
| PL1 | real-even reconstruction control | `NOT_RUN_CURRENT_SCOPE_O2_ONLY` |
| PL2 | non-even round-6 twin falsifier | `NOT_RUN_CURRENT_SCOPE_O2_ONLY` |
| PL3 | even complex-valued falsifier | `NOT_RUN_CURRENT_SCOPE_O2_ONLY` |
| PL4 | sign-anchor flip | `NOT_RUN_CURRENT_SCOPE_O2_ONLY` |

O2 type plants are also registered, not executed:

| plant | falsified substitution | expected stop | state |
|---|---|---|---|
| O2P1 | use `x -> -x` on `[0,L]` | `UNCENTERED_INVERSION` | `REGISTERED_NOT_EXECUTED` |
| O2P2 | infer an even ground from operator commutation alone | `GROUND_PARITY_PREMISE_MISSING` | `REGISTERED_NOT_EXECUTED` |
| O2P3 | replace `q_ground` by `kTrial_m_N` | `GROUND_TRIAL_TYPE_MISMATCH` | `REGISTERED_NOT_EXECUTED` |
| O2P4 | transport `kTrial` reality to `GroundUnit` | `REALITY_OBJECT_MISMATCH` | `REGISTERED_NOT_EXECUTED` |

## 5. V1 adjudication

Authority: `SOFT_L2_PRO_VERDICT_ROUND12_2026-07-13.md` (verbatim materialized
V1).

```text
CLAIM_V2                          ACCEPTED AS SOURCE-INJECTIVITY THEOREM;
SOFT_L2_SOURCE_INJECTIVITY_LOCKED PROVED after scope clarification;
REAL_ZERO_HYPOTHESIS              REDUNDANT;
H2a                               NOT AUTOMATICALLY CLOSED;
project gap                       SOFT_L2_GROUND_TO_CANONICAL_A_CROSSWALK;
smallest lemma                    GroundEigenspaceToCanonicalAutocorrelation;
progress class                    PROOF_PROGRESS;
RH                                NOT_RH.
```

V1 also separates the minimal uniqueness proof
`F_p^2=F_q^2 => (F_p-F_q)(F_p+F_q)=0 => p=+-q` from the stronger constructive
square-root theorem, whose stated inputs require even complex-zero
multiplicities, the order-at-zero condition, Paley--Wiener `L2`, and the exact
half-shift/sharp intertwiner.  This note adopts that adjudication and makes no
claim that the remaining ground crosswalk is closed.

Conclusion:
`CODEX_ANALYTIC_NOTE_001_MATERIALIZED / O2_OBJECT_CROSSWALK_BLOCKED / PL1_PL4_NOT_RUN / NOT_RH`.
