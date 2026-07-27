# SOFT_L2 — EvenRealSourceDetermination (V2 analytic claim, for V1 adjudication)

Status: `V2_CLAIM_REGISTERED / NOT_ADJUDICATED / NOT_RH`
Author: Mythos (V2, pen). Per AGENT_ANALYTIC_NOTE_PROTOCOL this claim is a
file + types + plants and goes to Proshka (V1) before any tree use.

## Claim (stronger than requested: no real-zero hypothesis needed)

Let q in L2(R,du) satisfy:
 (E) q(-u) = q(u) a.e.            [even: parity sector D0.4]
 (R) q real-valued a.e.            [SOFT_2_KTRIAL_SYMMETRY_AUDIT: real a.e.]
 (C) supp q compact, ||q||_2 = 1
 (K) anchor sign: F(i/4) > 0, where F(z) = int q(u) e^{-izu} du
     [equivalently c_0 > 0; F(i/4) != 0 is automatic once zeros are real,
      but positivity is taken as the sign convention]
Then the autocorrelation A_q determines q uniquely. In particular the
projection source E_proj(t) = <(I-S)U_t q, T_full q> of the lag equation is a
functional of (A, sector, window) alone: the equation is CLOSED in A.

## Proof skeleton (five lines)

1. (E)+(R) give F(x) = int q(u) cos(xu) du real on R, i.e. F^sharp = F with
   the ZEO conjugation sharp (SharpLock).
2. A_q determines the entire function F * F^sharp (Wiener–Khinchin + Paley–
   Wiener: A has compact support [-L,L], its transform extends to the entire
   function F(z) * conj(F(conj z)) of exponential type L).
3. F^sharp = F turns the known product into F^2.
4. F^2 is entire and every zero has EVEN multiplicity (it is a square), so a
   global holomorphic square root exists on the simply connected plane and is
   unique up to a global sign: sqrt(F^2) = ±F. Type/support are inherited.
5. The anchor sign (K) selects +F; inverse Fourier returns q. QED (skeleton).

## Why known counterexamples do not apply (structure audit, K3)

- Round-6 polynomial twins (1+5z+6z^2 vs 3+7z+2z^2 packets): NOT even —
  one-sided shift trains break (E). The ambiguity they exhibit lives exactly
  in the gap between F*F^sharp and F^2, which (E)+(R) close.
- Shifted family q(.-a_j): breaks (E) for a != 0; killed by the sector, as
  established in the parity-closure round.
- Note: the real-zero hypothesis H2a is NOT used. Its five prior duties are
  untouched; source determination is duty of parity+reality alone.

## Plants (executable, for Codex after V1 verdict)

 PL1 (even control): synthetic even real packet; reconstruct q from A via
     steps 2–5 numerically; must match up to sign, rel err < 1e-10.
 PL2 (odd falsifier): the round-6 twin construction (non-even); the two
     distinct packets must yield THE SAME A (reconstruction must be reported
     ambiguous, not silently pick one) — the plant fires if the pipeline
     claims uniqueness without (E).
 PL3 (complex falsifier): even but complex-valued packet with genuinely
     complex F on R; F*F^sharp != F^2 must be detected.
 PL4 (sign anchor): flip the sign of q; reconstruction must return the
     anchor-consistent representative.

## Open obligations before tree use

 O1 V1 adjudication (default REFUTED): the sqrt-monodromy step and the
    entire-extension step need line-level scrutiny (multiplicity parity at
    ALL zeros incl. z=0; growth of the root).
 O2 Canonical-sector crosswalk: one line each from D0.4 (evenness of the
    canonical ground in the chosen coordinates, incl. the half-shift
    centering) and from the symmetry audit (reality). If the canonical
    carrier is even only after re-centering, state the exact unitary.
 O3 Consequence wiring: with this lemma, ROUND9/ROUND10's source-closure
    obligation is met via variant 2 (gauge fixes the representative); the
    lag equation becomes an equation in A with a determined source term.

NOT_RH.
