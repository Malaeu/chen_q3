# THETAGRADE — observer audit and own Q3 extraction (2026-10-28)

Verdict: `PROSHKA_VERDICT_THETAGRADE_2026-10-28.md`. Request: `PROSHKA_REQUEST_THETAGRADE_2026-10-28.txt` (63eec554).

## Q1 — accepted
Rouché step checked: on ∂D, |F_m − Ξ| ≤ |F_m − T_m| + |T_m − Ξ| < b/2 < b ≤ |Ξ|, so F_m has as many zeros in D as Ξ (≥ 1);
D misses the real axis, so this contradicts real-rootedness. Then (T3) gives α_m ≥ (b/8C_H) m^(−H/2)/√log m eventually. No defect found.
Added hypotheses accepted: cofinal G1 instance, matched-port center floor (T3), same-family crosswalk, same schedule and normalization.
Q1c accepted as a GAP: only the necessary threshold η ≥ Θ − 1/2 holds; upper side for arbitrary Θ and the endpoint are unproved.
The observer's word "exactly" in ROPES_THETA_MAP and CHAT_DIGESTS (answer3 entry) is retracted; the map is corrected.

## Q2 — parity twin killed, accepted
Identity checked: R self-adjoint, [K,R] = 0 ⇒ ⟨v+,Kv−⟩ = 0 ⇒ ⟨v,Kv⟩ = ⟨v+,Kv+⟩ + ⟨v−,Kv−⟩.
The zero-pair symmetry gives nothing new: Q(Rf) = Q(f) has the same sector parts up to the sign of f−.
Observer's error: one negative witness was symmetrized into two independent sector witnesses.
G1 UNDECIDED. First fact: signed D_m = λ_min(K_m|odd) − λ_min(K_m|even) with ‖r_m‖, δ_m and the ground projection of q_m, cofinal.
Shelf for the next step: the reflection on the literal matrix is `ccmReflectionEndFinite` with its eigenspace lemma
(`q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean`, around 140–160) — Proshka asked for the exact parity block decomposition.

## Q3 — own extraction (Proshka's directive), source verified
paper.tex sha256 42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3 — MATCH (local copy; same blob 268c4e32 at adc7f124 and 7ef5c0cc).

1. Continuation criterion, lines 400–434 (proof 436–501). Hypotheses: σ0 ∈ (1/2,1); Δ0 = β* − σ0 > 0; C(s) = s + c, slope one;
   0 < ω < Δ0 and σ > 0 independent of the target; H_η holomorphic on Re s > σ0 with sup|H_η − 1| ≤ 1/2;
   signal f_η = (2πi)^(−1)∫_{Re s=2} Z^{C(s)} e^{(s−5/6)²} H_η/L ds; low probe |J_η| ≪ Z^{C(σ0)+ω}; high probe |J_η − f_η| ≪ Z^{C(β*)−σ}.
   No degree, no theta object and no character order appear. The Gaussian centre 5/6 is a fixed weight; the proof uses only its decay.
2. Normalization, lines 5584–5589: X = Z^{l_x}, Y = Z^{l_y}, l_x, l_y > 0, ℓ ≥ 0, h = 1 − l_x + ℓ > 0,
   C(s) = s + l_x/2 − 1 + h/6 = s − 5/6 + l_x/3 + ℓ/6. High-exponent bookkeeping, lines 6143–6152, subtracts C(σ0).
3. Where the 6 enters (object, not criterion): after Poisson every row is H = u a^6 with u sixth-power-free (3757–3760);
   the signal needs M(1/6) > 0 (3787–3788). Characters are sextic over Q(√−3) because the cubic theta has indices c n^3 (203–208, 2822–2830).
4. Low probe, Part II: |I| ≪ Z^{l_x/2 + b/12 + ε} = Z^{3/16+ε} (8569–8573); C_II(s) = s − 11/16, C_II(7/8) = 3/16 (8641–8644).
   Arithmetic: l_x/2 + h/6 = 5/16 and l_x/2 + b/12 = 3/16 with b = 1/8 give h = 13/16 and σ0 = 1 − 13/96 + 1/96 = 7/8.
5. Geometry: M = l_x + l_y = 5/6 and M + ℓ = 1 are the Part II choice (6864), NOT part of the general Definition 5584–5589.
   So h < 2 and "σ0 > 2/3" hold for this geometry only. In general ℓ ≥ 0 is free, and ℓ pays through ℓ(z0 − 1/2) in the high exponent (6147).
   Whether a larger ℓ lowers σ0 below 2/3 is a question of losses — open; the observer's earlier "method caps above 2/3" is retracted.
6. Lower-degree theta: the manuscript uses only the Kubota/Patterson cubic theta (121–140) and contains no analysis of a lower-degree object.
   The "first lower-degree admissibility obstruction" is not in the source. Naming one would be new mathematics; stop here.
Code earned (observer's extraction, not Proshka's): DEGREE_FROM_OBJECT. The criterion is degree-free; the 6 and the 1/6 come from the cubic theta rows.

## Prediction score (frozen probabilities unchanged)
| Prediction | p | Outcome | Score |
|---|---|---|---|
| P1 Q1a/Q1b with {G1,G2,G4,G3c,hmode/hchi,T5} | 0.80 | confirmed conditionally, with extra matched-port hypotheses | partial hit |
| P1c Q1c arbitrary Θ | 0.75 | GAP | miss |
| P1t Q1(iii) any route | 0.85 | confirmed on open strips | hit |
| P2 NOT_GRADED 0.50 / THETA_WITNESS 0.35 / UNDECIDED 0.15 | | UNDECIDED; parity-twin witness killed | miss |
| P3 DEGREE_FROM_OBJECT 0.70 | 0.70 | DEGREE_FROM_OBJECT (own extraction) | hit |
| P3 sub: σ0 < 2/3 reachable | 0.10 | not decided; the 2/3 cap is geometry-specific | open |
Signature: observer. Two claims withdrawn: "SP exponent exactly Θ − 1/2" and "qrh78 caps above 2/3 for any variant".
