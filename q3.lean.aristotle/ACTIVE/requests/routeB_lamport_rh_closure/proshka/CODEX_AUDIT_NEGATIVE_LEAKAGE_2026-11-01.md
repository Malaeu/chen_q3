# Codex independent PAPER audit: NEGATIVE_LEAKAGE

RESULT: ZERO_SIDE_ENVELOPE_AND_BACKGROUND_CRITERION_PAPER_CONFIRMED
LITERATURE_VERDICT: KNOWN_REFORMULATION
Source: ae344193b74c1394129b5fc6053342b620761f3c, PROSHKA_VERDICT_NEGATIVE_LEAKAGE_2026-11-01.md.
Source SHA256: e6b2c57864c8c4219e59f39e80a652ba9dc8db86593af7e3c0b04e597b7af9e7.
This records the independent audit already delivered to the owner, using the pasted text and standard full Weil explicit formula. Formula identifiers locate the audited statements; GitHub line numbers were unavailable at review time.

| Statement | Verdict |
|---|---|
| (1.3) | CONFIRMED: w cancels inside the integral; G_r remains. |
| (2.2)-(2.3) | CONFIRMED: rectangle normalization, both poles, zero-side sign. |
| (3.3) | CONFIRMED: quotient sum finite with multiplicities, without zero separation. |
| (3.4)-(3.7) | CONFIRMED: upper retains the unpaid off-real positive part. |
| (4.1)-(4.4) | CONFIRMED: perturbation changes the exact logarithmic derivative and symbol. |
| (5.1) | CONFIRMED conditional on RH. |
| (6.1)-(6.6) | CONFIRMED: total variation extension and fixed quartet witness. |
| (7.1)-(7.2) | CONFIRMED: finite return error, constant 20 sufficient. |

For the unit rectangle, Fourier transform is sqrt(L) sinc(L(z-t)/2), and spectral density is kappa_L(v-t)/(2 pi). The analytic Weil pairing yields kappa_L(t-z), including nonreal z. Smoothing endpoints has uniformly bounded variation at fixed L,t and summably dominates the zero products. Both pole terms must be retained.

The identity H(t)/(t-z)=integral_0^1 H'(z+v(t-z))dv handles arbitrarily small imaginary parts of zeros. Outside that neighborhood, local zero counting gives the integrable logarithmic majorant. This proves fixed-profile finiteness, not uniformity in growing P.

Bounded negative mass and convergent signed mean imply uniformly bounded total variation of eta_j. Only then may density of band-limited Schwartz tests extend the measure limit to C_0,even. No continuity of the whole Weil form in the G norm is assumed.

Dividing H by R_0 removes exactly multiplicity d at the selected quartet. Since Im(z_0^2) is nonzero, real interpolation coefficients exist. Values i,i,-i,-i give k[f]=-4d. The real-axis quotient exp(-t^2)(a+b t^2)/R_0(t) has no poles and belongs to C_0,even; its square equals |fhat|^2/H^2 after continuous extension at real zeros. The witness is fixed before the scale limit.

**Литературный вердикт для (6.1): `KNOWN_REFORMULATION` в смысле логического содержания критерия.**

Weil 1952, pp. 9-10 of the transcription, proves the positivity equivalence and constructs a negative Gaussian-polynomial witness when an off-line zero exists: https://denisevellachemla.eu/transc-Weil-1952.pdf . Bombieri 2000, Remarks on Weil's quadratic functional in the theory of prime numbers I, states the same positivity equivalence: https://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0 .

The exact formulation using one background h and bounded negative mass along arbitrary escaping positive averages was not located in these sources. KNOWN_REFORMULATION describes logical content, not a claim that this precise formulation appears verbatim in the literature or that its novelty has been exhaustively settled.

No useful uniform bound for (8.1) was established by this audit. PARTIAL_WITH_PRECISE_REMAINDER remains appropriate. No RH claim, Lean verification, Arb interval calculation, or numerical cofinal certification.
