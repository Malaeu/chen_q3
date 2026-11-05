# PROSHKA — ADDENDUM TO ROUND 3: A SIGN WE ALREADY PROVED IN SEPTEMBER (2026-11-05)

Repository: https://github.com/Malaeu/chen_q3. Branch: rh_clean. The commit is given in the owner's message.

This file extends the Round-3 request:
docs/routeB_bus/mythos/BRIEF_TO_PROSHKA_ROUND3_POLE_RENORMALIZED_2026-11-05.md
(rh_clean cde26769822ca51bc3c0af3f7004c68afdc85a5b, blob 7ad5c33ff6211afbcc7c95b113e7baeeb7a709d9).
The Round-3 request itself is not edited. Goal and acceptance are unchanged.

## Why this addendum exists

Your September Goal058 campaign lived only on the unmerged branch `codex_mac/gamma-reciprocity-20260914`. On 2026-11-05 it was merged into rh_clean:
- merge commit f3bd583263b14a71f4deba7124b5f0d3ce507397, follow-up e0909c3c1a202f6e8343ca18b34178d88db54490;
- 16 of your responses, 95 Codex reports, 83 certificates;
- index and digests: `docs/routeB_bus/mythos/DIGEST_GOAL058_SEPT_2026/INDEX.md` (rh_clean c603afe90d04317ba1eff828b89b30c49566bd8a, blob 5d4541dfe0863aef31aef5bb0355b5101aeba74d).

When you wrote the Round-3 kill list you could not see these results.

## 1. September kills to add to Round-3 acceptance item 1

All are listed in the INDEX, §1. Each one excludes a positive minorant or positive insurance of the theta-source form V:
- NULLFIELD;
- RESOLVENTGRAM;
- POINCARECOMP;
- RAW_RESPONSE_FLOOR;
- FINITE_PATH;
- the absolute majorant in SUPPORTSTABILITY.

## 2. The owner's practical idea (an idea, not an order)

In September a sign was **proved** for an object that contains the primes. Codex report `docs/Codex/REPORT_2026-09-17_SCATTERING_POISSON_FULL_FUNCTIONAL.md` (blob a6d21aa42faae590a2317587bfc142a076d2a6dc), accepted limited PAPER, shows the following.
- The pole-corrected scattering phase P(t) = 2 Re ξ′/ξ(1+it) = 2 Σ_ρ (1−β)/((1−β)² + (t−γ)²) is > 0 unconditionally. This uses only 0 < β < 1.
- E(ψ) = (1/2π)∫P|ψ̂|² is the COMPLETE Weil functional on the correlation damped by e^{−|u|/2}:
  - prime weights Λ(n)/n;
  - both poles;
  - the archimedean constant.
- Q = E + R, where R is proved to take both signs.

In Round 2 you proved (8.3): A_m = (1/2π)∫[α_m + v_L]|f̂|² + J_−, with J_− = ∫_0^L e^{−s/2}Q_f(s) ds ≥ 0. This has the same e^{−s/2} damping, but J_− carries only the pole.

**The idea in plain words.** We already hold a proved sign at exactly the kind of place where we are now looking for one, and that object even carries the arithmetic. Try to use it.

- **(a) Reservoir.** Inside the window, use the September-type E (pole and primes, damped) as the free positive part instead of the pole-only J_−. Then ask what remains. The September fact "R changes sign" does NOT refute a lower bound R ≥ −C m^ε. Only positivity of R was killed.
- **(b) Sliding the damping.**
  - Damping e^{−δ|u|} at δ = 1/2 is the line Re s = 1, where the sign is proved.
  - Inside a window of length L = log m, a damping δ = c/log m changes every weight only by a factor in [e^{−c}, 1].
  - Can the sign be carried from δ = 1/2 down to δ = c/log m, inside the window, with bounded loss?
  - Every uniform step below δ = 1/2 in the infinite setting is a zero-free-strip statement, which is open. If the window cannot avoid that, say exactly where.

**False-world bookkeeping (Mythos's observation; check it, do not trust it).**
- **DH.** The proved sign at δ = 1/2 already fails for Davenport–Heilbronn, whose zeros include some with β > 1. So the top rung uses the Euler product.
- **DMV.** A DMV system keeps β < 1, so it passes the top rung. It fails only once δ drops below its β − 1/2.
- **Consequence, if this holds.** The descent step must use what DMV lacks: the functional equation or the integer lattice.

Use any of this, or none of it. The object and the method remain your choice. A new specification built from this must still satisfy the Round-3 acceptance, including items 1–6 and the September kills above.
