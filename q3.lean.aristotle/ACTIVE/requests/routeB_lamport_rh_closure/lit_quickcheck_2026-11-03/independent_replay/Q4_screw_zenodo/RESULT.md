# Q4 — finite prime-side diagnostic

DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH.

Zenodo 23481975: **SOURCE_UNREACHABLE** in this audit. Exact statements (a)–(d), proof (b), and page references were not extracted and are not reconstructed. Attempted URLs were https://zenodo.org/api/records/23481975, https://zenodo.org/records/23481975 and https://doi.org/10.5281/zenodo.23481975. No externally retrieved theorem is credited. P6 is **NOT_TESTED**, including the purported external identity with F(X); agreement of the displayed constant alone would not test it.

The independent prime-side script scanned every prime-power event through X=100000 (9700 events), and included 1232 stationary minima inside successive event intervals. The smallest nonzero event/stationary candidate was

- X = 3099.709757559458, t = 8.03906375949627, between events 3089 and 3109;
- Ψ = 0.027520573353620804820414575074887567171993638035447568317922512831616904199461464 (80 decimal digit replay at the float root).

The float scan gave 0.027520573353399413. This is a numerical diagnostic, without interval error bounds, and does not cover the requested 10^9 range. Ψ(t) tends to zero at the origin: this candidate minimum is not a positive uniform minimum over the open interval (0,log 100000]. The finite numerical version of P7 is positive among the checked nonzero event/stationary candidates; P7 at its originally requested range remains untested.

The implemented normalization is Ψ(t)=K_source[χ_(0,t)]/2=−g_source(t), using

Ψ(t)=ct/2+S(t)−Σ_{n≤exp(t)}Λ(n)n^(−1/2)(t−log n)+4(exp(t/2)+exp(−t/2)−2),

c=−γ−log(8π)−π/2, S(t)=Σ_{k≥0}(1−exp(−(2k+1/2)t))/(2k+1/2)^2.

S(∞)=π²/4+2G, so regrouping its constant with the pole's −8 yields π²/4+2G−8. This algebraic observation does not verify the inaccessible external F(X). No twenty-point external cross-check was performed.

Reproduce with `python scan.py` (numpy, scipy, mpmath). Machine-readable output: `scan.json`. No zero table or eigenproblem is used.
