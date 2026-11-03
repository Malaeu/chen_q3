Route B = CHALLENGER / NOT_RH. DIAGNOSTIC_NEVER_A_PROOF.

External source is pinned to jose-paul-b/weil-positivity-certificates@0f7a85b392c4017cadc0a3bc7adcba19951a530f. Source safety review preceded execution; all four executable Git blob hashes match upstream. Execution used python -I in a fresh external directory. See SAFETY.md and SOURCES.json.

The two support±4/5 certificates are REPRODUCED, including exact printed lower-bound strings: even1.0266618704919108500e−17, odd1.1399115396618374143e−14. The support±31/32 pair is also REPRODUCED: even1.0073585468444951163e−27, odd2.1193782393913236324e−24. All four lower-bound strings match the upstream saved results exactly. Large runs took500/498s including verified Cholesky and discarded-tail bounds.

Our independently evaluated physical cosine/sine restrictions at N32 give:

| m | full window W | even minimum | odd minimum | odd/even |
|---|---:|---:|---:|---:|
| 3 | log3 | 5.9108083673e−8 | 1.7441873950e−5 | 295.0844 |
| exp1.6 | 1.6 | 1.9606578043e−17 | 1.9194999007e−14 | 979.0081 |
| 5 | log5 | 1.2082610177e−17 | 1.2370552540e−14 | 1023.8311 |
| 7 | log7 | 1.2525881686e−27 | 2.5325706335e−24 | 2021.8702 |

N16 comparison is saved too; the minima decrease with increasing basis size, so these are finite-dimensional variational upper bounds, not continuum lower certificates. Fixed-N validation at130dps/GL128 and160dps/GL160 agrees to all80 saved significant digits in all six cases; SUMMARY.json records the comparison. Our L1.6 finite minima exceed both external certificate constants, as required. A ratio of certificate lower bounds is not the ratio of actual continuum sector minima; there is no reason for that ratio to equal a finite Galerkin ratio.

The Q_2 negative odd witness at full window1.1147 is REPRODUCED by external Arb and by independent mpmath real-space integration with no external Python import. The independent replay evaluates the degree61 polynomial directly, its autocorrelation by GL64 (exact degree122 integration), and the arch integral by composite GL. At dps100/GL64×8 and dps130/GL80×8 it gives the same displayed75-digit total:

Q_2=−3.60762498685477970398068025663963975012403057762498587001713332537025507538e−8.

Pole−0.0231445503287037958534; arch−0.1746193314867173519517; prime+0.1977638457391712792573. Rescaling the same normalized polynomial to window1.114 gives Q_2=+1.3654438861155798093e−6. This independently brackets this witness's sign flip inside [1.1140,1.1147]. Positive Q of one vector does not establish positivity of the entire form at the low endpoint. The external whole-space low-endpoint certificate is retained as upstream source data, not claimed as rerun.

Our N16/N32 sine restrictions remain positive at1.1147; they miss this narrow negative direction. This is a useful basis-resolution discrepancy, not a contradiction with the independent polynomial witness. We therefore do not claim that these Fourier truncations locate the true Q_2 threshold. The reported P3/P5 brackets are source data only in this quickcheck.

NORMALIZATION.md gives the exact crosswalk: external half-width a, our W=2a=logm; same unit L2 norm, Fourier convention, pole, arch and prime terms; no global factor adjustment. Q_P restricts underlying primes p≤P and includes all powers fitting the window, rather than restricting n≤P. The two independent real-space/Arb witness evaluations check this crosswalk numerically.

The current primary abstract and PDFv2 of arXiv2608.24827 both name Xuefeng Zhu. No current author mismatch was observed. Theorem1.1 is a finite reduction with explicit tail control; its source statement and the distinction from a paper proof audit are recorded in PRIMARY_SOURCE.md.
