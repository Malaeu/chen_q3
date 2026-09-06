# Implementation B — semilocal sign table for S = {infinity, 2}

## What is here

| file | what |
|---|---|
| `phys.py`    | physical-variable model: grid u_i = i*delta (i=0..N), delta = 1/sqrt(2N), U_max = sqrt(N/2), trapezoid weights; DCT-I matrix for F_inf |
| `ops.py`     | F_inf, the Euler intertwiner B_S = I - (1/2)H with (Hf)(u)=f(u/2), F_S = B_S F B_S^{-1}, the projection pair (P,Q), angles alpha_n, xi_n, zeta_n, D_S, the Sonin projector S_S, and N_S / E_S |
| `quad.py`    | the INDEPENDENT quadrature path: ||v||^2, C_v(t), D(v), the prime sums, L_S, P_02, Q(v). No operator is used here |
| `tests.py`   | the test family (support-matched bumps, shifted, two-bump, complex, canonical cutoffs v_R with both a smoothstep and the explicit quintic cutoff, pole-null tests, wide control bumps, THEOREM_CONTROL_CC20 tests) |
| `halmos.py`  | the exact rational Halmos plant of verdict eq. (10) |
| `s1_phys.py` | S1 validation: F_inf involution/self-adjointness + prolate cross-check against an independent Gauss-Legendre Nystrom solve of the sinc kernel |
| `run_quad.py`| runs the quadrature path over the whole family -> `quad_results.json` |
| `run_ops.py` | runs the operator path (both S={inf} and S={inf,2}, lambda = 1, sqrt2, 2) -> `ops_results_N<N>.json` |
| `run_thm.py` | THEOREM_CONTROL_CC20 block -> `thm_results.json`, `thm_quad.json` |
| `mk_table.py`| (early) markdown table helper |
| `mk_final.py`| assembles the markdown tables from the json files |
| `mk_sec10.py`| section 10: sign verdicts recomputed from `Q - N_S` with the `N_S` error bar |
| `run_bar.py` | `N_S` recomputed with the SYMMETRISED `F_S` -> `bar_N<N>.json` (the model error bar) |
| `assemble.sh`| concatenates `table_head/valid/tail/concl`, `sec10_*` and the generated tables into `TABLE.md` |
| `dump_alpha.py`| angle spectra |
| `TABLE.md`   | the deliverable |

## How to rerun

```bash
cd /home/chirurgie/.claude/jobs/4b35770d/tmp/semitab_B
python3 s1_phys.py 4096          # S1 validation (prolate cross-check)
python3 halmos.py                # S3 Halmos plant
python3 run_quad.py              # quadrature path (needed first: run_ops.py reads its json)
python3 run_ops.py 2048          # ~1 min
python3 run_ops.py 4096          # ~5 min
python3 run_ops.py 8192          # ~25 min, ~8 GB RAM
python3 run_thm.py 4096 8192     # theorem control
python3 run_bar.py 4096            # N_S error bar (all tests)
python3 run_bar.py 8192 "pole-null" "v_R = chi" "h_b b=0.2" "two-bump (-) b=0.1" "wide cos bump b=3"
python3 dump_alpha.py
./assemble.sh                     # writes TABLE.md
```

Only numpy / scipy / mpmath are used (system python3, no venv needed).

## Conventions actually implemented

* log model x = log u, unitary f(u) = u^{-1/2} v(log u)  (int |f|^2 du = int |v|^2 dx).
* (F_inf f)(u) = 2 int_0^inf f(t) cos(2 pi u t) dt.
* theta(k) = convolution by v in x; kernel on the physical grid
  Theta_{ik} = sqrt(w_i w_k) (u_i u_k)^{-1/2} v(log u_i - log u_k).
* f = k * k^*, f(1) = ||v||^2, f(p^j) + f(p^{-j}) = 2 C_v(j log p).
* c_A = gamma + log(8 pi) + pi/2 = 5.372183419225665 (verdict Lemma 5, matches setup.tex).
* ell = log(TW) = 2 log lambda.
* L_S(f) = D(v) - c_A ||v||^2 - 2 sum_{j>=1} (log2 / 2^{j/2}) C_v(j log 2)   [eq. (14), S_f={2}]
* Q(v)  = D(v) - c_A ||v||^2 + P_02(v) - 2 sum_{n>=2} Lambda(n) n^{-1/2} C_v(log n)  [setup.tex]
* N_S = Tr(theta_f S_S) = ||theta(k) S_S||_HS^2 ;  E_S = Tr(theta_f D_S) - ell ||v||^2.
  E is NOT computed as N - L, and N is NOT computed as L + E, so the identity check is real.


## Headline result (see TABLE.md sections 6 and 10)

The CC20 theorem control passes for the pair `(Q, N_inf)` and fails for the directly computed
`E` column: the direct block trace `Tr(theta_f D_S)` is biased upward by `0.02 .. 0.5` because
`zeta_n` has a `1/u` tail that the finite carrier truncates. All sign verdicts are therefore taken
from `E_true = N_S - L_S` (`L_S` exact from quadrature, `N_S` the Hilbert-Schmidt norm), with an
`N_S` error bar from the translation defect and from recomputing `N_S` with the symmetrised `F_S`.
