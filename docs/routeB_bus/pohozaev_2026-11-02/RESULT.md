# Finite N44 Pohozaev dilation diagnostic

STATUS: DIAGNOSTIC_NEVER_A_PROOF

Source: PROSHKA_VERDICT_CCM_POHOZAEV_2026-11-02.md at d8983a2, equations (3.7)--(3.11) (owner labels E/F). Source SHA-256: a6b7f67ab1e4bb7f0af7171f67f838087e4b51d79056cb9b9a5d45d01edc392b.

At L=log8, N=44, D_reg=0.3369487425510696114472318428223701. The exact zero-step regular/atomic sum matches the one-sided finite-N Hellmann--Feynman slopes to about 1e-100. At tau=+/-1e-6 the O(tau) regular remainder is about 7.23e-7, overwhelming slopes of order 1e-30. Omitting it is invalid; the frozen-vector quotient also differs from the reoptimized eigenvalue quotient. The infinite-dimensional limiting inequality is not verified by this finite carrier.

For e=f-(<f,P_N h>/||P_N h||^2)P_N h, with full unnormalized theta h and D=x*d/dx+1/2, |<e,Dh>|=0.0629231065889271691 and ||e||^2=0.001444092632854163. Pairings use the window; e is zero outside.

See REPORT.txt and pohozaev_results.csv for both tau signs, frozen energy quotients, measured remainders, and fourth-order one-sided eigenvalue differences. Primary run:100dps/GL96; independent replay:140dps/GL128. Worst relative replay discrepancy:1.99e-64. No uniform remainder or interval certificate.

Replay from this directory:

```sh
uv run --with mpmath probe.py 96 100
uv run --with mpmath probe.py 128 140
uv run --with mpmath finalize.py
```

The only relocation edit is the path to the previously committed convergence builder (and its report description).
