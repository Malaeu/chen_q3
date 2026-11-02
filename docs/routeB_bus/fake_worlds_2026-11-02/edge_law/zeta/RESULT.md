# EDGE_LAW_v1: new zeta cells

**DIAGNOSTIC_NEVER_A_PROOF.** The preregistered finite prediction R∈[3,5] passes all three cells.

Literal N=m,L=log m and T=1.1*2πm/L are retained. U spans the physical row space of the positive-zero sampling matrix; f is the unit minimum eigenvector of UᵀAU lifted into the full even cosine carrier. The endpoint is f(L/2)=sum(d_n f_n)/sqrt(L). We use R=(fᵀAf)/[|f(L/2)|² log(T)/(πT)], and retain the compressed eigenvalue separately as a consistency check.

|m|q|lambda|endpoint squared|R|
|---:|---:|---:|---:|---:|
|160|89|4.78557635994e-16|1.55240602105e-14|3.91936171159|
|200|115|5.81805177347e-23|1.89378778463e-21|4.52547949348|
|240|139|2.34412716825e-25|9.41709511745e-24|4.1431678891|

Main matrices use120dps and eight-panel GL192. J-perp is formed by a row-scaled skinny Householder QR, preserving the raw row space. QR reconstruction is evaluated with30 additional digits, and a triangular inverse gives the reported singular-value lower bound/condition upper bound. These are numerical controls, not interval rank certificates. All Mangoldt powers and the original pole are retained.

At m240,160dps/GL256 changes lambda relatively by 2.749e-97, endpoint squared by 6.136e-96, and R by 4.212e-96. The source matrix Frobenius difference divided by lambda is 6.486e-93.

The full physical vectors are retained for the independent zero-side audit. Dense A/U/E caches are local/tmp artifacts and excluded from publication. Compact cells, predictions, run notes, code, CSV and validation constitute the publication subset. The initial reporting failure and restart are documented in RUN_NOTES.md; the prediction was not changed.

This establishes only the stated finite diagnostic. It does not prove an asymptotic endpoint law, a uniform bound, or RH.

Replay:
```bash
for m in 160 200 240; do uv run --with mpmath edge.py "$m" 120 192; done
uv run --with mpmath edge.py 240 160 256
uv run --with mpmath finalize.py
```
