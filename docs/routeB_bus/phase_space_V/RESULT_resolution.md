# Fixed-window V resolution diagnostic

All vectors are freshly computed L2-normalized even ground eigenvectors of the literal CCM matrix. L=log(window_m) stays fixed while N varies; the prime-power cutoff follows L, not N.

V=Apositive+integral log(1+x^2)|f(x)|^2 dx. Apositive uses the full jump kernel j(s)=exp(-s/2)/(1-exp(-2s)); spatial x is unscaled.

|window m|N|lambda0|Apositive|spatial term|V|w0|
|---:|---:|---:|---:|---:|---:|---:|
|8|44|6.2911538e-33|3.94781240819|0.0215565167622|3.96936892496|0.998555907367|
|8|56|5.4259991e-33|3.94777688771|0.0215576798636|3.96933456757|0.998557512094|
|8|68|5.1123902e-33|3.94777095664|0.0215578744661|3.9693288311|0.99855778034|
|12|44|3.7538334e-52|3.92371720581|0.0223602605819|3.94607746639|0.999437782206|
|12|48|7.0249192e-53|3.9244465411|0.0223354032298|3.94678194433|0.999417077834|
|12|52|2.1947867e-53|3.92486712878|0.0223210868061|3.94718821558|0.99940497002|
|12|56|1.1931821e-53|3.92503642994|0.0223153282036|3.94735175814|0.999400061817|
|12|60|9.1907269e-54|3.92506947164|0.0223142051714|3.94738367681|0.999399101961|
|12|64|8.2701992e-54|3.92510673732|0.0223129380626|3.94741967538|0.999398018103|
|16|44|1.7157383e-63|3.90472006198|0.0230185500604|3.92773861204|0.99984493725|
|16|48|6.6386019e-66|3.90767181539|0.0229147388826|3.93058655428|0.999798292909|
|16|52|8.0339896e-68|3.90954567131|0.0228491284854|3.93239479979|0.999765506432|
|16|56|2.1708983e-69|3.91092232333|0.022801069128|3.93372339245|0.999739847617|
|16|60|6.9953565e-71|3.91207198202|0.0227610286061|3.93483301063|0.99971740052|
|16|64|3.7380589e-72|3.91291193477|0.0227318288835|3.93564376365|0.999700414163|

Successive lambda and V ratios, changes in both V components, and w0 changes are in resolution_ratios.csv. Stability of V or overlap is not asserted to certify convergence of the bottom eigenvalue. No N is labeled converged.

Primary runs use140dps and eight-panel GL128. The log16,N64 cell is independently recomputed at160dps and GL160. Detailed discrepancies are in resolution_validation_comparison.json. This is a floating diagnostic, not an interval enclosure.

Ground coefficients, all eigenvalues, projected theta coefficients, source-code hashes and active atoms are preserved in resolution_main.json and resolution_validation.json. The source profile has H=hat h=4xi(1/2-it).

Replay:
```bash
uv run --with mpmath resolution.py
uv run --with mpmath resolution.py --validation
uv run --with mpmath resolution.py --finalize
```
