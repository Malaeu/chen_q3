# Positive fixed-weight SHAKE

**DIAGNOSTIC_NEVER_A_PROOF.**

Each atom 2^j ≤ m moves from log(2^j) to log(2^j)+jε, preserving its original log(2)/sqrt(2^j) weight. All other prime powers remain unchanged. The primary convention analytically continues q beyond L; the secondary convention sets q=0 beyond L. The archimedean and spatial matrices in V are unchanged; their expectations change because the ground vector changes.

Primary analytic-continuation results (180 dps, GL160):

|m|positive ε|λ₀|V|w₀(theta)|overlap² with true ground|
|---:|---:|---:|---:|---:|---:|
|8|0|1.023925871e-19|3.87964498|0.9996889777|1|
|8|1e-26|1.023925934e-19|3.87964498|0.9996889777|1.0|
|8|1e-20|1.086649501e-19|3.879648285|0.9996890498|1.0|
|8|1e-12|-2.653355844e-12|5.430461495|0.1493462785|0.1370188083|
|8|1e-6|-8.961360873e-6|6.073706507|0.01353444646|0.01169262416|
|12|0|6.7904267e-29|3.850686573|0.9987619747|1|
|12|1e-26|6.785462232e-27|3.851949172|0.9988160164|0.9999993949|
|12|1e-20|-2.680846938e-20|5.404240324|0.1488908746|0.1247542913|
|12|1e-12|-8.478716667e-12|5.9579621|0.01805090023|0.01335188669|
|12|1e-6|-1.452613255e-5|6.616105445|3.004226263e-6|2.451366523e-7|
|16|0|5.456138012e-38|3.843386438|0.9984375105|1|
|16|1e-26|-2.679114796e-26|5.396090737|0.1493653647|0.1223375913|
|16|1e-20|-8.090286986e-20|5.860799137|0.02197894573|0.01563201394|
|16|1e-12|-1.464634505e-11|6.602912514|0.0001368009503|8.140858734e-5|
|16|1e-6|-2.055678704e-5|6.716010548|0.0001507374892|0.000100769765|
|20|0|2.584465231e-46|3.840205723|0.9982856222|1|
|20|1e-26|-8.501738547e-26|6.025277442|0.01689177813|0.011858203|
|20|1e-20|-1.167650943e-19|6.532191255|0.001233972258|0.000961389734|
|20|1e-12|-2.051988614e-11|6.695560855|0.000153285159|0.0001005042733|
|20|1e-6|-4.450581423e-5|7.505563523|2.883466819e-6|1.932280668e-6|
|24|0|2.690512813e-54|3.840240026|0.9982912521|1|
|24|1e-26|-1.268573932e-25|6.570686739|8.758754499e-5|8.264607836e-5|
|24|1e-20|-1.849855077e-19|6.577432224|0.001291886975|0.0008942175366|
|24|1e-12|-3.691456382e-11|7.486049471|1.256504195e-5|8.766806194e-6|
|24|1e-6|-5.019096199e-5|7.473311297|4.774406324e-6|3.164605336e-6|

Physical clipping changes only the endpoint atoms for m=8 and m=16 on this ε grid. Both conventions and all differences from baseline are recorded in shake_summary.csv and individual JSON files.

|m|ε|clipped λ₀|clipped V|clipped w₀|
|---:|---:|---:|---:|---:|
|8|1e-26|1.023925934e-19|3.87964498|0.9996889777|
|8|1e-20|1.086649501e-19|3.879648285|0.9996890498|
|8|1e-12|-2.653355844e-12|5.430461495|0.1493462785|
|8|1e-6|-8.961362875e-6|6.073706172|0.01353444562|
|16|1e-26|-2.679114796e-26|5.396090737|0.1493653647|
|16|1e-20|-8.090286986e-20|5.860799137|0.02197894573|
|16|1e-12|-1.464634505e-11|6.602912514|0.0001368009503|
|16|1e-6|-2.055679399e-5|6.716010847|0.0001507354468|

Across these finite perturbations, V ranges from 3.85194917197 to 7.5055635229. The table reports growth with m directly; no cofinal bound or asymptotic law is inferred.

m24 at ε=10⁻²⁶ and 10⁻⁶ was rebuilt at 220 dps with GL192. Componentwise changes are in shake_validation.json. This is numerical validation, not an interval certificate.

For fixed ε=10⁻²⁰ and 10⁻¹², the sampled V increases with m. At ε=10⁻²⁶ it first decreases slightly from m8 to m12, then rises; at ε=10⁻⁶ it falls slightly from m20 to m24 after earlier growth. These five cells therefore do not support universal monotonicity. Positive shifts were used throughout; the negative ε examples in the reference script were not substituted.

Replay each cell with `uv run --with mpmath python3 shake.py m 180 160`; validation uses `shake.py 24 220 192 1e-26 1e-6`. Rebuild summary by importing shake and calling shake.summarize().
