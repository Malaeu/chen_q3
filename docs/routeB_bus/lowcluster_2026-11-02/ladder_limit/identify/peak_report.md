# Peak and theta-zero comparison

The peaks below are numerical stationary points evaluated at 100 dps for the fixed finite cosine series. They are not symbolic identities or interval certificates. The positive-coordinate global maximum of density is also a positive maximum of f in both cases.

|m|x*|2x*|2x*−log7|
|---:|---:|---:|---:|
|20|0.9837460685205989|1.967492137041198|0.0215819879858844|
|24|0.9835973648070345|1.967194729614069|0.02128458055875578|

All stationary candidates were bracketed on 8192 subintervals and refined. An independent degree 19/23 derivative-Chebyshev polynomial calculation returned all 19/23 polynomial roots, with exactly 8 real interior stationary points in each case, matching the bracketed candidates to better than 8e−99. Endpoints were included in the maximum comparison. This supports the numerical global-peak designation for these finite inputs.

Both 2x* values are nearest log 7 among n=2,...,12, but differ by about 0.0213–0.0216. There is no observed equality with a logarithmic atom.

|n|2x20−log n|2x24−log n|
|---:|---:|---:|
|2|1.27434495648125|1.27404754905412|
|3|0.868879848373088|0.868582440945959|
|4|0.581197775921307|0.580900368494178|
|5|0.358054224607097|0.357756817179969|
|6|0.175732667813143|0.175435260386014|
|7|0.0215819879858844|0.0212845805587558|
|8|-0.111949404638638|-0.112246812065767|
|9|-0.229732440295022|-0.23002984772215|
|10|-0.335092955952848|-0.335390363379977|
|11|-0.430403135757173|-0.430700543184301|
|12|-0.517414512746803|-0.517711920173931|

Located nonnegative full-theta zeros:

|Function|Nonnegative root|Initial bracket|
|---|---:|---|
|h_prime|0|[0.000,0.000]|
|D_h|0.1608081720189887|[0.160,0.161]|
|h_second|0.2613607760952814|[0.261,0.262]|

Here D h=−x h′−h/2. h′ is odd and its root at 0 is exact by parity. D h and h″ are even, so their positive roots reflect to negative roots. Neither x* nor 2x* is close to any of these roots; all differences are in peak_theta_comparison.csv.

The scan covers [0,3] with exact-decimal step 0.001. It uses scaled sums with the common factor exp(x/2−πexp(2x)) removed and always retains the n=1 term. Tiny tails are therefore not mistaken for numerical zeros. Root counts within [0,0.5] are numerical, not interval-certified.

There are analytically no further positive roots past 0.5. Write y=πn²exp(2x). For x≥0.5, y≥πe>8. The derivative polynomials are

P0=16y²−24y,
P1=−4y(8y²−30y+15)<0,
P2=2y[y²(32y−232)+345y−75]>0.

Also −xP1−P0/2≥−(P1+P0)/2=16y(y−3/4)(y−7/2)>0. Every theta summand has the indicated sign after multiplication by its positive exponential factor. Thus h′<0, h″>0 and D h>0 on x≥0.5.

Full precision roots, residuals, brackets and all comparisons are preserved in peak_results.json and the peak*.csv files. No RH or limiting-profile identity is claimed.
