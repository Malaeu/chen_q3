# Raw capacity conditioning

DIAGNOSTIC_NEVER_A_PROOF

Source: rh_clean e724ae65ed39a8ba8b8f07c928d790ea9820342a; retained capacity and quiet-space data bf89051 and 3bdd5f8. Literal even carriers N=m, L=log(m). All integers m=16..40 and optional m=60,80 completed.

There are 59 saturating (m,q) sectors. Saturation means the signed count of all A eigenvalues below 1.000001 delta equals r=m+1-q, where delta=||A Q||. Every zero-count state on kappa in [1,1.4] was checked, including states missed by the 0.02 grid at m60 and80. Only q26,27 pass at m60 and q36,37 at m80.

E uses raw, unscaled Fourier evaluation rows at positive zeta ordinates. U spans range(E*), with orthonormal columns; F=EU has exactly the nonzero singular values of E. Reported capacity is sigma_min(F)^2; the factor 2 includes negative ordinates for real even functions. See NORMALIZATION.md for precise scope. No row normalization enters these singular values.

## Main finding

Small raw capacity is not explained by small local zero gaps in these data. No included zero in any passing sector satisfies g L/(2pi)<0.3; the minimum is 0.5894071386. Across 59 distinct sectors, Pearson correlation of sigma_min with the minimum normalized gap is 0.3059238, Spearman 0.4178324; Pearson for log10(sigma_min) is 0.2699231. For m16..40 alone these are 0.3225314, 0.4173524, 0.2767954. Repeated kappa points are counted once. These dependent, observational samples do not establish a causal spacing law.

At m16,q7, sigma_min^2=0.000411777912 and 2sigma_min^2/lambda_r=0.0057607357. The weak left vector has 99.4574% mass on zero7 alone and only 0.5324% on zero6. Their raw row norms are 0.0576219 and 0.7280082; normalized absolute row correlation is 0.9090141. Thus a large adjacent-pair mass is not evidence of a balanced close-pair cancellation. At m80,q37, pair36/37 has 99.8530% mass but row correlation is only 0.441854. Small row amplitude and the carrier's sinc/modal geometry matter. all_cases.csv records nearest modal frequency, row norm, sinc factor, individual weights, and both top-two and adjacent-pair diagnostics.

The smallest value of 2sigma_min^2/lambda_r is 0.0057607357. The optional m60 and80 weakest sectors give 0.0860482 and 0.0210914. A bound on the quiet-space synthesis Gram in the e724ae6 PAPER audit is not a bound on this evaluation matrix's conditioning. These results supply no uniform active-complement coercivity or cofinal signed count.

## All passing sectors

q is the number of positive zeros below T; r=m+1-q and lambda_r uses zero-based indexing. Interior lower kappa endpoints are open and upper endpoints closed, because gamma<T is strict. Clipped endpoint1 is included when indicated in all_cases.csv. Table endpoints are rounded; use CSV for decisions. The pair column lists the two largest left-vector weights, in descending order, which need not be adjacent.

|m|q|r|kappa interval|sigma_min²|2sigma_min²|lambda_r|2sigma_min²/lambda_r|top two zero indices (weights)|
|---:|---:|---:|---|---:|---:|---:|---:|---|
|16|5|12|1.000000–1.036606|1.0872828|2.1745656|2.2856436|0.9514019|3,2 (0.4642,0.2031)|
|16|6|11|1.036606–1.128516|0.48329746|0.96659492|1.2368235|0.7815141|6,5 (0.9336,0.0341)|
|16|7|10|1.128516–1.194937|0.00041177791|0.00082355582|0.14296018|0.005760736|7,6 (0.9946,0.0053)|
|17|6|12|1.000000–1.085357|1.1605426|2.3210852|2.3872277|0.9722932|3,4 (0.4346,0.3033)|
|17|7|11|1.085357–1.149238|0.078623877|0.15724775|0.78662818|0.199901|7,6 (0.9426,0.0445)|
|18|6|13|1.000000–1.045739|1.1772409|2.3544818|2.3721944|0.9925332|3,2 (0.4208,0.3072)|
|18|7|12|1.045739–1.107288|0.091152895|0.18230579|0.50182249|0.3632874|7,6 (0.9957,0.0021)|
|19|7|13|1.009232–1.068633|0.99994428|1.9998886|2.1718162|0.9208369|7,6 (0.4371,0.3566)|
|19|8|12|1.068633–1.184014|0.035374407|0.070748814|0.54867545|0.1289447|8,7 (0.9357,0.0627)|
|20|7|14|1.000000–1.032886|1.0771821|2.1543642|2.3323866|0.9236738|7,6 (0.5662,0.3003)|
|20|8|13|1.032886–1.144408|0.30325993|0.60651985|0.95538168|0.6348456|8,7 (0.8989,0.0426)|
|20|9|12|1.144408–1.186572|0.00089417747|0.0017883549|0.12952279|0.01380726|9,8 (0.9788,0.0203)|
|21|8|14|1.000000–1.107664|1.1829569|2.3659139|2.375217|0.9960832|6,4 (0.3300,0.2945)|
|21|9|13|1.107664–1.148474|0.02512275|0.050245499|0.49963815|0.1005638|9,8 (0.9804,0.0107)|
|22|8|15|1.000000–1.073471|1.1697266|2.3394532|2.3477859|0.9964508|6,4 (0.3807,0.2961)|
|22|9|14|1.073471–1.113021|0.10925158|0.21850317|0.61148853|0.35733|9,8 (0.9854,0.0061)|
|23|8|16|1.000000–1.041564|1.1811804|2.3623607|2.3673936|0.9978741|7,6 (0.3605,0.3533)|
|23|9|15|1.041564–1.079939|0.0052794571|0.010558914|0.84808495|0.0124503|9,8 (0.9996,0.0002)|
|24|9|16|1.011715–1.048990|1.1164523|2.2329047|2.2727643|0.9824621|9,7 (0.4986,0.2607)|
|24|10|15|1.048990–1.116356|0.0097143131|0.019428626|0.41738518|0.04654843|10,9 (0.9643,0.0339)|
|25|9|17|1.000000–1.019965|1.2015767|2.4031535|2.4247201|0.9911055|7,6 (0.2988,0.2576)|
|25|10|16|1.019965–1.085468|0.52912505|1.0582501|1.4109534|0.7500249|10,9 (0.7241,0.2270)|
|25|11|15|1.085468–1.156697|0.0010787022|0.0021574044|0.19781022|0.01090644|11,10 (0.9736,0.0241)|
|26|10|17|1.000000–1.056436|1.1759546|2.3519093|2.3754647|0.9900838|6,7 (0.2689,0.2423)|
|26|11|16|1.056436–1.125760|0.091862734|0.18372547|0.68226163|0.2692889|11,10 (0.9368,0.0323)|
|27|10|18|1.000000–1.029093|1.1480218|2.2960437|2.3103468|0.9938091|6,7 (0.2497,0.2142)|
|27|11|17|1.029093–1.096622|0.13570504|0.27141008|0.68907141|0.393878|11,10 (0.9821,0.0117)|
|27|12|16|1.096622–1.152978|0.0059216296|0.011843259|0.13451921|0.0880414|12,11 (0.7262,0.2712)|
|28|11|18|1.003290–1.069126|1.0156559|2.0313118|2.0863625|0.973614|10,9 (0.2682,0.2398)|
|28|12|17|1.069126–1.124069|0.0021821494|0.0043642989|0.4374054|0.009977698|12,11 (0.9980,0.0017)|
|29|11|19|1.000000–1.043130|1.0491203|2.0982406|2.1127982|0.9931098|11,10 (0.3331,0.2714)|
|29|12|18|1.043130–1.096737|0.096936693|0.19387339|0.83380367|0.2325168|12,10 (0.9880,0.0040)|
|30|11|20|1.000000–1.018511|1.2020142|2.4040285|2.5187672|0.9544465|11,10 (0.2915,0.2482)|
|30|12|19|1.018511–1.070853|0.52765338|1.0553068|1.2317178|0.8567764|12,11 (0.7986,0.1132)|
|30|13|18|1.070853–1.097643|0.0027423277|0.0054846553|0.26856589|0.02042201|13,12 (0.9813,0.0182)|
|31|12|20|1.000000–1.046300|1.1742876|2.3485752|2.4939664|0.9417028|10,11 (0.2185,0.2026)|
|31|13|19|1.046300–1.072476|0.095697615|0.19139523|0.79073329|0.2420478|13,12 (0.9384,0.0366)|
|32|12|21|1.000000–1.022974|1.1242461|2.2484921|2.3066501|0.9747868|10,11 (0.2204,0.2077)|
|32|13|20|1.022974–1.048567|0.23111311|0.46222621|0.97035508|0.4763475|13,12 (0.9788,0.0152)|
|33|13|21|1.000783–1.025820|1.0213058|2.0426115|2.0733661|0.9851669|12,11 (0.2351,0.2019)|
|33|14|20|1.025820–1.098008|0.021782114|0.043564228|0.56068998|0.07769753|14,13 (0.9675,0.0302)|
|34|14|21|1.004150–1.074812|0.81428615|1.6285723|1.7309759|0.9408405|13,14 (0.3100,0.2281)|
|34|15|20|1.074812–1.107286|0.020773276|0.041546551|0.40409811|0.102813|15,14 (0.9476,0.0339)|
|35|14|22|1.000000–1.052686|0.90616929|1.8123386|1.8182258|0.9967621|13,14 (0.3372,0.3092)|
|35|15|21|1.052686–1.084491|0.02587707|0.05175414|0.53811449|0.09617682|15,12 (0.9956,0.0016)|
|36|14|23|1.000000–1.031554|1.0556089|2.1112179|2.2460139|0.9399843|13,14 (0.2736,0.2241)|
|36|15|22|1.031554–1.062721|0.033973266|0.067946533|0.61677031|0.1101651|15,13 (0.9894,0.0043)|
|37|15|23|1.011348–1.041904|1.0070116|2.0140232|2.0670736|0.9743355|15,14 (0.7381,0.1596)|
|37|16|22|1.041904–1.080216|0.01952959|0.039059179|0.43996143|0.08877864|16,15 (0.8906,0.1016)|
|38|15|24|1.000000–1.021978|1.0130822|2.0261645|2.0367096|0.9948225|13,14 (0.2737,0.2292)|
|38|16|23|1.021978–1.059557|0.071942504|0.14388501|0.77473404|0.1857218|16,15 (0.9795,0.0147)|
|39|16|24|1.002884–1.039761|1.0071509|2.0143019|2.0145446|0.9998795|13,14 (0.2939,0.2830)|
|39|17|23|1.039761–1.077448|0.044887471|0.089774943|0.55201183|0.1626323|17,16 (0.9359,0.0472)|
|40|16|25|1.000000–1.020773|1.0699918|2.1399837|2.1903564|0.9770025|14,13 (0.2915,0.2820)|
|40|17|24|1.020773–1.057772|0.099565469|0.19913094|0.75062314|0.2652875|17,14 (0.9924,0.0027)|
|60|26|35|1.004516–1.027969|1.2941013|2.5882025|2.6183536|0.9884847|17,25 (0.1704,0.1165)|
|60|27|34|1.027969–1.041211|0.024239328|0.048478656|0.56338952|0.0860482|27,26 (0.9484,0.0430)|
|80|36|45|1.000000–1.013237|0.80645482|1.6129096|1.7315011|0.9315094|34,35 (0.4241,0.4098)|
|80|37|44|1.013237–1.035590|0.007083879|0.014167758|0.67173296|0.02109135|37,36 (0.9969,0.0016)|

## Gap data and validation

all_local_gaps.csv reports every included zero in every passing sector, its previous and next gap, nearest gap, normalized gap, and weak singular-vector weight. The next zero outside T is included when determining nearest distance. For the first positive zero only the next positive neighbor is used. The requested <0.3 flag is a spacing diagnostic, not a certification of a classical Lehmer pair.

Main m16..40 computations use100dps/GL128, with saved higher-precision spectra and quiet residuals for m16,24,32,40. m20 reuses its saved full matrix. The optional m60,80 computations use120dps/GL128; their weakest passing sectors were independently repeated at160dps/GL160. Matrix Frobenius differences divided by the positive saturation gap are1.221e-117 and6.298e-117. Weak left vectors agree up to sign within1.36e-119 and7.83e-120. See RESULT_large.md and comparison JSONs. This is precision/quadrature agreement, not an interval certificate. Extreme bottom signs at m60,80 are not asserted; the positive lambda_r and count thresholds are well above the measured discrepancies.

Full raw cells retain U, F, singular values and weak vectors. scan.py performs the calculation; analyze.py makes combined CSVs without new eigenproblems; large_*.py reproduce the extension checks. all_grid.csv contains the sampled thresholds; cells also retain intervening zero-count states. SHA256SUMS covers committed artifacts. No RH or NOESCAPE theorem is claimed.
