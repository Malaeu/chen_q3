# V-gap stability and unheated theta reference

**DIAGNOSTIC_NEVER_A_PROOF.**

The functional and physical conventions are exactly those in ../v_forms.py and ../RESULT.md. This follow-up recomputes even eigenvectors at160dps, GL128 per each of eight panels; m32 and log12,N68 are replayed at180dps/GL160. The source includes the full archimedean tail, all active prime powers and the pole. Fixed-window N varies independently of L and the prime cutoff.

We report V_i=<f_i,B_V f_i> for the normalized eigenvectors of the CCM matrix K, in ascending K-eigenvalue order. g=V_1−V_0 is an expectation-value gap, not an eigenvalue gap of B_V. Two minima are reported: over the requested cluster i=1..7, and over all excited even levels i=1..N. Neither is an infimum over arbitrary linear combinations orthogonal to f_0.

## Gaps and projected unheated h

Here h_N=P_Nh/||P_Nh||, with hat h=4xi(1/2-it); no heat evolution is applied. In literal rows N=m. In fixed-window rows L=log(window m).

|window m|N|V0|V1−V0|min1..7 gap|min1..N gap|V[h_N]|V[h_N]−V0|
|---:|---:|---:|---:|---:|---:|---:|---:|
|12|12|3.850686572650|1.164036564203|1.164036564203|1.164036564203|3.907440545623|0.056753972972|
|16|16|3.843386437630|1.163708966074|1.163708966074|1.163708966074|3.907440545620|0.064054107989|
|20|20|3.840205722805|1.163868755374|1.163868755374|1.163868755374|3.907440545620|0.067234822815|
|24|24|3.840240026438|1.163970564748|1.163970564748|1.163970564748|3.907440545620|0.067200519182|
|32|32|3.842568077250|1.162126887366|1.162126887366|1.162126887366|3.907440545620|0.064872468370|
|8|56|3.969334567572|1.107796402389|1.107796402389|1.107796402389|3.907440549992|-0.061894017580|
|8|60|3.969338388874|1.107773936147|1.107773936147|1.107773936147|3.907440549992|-0.061897838882|
|8|64|3.969340954695|1.107726138981|1.107726138981|1.107726138981|3.907440549992|-0.061900404703|
|8|68|3.969328831102|1.107710383352|1.107710383352|1.107710383352|3.907440549992|-0.061888281110|
|12|56|3.947351758144|1.115913297636|1.115913297636|1.115913297636|3.907440545620|-0.039911212524|
|12|60|3.947383676815|1.115848992338|1.115848992338|1.115848992338|3.907440545620|-0.039943131195|
|12|64|3.947419675382|1.115858361017|1.115858361017|1.115858361017|3.907440545620|-0.039979129763|
|12|68|3.947420415902|1.115858811520|1.115858811520|1.115858811520|3.907440545620|-0.039979870282|

All minima in this finite scan occur at i=1. The complete all-level expectations are preserved in all_levels.csv.

## First eight levels

|window m|N|V0|V1|V2|V3|V4|V5|V6|V7|
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|12|12|3.8506865727|5.0147231369|5.4474343048|5.9152419942|6.2115671308|6.4314740614|6.7976961390|6.8574992343|
|16|16|3.8433864376|5.0070954037|5.4382766680|5.8795436380|6.2138242091|6.3147840995|6.7535173193|6.8420311815|
|20|20|3.8402057228|5.0040744782|5.4372531093|5.8708468731|6.2068447958|6.2805071650|6.7351050047|6.8284418694|
|24|24|3.8402400264|5.0042105912|5.4367521749|5.8709246753|6.2072460134|6.2747286712|6.7221802575|6.8067259896|
|32|32|3.8425680772|5.0046949646|5.4347791562|5.8720434038|6.2056636810|6.2764727667|6.7210223459|6.8035536689|
|8|56|3.9693345676|5.0771309700|5.5383866892|6.1489815045|6.1883167077|6.8170282180|6.9966322106|7.6127419251|
|8|60|3.9693383889|5.0771123250|5.5383228997|6.1490549049|6.1882832072|6.8167914095|6.9961255989|7.6127764646|
|8|64|3.9693409547|5.0770670937|5.5383338818|6.1490937355|6.1880622672|6.8166785791|6.9960200367|7.6130473051|
|8|68|3.9693288311|5.0770392145|5.5383798053|6.1490640258|6.1877663477|6.8167047376|6.9961402432|7.6134267457|
|12|56|3.9473517581|5.0632650558|5.5081752997|6.1027920003|6.1192158433|6.7727223890|6.6758614331|7.0367627397|
|12|60|3.9473836768|5.0632326692|5.5082809183|6.1029491483|6.1189039482|6.7729043297|6.6759237700|7.0363010697|
|12|64|3.9474196754|5.0632780364|5.5081926912|6.1029919989|6.1190641878|6.7724890410|6.6765078013|7.0353573290|
|12|68|3.9474204159|5.0632792274|5.5082591087|6.1028413079|6.1192651649|6.7722365823|6.6768015516|7.0348538727|

## Interpretation

The literal gaps range from1.162126887 to1.164036564; the fixed-window gaps range from1.107710383 to1.115913298. Thus the sampled gaps are of order one and remain positive, but the value is not exactly1 or resolution-invariant. These13finite cells do not establish a uniform cofinal lower bound.

The projected-h value is almost constant around3.90744055. It exceeds V0 on the literal cells, and is smaller than V0 on the high-resolution fixed-window cells. This is compatible with the CCM ground minimizing K rather than V. Positive diagonal expectation gaps do not make f0 a minimizer of V or establish coercivity of V on f0-perpendicular space: B_V has off-diagonal entries in the K-eigenbasis. Their largest magnitude is retained in summary.csv.

The label high resolution is not a claim of N-convergence. The corresponding lambda0 and lambda1, eigen residuals and w0 are recorded in summary.csv; stabilization of V expectations does not certify convergence of tiny K-eigenvalues.

## Reproduction and checks

gap.py builds each requested window at its largest N, then diagonalizes the principal submatrices. It records all even V expectations, first-eight eigenvectors and normalized h coefficients. source_v_forms_sha256 pins the unchanged shared implementation in every raw cell. validation.json compares both higher-precision replays and verifies the minimizer indices; zero saved differences mean agreement at100significant output digits, not exact equality.

Example runs:

```sh
uv run --with mpmath python3 gap.py --window 32 --N 32 --tag literal
uv run --with mpmath python3 gap.py --window 8 --N 56 60 64 68 --tag resolution
uv run --with mpmath python3 gap.py --window 12 --N 56 60 64 68 --tag resolution
uv run --with mpmath python3 gap.py --window 32 --N 32 --dps 180 --order 160 --tag validation
uv run --with mpmath python3 gap.py --window 12 --N 68 --dps 180 --order 160 --tag validation
uv run --with mpmath python3 finalize.py
```

For the other literal rows repeat the first command with m=N=12,16,20,24. No interval, NOESCAPE, RH or uniform-gap theorem is claimed.
