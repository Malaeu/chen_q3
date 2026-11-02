# Large-carrier capacity conditioning

Both optional carriers completed. Main computations use120dps/GL128, preserving literal L=log m and N=m. All continuous zero-count states on κ∈[1,1.4] were checked:18 states for m60,23 for m80. Missing grid states were filled with the independent polynomial kernel and the validated GL160 matrix. They all fail saturation; raw E conditioning is marked unavailable for these nonpassing supplements.

|m|q|r|delta|lambda_r|sigma_min²|2sigma_min²/lambda_r|pair mass|row correlation|
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|60|26|35|0.903688683921|2.61835363177|1.29410126687|0.988484711285|0.256263482454|0.189650673971|
|60|27|34|0.376646712929|0.563389515229|0.024239328219|0.0860482048877|0.991438221041|0.831856588211|
|80|36|45|0.958503375083|1.73150113377|0.806454824152|0.931509438168|0.833876580374|0.526093039854|
|80|37|44|0.624147553774|0.671732956632|0.00708387898944|0.0210913545911|0.998529719312|0.441853580983|

Only q26,27 pass for m60 and q36,37 for m80. Saturation uses the main scanner’s positive threshold mu=1.000001 delta and signed eigenvalue count. The weakest-gap/smallest-sigma passing sectors are q27 and q37 respectively. Both were checked at160dps/GL160. The m60q27 calculation reuses150-digit serialized entries from the160dps matrix; m80q37 uses the freshly built160dps matrix.

The main120dps computations do not resolve or certify the relative size or sign of the extreme ground eigenvalue. The reported positive threshold counts and lambda_r gaps are much larger than the measured matrix perturbations.

For m60,q27: max matrix-entry difference=5.5e-119; relative delta difference=1.377e-119; relative lambda_r difference=8.788e-120; relative sigma_min² difference=4.657e-119; matrix Frobenius difference divided by saturation gap=1.221e-117.

For m80,q37: max matrix-entry difference=6.039e-119; relative delta difference=2.023e-119; relative lambda_r difference=1.049e-119; relative sigma_min² difference=9.925e-120; matrix Frobenius difference divided by saturation gap=6.298e-117.

Continuous κ interval endpoints are retained. With strict gamma<T counting, an interior lower endpoint is excluded and its upper endpoint included; κ=1 is included when it lies inside the count interval. These finite diagnostics do not establish a uniform capacity bound or an asymptotic theorem.
