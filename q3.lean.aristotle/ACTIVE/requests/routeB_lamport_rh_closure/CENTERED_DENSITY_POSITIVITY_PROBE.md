# CENTERED_DENSITY_POSITIVITY_PROBE

Float64/complex128; exact `centeredTrialDensity` finite sum; 4001 equally spaced points including both window endpoints.

| (m,N) | min Re q | max Re q | min/max | max |Im q| | Re q < 0 count | fraction |
|---|---:|---:|---:|---:|---:|---:|
| (53,120) | -1.58502908854 | 3.88196915664e-09 | -408305430.72 | 1.96967794954e-16 | 3570 | 0.892276930767 |
| (257,120) | -1.58096884549 | 1.51362072632e-08 | -104449471.258 | 2.01041602483e-16 | 3413 | 0.853036740815 |

| (m,N) | Re c0 | phase sign | aligned min/max | aligned negative fraction |
|---|---:|---:|---:|---:|
| (53,120) | -0.439500954016 | -1 | -2.44914694923e-09 | 0.107723069233 |
| (257,120) | -0.372907762503 | -1 | -9.57400729711e-09 | 0.146963259185 |

| (m,N) | direct/recentered max abs delta | coefficient norm |
|---|---:|---:|
| (53,120) | 1.99840144468e-15 | 1 |
| (257,120) | 2.10948645725e-15 | 1 |
