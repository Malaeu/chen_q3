# Step33A A-source sync PSD sanity

This is a non-mutating diagnostic. It plugs the `Q3.a_star` candidate A
midpoints from `a_source_convention_audit.json` into the current finite
payload contour and checks the midpoint penalty matrices numerically.

It does not edit CSV files, radius payloads, radius-floor data, LDL data,
or Lean proof files.

## Summary

| family | source | A(0,0) | D min eig | D floor | D pass | R min eig | R floor | R pass |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| primary | current Step22 import | 1.2336444536392195e-01 | 1.2228595300390246e-04 | 1.2228594783222341e-04 | True | 1.3569220794537940e-01 | 1.3569220778186006e-01 | True |
| primary | -current Step22 import | -1.2336444536392195e-01 | -1.4181814057633806e+00 | 1.2228594783222341e-04 | False | -7.0879315415025079e-01 | 1.3569220778186006e-01 | False |
| primary | candidate Q3.a_star import | -7.8897741430231719e+01 | -1.0165250980604694e+02 | 1.2228594783222341e-04 | False | -1.0108826416650179e+02 | 1.3569220778186006e-01 | False |
| primary | -candidate Q3.a_star import | 7.8897741430231719e+01 | 3.9791780721886830e+01 | 1.2228594783222341e-04 | True | 4.0663921324025132e+01 | 1.3569220778186006e-01 | True |
| control | current Step22 import | 2.6248903658774844e-02 | 1.2636923475545920e-05 | 1.2636922821866160e-05 | True | 1.9590650942526585e-03 | 1.9590640625249765e-03 | True |
| control | -current Step22 import | -2.6248903658774844e-02 | -1.3670744647608697e+00 | 1.2636922821866160e-05 | False | -6.8456128081061085e-01 | 1.9590640625249765e-03 | False |
| control | candidate Q3.a_star import | -7.5205130170991836e+01 | -1.0027132888586563e+02 | 1.2636922821866160e-05 | False | -9.9636688709770411e+01 | 1.9590640625249765e-03 | False |
| control | -candidate Q3.a_star import | 7.5205130170991836e+01 | 3.2141441101211207e+01 | 1.2636922821866160e-05 | True | 3.2945920664575759e+01 | 1.9590640625249765e-03 | True |

## Interpretation

A blind A-table migration to the currently audited `Q3.a_star` candidate
does not preserve the existing finite penalty certificate contour. The
`-Q3.a_star` sign variant is tracked only as a diagnostic hint; the
source convention must be reconciled before mutating global A payloads.
