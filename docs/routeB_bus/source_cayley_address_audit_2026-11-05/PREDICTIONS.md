# Pre-registration: SOURCE_CAYLEY_ADDRESS_AUDIT

Route B = CHALLENGER / NOT_RH. DIAG only; no interval root certificate or RH claim.
Source verdict blob: 7cf72ea5ae3f3370eee05b9cc688887e10c37852 at inbox f96a9072071c13011cc0fb4a6408e2214ed64181.
Proshka registration sha256: 6f752df6628611336678d62edfad645127bff1d2f080e01ea975a7bd07fcca71.
Proshka numerical-design sha256: c06f31487f38c7667b5c56a25efaa0a100b055d34b89d45373657dd01f5d7103.

## Registered thresholds copied verbatim

```yaml
  threshold: "2*eps < positive DH/planted defect < 6*eps; real-axis modulus error < 1e-30 / 1e-50"
```

До вычислений зарегистрированы `dps=45,70`, `ε=10^−3,10^−4`, четыре DH-адреса, подсадка `7+i/3`, ζ и кривая как контроли. Порог: `2ε<|𝒮_D(w−iε)|²−1<6ε`; ошибка вещественной унитарности и относительная ошибка функционального уравнения DH меньше `10^−30` при 45 знаках и `10^−50` при 70. Отношение дефекта к `4ε` должно приближаться к 1 при уменьшении ε. Хеши регистрации приведены в YAML; полного перебора нулей этот дизайн не содержит.

## Owner audit gates (unchanged)

- 2*eps < |S_D(w-i*eps)|^2-1 < 6*eps at all four DH addresses and the plant, dps45 and70, eps0.001 and0.0001.
- For each address and precision, abs(defect/(4*eps)-1) decreases as eps decreases.
- DH real-axis unitarity and DH functional-equation relative errors <1e-30 at45dps and <1e-50 at70dps.
- Zeta via full M_Xi and E/F3 curve have nonpositive defects at the same points, allowing only the corresponding precision tolerance.
- Direct Cayley defect equals -4*Im(M)/|M+i|^2 to the corresponding precision tolerance.

Any failure is DIAG_FORMULA_OR_NORMALIZATION_FAILURE with point, precision and both sides. No threshold retuning.

## Independent predictions registered before any run

- C1 (P=0.95): all off-axis sign/size, unitarity, functional-equation and Cayley-identity gates pass in both independent and Appendix-A replays.
- C2 (P=0.90): the largest abs(defect/(4*eps)-1) over DH+plant at eps0.0001 is <0.001 at both precisions.
- C3 (P=0.95): independent analytic-Hurwitz-derivative implementation and Appendix A agree in their physically meaningful mathematical fields to at least29significant digits where serialized32-digit values allow this (absolute/relative scaled tolerance1e-29). Tiny root residuals and rounding diagnostics are compared against their own gates, not required to be identical.
- C4 (P=0.85): at m2000, the saved screen contains at least one failing event within j0+/-1 for at least three of the four DH addresses. This is a prediction about the saved rows only, not a new matrix threshold law.

Numerical design: dps={45,70}; eps={0.001,0.0001}; DH addresses gamma={85.6993484854,114.1633427308,240.4046723514,166.4793059132}; full planted quartet at7+i/3. Independently refine DH seeds from the pinned census by Newton with analytic Hurwitz-zeta derivatives; build M_D with conductor5, own oddGamma, no zeta pole. Use full mpmath zeta for M_Xi, curve M=log3*tan(log3*z), and the planted log-derivative source. Run Appendix A unmodified only after writing the independent implementation.

Saved-screen cross-check only: m={74,75,206,207,621,622,2000}, each j0=round(gamma*log(m)/(2*pi)), and all valid j0-1,j0,j0+1. Missing saved rows are reported missing, never recomputed. No new matrices or eigensystems.

This exact file is committed in an immutable registration Git object before numerical runs, without moving rh_clean; one final scoped branch commit carries the same blob and registration receipt.
