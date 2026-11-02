# DH complement envelope — diagnostic only

**DIAGNOSTIC_NOT_INTERVAL_CERTIFIED.** These are 120-digit evaluations of saved native κ=1.1 data. Neither the true-Q residual δ nor the zero census/coordinates is interval-certified by this computation. The source matrix is the pole-free DH form pinned at d26831357b6cb3b2b7d4a569d2031e454952b246.

Equation (7.1) assumes λ_min(A)=−R<0, Q isometric, and ||AQ||≤δ<R. Its complement upper envelope is −R+δ²/(R−δ). Here R comes from the saved full spectrum, not from the complement eigenvalue. The positive constant is c_D=γ+log(8π/5)−π/2=0.621152853201771969169555, the negative of the original signed constant.

|m|R|δ|upper envelope|C_violation|
|---:|---:|---:|---:|---:|
|55|0.663920646081049792|3.44079009708846421e-8|-0.663920646081048008|0.0427677928792760393|
|80|1.24068701234965723|1.07855923001334692e-11|-1.24068701234965723|0.619534159147885262|
|120|1.58825368803550097|6.85316657399964121e-14|-1.58825368803550097|0.967100834833729005|

C_violation=R−δ²/(R−δ)−c_D. If the inputs and hypotheses were independently certified, every fixed C<C_violation would make the envelope plus C+c_D strictly negative. The displayed positive thresholds are diagnostic numerical findings, not certified complement-floor violations.

An independently certified negative Rayleigh upper establishes the existence of a negative direction. It does not by itself certify the numerical full minimum R, the true interpolation residual δ, or this projected envelope. No global/cofinal conclusion is drawn here.

The CSV retains input SHA-256 hashes, the numerical δ<R check, and the comparison with the saved complement minimum. Replay with `uv --offline run --with mpmath python3 envelope.py`.
