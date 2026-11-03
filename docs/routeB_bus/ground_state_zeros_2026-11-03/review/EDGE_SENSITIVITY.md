# Selected edge sensitivity check

Preliminary saved zeta m160 vector, evaluated independently at 450 decimal
digits through review/transform_replay.py's sinc and analytic derivative.
No eigensolve or source-zero root seeding was performed.

The fixed cutoff is T=223.69095534901962685. At the first source ordinate,
|F'|=0.00186297656501. At the last source ordinate below Omega,
t=198.01530967625, |F'|=5.31512232967e-109. At the last source ordinate below
T, t=221.43070555469, |F'|=1.49094521097e-135 and |F|=1.10057932632e-156.
At T itself, |F'|=3.82240918215e-136.

This illustrates why a small coefficient supnorm replay discrepancy or
small transform residual alone does not control edge root positions.
Generic vector-error bounds can be much larger than the edge derivative.
The actual low/high coefficient perturbation may be strongly correlated
and produce a much smaller transform perturbation. A selected physical
root replay using separately computed source/eigenpair vectors is the
relevant discriminator; polynomial arithmetic replay for one fixed vector
does not supply it. The spectral and root workers were notified and have
arranged to retain selected low vectors for this check.
