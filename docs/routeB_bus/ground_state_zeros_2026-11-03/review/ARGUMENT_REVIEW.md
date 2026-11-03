# Bounded m300 numerical contour check

The independent sampled argument check agrees with the complete HIGH
polynomial census for the four completed LOW cases below. The LOW planted
odd case was stopped by the requested CPU budget and remains unchecked by
this contour method. No interval or between-node contour certificate is
claimed, and no source/eigenvector/root solve was performed.

The rectangle is 1e-6<Re(z)<370.17962509312907712492449151228407996098633395151,
|Im(z)|<1/2. The numerator is assembled independently using a barycentric
recurrence rather than the census implementation's polynomial quotients.
Flint evaluates its complex argument directly, avoiding Fourier underflow
or conversion of polynomial amplitudes to floating point.

|World/parity|Vector|Numerator count|Physical F count|Step / halfstep|HIGH isolated count agrees|
|---|---|---:|---:|---|---|
|zeta even|LOW|183|219|0.25 / 0.125|yes|
|zeta even|HIGH calibration|183|219|0.25 / 0.125|yes|
|DH even|LOW|299|335|0.5 / 0.25|yes|
|planted even|LOW|299|335|0.5 / 0.25|yes|
|DH odd, full finite ground|LOW|299|335|0.5 / 0.25|yes|
|planted odd, full finite ground|LOW|not completed|not completed|budget exhausted|pending|

All completed step/halfstep integer counts agree exactly at displayed
double precision. The physical count adds the 336 sine zeros and
subtracts the 300 denominator zeros, giving a correction of +36. This
also applies to odd parity because the forced origin is outside the
rectangle. DH even, planted even, and DH odd each have 299 distinct LOW
strip roots measured by the separate seeded Newton replay, consistent
with these sampled numerator counts. The zeta replay count was not yet
available in the bound high-census snapshot.

Every sampled polynomial ball excluded zero. The fine-grid maximum phase
increment is at most 1.047 radians, passing the conservative pi/2 guard.
The coarse-grid maximum is at most 2.073 radians, below pi but failing the
same stricter pi/2 guard. Both facts are retained in the JSON. Thus this is
step-halving numerical evidence with a coarse-grid guard limitation, not
a certified winding count. Argument error radii converted to float
underflowed to zero; that is explicitly labeled and is not an assertion
of exact phase evaluation.

The HIGH complete census has no roots in the excluded tiny axis strip
0<Re(z)<=1e-6. Its smallest positive real coordinate is 14.1347 for zeta,
0.554503 for DH even, 0.572274 for planted even, and 1.10038 for DH odd.
No completeness assertion is made about that tiny strip for LOW vectors.

The pilot used 62.741 CPU seconds and the remaining LOW checks stopped
at 57.263 CPU seconds, totaling 120.005 CPU seconds; the polling guard
accounts for the approximately 0.005-second total overrun. Remaining HIGH
cases were deliberately not sampled because their complete isolated root
censuses already exist. Exact sampled data, file hashes, phase guards,
and omissions are in argument_count.json and its two component JSON files.

Final dense-grid review is still pending the complete frozen payload.
