# Independent bounded read-only v2 review

A separate nonauthor reviewed the final numerical source definitions, selected
MP readbacks and the P1–P5 implementation. No material source/deformation error
was found. It verified the signed atom split, DH nonprime block, double2 rule,
face gate stops, rank-one price-map dimension bound, whitening/one-sided pole,
P5 counterterms, curvature−4E′ᵀE′ and MP bracket signs above the empirical floor.

Required reporting qualifications are retained: a positive face direction is
not a whole-source feasible ray; binary/MP faces differ with their floor;
no forced scaling-null relation; trace-zero dual gives no bound; indefinite
dual or nonzero equality residual is not annihilating stress; basis negativity
is not a negative form; the root is first sampled, not globally certifiedfirst.

A replay-path issue was repaired after numerical execution by exposing
STIFFNESS_BASE/STIFFNESS_LOCAL in p5.py. Its numerical kernel is unchanged;
the old executed hash and new portable-script hash are recorded separately in
p5_VALIDATION.json. The final additional all-knob MP inertias reuse the existing
cached matrices and precision. Neither change invokes a new source or frame
builder. Root verification checks all final bytes and numerical receipts.

This is bounded methodological/numerical readback review, not proof admission,
an interval certificate, cofinal positivity or RH.

Final saved-frame confirmation exposed an S4 orientation issue: the inherited
MP polynomial basis passes its diagonal test, while the authorized regenerated
saved basis at24 has a resolved positive column. The final score distinguishes
them. Original NPZ bytes are unavailable, so no original-byte diagonal score
is asserted. An MP projection removes tiny saved-frame quiet-space leakage.
