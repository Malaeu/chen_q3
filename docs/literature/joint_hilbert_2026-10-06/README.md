# Primary inputs to the full-carrier arithmetic bound (answer3)

Root fetched and read the stated theorem pages on 2026-10-06.
Shelf grep found earlier HSW usage in the September25 zero-orbit verdict;
that historical citation was not substituted for reading the source.

- Mossinghoff, Trudgian, Yang, arXiv:2212.06867v1, Theorem1.1, printed p2.
  https://arxiv.org/pdf/2212.06867
  SHA256 127c32eb86d0aea264cc5b1ba96cc83243ef6b763451591e1560edaca1767300.
  Quote: "There are no zeros of ζ(σ + it) for |t| ≥ 3".
  The displayed region is sigma>=1-1/[55.241(log|t|)^(2/3)(loglog|t|)^(1/3)].
  EXACT_FIT to answer3 (9) only. For U=4m² monotonicity bounds all
  3<=|gamma|<=U; finitely many lower ordinates are absorbed in m0.
  This is a shrinking region near sigma=1, not a fixed half strip or RH.
- Hasanalizade, Shen, Wong, arXiv:2107.06506v1, Corollary1.2, printed p2.
  https://arxiv.org/pdf/2107.06506
  SHA256 3fc4c89f49249924e61cb0d289d81559faed53fcbb838628ea32dc7ec6f89fbf.
  Quote: "For any T ≥ e, we have".
  Displayed bound: |N(T)-T/(2pi)log(T/(2pi e))|
  <=0.1038logT+0.2573loglogT+9.3675.
  EXACT_FIT to the O(log T) remainder used in answer3. Taking differences
  at t+1 and t-1 and conjugating negative heights gives O(log(|t|+2))
  zeros per unit interval, with multiplicity; bounded heights cost O(1).

Neither paper supplies the common-cell signed matrix inequality (21).
The twisted Perron argument and all carrier/endpoint budgets are our
application and require the separate bounded audit in JOINT_HILBERT_AUDIT.
No claim of best currently available constants; improving constants does
not change the exponent 1/2-o(1) into o(1).
