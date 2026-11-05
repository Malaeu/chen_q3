# Joint-source Y: reviewed obstruction and exact transfer audit

Date: 2026-09-15. Status: PAPER / independent analytic review accepted in the
scopes below. No Lean verification or canonical theorem admission is claimed.

## Receipt and source identity

Request `REQ-2026-09-15-JOINTSOURCE-Y`, commit
`f5e1654b3d3179ca5c47f17171f47037fc1c8bae`, TXT SHA256
`489b7efda64c594d1f98ffa89317261fc545a8a315b9e41b6f0aa31d711862dc`.
Context SHA256 `ebd240e49b001802b7a40dd25c07bebb148b9b81a0daefd5cd006d43b0b8a961`.
Natural completion was observed in the same living chat
`6aa52001-4094-83eb-9520-01a09f54eff2`, titled «Математическая цель и шаг»;
assistant message `c335f2e7-334d-45dd-b05d-416a7f1000f6`, displayed reasoning
duration 31m30s, status idle. No duplicate request or Answer now action.

Proshka reported inability to publish. The exact Markdown attachment was
downloaded and read, then relayed by Mac under the existing assigned output
scope. Its original NOT_PUBLISHED statement describes the producer's attempt;
the raw bytes are not rewritten to pretend that Proshka pushed them.

Raw assigned path:
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_JOINTSOURCE_Y_2026-09-15.md`.
SHA256 `207d69460d0a9fc7a2089bfc71dfd915b60ba8e48f22c72d4be412fdeae5e388`;
55575 bytes, UTF-8, 594 LF, final LF. Full report read by parent and reviewer.

## Accepted mathematical result

Use the actual full source probability law
dnu(t)=t^(1/4)r(t)dt/M_r(5/4), X=(log t)/2 and mu_j=E_nu X^j.
The proposed auxiliary function is

    H_r(z)=E_nu [sin(zX/2)/(zX/2)]^2.

The source construction and exact identity are valid:

    (z^2 H_r(z))''/2 = F(z)/F(0).

If H_r belonged to the Laguerre-Pólya class, multiplication by z^2 and two
derivatives of real-rooted polynomial approximants would give real zeros of
F. This is a closed sufficient criterion, not an extra hidden downstream
assumption. However the criterion is false for this chosen H_r.

The two source inputs together yield a symmetric decreasing density for X.
Its exact uniform-scale mixture gives mu4 >= (9/5)mu2^2. A necessary even
Laguerre-Pólya coefficient inequality is 3H''(0)^2-H''''(0)>=0, whereas here

    3H_r''(0)^2-H_r''''(0)
      = mu2^2/12-mu4/15 <= -11 mu2^2/300 < 0.

Thus KILL_JOINTSOURCE_DILATION_AVERAGED_LP_FACTOR is accepted only for the
specified auxiliary H_r. The source-tail justification, full H_r nonreal-zero
argument and finite H_N controls were also independently checked. Nonreal
zeros of H_r do not imply nonreal zeros of its differentiated expression F.
The Gaussian control in the raw report demonstrates this distinction.

AUTOPSY: dropped=SIGN; note=The chosen dilation average violates the necessary LP coefficient inequality on the actual full source; closed sufficiency does not establish the sufficient premise.

## Independent review certificates

Reviewer `/root/sibling5_check`, distinct from the author of each report,
read-only review, no edits or production admission:

* Raw response SHA `207d69460d0a9fc7a2089bfc71dfd915b60ba8e48f22c72d4be412fdeae5e388`:
  `ACCEPT_JOINTSOURCE_DILATION_LP_FACTOR_OBSTRUCTION_ONLY`. Reviewer verified
  normalization, sufficiency, envelope, moments, strict coefficient defect,
  and finite/full auxiliary nonreal-zero arguments.
* `docs/Codex/REPORT_2026-09-15_WEIL_ROSATI_TRANSFER_AUDIT.md`, SHA
  `11bcc8b0208ea8e992312c43f5428de602b10e4c200c99b86bfef34afc580754`:
  `ACCEPT_SCOPED`. Reviewer verified source inversion, negative reflected form,
  finite-rank trace -1, TN versus Hermitian positivity, Gaussian Fourier zeros,
  and the Milne source fit from the pinned web extraction.

The second audit rejects direct identification of source inversion or the raw
TN table with a positive Rosati structure. A positive unitary coefficient
realization alone does not identify zeros with a self-adjoint spectrum.

## Continuation boundary

Both candidate tests are complete. The general joint A+B mechanism, RH, and
the sign of the full V remain open. There is no negative V-row and no new
source-sign theorem. V stays parked. Native goal state is not changed.
No automatic new Proshka request is sent and no proof counter is reset.

Before a different Weil-style candidate is pursued, it must name one exact
source-derived object, the positive duality it uses, and the correspondence
to zeros of the full F. These must refer to the same object. Replacing H_r by
its differentiated expression merely restates the original real-zero target.
No assertion that all constructions from A+B fail is supported by this intake.
