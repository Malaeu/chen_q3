# STATUS: RUN_PINNED_THETA_11_12_DEPENDENCY_AUDIT
```yaml
OPERATIVE_CLASS: RUN_PINNED_THETA_11_12_DEPENDENCY_AUDIT
AUTHORITY: CURRENT_OWNER_READ_ONLY_AUDIT_REQUEST
REPOSITORY: Malaeu/chen_q3
BRANCH_LABEL: proshka_inbox_2026-10-31
SOURCE_COMMIT: 2258f6b02aad1e3c8cd073a7e1ecb80dbfbef2e1
MODE: READ_ONLY_DEPENDENCY_AND_CONDITIONAL_IMPACT_AUDIT
RESULT: AUDIT_COMPLETE_NO_NEW_SOURCE_THEOREM_CERTIFIED
SCALEJET_SHA256: 599e50b77946d7e9da82943f3dbfeef48ffa66d5dba6aca6a5727ec32d8669fb
HARDBREAK_SHA256: 5b727bfe4a7b99351852162a51ced4589cb662566235b35d49f1cebd028755ad
HASH_CHECKS: MATCH
HYPOTHETICAL_IMPORT_CLASS: CONDITIONAL
HYPOTHETICAL_IMPORT_LABEL: OpenAI_quasi_RH
HYPOTHETICAL_IMPORT_STATUS: UNPUBLISHED_NOT_LEAN_VERIFIED_AS_STIPULATED_BY_OWNER
HYPOTHETICAL_IMPORT_INDEPENDENTLY_VERIFIED: false
HYPOTHESIS: psi(x)-x=O_epsilon(x^(11/12+epsilon))_for_every_epsilon_positive
POWER_LOSS: M^(5/12+epsilon)
LOCK_2_POWER_LOSS_ENVELOPE: CONDITIONAL_WITH_CLASSICAL_ALL_HEIGHT_TRANSFER
LOCK_2_UNIFORM_CONSUMER_BOUND: NOT_PAID
LOCK_3_ALL_HEIGHT_POWER_LOSS_ENVELOPE: CONDITIONAL_WITH_CLASSICAL_ALL_HEIGHT_TRANSFER
LOCK_3_CONCENTRATION: UNTOUCHED
LOCK_3_UNIFORM_ALL_HEIGHT_CONSTANT: NOT_PAID
LATER_MUK_AND_NEGATIVE_LEAKAGE_ARTIFACTS_IMPORTED: false
PROOF_OR_REPLAY_EXECUTED: false
REPOSITORY_WRITES: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_CLAIM: NOT_MADE
```

## 0. Audit decision

**The stipulated input supplies a conditional power-saving arithmetic envelope, not either lock in its required uniform form.** At the exponent level the new price is

\[
\theta-\tfrac12=\tfrac{11}{12}-\tfrac12=\tfrac5{12}.
\]

With the classical all-height logarithmic-derivative/Perron transfer explicitly charged, the smoothed symbol and its negative outside mass can be budgeted at a price of order \(M^{5/12+\varepsilon}\). This is **CONDITIONAL_PAID_WITH_POWER_LOSS**, not \(O(1)\). Useful detector concentration, its tail mass, and conversion to a single constant remain unpaid. Existing \(E_M\), \(t_MD_K\), and projection tails must not be confused with that growing prime-discrepancy price: they already have separate, predominantly classical, decaying budgets.

This is a read-only audit, not a proof session. “Classical” below identifies the input used in the files, not a fresh independent verification of every inherited theorem. Conditional impact entries are explicitly separated from statements present at the pin. No source file has been edited, no script replayed, and no new mathematical result has been promoted.

## 1. Pin, bytes, terminology, and scope

Both requested files were fetched through the GitHub connector at the full commit above. Their Git blob identifiers match the Git blob hashes computed from the mounted attachments; SHA-256 was computed over the actual bytes, without newline normalization.

| Alias | File under `docs/routeB_bus/proshka/` | Bytes | LF count | Git blob |
|---|---|---:|---:|---|
| S | `PROSHKA_VERDICT_SCALEJET_2026-10-31.md` | 63,246 | 985 | `1cb3d650f0f9c7e25ef285e1fa8b3153d9356778` |
| H | `PROSHKA_VERDICT_HARDBREAK_2026-10-31.md` | 46,210 | 845 | `2fefd53e6dd2d9492ddbc5a8195fac3e9d4d8feb` |

All `L…` locators below are **original file line numbers**, not tool-response JSON line numbers. Repeated uses in headers, closeouts, and embedded code are indexed separately at the end.

The protocol was read from `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. The current owner instruction limits this task to a read-only audit. No queue, current mathematical branch head, or later verdict is substituted for the specified pin. In particular, the subsequent MUK and NEGATIVE_LEAKAGE files are outside this audit: H (5.4) is still an unpaid assertion **as of this pin**.

**Classification convention.** Each row has a scope and describes the source's PAPER-level ledger. `CLASSICAL` means elementary arithmetic, classical analytic-number-theory facts, or the inherited exact theta/Weil identities actually invoked. `NONE—exact` means there is no prime-error or zero-location estimate at that step. `NONE—missing` means the needed estimate is not supplied. All hypothetical replacements carry verifier `CONDITIONAL`, never `LEAN` or `ARB_INTERVAL`.

## 2. Conditional import: exactly what is being varied

**[COFINAL_FAMILY | CONDITIONAL — owner-stipulated premise, not independently verified here]**

\[
(\mathrm H_\theta)\qquad
\forall\varepsilon>0:\quad
\psi(x)-x=O_\varepsilon(x^{\theta+\varepsilon}),
\qquad \theta=11/12,
\qquad \psi(x)=\sum_{n\le x}\Lambda(n).
\]

Attribution and verification class are exactly those requested: **OpenAI quasi-RH; unpublished; not Lean-verified; CONDITIONAL**. This audit neither validates the unpublished argument nor replaces \(11/12\) by a different advertised exponent. The assumption includes the actual prime-power coefficients. Constants and the first valid cutoff are unspecified and may depend on \(\varepsilon\).

The following are **conditional impact rules**, not claims found in S or H and not new proofs supplied by this audit.

### C1. The primitive of the signed measure changes; its total variation does not

For the original

\[
d\nu(s)=\sum_{n\ge2}\Lambda(n)n^{-1/2}\delta_{\log n}(ds)-e^{s/2}ds,
\]

the ordinary partial-summation bookkeeping gives the power price

\[
\nu((0,L])=O_\varepsilon(e^{(\theta-1/2+\varepsilon)L})
          =O_\varepsilon(m^{5/12+\varepsilon}),\qquad L=\log m.
\]

It does **not** give the same bound for \(|\nu|\). The atomic positive measure and continuous negative measure are mutually singular. Their total variation still has the leading \(\sqrt m\) scale. Consequently S (2.8), an absolute shift-operator bound, or a projection-error bound cannot be changed from \(\sqrt m\) to \(m^{5/12+\varepsilon}\) by textual substitution.

For a signed pairing, conditional partial summation charges the variation/derivative of its test and all endpoint terms. For the oscillating test \(q_M(s)\cos(ts)\), direct partial summation incurs a factor depending on \(|t|\). A fixed-height estimate is not an all-height estimate.

### C2. All-height loss requires the classical analytic transfer to be named

To mark *all-height* coverage “paid with loss,” this audit explicitly includes the classical transfer through the actual zeta logarithmic derivative, not just C1. Under \(\mathrm H_\theta\), a contour at a fixed positive distance to the right of \(\Re s=\theta\) is zero-free. The classical local partial-fraction estimate and local zero count give logarithmic height growth for the pole-compensated logarithmic derivative. The triangular Fejer cutoff has the integrable Perron multiplier \(z^{-2}/L\); the \(s=1\) pole must remain canceled by the continuum. These are the additional classical inputs behind the all-height classification.

A deliberately non-sharp exponent-level impact statement is

\[
|\overline B_M(t)|\le R_\theta(M)w(t)\quad(t\in\mathbb R),
\qquad R_\theta(M)=C_{\varepsilon,s_0}\bigl(1+M^{5/12+\varepsilon}\bigr).
\tag{A}
\]

Logarithmic savings from the taper are not needed for this audit and are not certified as new constants. Here \(m\in[M,2M]\), so the powers of \(m\) and \(M\) are equivalent up to fixed factors. A fixed near cutoff costs only a fixed additive term. This is a **conditional budget consequence**, not an estimate already installed in the two source files.

**Gate distinction:** using only the unsupplemented Abel calculation does not justify (A) uniformly in \(t\). If the classical analytic transfer is not accepted into the dependency ledger, the all-height entry must remain `TRANSFER_REQUIRED`, and only the bounded-height version is credited. Neither file at the pin contains the \(\theta=11/12\) transfer or a numerical value of its constant. This audit records that dependency; it does not claim to have performed a new contour-proof audit.

Classical external check used only to identify this transfer: K. S. Kedlaya, *Notes on analytic number theory*, Chapter 9, (9.1.1), Lemmas 9.4 and 9.6: the literal von Mangoldt Dirichlet series, \(O(\log T)\) local zero count, and the local partial-fraction formula for \(\zeta'/\zeta\). Chapter 7 records the standard relationship between a fixed zero-free strip and a power error in \(\psi\). These references are not evidence for the unpublished OpenAI premise.

### C3. The narrower zero strip is not RH

For nontrivial zeros \(\rho\), the conditional strip is

\[
1/12\le\Re\rho\le11/12,
\qquad z_\rho=i(\rho-1/2):\quad |\Im z_\rho|\le5/12.
\tag{B}
\]

Endpoints are not silently excluded. This does not make all \(z_\rho\) real, eliminate real zeros of \(H\), establish simplicity or separation, prove \(\mathcal L_H\ge0\), or control the conditioning of theta polynomial Gram matrices.

### C4. A damped source tail is a different object from C1

For the exact S-tail

\[
E_L(r)=\int_{(L,\infty)}(s/L-1)Q_r(s)\,d\nu(s),
\]

the existing classical estimate is \(O((\log m)m^{-5/2})T_3(r)^2\). It stays valid unchanged.

A **signed** re-estimation under \(\mathrm H_\theta\) must additionally charge \(Q'_r\). At the power level, the factor \(e^{-3s}\) in the correlation combines with C1 to give

\[
m^{\theta-7/2+\varepsilon}=m^{-31/12+\varepsilon},
\]

with a profile cost such as

\[
T_3(r)^2+T_3(r)T_3(r'),
\]

and the taper/endpoints retained. This is the shape of a conditional reprice, **not** the same \(t_M\) with its published numerical constants. It is also not a replacement of \(t_MD_K\) by \(M^{5/12+\varepsilon}\). The old tail is already decaying; the conditional exponent can only improve its signed re-estimation after the extra derivative budget is retained. The dominating \(\beta_MM_r\) term and degree conditioning do not disappear.

## 3. Complete SCALEJET dependency inventory

Every row below is an audit of the pinned statement, not a fresh proof of it. The scope column refers to the audited claim; current verifier is PAPER and hypothetical changes are CONDITIONAL. Repeated summaries and code uses appear in §5.

| ID / original locator | Scope | Current input: classical / none | What changes under H_theta |
|---|---|---|---|
| S01 — §1, L68–85; (1.1), L87–110 | ABSTRACT | CLASSICAL inherited theta/Fourier normalization, complete Weil radicality and literal measure. **No recent zero-free theorem**; explicitly disclaimed at L74. | Definitions, carrier, prime powers, poles and normalization are unchanged. The hypothetical input is new; it is not retroactively a premise of the existing proof. |
| S02 — §2, (2.5), L151–157 | FINITE_CELL | NONE—exact: same nonnegative filter applied jointly to prime atoms and continuum. | This is the insertion point for C1/C2. The compensated sum can be repriced conditionally; the source is not replaced by a smooth density. |
| S03 — §2, (2.7), L172–178 | COFINAL_FAMILY | CLASSICAL elementary Chebyshev bound \(\psi(x)\le4\log2\,x\), proved by central binomial coefficients. Not a PNT error estimate. | The new input controls \(\psi-x\), a stronger and different object. Existing Chebyshev estimate remains usable for positive coefficient mass. |
| S04 — §2, (2.8), L180–186 | COFINAL_FAMILY | CLASSICAL partial summation of Chebyshev: positive mass \(O(\sqrt X)\), total variation \(O(\sqrt X)\). | **No exponent substitution for total variation.** Only the signed difference has the \(X^{5/12+\varepsilon}\) price. |
| S05 — §2, (2.6), L158–186 | COFINAL_FAMILY | CLASSICAL coefficient mass times \(\|q^d-q^c\|_\infty\le1/(M\log M)\): grid error \(O(M^{-1/2}/\log M)\); derivative price \(L_+\epsilon_{grid}\). | Already paid uniformly in \(t\). Keep unchanged. A signed alternative would need variation and height costs for \(q^d-q^c\); no automatic better uniform error follows from its sup norm. |
| S06 — §2, (2.9), L190–197 | COFINAL_FAMILY | NONE—exact positivity/scale geometry: \(\beta_M\asymp1/\log M\). | Unchanged. An improved prime error cannot make a positive filter cancel the first logarithmic moment. |
| S07 — §3, (3.1)–(3.2), L203–243 | COFINAL_FAMILY | CLASSICAL tapered Chebyshev mass plus continuum, giving \(A_M\asymp\sqrt M/\log M\) and derivative \(L_+A_M\). | These absolute-mass bounds remain valid. C2 gives a different **signed, energy-weighted** all-height envelope with power loss \(M^{5/12+\varepsilon}\). Do not call it a new bound for the total coefficient mass. |
| S08 — §3, (3.3), L220–243 | COFINAL_FAMILY | CLASSICAL \(w(t)\sim\log(2+|t|)\) combined with S07: only \(|t|\ge(5/2)e^{A_M}\) has unit upper constant. | With C2 the previously uncovered heights get an envelope **with a growing loss**. The original unit-constant high-height region remains valid. No replacement of \(A_M\) inside this exponential cutoff from bare Abel summation is justified. |
| S09 — §3, (3.4), L247–254 | FINITE_CELL | CLASSICAL integration by parts of the continuum only; lower-endpoint term retained. | Unchanged. The premise concerns the joint discrepancy, not additional smoothness or a new sign of the continuum. |
| S10 — §3, (3.5) and discussion, L256–270 | FINITE_CELL | NONE—exact finite-frequency mean square/recurrence. No twisted-prime cancellation estimate is supplied. | Finite prime polynomials still do not decay as \(|t|\to\infty\). C2 controls their **compensated, normalized** symbol; it does not contradict this recurrence or supply a decay theorem for the isolated atoms. |
| S11 — §4, (4.1)–(4.2), L276–303 | ABSTRACT | CLASSICAL \(\Lambda(n)\le\log n\), \(|Q_r(s)|\le2T_3(r)^2e^{-3s}\), absolute sum and continuum; \(124/75\) is an explicit auxiliary-error constant. | Existing bound unchanged. A signed estimate from H_theta would require \(Q'_r\) and endpoint costs. It supplies neither a sign nor a polynomial-in-K price for the infinite first moment. |
| S12 — §4, (4.3)–(4.5), L305–340 | COFINAL_FAMILY | CLASSICAL \(\Lambda\le\log\) plus exponential correlation decay; exact \(E_L\) tested against total variation; \(t_M=O((\log M)M^{-5/2})\). | **Already paid at the stated profile cost.** C4 is an optional signed reprice, with derivative cost; no drop-in numerical replacement of \(t_M\). |
| S13 — §4, (4.4), L313–346 | COFINAL_FAMILY | CLASSICAL inherited exact radicality and the preceding classical tail. No zero-location assumption; the mean is signed. | Equality is unchanged. More accurate \(E_M\) does not control the Jordan negative part. \(\beta_M\asymp1/\log M\) remains. Grid error is not added unless changing to the continuum model. |
| S14 — §5, (5.1)–(5.2), L352–383 | ABSTRACT | CLASSICAL theta series and Cauchy estimate in a fixed **physical analytic strip**. This is not a zeta zero-free strip. | Unchanged. H_theta does not replace the factorial derivative bound, change its strip width, or prove a sharper degree law. |
| S15 — §5, (5.3)–(5.8), L387–440 | ABSTRACT | CLASSICAL positivity of h, explicit H(0) lower bound, local nonvanishing on a fixed interval, and Legendre coefficient comparison. No global zero-location input. | Unchanged. H_theta gives no lower bound for \(|H|\) on expanding real intervals and no better Gram conditioning. |
| S16 — §5, (5.9)–(5.12), L444–480 | COFINAL_FAMILY | CLASSICAL assembly \(D_K[(124/75)/\log M+t_M]\le1/2\); fixed near constant \(C_{s_0}\). | Tail improvements alone do not remove the dominating first-moment/Gram price. The published sufficient \(K_{cert}\) does not automatically become \(\sqrt{\log M}\). Near constants are unchanged. |
| S17 — §5, (5.13), L482–496 | ABSTRACT / COFINAL_FAMILY | NONE—missing sharp signed estimate; exact matrices are defined. Current fallback is \(\beta_M\|G_K^{-1/2}\mathbb M_KG_K^{-1/2}\|+t_MD_K^{sharp}\). | H_theta does not supply matrix sign, conditioning, or the K-rate. A conditional scalar error bound cannot be substituted for this generalized matrix norm without profile costs. |
| S18 — §6, (6.1)–(6.4), L513–550 | COFINAL_FAMILY | CLASSICAL theta derivative bounds, Parseval, cutoff decay and **both window endpoints**. Source-independent Fourier tail; physical tail uses \(T_{12}\). | Unchanged. No zero-location or prime-distribution input is needed for these terms. |
| S19 — §6, (6.5), L552–565 | COFINAL_FAMILY | CLASSICAL inherited full mixed-source bound, including \((2+4L)\sqrt m\epsilon_0\), arch terms and traces. | Keep as written. H_theta does not automatically improve a positive pole term or an operator/shift norm to \(m^{5/12+\varepsilon}\); a joint signed return estimate would be a different supplier. |
| S20 — §6, (6.6), L558–565 | COFINAL_FAMILY | CLASSICAL absolute infinite prime-power tail: \(S_\Lambda=\sum\log n/n^{3/2}\le16\), plus pole and physical-tail factors. | Convergent positive series unchanged. The prime powers beyond m are not a removable error in the prime number theorem. No deletion or uniform power substitution is licensed. |
| S21 — §6, (6.7)–(6.8), L567–583 | COFINAL_FAMILY | CLASSICAL assembly of S18–S20 and \(D_K=O(\log M)\) on the certified horizon; explicit negative powers of m. | Already paid on that horizon. Wider K remains subject to its own coefficient/derivative costs; H_theta alone does not enlarge it. |
| S22 — §6, (6.9), L585–594 | COFINAL_FAMILY | CLASSICAL total-variation estimate for correlation error when replacing r by u. | Keep the existing uniform-in-height return budget. Using C2 instead requires energy/weighted Fourier differences, not merely the old L2 error. |
| S23 — §7, (7.1)–(7.6), L600–668 | ABSTRACT / COFINAL_FAMILY | CLASSICAL finite Gram concentration, local H lower bound and explicit treatment of real zeros/multiplicity. No RH; no global zero avoidance. | **Untouched:** neither p_K^*(I), detector width nor outside mass is improved. Real zeros and their multiplicities are not removed by H_theta. |
| S24 — §7, (7.7), L670–688 | ABSTRACT / COFINAL_FAMILY | CLASSICAL theta Fourier decay and incomplete-gamma estimate; not a zero-free estimate. | **Untouched:** the detector's high-frequency reach does not improve. Do not confuse this probability tail with the arithmetic source tail E_M. |
| S25 — §8, (8.1)–(8.2), L694–720 | FINITE_CELL / COFINAL_FAMILY | CLASSICAL fallback \(\mathcal N_M\le A_M(1-p)\), derivative envelope, exact signed-mean inequality. **NONE—missing** useful source-specific outside bound. | C2 permits \(\mathcal N_M\le R_\theta(M)(1-p)\), conditional. This is lock 2 **only at the power-loss level**. It still requires outside mass small enough to absorb that loss; no such concentration is supplied. |
| S26 — §8, (8.3)–(8.5), L724–775 | COFINAL_FAMILY | NONE—synthetic symbol, not arithmetic input. Uses the existing D_K/A_M ledgers. | Remains a control on the generic inference. A statement for the literal ψ is not a theorem for arbitrary synthetic symbols; conversely, H_theta is not a proof of the missing detector comparison. |

## 4. Complete HARDBREAK dependency inventory

| ID / original locator | Scope | Current input: classical / none | What changes under H_theta |
|---|---|---|---|
| H01 — source list, L77–86 | ABSTRACT | CLASSICAL inherited complete explicit formula; order-one Hadamard factorization; summability of inverse squared zeros; classical critical strip and functional equation. | H_theta is a new CONDITIONAL input. It can narrow the zero strip as in (B); it does not replace these other classical facts. |
| H02 — §1, (1.1)–(1.2), L119–144 | ABSTRACT | CLASSICAL exact full-source identity and absolute convergence on each fixed exponentially decaying profile; no prime-error asymptotic. | Identities, both pole sectors and prime powers are unchanged. Absolute convergence remains paid without H_theta. |
| H03 — §1, (1.3)–(1.4), L146–164 | COFINAL_FAMILY | CLASSICAL inherited S (4.4) and E_M; exact dangerous sign \(-\beta_MM_r\). **NONE—missing** uniform degree rate for \(\gamma_K^-\). | Conditional tail impact is S12/C4. Neither moment sign nor degree rate is supplied. The adverse sign remains the negative part of M_r. |
| H04 — §2, Lemma 1, (2.1), L168–188 | ABSTRACT | CLASSICAL radical identity and exponential domination to differentiate; NONE—no zero-location input. | Unchanged. H_theta does not turn \(sQ'_r\) into \(sQ_r\), or make dilations radical at every scale. |
| H05 — §2, Lemma 2, (2.2)–(2.3), L194–231 | ABSTRACT | CLASSICAL Fubini through \(\int s|Q_r|(j_+ds+d|\nu|)<\infty\); any fixed spatial exponential weight greater than 1/2 pays the prime tail. | Keep the absolute-convergence argument. The absolute measure still grows like \(e^{s/2}\); a narrower zero strip does not lower that absolute threshold. A signed alternative would be a different calculation. |
| H06 — §2, (2.4), L233–240 | ABSTRACT | CLASSICAL archimedean integral; no prime error or zero-location input. | Unchanged: \(|J_r|\le(18/25)\|r\|^2\). |
| H07 — §3, (3.1)–(3.2), L246–269 | ABSTRACT | CLASSICAL complete zero-side explicit formula. Squares, not absolute squares; nonreal zeros and multiplicities retained. | Formula unchanged. H_theta does not license replacing squares by positive absolute squares. |
| H08 — §3, (3.3), L271–278 | ABSTRACT | CLASSICAL \(|\Im z_\rho|\le1/2\), fixed-strip decay of R,R', and summability \(\sum(1+\gamma^2)^{-1}\). | Replace strip width by 5/12 only conditionally. It may change fixed-profile constants, not the summability exponent or yield a K-uniform bound. There is no window-size power to improve in this fixed-profile exchange. |
| H09 — §3, (3.4), L280–288 | ABSTRACT | CLASSICAL contour shift through removable zeros and absolute real-axis series; same strip bounds. | Same removability and multiplicities. Narrower shift is available, but no sign conclusion follows. |
| H10 — §3, (3.5), L290–297 | ABSTRACT | CLASSICAL order-one Hadamard product and H(0)≠0; second logarithmic derivative sums all zeros. | Exact identity unchanged. H_theta does not remove nonreal terms. |
| H11 — §3, (3.6)–(3.7), L301–329 | ABSTRACT | CLASSICAL exact elimination of the infinite prime moment via H07–H10; finite near moment retained; theta decay pays endpoints. | No prime-error remainder remains in this formula to replace by \(m^{5/12+\varepsilon}\). Only the same fixed near contribution and analytic norms remain. |
| H12 — §3, (3.8), L331–338 | ABSTRACT | NONE—no nonnegativity input supplied. The text says **under RH only** each zero term is nonnegative; an off-real pair has a negative region. | **Untouched sign obstruction.** Nonzero \(|b|\le5/12\) is still permitted, and the pair still has negative curvature near its real part. QRH is not the RH branch. |
| H13 — §4, L342–349 | ABSTRACT | NONE—missing polynomial normalized moment rate; S's D_K is only an upper majorant. | Unchanged. The power error does not prove the weighted polynomial inequality. |
| H14 — §5, (5.1)–(5.3), L355–406 | ABSTRACT | CLASSICAL square completion, arch bound, fixed finite near sum \(C_{s_0}^{(1)}\), physical Gram entries. No zero-location assumption. | Constants/identities remain. H_theta neither changes the fixed H² weight nor bounds μ_K uniformly in degree. |
| H15 — §5, (5.4) and tail, L408–427 | COFINAL_FAMILY | **NONE—missing μ_K≤CK² at this pin.** Conditional on that separate assertion, the source tail \(t_MD_K=\exp[-(5/2)\log M+O(\sqrt{\log M}\log\log M)]\) and carrier return are already classically small. | H_theta does not supply (5.4). Tail may be repriced only as in C4, but this is not the pending bottleneck. No later MUK result is imported into this pinned audit. |
| H16 — §6, Lemma 6, L433–459 | ABSTRACT | NONE—exact signed mean gives no bound on its Jordan parts; actual theta background, synthetic perturbation. | Logical fact unchanged. Conditional negative-mass control must come from a separate arithmetic envelope, not from the equality of means. |
| H17 — §6, Lemma 7, L461–518 | FINITE_CELL | NONE—synthetic smooth compact source perturbation; finite cross means and first moments vanish, near/tails unchanged, whole infinite radical not preserved. | The literal comb is excluded by definition, not by a newly proved sign. A power-law asymptotic alone, with an unspecified source-dependent constant, does **not** rule out every fixed compact perturbation: its cumulative contribution is bounded. Exact ζ/Euler-source structure must remain in C2. |
| H18 — §6, (6.7)–(6.8), L520–538 | ABSTRACT | NONE—Gaussian finite-difference control, not primes or a zero-location assertion. | Unchanged logical control. No conditional arithmetic promotion. |
| H19 — §7, (7.1), L540–568 | COFINAL_FAMILY | **NONE—missing** sufficient negative outside bound, useful concentration and all-height uniformity; exact identity plus known signed mean. | Lock 2 gets only C2's conditional loss envelope. Lock 3's all-height *envelope* gets the same loss, while its concentration requirement is untouched. Neither original lock is closed. |
| H20 — §8.2, L582–621 | FINITE_CELL | **NONE—unpaid numerical tails/roundoff** in the K=3 diagnostic: six theta terms, prime powers through 40, continuum through 3.5, physical halfwidth 3. | An unspecified asymptotic O_epsilon is not a finite interval certificate at 40. It does not pay quadrature, theta truncation, roundoff, or exact eigenvalue signs. |

## 5. Repeated uses and embedded-code inventory

This section prevents declarations and numerical truncations from being omitted from the audit merely because the main mathematical occurrence is already listed.

| Locator | Repeated dependency / outstanding input | Conditional effect |
|---|---|---|
| S header L14–24; §0 L44–58 | Existing growing-jet/error claims and missing uniform all-height bound | S11–S25; no promotion of the missing constant. |
| S §9 L781–810; §10 L822–837 | E_M, D_K, return, concentration and negative leakage collected into the route ledger and next supplier | Same dispositions as S12, S16–S25. The required independent constant remains missing. |
| S §11 L841–865; §12 L870–876 | Prime-atom recurrence prediction; “no new prime-distribution theorem or RH assumption” | Historical record unchanged. H_theta is prospective CONDITIONAL only. |
| S Appendix A L906–920 | Exact algebra for the tapered Chebyshev integral and the constant 124/75 | Classical arithmetic factors only; no prime-error or cofinal theorem certification. Not replayed in this audit. |
| S Appendix A L945–959 | Synthetic spike and leakage-factor algebra using A_M | No arithmetic upgrade; conditional loss affects a future envelope, not these exact identities. |
| H header L11–21; §0 L44–67 | First-moment/Laguerre crosswalk, no K-rate, null perturbation scope | H07–H17; the current pin still records no proof of (5.4). |
| H §8.1 L574–580; Appendix A L739–742 | Algebraic off-real-pair curvature check | Conditional strip narrowing does not change the negative sign for any nonzero admissible b. Not rerun. |
| H §9 L625–644; §10 L648–666; §11 L679 | Absolute zero-sum exchange, order-one requirement, absent degree/leakage suppliers, no disputed zero-free theorem used | Same dispositions as H08–H19. Historical absence of the new import remains explicit. |
| H Appendix A L753–772 | K=3; six theta terms; continuum cutoff 3.5; physical halfwidth 3; numerical quadrature and truncated correlations | NONE—finite numerical budgets remain unpaid. H_theta does not fix any of these settings. |
| H Appendix A L773–794 | Literal von Mangoldt evaluation and prime-power sum only through 40; finite continuum/J integration and fixed near subtraction | Coefficients through 40 are exact in intent; arithmetic and quadrature tails are not certified. Conditional asymptotics do not certify their numerical error. |
| H Appendix A L795–801 | Tiny-s interval replaced by zero below 1e−7; 15-term arch-tail series; finite physical integrations | Archimedean/physical numerical truncations, not prime-distribution errors; untouched. |
| H Appendix A L807–815; Appendix B L835–845 | Floating generalized eigenvalues and execution hashes | No exact sign, growing-K proof or zero-location input is supplied; unchanged. |

No other location in these two complete files supplies a prime-counting remainder theorem, a conditional zero-free theorem, or a missing source-tail certificate. Exact kernel/Gram algebra not repeated in the tables has no additional prime-error or zero-location assumption.

## 6. What is and is not “paid up to M^(theta−1/2+epsilon)”

**[COFINAL_FAMILY | CONDITIONAL; budget impact only]** Let \(R_\theta(M)\) be the C2 loss envelope. Since the actual density is normalized in the energy norm, the conditional leakage ledger becomes

\[
\mathcal N_M(r,I)
\le R_\theta(M)\,\sigma_r(I^c)
=R_\theta(M)(1-\sigma_r(I)).
\tag{C}
\]

This is the direct meaning of “lock 2 paid up to loss.” It is **not** an M-independent bound. For the generic peak conversion in H (7.1), one would still have to absorb the loss, for example through an adequately small outside mass, together with an appropriate lower bound for the in-window mass and the Lipschitz term. The audit supplies no such detector.

| Requested lock / sub-obligation | Current input at 2258f6b | Conditional credit | Final disposition |
|---|---|---|---|
| Lock 2: arithmetic envelope for actual negative outside contribution | NONE—sufficient bound missing; elementary fallback \(A_M(1-p)\) exists | **PAID_WITH_POWER_LOSS**, via (C) and explicitly charged C2, uniformly over admissible profiles | **NOT PAID** as the constant needed by H (7.1); \(M^{5/12+\varepsilon}\) still diverges. |
| Lock 3a: useful localization at the required width | CLASSICAL exact Gram problem; NONE—sufficient concentration theorem | **NO CREDIT** from H_theta | **UNTOUCHED.** The matrices, real-zero obstruction, detector reach and negative-tail mass still need control. |
| Lock 3b: arithmetic coverage of every height | CLASSICAL bound only beyond very large T0; NONE—uniform useful bound at all remaining heights | **PAID_WITH_POWER_LOSS** if C2 is included; direct Abel alone is not sufficient to claim this | All heights can be covered at a growing price, but **no common constant** and no improved localization follow. |
| Lock 3c: final all-height upper constant feeding SCALEBRIDGE | NONE | \(\overline B_M/w\ll M^{5/12+\varepsilon}\), not \(O(1)\) | **NOT PAID**, even on an unbounded subsequence: the bound's loss grows along every such sequence. This does not refute a better true bound. |
| Tail \(E_M\), \(t_MD_K\) at the degree schedules actually stated | CLASSICAL, already decaying; H's larger schedule separately assumes (5.4) | Optional C4 reprice, not a new missing-lock payment | **ALREADY PAID WITHIN ITS STATED SCOPE**; no retroactive expansion to all K. |
| Lock 1 / H (5.4), for completeness only | NONE at this pin | **NO CREDIT** from ψ error alone | Outside locks 2/3; not imported from the later MUK artifact. |

At the coarse exponent level the arithmetic improvement is from \(1/2\) to \(5/12\), a saving of \(1/12\). It is a saving, not the disappearance of a loss. The factor \(1/\log M\) from tapering cannot turn a positive power into a constant.

## 7. Four forbidden audit upgrades

**[ABSTRACT | PAPER — logical scope checks]**

1. **Signed error versus total variation.** Do not replace \(|\nu|\), positive prime mass, or a full shift-operator norm by the error in \(\psi-x\). S's grid and return estimates use different objects.
2. **Fixed height versus all heights.** A partial-summation factor \(1+|t|\) cannot be suppressed. All-height credit requires C2, with pole cancellation, standard ζ estimates and near terms preserved. The existence of those classical inputs is distinct from a repository certificate for the new import.
3. **Narrow zero strip versus real zeros only.** H_theta permits nonreal \(z_\rho\); H (3.8) remains a negative-pair control. No Laguerre positivity, RH, zero separation or weighted polynomial theorem is thereby supplied.
4. **Exact finite means versus Jordan control.** Lemma 7 still diagnoses an invalid generic inference. A fixed compact perturbation can preserve an asymptotic power class after changing its constant. The exact arithmetic identity, not the bare exponent alone, distinguishes the literal source in the conditional all-height transfer.

## 8. Closeout

**[ABSTRACT | PAPER — audit findings]**

- The existing files use elementary Chebyshev/\(\Lambda\le\log\) bounds for positive prime mass and absolute tails, plus classical theta/Weil/Hadamard inputs. Neither contains the stipulated quasi-RH import.
- The new input can be assigned a precise conditional signed-error price. It does not alter exact identities, total-variation leading scales, the Gram/concentration problems, or finite numerical certification.
- Locks 2 and the arithmetic-height component of lock 3 receive conditional **power-loss envelopes only**. Detector concentration and the M-independent consumer constant remain unpaid.
- No new proof, proof replay, independent theorem validation, repository write, branch update or route promotion was performed. Hashing and source reading were the only computations on the supplied artifacts.

There is no new mathematical directive in this read-only deliverable. The unresolved items remain the ones named in H §7, with the conditional prices and dependencies made explicit above.

## 9. Source locators

Pinned sources (the complete two files, including appendices):

```text
https://github.com/Malaeu/chen_q3/blob/2258f6b02aad1e3c8cd073a7e1ecb80dbfbef2e1/docs/routeB_bus/proshka/PROSHKA_VERDICT_SCALEJET_2026-10-31.md
https://github.com/Malaeu/chen_q3/blob/2258f6b02aad1e3c8cd073a7e1ecb80dbfbef2e1/docs/routeB_bus/proshka/PROSHKA_VERDICT_HARDBREAK_2026-10-31.md
```

External classical comparison only; not a quasi-RH verification:

```text
K. S. Kedlaya, Notes on analytic number theory:
https://kskedlaya.org/ant/chap-von-mangoldt.html
  (9.1.1); Lemma 9.4; Lemma 9.6; contour framework in §§9.1–9.5.
https://kskedlaya.org/ant/part-2-4.html
  §7.3, fixed zero-free strip and power prime-counting error.
```

External statements about current progress printed elsewhere in those course notes were not used. The requested unpublished-import status is owner-stipulated, not independently established by those references.
