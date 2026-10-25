# Actual theta weights: prime-2 telescoping with complete return

2026-10-25. Own bounded attempt while Q18 is pending; no Proshka interaction.
Source: CCM_Q18_THETA_FILTER_TRANSFER.md; Q17 finite resolvent source therein.
Target unchanged: original full pair, same sparse three-contact P, all prime
powers and both temporal signs. No new favorable arithmetic exponent.

## Selection and bounded novelty check

Abel/PNT was already tried (Q02, C5 audit, Q10); van der Corput correlations
already in Q01. Q11 also contains a different telescoping of an isometry on a finite
divisor support (its section8.1), used to bound 1-Re kappa_2. Search of CCM* and PROSHKA_CCM* in the active literature folder found no
prior prime-2 odd-theta removal plus full autocorrelation return. This is a
bounded shelf finding, not a claim of novelty in mathematics or all archives.
Selected technique: finite telescoping along actual theta dilations.

## Exact removal of even theta indices with their weights

Write h=log2,c=2^(-1/2),T_h f(t)=f(t+h), B=D²-1/4, F=B G=F0.
The actual source scaling is c T_h phi_j=phi_(2j). Therefore
 Psi=(I-c T_h)G=-4 sum_(j odd) phi_j,
 Z=B Psi=(I-c T_h)F.
The theta series statement and its derivatives hold locally normally; the
functional definitions by translations are valid globally in L2. No global
exchange of an absolute theta series with an improper integral is used.
B commutes with translation, not with the original P (no such claim made).
This cancellation acts on the REAL weights, not only on d_m coefficients.

For every finite integer J>=1, exact telescoping gives
 F=F_J+E_J,
 F_J=sum_(j=0..J-1)c^j T_(jh)Z,
 E_J=c^J T_(Jh)F.                                      (1)
Indeed the adjacent translated F terms cancel in the finite sum. In theta
index language, F_J retains valuations v_2(k)<J and E_J retains v_2(k)>=J;
every k occurs once. No theta-index edge has been discarded.
Unitary translation in L2 gives ||E_J||=c^J||F|| and
 ||F_J||<= (1+c^J)||F||.                               (2)
The independent-layer completion also gives
 ||F_J||<= (1-c^J)/(1-c)||Z||,
 ||Z||<= (1+c)||F||.                                  (3)

## Preserve the full signed bilinear quantity

For fixed hypothetical w=delta+i gamma,0<delta<1/2,multiplicity r and the
separate partner normalization, retain b=conjugate(w) and
kappa=(-1)^r/(conjugate(c_w)c_v), not its modulus as an identity.
Define
 R(f,g;s)=integral conjugate(f(t))g(t+s)dt,
 H_m(f,g;y)=sum_(2<=n<=m)Lambda(n)/sqrt(n)
                    [R(f,g;y-log n)+R(f,g;y+log n)],
 J_m(f,g;y)=kappa integral_0^infinity
              exp(-bu)u^(2r-1)/(2r-1)! H_m(f,g;y+u)du.
Then the original cross term is J_m(F,F;2a). Both temporal sides and ALL
prime powers are retained for each bilinear term. For finite m these integrals
are absolutely bounded using L2 and exp(-delta u).

Substitute (1) BEFORE taking moduli:
 J_m(F,F)=J_m(F_J,F_J)+J_m(F_J,E_J)
                      +J_m(E_J,F_J)+J_m(E_J,E_J).      (4)
In particular the main term is the FULL double sum
 sum_(j,k<J)c^(j+k) J_m(T_(jh)Z,T_(kh)Z).
Its off-diagonal j!=k terms have not been deleted. The target is the real
part with the original exp(2i gamma a) factor; individual mixed terms cannot
be assigned favorable signs. This uses the Q17 formula before moving B²
onto the resolvent kernel, so no Q18 E1/E2 endpoint is being dropped:
if one performs that additional integration by parts, those endpoints return.

## Complete finite-m price

Let W(m)=sum_(n<=m)Lambda(n)/sqrt(n)<=6sqrt(m) and
 K_m^*=2|kappa| W(m) delta^(-2r).
This scalar budget symbol is NOT the CCM matrix K_m.
Cauchy-Schwarz on correlations and the gamma integral give
 |J_m(f,g;y)|<=K_m^* ||f||||g||.                        (5)
Set e=c^J. From (4),(2), the sum of absolute return costs is at most
 K_m^*||F||²[2e+3e²].                                 (6)
A sharper bound on the JOINT error follows by substituting F_J=F-E:
 J_m(F,F)-J_m(F_J,F_J)
   =J_m(F,E)+J_m(E,F)-J_m(E,E),
so its absolute value is <=K_m^*||F||²(2e+e²).          (7)
All signs in (4) and (7) are identities; (7) does not assert positivity.
For any fixed sigma>0 choose
 J=ceil((1+2sigma)log_2 m).
Then e<=m^(-1/2-sigma), and (7) costs O_w(m^-sigma).
Thus the full tail, INCLUDING mixed terms, can be made power-small.

But the retained main quantity has no new signed estimate. Using (2),(5)
its complete available price is
 |J_m(F_J,F_J)|<=12|kappa|delta^(-2r)||F||²
                             (1+e)² sqrt(m).          (8)
So (7)+(8) still cost O_w(sqrt(m)). Using independent layers (3) instead
would have asymptotic constant factor
 ((1+c)/(1-c))²=17+12sqrt2
in place of 1 in the same old half-power bound. This larger sufficient
constant is NOT a lower bound for the actual main term or a no-go theorem.

## Original P, all remaining fees and consumer

The decomposition is an exact identity inside the finite-prime J. It does
not introduce separately projected source vectors or commute P with T_h.
Return the ORIGINAL full pair as a whole by the inherited receiver with
fixed q>1/epsilon+2: rho_K,rho_S=o(1), all projection cross terms included.
The self terms S_m[g]+S_m[k] remain their inherited O_w(1); the cross term
is -2Re(exp(2i gamma a)J). Thus (8) contributes at most twice its coefficient
to the direct one-sided S bound. The full-tail error (7) likewise doubles.
The archimedean price D_w(50log m+8) occurs once. Hence
 average K(original returned pair)
 >= -24|kappa|delta^(-2r)||F||²(1+e)²sqrt(m)
    -O_w(m^-sigma)-D_w(50log m+8)-O_w(1)-o(1).
If a finite u-horizon is used, use the ORIGINAL unsplit integrand and its
source bound O_w(sqrt(m)(1+log m)^C exp(-c_w(log m)^2))=o(1); no uniform
per-shift tail claim is needed as J grows. All exact equalities above may
instead be used with the convergent integral to infinity at fixed finite m.

The inherited averaged sqrt(m)/log²m completion remains stronger by logs.
Against the conditional m^delta/(log m)^(2delta+1) signal it still leaves the
power deficit 1/2-delta. No eta(epsilon)->0 obtained, no extra ZF78 premise.
The tail is cheap; the unresolved signed main double sum holds the burden.
This is an explicit rollback point: before independently bounding the full
retained j,k sum. Making J larger alone cannot improve the proved main bound.

## Verification and limits

experiments/ccm_theta_telescoping_2026_10_25/check.py: exact weighted-index
reconstruction and formal finite telescoping; no full CCM numerical run,
no hypothetical zero assigned, no Lean or Arb. Analytic bounds are the
paper derivation above, not inferred from finite tests.
Independent bounded read-only PAPER audit q18_dyadic_telescoping: PASS on scaling/telescoping, both error constants, full doubled pair budget and limited shelf novelty. The audit accepts inherited source/receiver inputs; it does not recertify all earlier mathematics. Important scope: this telescope acts on the base theta F; actual finite-prime weights stay inside J_m and are fully retained, but their divisor structure is not exploited to improve the main bound. This is a specialization of the existing scaling idea, not a new arithmetic cancellation theorem.
