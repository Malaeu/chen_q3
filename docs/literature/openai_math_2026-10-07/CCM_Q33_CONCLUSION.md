# Q33 — full Ramanujan majorant return

Status: bounded independent PAPER PASS, conditional on inherited source inputs. Full CCM/RH OPEN.

Original: PROSHKA_CCM_SOURCE_DEPENDENT_SIGNED_COMPARISON_Q33_VERDICT_2026-10-26.md,
1036 LF / 64375 bytes, SHA256
716c8d9f3d02e88e3760e02bc3c6906fac05f23f59e19fc934f720f42a653e7f.
The complete original and all five embedded assets have been read. The canonical
request and eight size-locked source bodies reproduce exactly.

## Exact target and checked calculation

Keep original N=m, L=log m, M=R=floor(m^epsilon), fixed 0<epsilon<1/32,
original three-contact P, h(n)=n^(-1/2)P Q_M(log n)P. Let A=sum Lambda(n)h(n)
and C0=A+H_decay. All sums include every integer through m and all prime powers.
For the finite Ramanujan model b_Z=log(n)lambda_Z(n)^2/C_Z^2, define
ell_Z(p^k)=log p for every p<=Z and every supported k, zero otherwise.
D_Z=b_Z+ell_Z-Lambda>=0 is a coefficient comparison, not Loewner comparison.
On zero-extended physical functions, use the full unitary translations:
J_n=h(n)+2n^(-1/2)P>=0. With E_Z=sum D_Z(n)J_n,

    C0=B_Z+H_decay+A_smallbase+2 D_mass P-E_Z.

All complex cross terms remain inside E_Z. At n=m the original overlap h(m)
is zero but J_m=2m^(-1/2)P: diagonal and energy cancel exactly. Dropping just
the top energy is invalid. Replacing E_Z by zero yields the stated allowance

    s_Z=F_Z+2 mathfrak_b_Z-2 W+4 W_smallbase,

where W=sum Lambda(n)/sqrt(n), mathfrak_b_Z=sum b_Z(n)/sqrt(n).
Q33 derives mathfrak_b_Z=I(m)/C_Z+O(G_Z),
I=2sqrt(m)log(m)-4sqrt(m)+4, C_Z=log Z+O(1).
For Z=floor(m^(epsilon/4)), the model and small-base fees are o(sqrt(m));
ordinary PNT gives s_Z=(16/epsilon-4+o(1))sqrt(m). Without PNT the displayed
liminf is already at least16/epsilon-12. These are prices of this completion,
NOT lower bounds on actual A, C0 or the CCM spectrum.

Keep the old12sqrt(m) fallback. The full return from A<=sP is
T_>R<=(s+b_div)P and PK_mP>=-(s+50log(m)+8)P; the divisor-short fee is
not charged again in the direct K bound. No eta(epsilon)->0 is supplied.

## Mandatory shelf correction: no new model-return gain

CCM_MOMENT_Q08_CONCLUSION.md already paid the full Ramanujan model on original P,
including all lower blocks, endpoints and prime-power corrections.
CCM_WEIGHTED_LCM_RETURN_CONCLUSION.md improved its quadrature on20.10 to
O(m^(alpha+beta)log^2 m), retaining all mixed divisor terms.
At alpha=epsilon, beta=epsilon/4 this is O(m^(5epsilon/4)log^2 m),
stronger than the new displayed model bound O(m^(3epsilon/2)).
Substitution of that inherited fee into the square-dropping completion leaves
the same leading (16/epsilon-4)sqrt(m): the large scalar diagonal persists.
This comparison is bookkeeping on existing bounds, not a fresh arithmetic attempt.

The remainder U_Z=sum(Lambda-b_Z)h is the old full D_R from
CCM_FULL_RAMANUJAN_RETURN.md (R renamed Z), and the C5 decomposition in
CCM_COMPOSITE_SIGN_TARGET.md already preserves proper powers on both sides.
Do not count Q33's return to U_Z as a newly discovered target. Its square
comparison may delimit a certificate, but the central source-dependent sign
remains the existing research debt.

## Reproduction and scope

q33_replay contains all five extracted assets, each byte count/hash verified.
Existing Python3.13.17/SymPy1.14.0 ran211 exact local controls and rejected8
planted errors. Both output JSONs were byte-identical to the embedded results;
source verification checked the exact request and8complete bodies.
No installs, Lean, Arb or production spectral runs. Finite controls do not
prove the infinite-family estimate. q32_annulus_audit returned bounded PASS for §§2–6: coefficient cases, full
shift-square signs and endpoints, Euler return, scalar mass and complete price.
Inherited kernel/contact/receiver inputs were not re-proved; no external proof
was re-audited. The reviewer also confirmed the Q08/weighted-LCM comparison.
The original has a harmless broken D_mass typesetting; its bytes remain unchanged.
No Q34 sent. The original-P signed bound and RH remain OPEN.

AUTOPSY: dropped=SIGN; note=dropping E_Z retains the large returned diagonal; small full model was already paid and does not supply the missing signed source bound.
