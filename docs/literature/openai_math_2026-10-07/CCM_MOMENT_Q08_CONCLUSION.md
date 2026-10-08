# CCM moment Q8 — complete divisor return improved; sign remains open

2026-10-08. Terminal response observed after owner notification, around21:01–21:05UTC, in the same Derive CCM Drift chat. Root read all1029 original lines; original checksum matches the displayed checksum. Independent read-only sparse_band_receiver audit PASS for (7)–(14) and complete price (13), conditional on explicitly accepted inputs (5)–(6); no correction found. RH/full-SP/C5 remain OPEN; no Q9 sent.

## Evidence

Request PROSHKA_CCM_MOMENT_Q08.txt:730772bytes,12470newlines,final newline,SHA2569f0ec34236557c129799f731badf4b34a3d52f71d5e21c6261620f22f3922d72; source403cabdf; sent20:11UTC. Original PROSHKA_VERDICT_FULL_CCM_RAMANUJAN_Q08.md:88280bytes,1029newlines,SHA256e77e96f8cecc9c3d5babacb424fe87d8a8f9ff56800583f7c1bab93b263a3c87. Original bytes copied unchanged from downloaded attachment. Chat: https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac65a73-ba24-83eb-aa2a-97c07f5e0214 . Last scheduled check20:51 saw ongoing reasoning; completion was established on the owner's next prompt before the planned21:11 check. No resend or Answer now.

## Accepted bounded PAPER result

Keep original m=N, L=log m, frequencies2pi*j/L and original three-constraint projection P within |j|<=M. For integer m>=4,1<=M<=m,2<=R<m, use the original finite Ramanujan lambda_R, C_R and b_R=log(n)*lambda_R(n)^2/C_R^2.

The exact finite divisor expansion is lambda_R(n)/C_R=sum_{d|n,d<=R}u_R(d), where u_R(d)=mu(d)d/(phi(d)C_R)*sum_{k<=R/d,(k,d)=1}mu(k)^2/phi(k). Squaring and grouping by lcm gives g_R(l), sum g_R(l)/l=1/C_R and sum|g_R(l)|<=64R^2/C_R^2. This coefficient bound is for all R, not inferred from finite samples.

For f(t)=log(t)P Q_M(log t)P/sqrt(t), both f(1)=f(m)=0. The exact discrepancy B_l(t)=floor(t/l)-(t-1)/l has |B_l|<=1, also when l>m. Full Abel summation therefore gives

    ||E_R|| <= 64 R^2/C_R^2 * (8+4 D_M), D_M=(2+8pi M)/L.

No low block, large divisor or endpoint is deleted. Pointwise |lambda_R(n)/C_R|<=3^omega(n), hence b_R(n)<=log(n)tau_9(n). Summing the nine-factor divisor function gives the improved entire small-integer fee

    ||S_small|| <= 4 sqrt(R)log(R)[1+(1+log R)^8].

Combine with the previously accepted ||J||<=8 and proper-power fee Kpow L(1+L), Kpow=2/(1-1/sqrt2). The unchanged exact identity is

    A + C_comp = PJP/C_R + E_R + S_small + T_power,
    A=P A_prime P.

Thus -F P <= A+C_comp <= F P, where F is exactly Q08(13). Proper powers occur in both T_power and C_comp with their required coefficients. For fixed0<alpha,beta<1, M=floor(m^alpha),R=floor(m^beta), F=O_{alpha,beta}(m^(alpha+2beta)). This improves the previous alpha+4beta price for the JOINT return, not a separate spectral floor. No growing-p limit or substituted spectral weight is used. The corresponding trace estimate holds for any W=PWP>=0.

## Scope and next mathematical action

The principal unpaid statement is still a lower bound for actual C_comp with exponent proportional to small fixed parameters. Knowing A+C_comp is small does not bound either summand separately. With C5 supplied, the already accepted fixed sparse-band witness would give a conditional contradiction after choosing parameters once for a hypothetical off-critical zero. C5 was not supplied; full-SP additionally retains the complement and all cross terms.

Q08 also proposes a finite constrained negative control, a whole-line symbol falsifier, a quantified half-density weight mismatch, and a paid finite-P frequency tail. These are retained in the original as author-derived PAPER claims, outside the single independent Q08-D acceptance. No new route-kill or tail-supplier status is promoted from these auxiliary claims in this closeout.

Next own attempt remains on the same actual compressed signed source: test joint domination of its negative frequency matrix by its positive frequency matrix plus a parameter-proportional allowance. Q08(43) is a candidate sufficient inequality, not a proved estimate or automatic improvement from taking square roots/inverses. Do not send Q9 before an own attempt. Do not replace the full-SP consumer silently by the distinct conditional sparse receiver.

Linux zeta Comparator remains its reported zeta-only scope; no Mac rerun, Lean run, Hecke/Dirichlet/Siegel import or RH claim. Scoped request+original answer+conclusion delivery closes Q8 only. Pause its heartbeat after push; native full RH goal remains active.

AUTOPSY: dropped=THEOREM_SHAPE; note=small norm of the joint prime-plus-composite return does not bound either separate spectral extremum; C5 is still the missing arithmetic estimate.
