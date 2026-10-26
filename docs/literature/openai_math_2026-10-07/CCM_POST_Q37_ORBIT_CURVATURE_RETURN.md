# Post-Q37: full orbit-curvature repair and its price

2026-10-26. One bounded own repair of Q37, original source and original P.
No new exponent; read-only q32_annulus_audit bounded algebra/budget PASS. Literal shelf search found other
commutators but no identical orbit-curvature return; no global novelty claim.

Use Q37's full physical B=sum Lambda(n)/sqrt(n)V_log(n), A=B+B*,
U(t)=exp(tB), unit f=F_Mc with c=Pc. Set v_t=U(t)f/||U(t)f||.
The finite nilpotent exponential is invertible, so v_t is defined for all t.
The intermediate v_t is NOT asserted to belong to ran F_MP.
Let F(t)=log||U(t)f||^2. Differentiating the full norm twice gives exactly
 F''(t)=<v_t,A^2 v_t>-<v_t,A v_t>^2
        +<v_t,(B*B-BB*)v_t>.
The first two terms are Var_v(A)>=0. This follows from
 N''=<Uf,((B*)^2+2B*B+B^2)Uf> and
 A^2=(B*)^2+B*B+BB*+B^2. No mode or temporal mixed term is removed.
Taylor with integral remainder, F(0)=0, gives
 <f,Af>=F(1)-integral_0^1(1-t)[Var_vt(A)+<vt,(B*B-BB*)vt>]dt.
Thus the exact failed chord has a concrete signed curvature return.

First loss: discard only the nonnegative variance, then use
 BB*-B*B <= BB* <= ||B||^2 I <= W(m)^2 I.
With Q37's |F(1)|<=G_m=2log(1+m^(3/2)), this pays the complete cap
 A <= [G_m+W(m)^2/2]P <= [G_m+18m]P.
The explicit price is power1, worse than the retained half-power fallback.
This is an upper-budget computation, not a lower bound on repair or source.
No argument proves a constant/polylog curvature return impossible.

In the commutator, keep every pair u,v with actual weights
 a_u a_v [V_log(u)^* V_log(v)-V_log(u)V_log(v)^*].
The cutoff uv>=m from B^2 does NOT apply to these reverse shifts. For u=v,
 V_s*V_s=1_[0,L-s], V_sV_s*=1_[s,L]; their difference is a nonzero
boundary operator for 0<s<L. Prime powers and mixed u!=v terms remain.
A bound only on the original-P compressed commutator would not control the
above integral unless departure of v_t from that subspace were separately
returned. No projection is inserted inside U or its products here.

Full centered C0=A+Hd keeps the same inherited Hd; direct K return needs no
extra 4. Preserve S10 instead of the weaker new cap:
 A<=s_keep P, s_keep<=6sqrt(m)+6m^(1/4),
 T_>R<=(s_keep+b_div)P,
 P K_m P>=-(s_keep+50log(m)+8)P.
No new zero-selective margin or eta(epsilon)->0.

11 exact rational two-dimensional curvature controls checked algebra/signs;
they are toy controls, not actual-source numerical measurements. The proof
above applies to the actual bounded physical operator without a matrix model.
A useful repair would need an independent upper on the integrated negative
curvature, keeping its variance credit and actual orbit, not just the generic
commutator norm. That arithmetic property is OPEN. This is one completed
repair test, not three attempts; no Q38 sent. Goal/RH OPEN.
