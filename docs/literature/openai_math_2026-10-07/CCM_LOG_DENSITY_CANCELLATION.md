# Full-window logarithmic density cancellation under the original constraints

2026-10-08. Root derivation; independent read-only sparse_band_receiver audit PASS for L1-L5, signs, endpoints and the positivity consequence below. Same original K_m, N=m and L=log m. This is a full-window continuous identity, not a prime estimate or a claimed full Ramanujan quadrature return.

Let F be the original Fourier isometry into L2([0,L]), and Q(s)=F*(T_s+T_s*)F. Let P be either the full-band constraint projection or its sparse-band counterpart, padded into the original carrier. Both satisfy P v_+=P v_-=0 for v_±=F*exp(±t/2). The extra b constraint is retained but not needed for this identity.

For real a>0 write G_a=F*[kernel exp(a|t-u|)]F and H_a=F*[kernel exp(-a|t-u|)]F. The accepted identity is

    G_a = v_+(a)v_-(a)*+v_-(a)v_+(a)*-H_a,
    G_a = integral_0^L exp(as) Q(s) ds.

Here v_±(a)=F*exp(±at). Differentiate in a on the finite interval, with F and P held FIXED. Each derivative of the rank-two term has at least one undifferentiated v_+(a) or v_-(a). At a=1/2 it is killed by two-sided P compression. Consequently, with J=F*[kernel |t-u| exp(-|t-u|/2)]F,

    P G'_(1/2) P = P J P,       ||J||<=8.                 (L1)

The sign is positive here because dH_a/da is the negative of the |t-u| decaying kernel. The norm bound follows from the Schur row integral over the whole line, 2 integral_0^infinity s exp(-s/2)ds=8. Positivity of J as an operator is NOT asserted. No parameter-dependent projection is differentiated.

Set A(t)=P Q(log t)P/sqrt(t), 1<=t<=m. Changing variables s=log t gives exactly

    integral_1^m log(t) A(t)dt = P J P.                    (L2)

Also the accepted rank-two identity gives

    integral_1^m (1-1/t) A(t)dt = -2 P H_(1/2) P,
    ||H_(1/2)||<=4.                                       (L3)

For every fixed cutoff R>=1, its positive C_R is a scalar independent of t. Therefore the full smooth density term from the Ramanujan model has

    integral_1^m [log(t)/C_R-1+1/t] A(t)dt
       =P[J/C_R+2H_(1/2)]P,
    norm <=8/C_R+8.                                       (L4)

This remains true if R depends on m, since no derivative in m or R is used. It holds on the same sparse band as the conditional witness. Large smooth upper blocks need not be small individually; the full-window identity retains their mutual cancellation.

The full combination in L4 is also positive semidefinite for C_R>=1. With Fourier variable xi, the whole-line multiplier of J/C+2H is

    2[(1+1/C)/4+(1-1/C)xi^2]/(1/4+xi^2)^2 >=0.

Zero-extension and compression preserve this positivity. This does not imply J alone is positive, nor any sign for the arithmetic discrepancy.

## Exact unpaid arithmetic return

Define b_R(n)=log(n)lambda_R(n)^2/C_R^2 as in CCM_DENSITY_PAIRING_TEST.md, and set b_R(1)=Lambda(1)=0. Define the FULL (not yet bounded) quadrature discrepancy

    E_R = sum_(1<=n<=m) b_R(n) A(n)
             -integral_1^m [log(t)/C_R] A(t)dt,
    D_R = sum_(1<=n<=m) [Lambda(n)-b_R(n)] A(n).

Then the full projected prime matrix satisfies

    P Aprime P = P J P/C_R + E_R + D_R.                   (L5)

Hence a subpolynomial upper bound for E_R+D_R would meet the prime receiver, since J/C_R has bounded norm (C_R>=1). The sparse smooth upper-block quadrature result does not yet bound E_R: all lower blocks and endpoints must be included, and small primes <=R can contribute to D_R. No term is omitted or given a favorable sign without proof.

L4 supplies a bounded FULL smooth term, strengthening the earlier scalar observation that log(t)/C_R tends to 1/beta on upper blocks. It does not prove the combined arithmetic estimate in L5. The ongoing full-SP phase is unchanged; Q8 has not been sent.
