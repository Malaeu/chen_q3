# Source resolvent Gram through a second-derivative Mellin integral

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; EXACT_IDENTITY_AND_COMPONENT_FAILURE_ONLY.
SOURCE_BASE: 1bfb3e72aadbf86840750b13e3b7dd8369cc921e.
SCOPE: exact identity and obstruction to termwise positivity of one natural
transport; no sign theorem for K_2, V, or RH.

The K_2 below is the Weil atom kernel from FULL_SIGN_TRANSFER_AUDIT,
not the unrelated two-increment renewal kernel also called K_2 elsewhere.

## 1. Positive source data and an exact Mellin operation

Keep the full source T=sum_{n>=1} Gamma(2,1)/(pi*n^2), lambda_n=pi*n^2.
For real s>0 let

    L(s)=E exp(-sT)=[sqrt(pi*s)/sinh(sqrt(pi*s))]^2,
    A(s)=2 sum_n 1/(lambda_n+s),
    G(s,s)=2 sum_n 1/(lambda_n+s)^2.

Differentiating the convergent product gives

    L''(s)=L(s)[A(s)^2+G(s,s)].                         (P1)

All terms here are nonnegative. In particular P1 is a source-built squared
norm of W(s)=sqrt(L(s))*(A(s), (sqrt(2)/(lambda_n+s))_{n>=1})
in R direct-sum ell^2. This is an exact use of the request's source Gram;
it is not a guessed feature map for the final kernel.

Put H(a)=E T^a=integral_0^infinity t^a r(t)dt=2xi(2a), and

    J(a)=integral_0^infinity s^(1-a)L''(s)ds,
    Re a<2.

Then

    J(a)=Gamma(2-a)H(a).                               (P2)

For complex a with Re a<2, absolute Fubini is licensed by

    integral_0^infinity s^(1-Re a)E[T^2 exp(-sT)]ds
        =Gamma(2-Re a)E T^(Re a)<infinity.

Every real moment of T is finite by the full source's exp(-pi*t) large
end and reciprocal exp(-pi/t) small end, with polynomial factors. These
same envelopes justify derivatives of H. Alternatively at s=0, L'' is
bounded and s^(1-Re a) is integrable for Re a<2; at infinity the explicit
hyperbolic formula and its first two derivatives decay like a polynomial
in sqrt(s) times exp(-2sqrt(pi*s)). These bounds with powers of |log s|
also prove local uniform holomorphy and differentiation of J in Re a<2.

P2 is the entire full-source Mellin moment, not a finite approximation.
The exact reciprocal law r(1/t)=t^(5/2)r(t) also gives

    H(a)=H(1/2-a).                                     (P3)

This follows by t=1/y, including dt=y^-2 dy. P3 is a reflection identity,
not a positivity rule for a logarithmic derivative.

## 2. Exact quotient at the consumer line

For real u put a_u=5/4-iu/2. Euler nonvanishing at Re(2a_u)=5/2 and
Gamma nonvanishing imply H(a_u) and J(a_u) are nonzero. From P2,

    R_2(u)=xi'(5/2-iu)/xi(5/2-iu)
          =H'(a_u)/(2H(a_u))
          =1/2 [psi(2-a_u)+J'(a_u)/J(a_u)],             (P4)

where

    J'(a)=-integral_0^infinity (log s)s^(1-a)L''(s)ds.

Consequently the EXACT full atom kernel is

    K_2(u,v)=K_Gamma(u,v)+K_log(u,v),                   (P5)

    K_Gamma(u,v)=[conj(psi(2-a_u))+psi(2-a_v)]
                    /[2(4+i(u-v))],
    K_log(u,v)=[conj(J'(a_u)/J(a_u))+J'(a_v)/J(a_v)]
                    /[2(4+i(u-v))].

No term has been omitted in P5. This includes the gamma normalization
created by the Mellin integral. The original two pole terms, primes,
and archimedean terms remain inside the exact xi logarithmic derivative;
P5 does not claim a separate prime-term estimate.

The positive integral in P1 proves that J on any admissible vertical line
is, after normalization, a characteristic function of log s. It does not
by itself prove positivity of P5. Specifically J'/J is a ratio of complex
integrals. It is not the scalar expectation of log s under a positive
probability measure when Im a is nonzero. Even on the real line its sign
is a first moment of a variable log s with both signs, not a norm square.

## 3. A precise failure of termwise positivity in this operation

At u=v=0,

    K_Gamma(0,0)=psi(3/4)/4<0.                         (P6)

One can prove the strict sign without a numerical value or a special
quarter-argument formula: for positive real x,
psi'(x)=sum_{k>=0}(k+x)^(-2)>0 and psi(1)=-gamma<=0.
Thus psi(3/4)<psi(1)<=0.

Therefore K_Gamma alone is NOT a PSD kernel, already on a single node.
The attempted proof 'each component after the positive Mellin integral
is independently nonnegative' is false for this exact decomposition.
This does not disprove K_2: K_log may compensate for K_Gamma. Indeed the
positive even theta profile implies xi'(sigma)>0 for sigma>1/2 via the
derivative of its cosh integral. At sigma=5/2 the TOTAL K_2(0,0)>0.
This verifies that the one-node negative correction is not a V witness.

## 4. What this preflight supplies and does not supply

P1-P5 give one fully specified route from the source Gram to the actual
consumer, with its normalization correction retained. P6 excludes a
termwise-positive proof for this decomposition, not every resolvent Gram
transport and not the joint use of total positivity and reciprocity.

The remaining all-finite-complex-row inequality is literally

    sum_ij conj(c_i)[K_Gamma(u_i,u_j)+K_log(u_i,u_j)]c_j>=0.

This is still the original full sign through an exact identity. We do not
introduce it as a new proved supplier, or claim that writing P5 reduces its
difficulty. The point is to detect and retain a specific mandatory correction
before treating a positive input Gram as a proof of the output sign.

Source references: the attached RESOLVENTGRAM request at 5fb0c069 and its
full FULL_SIGN_TRANSFER_AUDIT / THETA_TN_INFINITY_INTAKE / EXACT_RECIPROCAL_PAIRING
frames. The classical Gamma facts in P2/P6 are the standard defining gamma
integral, logarithmic differentiation, and its positive-real trigamma series.
Independent checking is required before publication.

## Sources and independent acceptance

The classical inputs were checked against [DLMF 5.9.1](https://dlmf.nist.gov/5.9.E1), [DLMF 5.15.1](https://dlmf.nist.gov/5.15.E1), and [DLMF 5.4.12](https://dlmf.nist.gov/5.4.E12).

Candidate SHA256: `038cb8cf51ed7e8badfad0ab38848651642262361903476a288a8032dcadbf19`. Review SHA256: `b359e6946b2220e5677d13eba42d67059eafe742644fe141714458c0e998801b`.
Reviewer: `/root/sibling5_check`; verdict: ACCEPT_EXACT_MELLIN_IDENTITY_AND_TERM_COMPONENT_FAILURE_ONLY.
The parent read the complete review and checked P1-P6, Mellin endpoints,
the quotient derivative sign, and the exact atom normalization. Only status,
source links, and this receipt were added after review. No Lean or canonical
admission, no new lower bound for V, and no full-sign conclusion.
