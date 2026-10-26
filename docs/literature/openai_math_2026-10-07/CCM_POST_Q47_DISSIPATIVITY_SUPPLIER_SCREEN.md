# Post-Q47 dissipativity supplier screen

Status: NO_INDEPENDENT_SUPPLIER; original arithmetic target OPEN.
This is a supplier preflight, not a new arithmetic gain or a route no-go.

Three bounded local ask queries returned INCOMPLETE due semantic-index freshness;
adjacent hits do not establish absence. One primary candidate was checked:
G. Lumer and R. S. Phillips, Dissipative Operators in a Banach Space (1961),
DOI https://doi.org/10.2140/pjm.1961.11.679 . Official whole-issue PDF:
https://msp.org/pjm/1961/11-2/pjm-v11-n2-s.pdf
Local inspected copy /tmp/q47_lumer_phillips_1961.pdf, SHA256
c3fabd0588ac9460cc166e591fa7d5811389c831dcee181e18d26d621c7d7254.
Root checked printed p679 Eq(1.1) and p686 Theorem3.1 in extracted text.
The theorem requires dissipativity and surjectivity of I-A; it supplies neither
an arithmetic dissipativity constant nor the needed prime comparison.

## Exact original-P map, without an invariance assumption

Let H_P=ran P with its original coefficient norm and J=I_m restricted to H_P,
using the inherited isometric synthesis. Let B be the full finite causal
prime-power operator of Q47 and B_P=J* B J on H_P. This is final compression;
no P is inserted inside B, Z, or their products. Both time directions and
all mixed entries remain in B_P+B_P*. The desired A_prime upper bound s is
exactly B_P+B_P* <= s I on H_P. Equivalently A_s=B_P-s I/2 is dissipative.

In finite dimension the equivalence can be checked without invoking any
unbounded-generator theorem. If A_s is dissipative, d/dt ||exp(t A_s)c||^2
=2 Re <exp(t A_s)c,A_s exp(t A_s)c> <=0. Conversely contraction for every
t>=0 gives dissipativity by the right derivative at t=0. Also I-A_s is
injective since Re <x,(I-A_s)x> >= ||x||^2, hence surjective. Thus the
semigroup criterion is exactly a restatement of the unpaid upper bound.
Compression does NOT justify identifying exp(t B_P) with J*exp(t B)J.
Using B on the entire physical carrier would instead demand a stronger,
unneeded inequality, not automatically an original-P supplier.

With such an independently proved s one would obtain T_>R <= (s+b_div)P
and PKP >= -(s+50 log(m)+8)P. No extra H_d fee: A_prime=C0-H_d.
No improved s was proved. Keep Q47 inherited s_keep<=6sqrt(m)+6m^(1/4).
The position-similarity control is only a generic negative control; it is not
an actual CCM counterexample. No numerical precision claim enters this screen.

Decision: do not use generic dissipativity/positive storage as a supplier unless
its source-specific hypotheses can be proved without assuming the requested
Hermitian bound. Return before abstract semigroup conversion. No Q48 sent;
this preflight does not manufacture three new failed arithmetic attempts.
