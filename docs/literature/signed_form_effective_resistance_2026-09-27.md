# Signed difference forms and effective resistance: bounded alias hunt

2026-09-27. Discovery evidence only; no Goal058 supplier or RH claim.

## Exact obstruction and source

For the finite selected Hermitian matrix `K_j`, normalized selected vector
`q_j`, and `a_j = <q_j,K_j q_j>`, the proposed strong floor would require
`<y,(K_j-a_j I)y> >= delta_j ||y||^2` for **every** complex `y` in
`H_j = q_j^perp`, with `delta_j > 0` on the admitted selected tail. The
constant-beta version is already refuted; a different source-matched
cofinal interface remains open (`docs/Codex/NEXT.md`, G1/G3; the exact
finite-cell negative control is in
`docs/literature/complement_coercivity_2026-09-25.md`). A close `q_j` alone
does not prove this Rayleigh-shifted floor.

The existing global Weil ground-state identity is
`Q(f_0 s) = int_0^infty b(t) E_s(t) dt + sum_{n>=2} w_n E_s(log n)`,
`E_s(t) = int f_0(x)f_0(x+t)|s(x+t)-s(x)|^2 dx >= 0`, and
`w_n = Lambda(n)/sqrt(n) >= 0`. Here `b(t)>0` only for
`0<t<log(plastic number)` and `b(t)<0` afterward; all prime atoms lie in
the negative-density region. Source: `paper_weil/sections/groundstate.tex`,
Theorem `GS`, Lemma `plastic`. Thus the identity supplies **squares with
signed coefficients**, not positivity. Comparing total masses cannot
control every profile.

Search hints, **UNVERIFIED as Q3 bridges**: regard the positive lags/prime
atoms as a network of positive edges and the negative continuous lags as
negative edges; regard the selected compression as a Schur complement of
that signed network. The actual finite-window source has endpoint jumps,
exterior tails, returned prime powers, projection to `q_j^perp`, and
the shift `-a_j I`. Their exact effect is not supplied by the global
ground-state identity.

## A worked sign proof in the literature's class

For a connected finite positive-weight graph, its Laplacian `L_+` has
`x*L_+x > 0` on `1^perp`. Add one edge `(u,v)` of negative weight `-w`,
`w>0`; write `d=e_u-e_v` and `L=L_+-w dd*`. Define

`R_eff(u,v) = sup_{x in 1^perp, x != 0} |d*x|^2/(x*L_+x)
            = d* (L_+|_{1^perp})^{-1} d`.

Then, **for every** `x in 1^perp`, exactly

`x*Lx = x*L_+x - w |d*x|^2
     >= (1-w R_eff(u,v)) x*L_+x`.

Hence `w R_eff < 1` gives a strict all-directions floor
`L|_{1^perp} >= (1-w R_eff) lambda_min(L_+|_{1^perp}) I`.
At equality another zero direction can appear. This is the exact
one-edge condition of Zelazo--Buerger, Theorem IV.7 (their statement
allows semidefiniteness at equality). Short source quote, PDF p. 4:
"positive semidefinite if and only if" the negative weight obeys the
reciprocal effective-resistance bound.

For many negative edges, let `D_-` have their incidence columns and
`W_- >= 0` their magnitudes. On `1^perp` the same elementary factorization
gives `L=L_+-D_-W_-D_-*` and

`theta = || W_-^(1/2) D_-* (L_+|_{1^perp})^{-1}
              D_- W_-^(1/2) ||_2`.

If `theta<1`, then `L|_{1^perp} >= (1-theta)
lambda_min(L_+|_{1^perp}) I`. This is a sufficient bound on the full
matrix of mutual negative-edge interactions, not a sum of scalar edge
bounds. Chen et al., Theorem 1 and equation (5), instead characterize
the signed Laplacian through a resistance matrix of a negative-edge
spanning forest. Their matrix uses the **full signed** `L` pseudoinverse;
it is an exact characterization, not automatically a non-circular Q3
estimate. Short quote, PDF p. 3: "A signed Laplacian L is positive
semidefinite with a simple zero eigenvalue if, and only if" its graph is
connected and their resistance matrix is positive definite.

## Hypothesis map and negative control

| Needed input | Literature | Q3 status |
|---|---|---|
| Exact weighted-square identity | Graph edge energy | **PROVED globally** in `groundstate.tex` for smooth compact `s` |
| Nonnegative weights | Frank--Seiringer Assumption 2.1 | **FALSE** for Q3 `b(t)` |
| Positive sector coercive on the exact complement | Connected `L_+` on `1^perp` | **OPEN** for actual `H_j=q_j^perp` |
| All negative channels controlled jointly | `w R_eff<1` or `theta<1` | **OPEN**, and negative lags form a continuum |
| Exact finite selected-source identification | Same graph and domain throughout | **OPEN**; endpoint, exterior, prime powers, and `-a_j I` must be paid |

Frank--Seiringer, §2, explicitly assumes a symmetric **non-negative**
kernel and, for `p=2`, obtains equality in Proposition 2.3. Short
source quote, PDF p. 5: "a non-negative measurable function k".
Its positivity conclusion therefore cannot be transferred to the signed
Q3 density. Likewise, a 2-plane metric or a few positive sample values
cannot control the entire complement. The finite negative control in the
previous literature note has a `q` close to the exact ground but a
negative `q^perp` Rayleigh direction. It disproves transfer from
closeness alone, independently of any proposed factorization.

## One bounded bridge to test

On one **actual selected cell**, derive or refute a source-exact
decomposition on `H_j` of the form
`B_j=P_j-C_j*W_j C_j+R_j`, where
`B_j=(K_j-a_j I)|_{H_j}`, `P_j>=p_j I`, `W_j>=0`,
`R_j>=-e_j I`, and `p_j>e_j>=0`. Then calculate the joint number
`theta_j=||W_j^(1/2) C_j (P_j-e_j I)^{-1}
C_j* W_j^(1/2)||_2`. If `theta_j<1`, the elementary factorization
would prove `B_j>0` at that cell. To supply Goal058, all definitions,
`p_j-e_j`, and `theta_j<1` must be certified **cofinally in the actual
selected source**, retaining the listed correction terms. Stop this
route if the positive sector is not coercive or its loss is not smaller
than its floor. The current Proshka finite-coefficient-panel request is
a separate source-sign test; do not replace or duplicate it.

Status: **PARTIAL ANALOGUE / INCOMPLETE**, not `EXACT_FIT`.

## Fetched primary sources

- Daniel Zelazo and Mathias Buerger, *On the Robustness of Uncertain
  Consensus Networks*, Theorem IV.7, PDF p. 4,
  <https://connect-lab-technion.github.io/Publications/Zelazo_TCNS2014.pdf>.
  Fetched PDF SHA-256:
  `770b5e5a7c8f439cab9cb3c0a57e1506b2a37089ae0406d504c4f1108af5e661`.
- Wei Chen et al., *Characterizing the Positive Semidefiniteness of Signed
  Laplacians via Effective Resistances*, IEEE CDC 2016, DOI
  `10.1109/CDC.2016.7798396`, Theorem 1/equation (5), PDF p. 3,
  <https://eeqiu.people.ust.hk/wp-content/uploads/2021/09/Characterizing-the-Positive-Semidefiniteness-of-Signed-Laplacians-via-Effective-Resistances.pdf>.
  Fetched PDF SHA-256:
  `b914e827b20649fe9ef3c526825d783ed89e95028f7870324fcb55801a9be0a4`.
- Rupert L. Frank and Robert Seiringer, *Non-linear ground state
  representations and sharp Hardy inequalities*, JFA 2008, DOI
  `10.1016/j.jfa.2008.05.015`, §2 Assumption 2.1/Proposition 2.3,
  <https://arxiv.org/abs/0803.0503>. Fetched PDF SHA-256:
  `10835c6acadc02a4565ca0533f420d8f47b188a954bc921bf35314da928fc6ef`.

Primary PDFs were inspected as local downloads in `/tmp`. Discovery mapping
and the Q3 source comparison were read at root; no independent audit of this
new cross-domain map has been performed.
