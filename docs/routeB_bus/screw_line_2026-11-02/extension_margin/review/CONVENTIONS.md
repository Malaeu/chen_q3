# Extension-margin conventions and independent finite checks

DIAGNOSTIC_NEVER_A_PROOF. No RH claim, no route-state change, and no new
all-node arithmetic bound are supplied. Source: the pinned PASSIVE_SECTION_P
verdict at11f6368323d8aaac3d3c0a6a95873b86294cc540, copied in SOURCE_PASSIVE.md.
This review fixes the finite diagnostic interpretation rather than claiming a
complete independent audit of that document's global equivalence theorem.

## Infinite fresh space versus sampled fresh nodes

Source(17) defines M on the completion of all fresh step profiles in the
positive fresh Weil form. It is an old-history-sized matrix of Riesz
representers. For distinct finite fresh nodes0<h_j<=delta, the corresponding
restriction is

    F_ij=K(h_i,h_j),
    V_ij=K(s_i,a+h_j)-K(s_i,a),
    M_q=V F^-1 V^T,
    S_q=F-V^T C^-1 V.

The finite margin is

    mu_q=1-lambda_max(C^-1/2 M_q C^-1/2)
        =1-||L_C^-1 V L_F^-T||_2^2,

where C=L_C L_C^T and F=L_F L_F^T. This is the smallest eigenvalue of
L_F^-1 S_q L_F^-T. Thus its sign agrees with the sampled Schur block when
C and F are positive. Its numerical value is a relative fresh-energy
margin, not the unnormalized smallest eigenvalue of S_q.

M_q is a restriction of the full representer problem, so M_q<=M and
mu_q>=mu_full whenever the full positive fresh form exists. At fixed
delta and fixed old history, nested future-node spaces give increasing M_q
and decreasing mu_q. A finite negative sampled margin is a finite witness
against the all-node section property. A positive sampled margin is not a
lower bound for the full margin and does not certify all future nodes.

The source's fresh-form coercivity guarantees the positive-form setting for
zeta when0<delta<=1/16. For other worlds or larger fresh intervals, positivity
must be checked or separately supplied. The zeta lemma must not be silently
applied to DH. The source supplies a modified local bound for its planted
world, with the quartet price retained.

## Guards

C must be positive before it is interpreted as a past Hilbert metric. A
negative old direction already makes the unrestricted prediction minimum
minus infinity. Numerically square-rooting absolute eigenvalues of C changes
the problem. F must likewise be positive for the displayed inverse and
whitening. No PSD clipping or small-eigenvalue truncation belongs in this
diagnostic.

Fresh h=0 or duplicate nodes create known structural zero directions. They
may be removed with their exact dependence relations. In a general singular
F, check Vz=0 for every z in ker F before quotienting: otherwise
z^T S_q z=-||C^-1/2 Vz||²<0 already. A pseudoinverse without this range check
can conceal a negative extension. Unresolved numerical signs require more
precision or an unresolved label.

## Extension length and nested domains

For a fixed old history, the exact all-node property on(0,delta] is monotone
in delta: if it fails on one interval, the same witness remains in every
larger interval. Its maximal admissible length delta_star therefore refers
to an interval property. Testing only the one new endpoint is weaker;
the one-point Schur value may change sign more than once. Several new
points can produce a negative combination even when each separate
one-point extension is nonnegative.

Moving q equally spaced nodes h_j=j delta/q while varying delta does not
produce nested finite spaces. A positive/negative crossing in that moving
family is not automatically a monotone threshold. To diagnose a finite
delta_star, use a fixed fine future lattice and cumulative prefixes, or
retain the union of all previously tested nodes as delta grows. Report the
actual node sets. A sampled negative block bounds the all-node admissible
length from above; finite positive blocks alone do not give its lower bound.

For resolution, hold delta and C fixed and use q=1,4,8,16,32 with all grids
containing the endpoint delta. These sets are nested. A significant upward
step in mu_q signals numerical or convention trouble under the positivity
guards. The change mu_16-mu_32 is a resolution diagnostic, not a rigorous
tail bound. If the two margins are near zero relative to their difference,
report unresolved continuum sign even if both finite signs are positive.

## No automatic zero margin from fresh-only boundary infill

The source's own fixed-history budget gives

    mu_full >= 1-rho_delta/beta(delta)

when beta>0. For each fixed finite positive past, its stated bounds have
rho_delta=O_history(delta log²(1/delta)) and beta(delta) of order
log(1/delta). Thus the bound tends to one as delta shrinks, uniformly over
the number of fresh nodes. This prevents interpreting a shared boundary or
the logarithmic endpoint response, by itself, as forcing a zero margin.

Refining the old history at the same time changes C and the constants; the
source explicitly gives no uniform inverse-history bound. The conclusions
above do not settle that different limit. Old-side refinement, fresh-side
refinement and shrinking the extension length must be reported separately.

## Relation to the earlier planted Theta

The previous plant diagnostic factors the entire sampled signed matrix as
T_w=C_plus-UU^T and studies Theta=U^T C_plus^-1 U. Here C_plus includes
the zeta baseline and the positive quartet squares; it is not the old-history
matrix C in the extension problem.

For the same combined node set and a positive old C and positive fresh F,
the extension Schur sign and the quartet Theta crossing describe the same
combined matrix inertia. In a one-new-point extension, mu=sigma²/F_11.
Thus their first zero crossings agree when all those guards and node sets
are identical. Their scalar values need not agree. After the old planted
block becomes indefinite, this positive-metric extension mu is no longer
defined as a prediction margin, even though the previous Theta diagnostic
can continue accumulating the full signed index.

## Executed source-section16 replay

Fixed old nodes are a/4,a/2,3a/4,a with a=log16. The source section length
is delta=log(17/16). Five nested q grids were evaluated at80digits, with
q32 repeated at100digits. Direct point-kernel and fresh-increment Schur
forms agreed, as did both normalized-margin formulas.

|q|mu_q at delta=log(17/16)|
|---:|---:|
|1|0.5083101847020927850|
|4|0.4578611339021679773|
|8|0.4524571476008527209|
|16|0.4506174773416873781|
|32|0.4500049864354327276|

The source-derivative quadrature at80digits independently reproduces
beta=0.3577210476825983515 and rho=0.9553248978416185076. The coarse
normalized lower bound is1-rho/beta=-1.670586212442458723, while all five
sampled full-form margins above are positive. This illustrates the source's
scalar-envelope loss without claiming positivity of the all-node limit.

With the same fixed old nodes, shortening delta to0.001 gives q32 margin
0.9735704147740228466; delta0.00001 gives0.9995328068562533045. In both
cases the entire q1,4,8,16,32 sequence decreases with refinement and stays
positive. These are70-digit calculations, not interval certificates.

All source-return errors, normalized eigenvalue errors, positive-guard
eigenvalues and the80/100-digit comparison are saved in
finite_margin_checks.csv/json. coarse_source.json retains the direct
response quadrature. The small prescribed budget is complete; no
delta_star or universal continuation claim is inferred from these cells.
