# Arithmetic-section margins with complete sampled past

DIAGNOSTIC_NEVER_A_PROOF. Route B remains CHALLENGER / NOT_RH.

The registered finite prediction min mu>=0.1 fails. At n=16, old mesh1/32,
the80-digit margin is0.0833588792525536168 with only four fresh nodes, and
0.0616360758945332737 with32 fresh nodes. The section has
delta=log(17/16)<1/16, inside the source's short fresh-form range.
On the finest old mesh1/256 even one fresh endpoint gives
mu=0.0915734519013928067 at n=30, independently replayed at80digits.
These are floating diagnostics, not directed-rounding proof certificates.

For every n=2..240, a=log n, the past includes every uniform increment
before a and the remaining partial increment ending exactly at a. This
retains the entire sampled past rather than dropping to a few old anchors.
The q fresh nodes are equally spaced on(a,log(n+1)], with q=1 on every
section and q=1,4,8,16,32 on n=16,32,64,120,240 and the q1-minimizing
section for each world and old mesh. A separately preregistered extension
also computed q4 and q8 for every zeta section on every mesh. The future
grids at a fixed section are nested. No q32 scan over every n is claimed.

|Old mesh denominator|Zeta minimum q1 margin over n2..240|Argmin n|Minimum over representative/refined cells|Representative argmin n,q|
|---:|---:|---:|---:|---:|
|32|0.179550808490472|8|0.0259599043879202|8,32|
|64|0.140119401928432|18|0.0251065505989658|16,32|
|128|0.111055288978052|18|0.00951924113152658|16,32|
|256|0.0915734519014028|30|0.00377376428130505|16,32|

All tested zeta cells have positive sampled margins. Their decline under
old and fresh refinement does not supply a continuum positive lower bound.
In particular, the observed q32 minimum need not be the all-node minimum.
For n=16 the q32 margins on meshes32,64,128,256 are respectively
0.061636075895,0.025106550599,0.009519241132,0.003773764281.

The first row's refined minimum at n8 is outside the source's proved
delta<=1/16 coercivity range; all n<16 have an explicit flag. Their sampled
fresh Gram was checked directly. The separate n16 MP replay removes this
boundary concern from the0.1-prediction failure.

The additional all-section zeta profile completed all1,912 q4/q8 cells in
30.1seconds, within the120-second budget. Every sampled margin was positive
and every section obeyed mu8<=mu4<=mu1 within the recorded numerical guard.

|Old mesh denominator|Minimum q4 over n2..240|Argmin n|Minimum q8 over n2..240|Argmin n|
|---:|---:|---:|---:|---:|
|32|0.0592095267848|7|0.0303417820251|6|
|64|0.0464932733095|10|0.0205091908508|6|
|128|0.0363591573297|13|0.0158163079671|9|
|256|0.0294241253663|20|0.0121705154941|13|

These argmins often lie below n16 and retain the same outside-coercivity
flags. Their signs are finite sampled observations, not an import of the
short-source theorem beyond its stated range.

## Broken worlds and history guards

|World|Mesh denominator|Sections with positive sampled old history|Minimum q1 margin|Minimum refined representative margin|First invalid old section n|
|---|---:|---:|---:|---:|---:|
|DH|32|239|0.2166113250|0.1219097430|none through240|
|DH|64|71|-6.347284524|-17.392355789|73|
|DH|128|42|-0.0613325497|-0.1187169192|44|
|DH|256|38|0.0848456216|-0.0193334237|40|
|plant|32|3|0.0290674710|-0.3258618257|5|
|plant|64|2|0.0883491861|-0.1129948937|4|
|plant|128|1|0.1006583474|-0.0009802970|3|
|plant|256|1|0.0998292626|-0.0014086442|3|

Here a valid past is a positive old block; the extension itself may already
be negative. The DH mesh256 case at n39 has a positive one-point margin
but a negative32-node margin. The plant at n2 on meshes128 and256 behaves
the same way. Endpoint-only acceptance can therefore miss a negative
combination of fresh nodes.

The full table has2,868 q1 rows:1,353 valid finite margins,1,514 histories
already excluded by the high-precision uniform-prefix negative index, and
one additional negative partial-old pivot. The latter is DH mesh64,n73:
the partial endpoint log73 has old Schur pivot-0.2309996368 even though
the preceding uniform grid prefix is still positive. This new old
direction is retained and causes rejection, rather than being discarded.
No unresolved partial pivot or failed fresh Cholesky occurred in this run.

n=1 would have a=0 and empty old history; conditional on positive fresh F,
its finite normalized margin is identically1. It is outside the source's
C>0 nonempty-history contract and is not included in the n2..240 scan or
in the reported minimum.

## Validation and interpretation

The implementation reuses one Cholesky of the largest known-positive
uniform Toeplitz prefix. It then conditions the exact partial old interval
before forming the fresh normalized coupling. All old coordinates remain
present. The old Toeplitz entries come from the committed100-digit source
scan; off-grid entries use the vectorized floating source. No eigenvalue
clipping or pseudoinverse threshold is used. A partial pivot within1e-11
of zero is marked unresolved; a clearly negative pivot rejects that past.

The independent80-digit n16,mesh32 calculation used the full89-dimensional
old Gram, exact logarithmic endpoints and a fresh32-bin Gram. Aggregating
the fresh bins reproduced every q=1,4,8,16,32 margin. The maximum absolute
change from float64 was4.61e-14; normalized Schur eigenvalues and the
coupling formula agreed within7.38e-81. The partial-old pivot was
0.0196088994717291259 and all fresh Cholesky pivots were positive.

The80-digit n30,mesh256 scalar replay retained870 uniform increments plus
the partial terminal interval, using Toeplitz innovation whitening. Its
margin changed by9.95e-15 from float64. The partial-old pivot was
0.0059149461800663681, and an independent dense32-coordinate whitening
check differed by8.25e-84. This replay took about8seconds; it did not
replace the871-dimensional history with a32-dimensional approximation.

The fresh finite margin is an upper bound on the all-node margin when the
full positive fresh-form setting applies. Hence the observed finite values
below0.1 contradict that proposed uniform diagnostic reserve; they do not
contradict nonnegative continuation, and positive finite values do not
prove it. No constant lower bound or cofinal conclusion is inferred.

Reproduce with Python3 and mpmath, NumPy, SciPy already installed:

```
python3 sections.py
python3 validate_mp.py
python3 validate_fine_scalar.py
python3 profile_blocks.py
```

`all_sections_q1.csv` and `representative_q_refinement.csv` contain all
requested cells and guard statuses. `mp_validation.*` and
`fine_scalar_validation.json` preserve the precision checks. The field
`fresh_gram_entrywise_norm_condition_upper` is a product of entrywise
one-norms, an upper bound for the induced-one-norm condition number,
not the spectral condition number.

`zeta_all_sections_q4_q8.csv` and `zeta_block_profile_summary.*` retain the
complete additional block profile, with its own preregistration and budget
receipt. No adaptive extension was used to rescue the rejected0.1 reserve.
