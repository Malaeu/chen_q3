# Input availability at the pinned commit

Git commit cdb84497649c7399448737732b7dd3d632e141f0 checked through GitHub
and a blob-filtered checkout. Repository tree enumeration finds no NPZ files
under docs/routeB_bus/arithmetic_coupling_2026-11-03/.
quiet/INDEX.csv and all scalar/vector receipts exist.
DATA_ARCHIVE.json explicitly says:

> Dense source matrices and quiet frames regenerate from code; all scalar/vector receipts retained.

Its member list contains quiet/frames/*.json metadata but not the requested
quiet/frames/*.npz. The whole quiet/ directory listing likewise contains no
frames/ directory. The original RESULT and quiet/RESULT describe numerical
intermediates generated in the earlier execution environment; they are not
binary source/frame artifacts committed in this input revision.

The owner explicitly requested REUSE(do not rebuild). No dense source or
quiet frame regeneration has been performed. Dependent new numerical results
are held until the existing artifact location is supplied or regeneration
with unchanged pinned builders is explicitly authorized. This is an input
availability block, not a mathematical gate failure and not a failed SVD/SDP.

V2 RESOLUTION: the owner subsequently explicitly authorized unchanged source
and frame regeneration on the bounded calibration/pilot set. That regeneration
has now been performed and hash-inventoried. The text above records the v1
availability issue and the reason authorization was sought; it is not a current
block on v2. See REGENERATED_ARRAYS.json and REPRODUCE.md.
