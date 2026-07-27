# CODEX DIRECTIVE

Один следующий target:

```text
D0AnchorFloorFromUnprojectedCentralMass
```

## Statement

Для всех допустимых (m,N), при source bounds

[
\sqrt{L_m}
|\langle V_{0,m},g_m^{\mathrm{Trial}}\rangle|
\ge a,
\qquad
|g_m^{\mathrm{Trial}}|\le C,
\qquad
a>0,\ C>0,
]

доказать

[
\boxed{
|F^+_{m,N}(0)|\ge a/C.
}
]

Дополнительные outputs того же theorem packet:

```text
P_mN gTrial_m ≠ 0
central index exists
sqrt(L_m) * |c0(m,N)| ≥ a / C
```

## Proof route

```text
P V0 = V0
→ <V0, P gTrial> = <V0, gTrial>
→ |c0| = |<V0,gTrial>| / ||P gTrial||
→ ||P gTrial|| ≤ ||gTrial|| ≤ C
→ Fplus(0) = sqrt(L) c0
→ floor a/C.
```

## Forbidden

```text
no numerical plateau;
no lower bound on ||P gTrial||;
no weighted projection theorem;
no phase-consistency assumption;
no use of RH;
no new axiom/sorry/admit.
```

## Validation gate

```bash
lake env lean <anchor-floor-file>
lake build
grep -R "sorry\|admit" <touched-files>
#print axioms D0AnchorFloorFromUnprojectedCentralMass
```

## Success code

```text
ANCHOR_FLOOR_PROVED
```

## Failure report

```text
ANCHOR_SOURCE_LOCK_MISMATCH:
- exact definition of kTrial;
- exact projection type;
- exact normalization norm;
- exact V0 membership theorem;
- extra scalar or phase found;
- weakest repaired statement.
```

------


(Гол 006 извлечён Mythos из вердикта Прошки; ПРЕКОНДИЦИЯ: сверить его 4 source-lock пункта — ортогональность P в норме нормировки kTrial, V0 в range P, kTrial = unit-фаза × Pg/||Pg||, вещественность/знак overlap — против D0KTrialStage1–3 ДО доказательства.)
