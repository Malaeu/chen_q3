# D0.7e.5b — exact downstream parameter interface

Status: `PROVED_INTERFACE_TYPECHECK_ONLY / NOT_RH`

This leaf closes only the type-level part of the owner-ratified B-prime slot.
It supplies no value, asymptotic estimate, selector, filter choice, or
existence theorem.

## Independent carrier

The carrier is the direct two-parameter product

```text
I_two = {(m,N) : m is a natural index and N is a positive natural index}.
```

The coordinates are independent. No map from one coordinate to the other is
part of this interface.

## Supplied downstream parameters

For `i` in `I_two`, the consumer receives the following typed hypotheses:

```text
alpha       : I_two -> RealNonnegative
DeltaE      : I_two -> RealStrictlyPositive
delta_dict  : I_two -> RealNonnegative
FilterSpace : I_two -> Type
F           : product over i in I_two of FilterSpace(i)
```

Thus `alpha(i) >= 0`, `DeltaE(i) > 0`, and `delta_dict(i) >= 0` are type
invariants. `FilterSpace` and `F` remain abstract downstream parameters.

## Firewall

- The definitional home of `alpha` remains H0/A1 and is still OPEN_CRITICAL.
- The spectral meaning of `DeltaE` remains downstream and unproved here.
- No filter is selected.
- No relation between the independent coordinates is selected.
- No model gap replaces the true complementary spectral distance.
- No H3 or H4 theorem is imported into D0.

Verdict: `D0_7E_5B_TYPED_INTERFACE_LOCKED`. This does not close D0.7e.5,
does not define WPrime, and proves nothing about RH.
