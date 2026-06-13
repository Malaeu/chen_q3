# Track B S5 Failure Atlas Entry

Status: ACTIVE_NEGATIVE_KNOWLEDGE.  This file records what not to reuse after
S4/S5.1.  It is diagnostic strategy documentation only.

## DO_NOT_USE

```text
L = Mplus * F_v
```

as the zero-side PSD lift.

## Reason

```text
S4 planted detector valid.
hat(L) has large negative values.
L is not PSD eligible.
S5.1 shows the negative spectral mass is broad, not local.
```

## Scope

```text
kills current lift only
does not kill all B2b
does not reopen B2a
does not make S3 closure false
```

## Corrected Route B Note

Do not record the false reason:

```text
spectral clipping kills Hermitian-square
```

The corrected reason is:

```text
hat(L_proj)=max(hat(L),0) repairs Fourier-side PSD, but may destroy physical
edge-control and exceed the mu-budget through projection loss.
```

So Route B is deferred / likely expensive because edge-control is endangered,
not because PSD cannot be repaired.
