# Codex source record — W4 fixed-`k` shifted form-domain assembly

```yaml
schema: q3_codex_source_record.v1
date: 2026-08-24
branch: rh_clean
implementation_parent: 5ff744eb10e7ee38c79293390670af6027f7e81c
status: KERNEL_GREEN_PENDING_SEMANTIC_REFRESH
node: W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY
route: CHALLENGER_NOT_RH
route_promotion: false
rh_claim: false
```

## Scoped source bytes

```yaml
q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean:
  git_blob: 9530f4609b82bf3edf4f61e1e1de459524f516b7
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean:
  git_blob: 3d04cb1e2b6ee3390d7933f65958506b86ffe1d1
q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFixedKShiftedRootEnergy.lean:
  git_blob: ce9182cfab45f8f239f501711844794344399eb1
```

The first two files expose already-proved transport and integrability facts as
public suppliers.  The new assembly file is the exact consumer frozen by the
W4 verdict; no surrogate form domain is introduced.

## Public declarations

```text
sourceLogWindow_measurePreserving
sourceExpWindow_measurePreserving
vModeLogGrowthEnvelope_sq_div_one_add_abs_sq_integrable
selectedFerrersAbelLimitHm
sourceLogWindowZeroExtension_selectedFerrersAbelLimitHm_ae
selectedFerrersAbelLimit_mem_sourceArchimedeanShiftedFormDomain
```

Every declaration printed during the direct/build gate has exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The assembly keeps the four load-bearing categories separate:

1. W3 supplies `selectedFerrersAbelLimit_memLp` and hence the literal `H_m`
   vector `selectedFerrersAbelLimitHm`.
2. Measure-preserving inverse log transport proves only an a.e. provenance
   equality between its chosen additive representative and the direct W4
   representative.  Full endpoint values are not rewritten pointwise.
3. W1 identifies the synthesized `L²` isometry with the ordinary Fourier
   integral only a.e.; the final `MemLp` transfer spends that exact theorem.
4. The repaired W4 fixed-`k` decay is squared and combined with the literal
   source archimedean square-root weight through the proved logarithmic symbol
   envelope.

No constant uniform in `k`, cofinal rate, W5 statement, downstream Goal 058
assembly, Route promotion, or RH claim occurs in the theorem or proof.

## Kernel gates

From `q3.lean.aristotle`:

```text
lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersFixedKShiftedRootEnergy.lean
  PASS

lake build Q3.Proofs.RouteB.G6N1SelectedFerrersFixedKShiftedRootEnergy
  PASS
  Build completed successfully (7872 jobs)
```

From repository root:

```text
scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersFixedKShiftedRootEnergy.lean
  PASS
  q3_check ok
```

Source scan:

```text
sorry: 0
admit: 0
native_decide: 0
```

Kernel-green exit:

```text
W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY_KERNEL_GREEN
```

Semantic admission remains conditional on the post-push strict semantic-index
refresh.  The only intended successor after phase close is:

```text
W5_COFINAL_RATE
```
