import Q3.Proofs.PrimeCert.PrimeCert_Margin_Spec
import Q3.Proofs.PrimeCert.PrimeCert_Margin_PathB

namespace Q3.Proofs.PrimeCert

/-- Single integration point for the `PrimeCertMarginOnBrange` contract.

`prime_cert_margin_from_gate` is now a single switch between implementations.
Today it is wired to Path B for a controlled bypass of certificate tables in the
main import chain.
-/
theorem prime_cert_margin_from_gate : PrimeCertMarginOnBrange :=
  prime_cert_margin_from_pathB

-- Compatibility spelling for older comments and downstream names.
theorem prime_cert_margin_gate : PrimeCertMarginOnBrange :=
  prime_cert_margin_from_gate

end Q3.Proofs.PrimeCert

namespace Q3

/-- Compatibility alias kept for existing `Main` signatures. -/
abbrev PrimeCertMarginOnBrange : Prop := Q3.Proofs.PrimeCert.PrimeCertMarginOnBrange

/-- Compatibility alias for the same contract entry point. -/
theorem prime_cert_margin_from_gate : PrimeCertMarginOnBrange :=
  Q3.Proofs.PrimeCert.prime_cert_margin_from_gate

end Q3
