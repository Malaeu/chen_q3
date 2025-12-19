import Lake
open Lake DSL

package TwinPrimeProject where
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib TwinPrimeConjecture where
  globs := #[.one `TwinPrimeConjecture]
