# OmegaPrime Order-17 Rational Payload

schema: `q3_psdpd_step33_a1_sub0_omega_prime_order17_payload.v1`
route: `omega_prime_order17_rational_tail_payload`

## Verdict

- proofGrade: `True`
- firstFailure: `None`
- Lean file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17RationalPayload.lean`
- theorem: `Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_generated`
- budget theorem: `Step33Sub0OmegaPrimeOrder17Payload.half_tsum_majorant_le_generated`

## Exact Constants

- m: `17`
- prefixN: `2`
- prefixPolicy: `first candidate with tail <= last retained half-prefix term`
- coeffNorm: `97692469875/2`
- prefixAbs: `1024379792916533707003286859546624/152587890625`
- tailAbs: `745930601206382592/30517578125`
- order17Abs: `1024379792916537436656292891459584/152587890625`

## Candidate Scan

- N=`2`, order17Abs=`1024379792916537436656292891459584/152587890625`, tailLeLastPrefixTerm=`True`
- N=`3`, order17Abs=`23434523917607469960718685634103724456399601664/3490721504968414306640625`, tailLeLastPrefixTerm=`True`
- N=`4`, order17Abs=`23718050314919341925836504088418207013982101936765547046579055099904/3532954566574549728346961567728686676025390625`, tailLeLastPrefixTerm=`True`
- N=`5`, order17Abs=`333548944617102205815592529176033356394240017507834704640404666238435222103456713996763136/49684238435056218499873445756847359912599125905349260175933837890625`, tailLeLastPrefixTerm=`True`
- N=`6`, order17Abs=`77593662426166927680928421690271107873768663275747977358830469726584285857141355097928480921771313201152/11558069924210073266222194418097639364443581459950233126540086053058047943115234375`, tailLeLastPrefixTerm=`True`
- N=`7`, order17Abs=`1479981659434641412371223836314903396266483316489073708454451717669127902162553332887797873546786966981241830796951552/220452688678933587383693588602021014489051465224270498781968804417763670790009200572967529296875`, tailLeLastPrefixTerm=`True`
- N=`8`, order17Abs=`9032714707691393785831217277982898289413724518696770474894299888526999690747030021047329215380632524146135524103021010167440785164535510165618688/1345480351520703510661998047677959923997725715510194918970411122868071056175759069625485289900753376423381268978118896484375`, tailLeLastPrefixTerm=`True`

## Required Lean Symbols

- `primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN`: present=`True`, line=`28`
- `primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixAbs`: present=`True`, line=`30`
- `primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TailAbs`: present=`True`, line=`33`
- `primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs`: present=`True`, line=`36`
- `omegaPrimeTrigammaDerivCoeff_norm_eq_order17`: present=`True`, line=`39`
- `omegaPrimeOrder17_half_prefix_majorant_le_generated`: present=`True`, line=`64`
- `omegaPrimeOrder17_half_shifted_tsum_le_generated`: present=`True`, line=`79`
- `half_tsum_majorant_le_generated`: present=`True`, line=`108`
- `primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_generated`: present=`True`, line=`147`

## Boundary

This closes only the OmegaPrime order-17 rational source row.  It does not close the RawProduct18 majorant, the degree-0 budget, or Step33A.1-A.
