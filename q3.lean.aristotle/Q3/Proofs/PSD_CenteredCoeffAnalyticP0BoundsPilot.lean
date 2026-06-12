import Q3.Proofs.PSD_CenteredCoeffAnalyticP0ProfileImport
import Q3.Proofs.PSD_CenteredCoeffAnalyticP0ExpHboxImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffAnalyticP0BoundsPilot

private theorem primaryK11_p0_d0_plus_seg0_upper_pilot :
    p0PieceK11D0PlusWindowSegmentExpIntegral 0 <= (1 : Real) := by
  have hp3_10 := abs_sub_le_iff.mp p0ExpK11_p3_10_hbox
  have hp11_40 := abs_sub_le_iff.mp p0ExpK11_p11_40_hbox
  unfold p0PieceK11D0PlusWindowSegmentExpIntegral
  rw [expPolyIntegral_eq_exp_linear]
  norm_num [
    p0PieceK11D0PlusWindowSeg0Coeff,
    expPolyIntegralRightCoeff,
    expPolyIntegralLeftCoeff,
    expMulPowIntegralRightCoeff,
    expMulPowIntegralLeftCoeff,
    Finset.sum_range_succ
  ]
  linarith [hp3_10.1, hp3_10.2, hp11_40.1, hp11_40.2]

end CenteredCoeffAnalyticP0BoundsPilot
end PSDpd
end Q3
