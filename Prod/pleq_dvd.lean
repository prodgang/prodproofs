import Prod.poset
import Prod.interp

namespace RawProd


theorem pleq_lt {x y : RawProd} : x ⊑ y → interp_raw x ≤ interp_raw y := by
  revert x y
  --apply induction_list₂
  sorry


theorem pleq_dvd {x y : RawProd } : x ⊑ y → interp_raw x ∣ interp_raw y := by sorry



end RawProd
