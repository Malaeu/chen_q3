-- Compatibility wrapper: moved into Q3.Proofs to avoid global name clashes.
import Q3.Proofs.A3_Floor_Bounds

namespace A3_FLOOR_v20_bounds_core

-- Re-export under a namespaced prefix to avoid duplicate globals.
export Q3.Proofs.A3_Floor_Bounds (B_min t_sym w)

end A3_FLOOR_v20_bounds_core
