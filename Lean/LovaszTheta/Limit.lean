module

public import LovaszTheta.CirculantLimit
public import LovaszTheta.IndependentLimit

/-!
# The two Lovász theta limits

The normalized expectations for the independent-edge graph and
the random circulant both tend to one through all positive orders.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LovaszTheta

/-- The main theorem for the two random graph models. -/
theorem tendsto_normalizedExpectedTheta_both :
    Tendsto (fun m : ℕ ↦
      (Independent.expectedTheta (m+1)/Real.sqrt (m+1 : ℕ),
       Circulant.expectedTheta (m+1)/Real.sqrt (m+1 : ℕ))) atTop (𝓝 (1,1)) :=
  Independent.tendsto_normalizedExpectedTheta.prodMk_nhds Circulant.tendsto_normalizedExpectedTheta

end LovaszTheta
