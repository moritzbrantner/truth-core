import TruthCore.Causality.DependenceStrictGroundMapStrength
import TruthCore.Results.Modern.Fine.StrictGroundAcyclic.Solution
import TruthCore.Results.Modern.Fine.InfiniteDescent.Solution

namespace TruthCore.Results.Causality.DependenceStrictGroundMapStrength

open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.DependenceStrictGroundMapStrength
open TruthCore.Modern.Fine.PureLogicOfGround

/-- Structural strength of the strict-ground support bundle: consistency and
the dependence-to-strict-ground map already force distinct-step dependence to
have no finite cycle, which is more than nonmutuality. -/
theorem mapForcesDistinctDependenceAcyclic {B Atom : Type}
    (D : B → B → Prop) (existenceFact : B → Atom)
    (S : Set (Sequent Atom))
    (hCons : Consistent S)
    (hMap : DependenceMapsToStrictExistenceGround D existenceFact S) :
    DistinctDependenceAcyclic D := by
  sorry

/-- The support bundle has a populated model with a distinct dependence
edge, so it is not satisfied only by an empty dependence relation. -/
theorem nonvacuity :
    TruthCore.Causality.DependenceStrictGroundMapStrength.Control.Nonvacuous := by
  sorry

end TruthCore.Results.Causality.DependenceStrictGroundMapStrength
