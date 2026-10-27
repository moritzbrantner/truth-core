import TruthCore.Causality.NecessaryConcreteRoot
import TruthCore.Logic.Configuration

namespace TruthCore.Results.Causality.NecessaryConcreteRoot.CoreIncompatible
open TruthCore.Causality.NecessaryConcreteRoot
open TruthCore.German.Kant.CosmologicalInference

/-- Exact four-premise inconsistent core at one common world, carrier, frame and causal relation. -/
theorem checks {W E : Type} (m : Ontic W E) (concrete : E → Prop) (w : W)
    (hPop : PopulatedConcreteAt m concrete w)
    (hWF : WellFoundedConcreteAt m concrete w)
    (hDep : ContingentConcreteDependenceAt m concrete w)
    (hAll : AllActualConcreteContingent m concrete w) :
    TruthCore.Logic.ConfigurationFalse := by
  exact actualConcreteCoreFalse m concrete w hPop hWF hDep hAll

end TruthCore.Results.Causality.NecessaryConcreteRoot.CoreIncompatible
