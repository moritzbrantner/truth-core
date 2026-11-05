import TruthCore.Explanation.GroundingBaseline
import TruthCore.Logic.Configuration
namespace TruthCore.Results.Explanation.GroundingBaseline.Core
open TruthCore.Explanation.GroundingBaseline
theorem incompatible {W F : Type} (K : TruthCore.Modal.Frame W) (truth : W → F → Prop)
    (a : W) (p q : F) (hc : ConditionContingent K truth a p)
    (hn : ConditionNecessary K truth a q) (hs : ConditionImplication K truth a q p) :
    TruthCore.Logic.ConfigurationFalse := by sorry
end TruthCore.Results.Explanation.GroundingBaseline.Core
