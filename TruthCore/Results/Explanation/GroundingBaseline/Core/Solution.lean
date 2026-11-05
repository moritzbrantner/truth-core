module

public import TruthCore.Results.Explanation.GroundingBaseline.Solution

@[expose] public section
namespace TruthCore.Results.Explanation.GroundingBaseline.Core
open TruthCore.Explanation.GroundingBaseline
/-- Exact data-only specialization: all original C/N/S premises remain. -/
theorem incompatible {W F : Type} (K : TruthCore.Modal.Frame W) (truth : W → F → Prop)
    (a : W) (p q : F) (hc : ConditionContingent K truth a p)
    (hn : ConditionNecessary K truth a q) (hs : ConditionImplication K truth a q p) :
    TruthCore.Logic.ConfigurationFalse :=
  necessitationImpossible (conditionArena K truth) a p q hc hn hs
end TruthCore.Results.Explanation.GroundingBaseline.Core
