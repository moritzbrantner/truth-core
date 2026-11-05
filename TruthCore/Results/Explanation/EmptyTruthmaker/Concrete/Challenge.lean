import TruthCore.Explanation.EmptyTruthmaker
namespace TruthCore.Results.Explanation.EmptyTruthmaker.Concrete
open TruthCore.Explanation.PSRStrength TruthCore.Explanation.TruthmakerTheories
open TruthCore.Explanation.EmptyTruthmaker
 theorem incompatible (W B K : Type) (A : Arena W B K) (M : Making W B K)
    (C : W → B → Prop) (w : W) (f : K)
    (hE : ConcreteEmptyAt A C w f) (hT : NeedsMakerAt A M w f)
    (hC : ConcreteMaker M C) : TruthCore.Logic.ConfigurationFalse := by sorry
end TruthCore.Results.Explanation.EmptyTruthmaker.Concrete
