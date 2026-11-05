module
public import TruthCore.Explanation.EmptyTruthmaker
@[expose] public section
namespace TruthCore.Results.Explanation.EmptyTruthmaker.Concrete
open TruthCore.Explanation.PSRStrength TruthCore.Explanation.TruthmakerTheories
open TruthCore.Explanation.EmptyTruthmaker
/-- ConcreteMaker must mean membership in a concrete-EXISTENT extension for
that interpretation. The proof needs only membership; existence is not smuggled
into the supplied C predicate. No abstract-maker policy is refuted. -/
 theorem incompatible (W B K : Type) (A : Arena W B K) (M : Making W B K)
    (C : W → B → Prop) (w : W) (f : K)
    (hE : ConcreteEmptyAt A C w f) (hT : NeedsMakerAt A M w f)
    (hC : ConcreteMaker M C) : TruthCore.Logic.ConfigurationFalse := by
  obtain ⟨b, hb⟩ := hT hE.2
  exact (hE.1 w).1 hE.2 b (hC w b f hb)
end TruthCore.Results.Explanation.EmptyTruthmaker.Concrete
