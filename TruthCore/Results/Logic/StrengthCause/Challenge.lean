import TruthCore.Logic.Strength.Cause
namespace TruthCore.Results.Logic.StrengthCause
open TruthCore.Logic.Strength.Cause TruthCore.Greek.Plato.Timaeus
universe u
theorem implication {Entity : Type u} [DecidableEq Entity] (G : Entity → Prop)
    (C : Entity → Entity → Prop) (hS : DistinctCausePrinciple G C) : CausePrinciple G C := by sorry
theorem deltaForward {Entity : Type u} [DecidableEq Entity] (G : Entity → Prop)
    (C : Entity → Entity → Prop) (hS : DistinctCausePrinciple G C) :
    SelfCausingGeneratedHaveAlternativeCause G C := by sorry
theorem reconstruction {Entity : Type u} [DecidableEq Entity] (G : Entity → Prop)
    (C : Entity → Entity → Prop) (hW : CausePrinciple G C)
    (hD : SelfCausingGeneratedHaveAlternativeCause G C) : DistinctCausePrinciple G C := by sorry
theorem equivalence : ExactDelta := by sorry
theorem separator : SelfOnlySeparates := by sorry
theorem mixedControl : MixedSelfAndOtherAllowed := by sorry
theorem noCauseControl : NoCauseDeltaControl := by sorry
theorem nonRestatementControl : DeltaNotConditionalRestatement := by sorry
end TruthCore.Results.Logic.StrengthCause
