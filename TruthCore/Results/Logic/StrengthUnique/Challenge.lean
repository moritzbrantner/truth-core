import TruthCore.Logic.Strength.UniqueExistence
namespace TruthCore.Results.Logic.StrengthUnique
open TruthCore.Logic.Strength.UniqueExistence
universe u
theorem implication {α : Type u} (P : α → Prop) (hS : Unique P) : TruthCore.Logic.Strength.UniqueExistence.Exists P := by sorry
theorem deltaForward {α : Type u} (P : α → Prop) (hS : Unique P) : AtMostOne P := by sorry
theorem reconstruction {α : Type u} (P : α → Prop) (hW : TruthCore.Logic.Strength.UniqueExistence.Exists P) (hD : AtMostOne P) : Unique P := by sorry
theorem equivalence : ExactDelta := by sorry
theorem separator : TwoPointsSeparate := by sorry
end TruthCore.Results.Logic.StrengthUnique
