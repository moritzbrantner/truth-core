import TruthCore.Logic.Strength.Order
namespace TruthCore.Results.Logic.StrengthOrder
open TruthCore.Logic.Strength.Order
universe u
theorem implication {α : Type u} [LinearOrder α] (x y : α) (hS : Strict x y) : Weak x y := by sorry
theorem deltaForward {α : Type u} [LinearOrder α] (x y : α) (hS : Strict x y) : Unequal x y := by sorry
theorem reconstruction {α : Type u} [LinearOrder α] (x y : α) (hW : Weak x y) (hD : Unequal x y) : Strict x y := by sorry
theorem equivalence : ExactDelta := by sorry
theorem allowedCases : AllowedCasesLaw := by sorry
theorem remainderIdentity : RemainderLaw := by sorry
theorem separator : ZeroSeparates := by sorry
end TruthCore.Results.Logic.StrengthOrder
