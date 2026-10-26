import TruthCore.Logic.Relativism
namespace TruthCore.Results.Aristotle.Metaphysics.ExemptionRegress
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Relativism
/-- Aristotle's cost of exemption (*Metaphysics* IV.8, 1012b18-22): whoever
holds that nothing in scope is absolutely true, yet exempts an absolutely true
thesis, must exempt every truth-ascent iterate of it as well, given that the
statement that a truth is true is itself true. -/
theorem exemptionRegress {Agent Content : Type} (T : TruthSemantics Agent Content)
    (scope : Content → Prop) (trueOf : Content → Content) (thesis : Content)
    (hThesis : NoAbsoluteTruth T scope) (hTrue : ExemptedThesisAbsolutelyTrue T thesis)
    (hAscent : TruthAscent T trueOf) : ExemptionRegress scope trueOf thesis := by
  have hIter : ∀ n : Nat, T.trueAbs (Nat.repeat trueOf n thesis) := by
    intro n
    induction n with
    | zero => exact hTrue
    | succ n ih => exact hAscent _ ih
  intro n hScope
  exact hThesis _ hScope (hIter n)
end TruthCore.Results.Aristotle.Metaphysics.ExemptionRegress
