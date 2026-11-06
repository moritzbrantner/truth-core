module
public import TruthCore.Refutations.Emotivism

/-! Invariant sentence meaning and occasion-attitude meaning can coexist.
Actual loss/change of an expressed attitude plus moral population supplies
the missing discrimination; source predicates retain their exact meanings. -/
@[expose] public section
namespace TruthCore.Metaethics.MeaningRivalBoundary
open TruthCore.English.VanRoojen
open TruthCore.Refutations.Emotivism

def Controls : Prop :=
  (∃ (Moral : Unit → Prop) (meaning : Unit → Bool → Unit)
      (Expresses : Unit → Bool → Unit → Prop),
    Moral () ∧ ExpressivistMoralMeaningInvariantReading Moral meaning ∧
    EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses ∧
    Expresses () true () ∧ Expresses () false ()) ∧
  (∃ (Moral : Unit → Prop) (meaning : Unit → Bool → Unit)
      (Expresses : Unit → Bool → Unit → Prop),
    Moral () ∧ ExpressivistMoralMeaningInvariantReading Moral meaning ∧
    FreeMoralAssertionExpressesAttitudeReading Moral Expresses true ∧
    AntecedentLacksFreeStandingAttitudeReading Expresses true false () ∧
    Expresses () true () ∧ ¬ Expresses () false () ∧
    EmotivistMeaningFails Moral meaning Expresses)
end TruthCore.Metaethics.MeaningRivalBoundary
