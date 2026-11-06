module

public import TruthCore.Refutations.QuasiRealism

/-! Exact rival to the existing universal realist explanatory-order reading.
Opposite directions alone do not imply incompatibility: the separately OPEN
asymmetry premise and populated moral scope must be retained. No new meaning
of actual explanation, grounding or historical theory is introduced. -/
@[expose] public section
namespace TruthCore.Metaethics.ExplanationRivalBoundary
open TruthCore.English.VanRoojen
open TruthCore.Refutations.QuasiRealism

def NotRealistOrder {Sentence : Type}
    (Moral TruthExplainsTalk : Sentence → Prop) : Prop :=
  ¬ RealistOrderOfExplanationReading Moral TruthExplainsTalk

/-- Exact controls: both directions on populated scope without asymmetry;
both vacuously with asymmetry on empty scope; neither direction on populated
scope with asymmetry. These are predicate models, not full worldviews. -/
def Controls : Prop :=
  (∃ Moral TalkToTruth TruthToTalk : Unit → Prop,
    GeachMinorPremiseIsMoralReading Moral () ∧
    AntirealistOrderOfExplanationReading Moral TalkToTruth ∧
    RealistOrderOfExplanationReading Moral TruthToTalk ∧
    ¬ ExplanatoryOrderAsymmetric Moral TalkToTruth TruthToTalk) ∧
  (∃ Moral TalkToTruth TruthToTalk : Unit → Prop,
    (∀ s, ¬ Moral s) ∧ ExplanatoryOrderAsymmetric Moral TalkToTruth TruthToTalk ∧
    AntirealistOrderOfExplanationReading Moral TalkToTruth ∧
    RealistOrderOfExplanationReading Moral TruthToTalk) ∧
  (∃ Moral TalkToTruth TruthToTalk : Unit → Prop,
    GeachMinorPremiseIsMoralReading Moral () ∧
    ExplanatoryOrderAsymmetric Moral TalkToTruth TruthToTalk ∧
    ¬ AntirealistOrderOfExplanationReading Moral TalkToTruth ∧
    NotRealistOrder Moral TruthToTalk)

end TruthCore.Metaethics.ExplanationRivalBoundary
