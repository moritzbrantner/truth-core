import TruthCore.Alternatives.PotencyAnalysisPartition
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Alternatives.PotencyAnalysisPartition
open TruthCore.Alternatives.PotencyAnalysisPartition
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic

/-- Exhaustiveness of the Q-F7 partition from excluded middle alone (#1007):
every interpretation satisfies F7 or lies in one of the three ¬F7 cells. No
list of worldviews enters. -/
theorem partition {Being Respect : Type} (hEM : ExcludedMiddle)
    (InAct InPotency CanBe : Being → Respect → Prop) :
    PotencyAnalysisPartition InAct InPotency CanBe := by
  sorry

/-- The cells are exactly ¬F7 territory: each of them contradicts F7. -/
theorem cellsDenyF7 {Being Respect : Type} (InAct InPotency CanBe : Being → Respect → Prop)
    (hCell : PotencyWithActCell InAct InPotency ∨ PotencyWithoutCapacityCell InPotency CanBe ∨
      UnexercisedCapacityWithoutPotencyCell InAct InPotency CanBe) :
    ¬ PotencyIsUnactualizedCapacityReading InAct InPotency CanBe := by
  sorry

/-- What a floor would need: F7 is equivalent to the conjunction of the three
constraints that exclude cells (a), (b) and (c). So any floor that defeats
every ¬F7 cell entails F7 itself. Constructive. -/
theorem f7IffCellConstraints {Being Respect : Type} (InAct InPotency CanBe : Being → Respect → Prop) :
    PotencyIsUnactualizedCapacityReading InAct InPotency CanBe ↔
      NotActAndPotencyInSameRespectReading InAct InPotency ∧ PotencyImpliesCapacity InPotency CanBe ∧
        UnexercisedCapacityIsPotency InAct InPotency CanBe := by
  sorry

/-- Each ¬F7 cell has an interpretation in which something is moved (F4), on
one being and one respect. -/
theorem cellsSurviveFloor : CellsSurviveFloor := by
  sorry
end TruthCore.Results.Alternatives.PotencyAnalysisPartition
