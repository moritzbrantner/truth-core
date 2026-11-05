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
  rcases hEM (∃ x r, ¬ (InPotency x r ↔ CanBe x r ∧ ¬ InAct x r)) with ⟨x, r, hFail⟩ | hNone
  · right
    rcases hEM (InPotency x r) with hPot | hNotPot
    · rcases hEM (CanBe x r) with hCan | hNotCan
      · rcases hEM (InAct x r) with hAct | hNotAct
        · exact Or.inl ⟨x, r, hPot, hAct⟩
        · exact absurd ⟨fun _ => ⟨hCan, hNotAct⟩, fun _ => hPot⟩ hFail
      · exact Or.inr (Or.inl ⟨x, r, hPot, hNotCan⟩)
    · rcases hEM (CanBe x r ∧ ¬ InAct x r) with hCap | hNoCap
      · exact Or.inr (Or.inr ⟨x, r, hCap.1, hCap.2, hNotPot⟩)
      · exact absurd ⟨fun h => absurd h hNotPot, fun h => absurd h hNoCap⟩ hFail
  · left
    intro x r
    rcases hEM (InPotency x r ↔ CanBe x r ∧ ¬ InAct x r) with h | h
    · exact h
    · exact absurd ⟨x, r, h⟩ hNone

/-- The cells are exactly ¬F7 territory: each of them contradicts F7. -/
theorem cellsDenyF7 {Being Respect : Type} (InAct InPotency CanBe : Being → Respect → Prop)
    (hCell : PotencyWithActCell InAct InPotency ∨ PotencyWithoutCapacityCell InPotency CanBe ∨
      UnexercisedCapacityWithoutPotencyCell InAct InPotency CanBe) :
    ¬ PotencyIsUnactualizedCapacityReading InAct InPotency CanBe := by
  intro hF7
  rcases hCell with ⟨x, r, hPot, hAct⟩ | ⟨x, r, hPot, hNotCan⟩ | ⟨x, r, hCan, hNotAct, hNotPot⟩
  · exact ((hF7 x r).mp hPot).2 hAct
  · exact hNotCan ((hF7 x r).mp hPot).1
  · exact hNotPot ((hF7 x r).mpr ⟨hCan, hNotAct⟩)

/-- What a floor would need: F7 is equivalent to the conjunction of the three
constraints that exclude cells (a), (b) and (c). So any floor that defeats
every ¬F7 cell entails F7 itself. Constructive. -/
theorem f7IffCellConstraints {Being Respect : Type} (InAct InPotency CanBe : Being → Respect → Prop) :
    PotencyIsUnactualizedCapacityReading InAct InPotency CanBe ↔
      NotActAndPotencyInSameRespectReading InAct InPotency ∧ PotencyImpliesCapacity InPotency CanBe ∧
        UnexercisedCapacityIsPotency InAct InPotency CanBe := by
  constructor
  · intro hF7
    exact ⟨fun x r h => ((hF7 x r).mp h.2).2 h.1, fun x r h => ((hF7 x r).mp h).1,
      fun x r h => (hF7 x r).mpr h⟩
  · rintro ⟨hNonSimul, hCap, hUnex⟩ x r
    exact ⟨fun h => ⟨hCap x r h, fun hAct => hNonSimul x r ⟨hAct, h⟩⟩, hUnex x r⟩

/-- Each ¬F7 cell has an interpretation in which something is moved (F4), on
one being and one respect. -/
theorem cellsSurviveFloor : CellsSurviveFloor := by
  refine ⟨⟨Unit, Unit, fun _ _ => True, fun _ _ => True, fun _ _ => True, ⟨(), (), trivial, trivial⟩, (), (), trivial⟩,
    ⟨Unit, Unit, fun _ _ => True, fun _ _ => False, fun _ _ => True, ⟨(), (), trivial, fun h => h⟩, (), (), trivial⟩,
    ⟨Unit, Unit, fun _ _ => False, fun _ _ => False, fun _ _ => True, fun _ _ => True,
      ⟨(), (), trivial, fun h => h, fun h => h⟩, (), (), trivial⟩⟩
end TruthCore.Results.Alternatives.PotencyAnalysisPartition
