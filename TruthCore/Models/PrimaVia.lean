import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.PrimaVia

namespace Strong
def model := TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel
theorem enumerateBeing : ∀ x : TruthCore.Models.PrimaVia.Strong.model.Being, x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.StrongBeing.g ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.StrongBeing.f ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.StrongBeing.x := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Models.PrimaVia.Strong.model.Respect, x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.StrongRespect.heat ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.StrongRespect.other := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.PrimaVia.Strong.model.Being) (TruthCore.Models.PrimaVia.Strong.model.Respect) (TruthCore.Models.PrimaVia.Strong.model.MovedIn) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel_premises.1

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.PrimaVia.Strong.model.Being) (TruthCore.Models.PrimaVia.Strong.model.Respect) (TruthCore.Models.PrimaVia.Strong.model.MovedIn) (TruthCore.Models.PrimaVia.Strong.model.InPotency) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel_premises.2.1

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.PrimaVia.Strong.model.Being) (TruthCore.Models.PrimaVia.Strong.model.Respect) (TruthCore.Models.PrimaVia.Strong.model.MovesIn) (TruthCore.Models.PrimaVia.Strong.model.InAct) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel_premises.2.2.1

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.PrimaVia.Strong.model.Being) (TruthCore.Models.PrimaVia.Strong.model.Respect) (TruthCore.Models.PrimaVia.Strong.model.MovedIn) (TruthCore.Models.PrimaVia.Strong.model.MovesIn) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel_premises.2.2.2.1

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.PrimaVia.Strong.model.Being) (TruthCore.Models.PrimaVia.Strong.model.Respect) (TruthCore.Models.PrimaVia.Strong.model.InAct) (TruthCore.Models.PrimaVia.Strong.model.InPotency) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel_premises.2.2.2.2.1

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.PrimaVia.Strong.model.Being) (TruthCore.Models.PrimaVia.Strong.model.Respect) (TruthCore.Models.PrimaVia.Strong.model.MovedIn) (TruthCore.Models.PrimaVia.Strong.model.MovesIn) (TruthCore.Models.PrimaVia.Strong.model.MovesAsMoved) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel_premises.2.2.2.2.2.1

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.PrimaVia.Strong.model.Being) (TruthCore.Models.PrimaVia.Strong.model.MovesAsMoved) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel_premises.2.2.2.2.2.2

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverCannotBeLackingReading (TruthCore.Models.PrimaVia.Strong.model.Being) (TruthCore.Models.PrimaVia.Strong.model.Respect) (TruthCore.Models.PrimaVia.Strong.model.MovedIn) (TruthCore.Models.PrimaVia.Strong.model.MovesIn) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongReadingYields model TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.strongModel_premises

end Strong
namespace Weak
def model := TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel
theorem enumerateBeing : ∀ x : TruthCore.Models.PrimaVia.Weak.model.Being, x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.WeakBeing.f ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.WeakBeing.g ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.WeakBeing.x := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Models.PrimaVia.Weak.model.Respect, x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.WeakRespect.heat ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.WeakRespect.other ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.WeakRespect.other2 := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.PrimaVia.Weak.model.Being) (TruthCore.Models.PrimaVia.Weak.model.Respect) (TruthCore.Models.PrimaVia.Weak.model.MovedIn) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel_premises.1

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.PrimaVia.Weak.model.Being) (TruthCore.Models.PrimaVia.Weak.model.Respect) (TruthCore.Models.PrimaVia.Weak.model.MovedIn) (TruthCore.Models.PrimaVia.Weak.model.InPotency) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel_premises.2.1

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.PrimaVia.Weak.model.Being) (TruthCore.Models.PrimaVia.Weak.model.Respect) (TruthCore.Models.PrimaVia.Weak.model.MovesIn) (TruthCore.Models.PrimaVia.Weak.model.InAct) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel_premises.2.2.1

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.PrimaVia.Weak.model.Being) (TruthCore.Models.PrimaVia.Weak.model.Respect) (TruthCore.Models.PrimaVia.Weak.model.MovedIn) (TruthCore.Models.PrimaVia.Weak.model.MovesIn) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel_premises.2.2.2.1

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.PrimaVia.Weak.model.Being) (TruthCore.Models.PrimaVia.Weak.model.Respect) (TruthCore.Models.PrimaVia.Weak.model.InAct) (TruthCore.Models.PrimaVia.Weak.model.InPotency) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel_premises.2.2.2.2.1

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveAsMovedInRelevantRespectReading (TruthCore.Models.PrimaVia.Weak.model.Being) (TruthCore.Models.PrimaVia.Weak.model.Respect) (TruthCore.Models.PrimaVia.Weak.model.MovedIn) (TruthCore.Models.PrimaVia.Weak.model.MovesIn) (TruthCore.Models.PrimaVia.Weak.model.MovesAsMoved) (TruthCore.Models.PrimaVia.Weak.model.RelevantTo) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel_premises.2.2.2.2.2.1

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.PrimaVia.Weak.model.Being) (TruthCore.Models.PrimaVia.Weak.model.MovesAsMoved) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel_premises.2.2.2.2.2.2

theorem evaluation7 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverCannotBeLackingReading (TruthCore.Models.PrimaVia.Weak.model.Being) (TruthCore.Models.PrimaVia.Weak.model.Respect) (TruthCore.Models.PrimaVia.Weak.model.MovedIn) (TruthCore.Models.PrimaVia.Weak.model.MovesIn)) := by exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels.weakModel_no_unmoved_mover

end Weak
end TruthCore.Models.PrimaVia
