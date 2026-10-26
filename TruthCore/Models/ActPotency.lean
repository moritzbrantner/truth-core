import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.ActPotency
open TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels
namespace M1
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.M1.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.InAct) (TruthCore.Models.ActPotency.M1.model.esse) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.InAct) (TruthCore.Models.ActPotency.M1.model.InPotency) (TruthCore.Models.ActPotency.M1.model.PriorSimply) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.GoodIn) (TruthCore.Models.ActPotency.M1.model.InAct) := by intro x r; exact Iff.rfl

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.MovesIn) (TruthCore.Models.ActPotency.M1.model.InAct) := by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.MovedIn) (TruthCore.Models.ActPotency.M1.model.MovesIn) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.MovedIn) (TruthCore.Models.ActPotency.M1.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation8 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.MovedIn) (TruthCore.Models.ActPotency.M1.model.MovesIn) (TruthCore.Models.ActPotency.M1.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation9 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotency.M1.model.Being) (TruthCore.Models.ActPotency.M1.model.Respect) (TruthCore.Models.ActPotency.M1.model.InAct) (TruthCore.Models.ActPotency.M1.model.InPotency)) := by
  intro hT
  exact hT B.b R.h ⟨trivial, trivial⟩

end M1
namespace M2
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.M2.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.InAct) (TruthCore.Models.ActPotency.M2.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.InAct) (TruthCore.Models.ActPotency.M2.model.InPotency) (TruthCore.Models.ActPotency.M2.model.PriorSimply) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.GoodIn) (TruthCore.Models.ActPotency.M2.model.InAct) := by intro x r; exact Iff.rfl

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.MovesIn) (TruthCore.Models.ActPotency.M2.model.InAct) := by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.MovedIn) (TruthCore.Models.ActPotency.M2.model.MovesIn) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.MovedIn) (TruthCore.Models.ActPotency.M2.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation8 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.MovedIn) (TruthCore.Models.ActPotency.M2.model.MovesIn) (TruthCore.Models.ActPotency.M2.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation9 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading (TruthCore.Models.ActPotency.M2.model.Being) (TruthCore.Models.ActPotency.M2.model.Respect) (TruthCore.Models.ActPotency.M2.model.InAct) (TruthCore.Models.ActPotency.M2.model.esse)) := by
  intro hT
  exact hT B.a R.h trivial

end M2
namespace M3
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.M3.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.InAct) (TruthCore.Models.ActPotency.M3.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.InAct) (TruthCore.Models.ActPotency.M3.model.esse) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.GoodIn) (TruthCore.Models.ActPotency.M3.model.InAct) := by intro x r; exact Iff.rfl

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.MovesIn) (TruthCore.Models.ActPotency.M3.model.InAct) := by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.MovedIn) (TruthCore.Models.ActPotency.M3.model.MovesIn) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.MovedIn) (TruthCore.Models.ActPotency.M3.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation8 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.MovedIn) (TruthCore.Models.ActPotency.M3.model.MovesIn) (TruthCore.Models.ActPotency.M3.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation9 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotency.M3.model.Being) (TruthCore.Models.ActPotency.M3.model.Respect) (TruthCore.Models.ActPotency.M3.model.InAct) (TruthCore.Models.ActPotency.M3.model.InPotency) (TruthCore.Models.ActPotency.M3.model.PriorSimply)) := by
  intro hT
  obtain ⟨y, hy, hp⟩ := hT B.b R.h trivial; cases y <;> first | exact False.elim hy | exact False.elim hp

end M3
namespace M4
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.M4.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.InAct) (TruthCore.Models.ActPotency.M4.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.InAct) (TruthCore.Models.ActPotency.M4.model.esse) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.InAct) (TruthCore.Models.ActPotency.M4.model.InPotency) (TruthCore.Models.ActPotency.M4.model.PriorSimply) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.MovesIn) (TruthCore.Models.ActPotency.M4.model.InAct) := by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.MovedIn) (TruthCore.Models.ActPotency.M4.model.MovesIn) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.MovedIn) (TruthCore.Models.ActPotency.M4.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation8 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.MovedIn) (TruthCore.Models.ActPotency.M4.model.MovesIn) (TruthCore.Models.ActPotency.M4.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation9 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading (TruthCore.Models.ActPotency.M4.model.Being) (TruthCore.Models.ActPotency.M4.model.Respect) (TruthCore.Models.ActPotency.M4.model.GoodIn) (TruthCore.Models.ActPotency.M4.model.InAct)) := by
  intro hT
  exact (hT B.a R.h).mpr trivial

end M4
namespace M5
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.M5.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.InAct) (TruthCore.Models.ActPotency.M5.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.InAct) (TruthCore.Models.ActPotency.M5.model.esse) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.InAct) (TruthCore.Models.ActPotency.M5.model.InPotency) (TruthCore.Models.ActPotency.M5.model.PriorSimply) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.GoodIn) (TruthCore.Models.ActPotency.M5.model.InAct) := by intro x r; exact Iff.rfl

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.MovedIn) (TruthCore.Models.ActPotency.M5.model.MovesIn) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.MovedIn) (TruthCore.Models.ActPotency.M5.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation8 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.MovedIn) (TruthCore.Models.ActPotency.M5.model.MovesIn) (TruthCore.Models.ActPotency.M5.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation9 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotency.M5.model.Being) (TruthCore.Models.ActPotency.M5.model.Respect) (TruthCore.Models.ActPotency.M5.model.MovesIn) (TruthCore.Models.ActPotency.M5.model.InAct)) := by
  intro hT
  exact hT B.a B.b R.h trivial

end M5
namespace M6
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.M6.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.InAct) (TruthCore.Models.ActPotency.M6.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.InAct) (TruthCore.Models.ActPotency.M6.model.esse) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.InAct) (TruthCore.Models.ActPotency.M6.model.InPotency) (TruthCore.Models.ActPotency.M6.model.PriorSimply) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.GoodIn) (TruthCore.Models.ActPotency.M6.model.InAct) := by intro x r; exact Iff.rfl

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.MovesIn) (TruthCore.Models.ActPotency.M6.model.InAct) := by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.MovedIn) (TruthCore.Models.ActPotency.M6.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation8 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.MovedIn) (TruthCore.Models.ActPotency.M6.model.MovesIn) (TruthCore.Models.ActPotency.M6.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation9 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotency.M6.model.Being) (TruthCore.Models.ActPotency.M6.model.Respect) (TruthCore.Models.ActPotency.M6.model.MovedIn) (TruthCore.Models.ActPotency.M6.model.MovesIn)) := by
  intro hT
  obtain ⟨y, hy⟩ := hT B.b R.h trivial; cases y <;> exact False.elim hy

end M6
namespace M7
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.M7.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.InAct) (TruthCore.Models.ActPotency.M7.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.InAct) (TruthCore.Models.ActPotency.M7.model.esse) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.InAct) (TruthCore.Models.ActPotency.M7.model.InPotency) (TruthCore.Models.ActPotency.M7.model.PriorSimply) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.GoodIn) (TruthCore.Models.ActPotency.M7.model.InAct) := by intro x r; exact Iff.rfl

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.MovesIn) (TruthCore.Models.ActPotency.M7.model.InAct) := by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.MovedIn) (TruthCore.Models.ActPotency.M7.model.MovesIn) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩

theorem evaluation8 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.MovedIn) (TruthCore.Models.ActPotency.M7.model.MovesIn) (TruthCore.Models.ActPotency.M7.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation9 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotency.M7.model.Being) (TruthCore.Models.ActPotency.M7.model.Respect) (TruthCore.Models.ActPotency.M7.model.MovedIn) (TruthCore.Models.ActPotency.M7.model.InPotency)) := by
  intro hT
  exact hT B.b R.h trivial

end M7
namespace M8
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.M8.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.InAct) (TruthCore.Models.ActPotency.M8.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.InAct) (TruthCore.Models.ActPotency.M8.model.esse) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.InAct) (TruthCore.Models.ActPotency.M8.model.InPotency) (TruthCore.Models.ActPotency.M8.model.PriorSimply) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.GoodIn) (TruthCore.Models.ActPotency.M8.model.InAct) := by intro x r; exact Iff.rfl

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.MovesIn) (TruthCore.Models.ActPotency.M8.model.InAct) := by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.MovedIn) (TruthCore.Models.ActPotency.M8.model.MovesIn) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩

theorem evaluation8 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.MovedIn) (TruthCore.Models.ActPotency.M8.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation9 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotency.M8.model.Being) (TruthCore.Models.ActPotency.M8.model.Respect) (TruthCore.Models.ActPotency.M8.model.MovedIn) (TruthCore.Models.ActPotency.M8.model.MovesIn) (TruthCore.Models.ActPotency.M8.model.MovesAsMoved)) := by
  intro hT
  exact hT B.a B.b R.h (fun h => nomatch h) trivial ⟨R.k, trivial⟩

end M8
end TruthCore.Models.ActPotency
