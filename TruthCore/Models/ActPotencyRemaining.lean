import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct.Solution

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.ActPotencyRemaining
open TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels
namespace S1
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.S1.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading (TruthCore.Models.ActPotencyRemaining.S1.model.Being) (TruthCore.Models.ActPotencyRemaining.S1.model.Respect) (TruthCore.Models.ActPotencyRemaining.S1.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.S1.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.S1.model.InAct) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩

theorem evaluation1 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotencyRemaining.S1.model.Being) (TruthCore.Models.ActPotencyRemaining.S1.model.Respect) (TruthCore.Models.ActPotencyRemaining.S1.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.S1.model.InAct)) := by intro hT; exact hT B.c B.b R.h trivial

end S1
namespace S2
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.S2.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.b ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B.c := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.k ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R.e := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.Respect) (TruthCore.Models.ActPotencyRemaining.S2.model.MovedIn) := by exact Exists.intro B.b (Exists.intro R.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.Respect) (TruthCore.Models.ActPotencyRemaining.S2.model.InAct) (TruthCore.Models.ActPotencyRemaining.S2.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.Respect) (TruthCore.Models.ActPotencyRemaining.S2.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.S2.model.InAct) := by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.Respect) (TruthCore.Models.ActPotencyRemaining.S2.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.S2.model.MovesIn) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.Respect) (TruthCore.Models.ActPotencyRemaining.S2.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.S2.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.Respect) (TruthCore.Models.ActPotencyRemaining.S2.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.S2.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.S2.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.Respect) (TruthCore.Models.ActPotencyRemaining.S2.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.S2.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.S2.model.InAct) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩

theorem evaluation8 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Models.ActPotencyRemaining.S2.model.Being) (TruthCore.Models.ActPotencyRemaining.S2.model.Respect) (TruthCore.Models.ActPotencyRemaining.S2.model.InAct) (TruthCore.Models.ActPotencyRemaining.S2.model.InPotency) (TruthCore.Models.ActPotencyRemaining.S2.model.PriorSimply)) := by
  intro hT
  obtain ⟨y, hy, _⟩ := hT B.c R.k trivial
  cases y <;> exact False.elim hy

end S2
namespace NSense
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.NSense.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.b := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.k := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotencyRemaining.NSense.model.Being) (TruthCore.Models.ActPotencyRemaining.NSense.model.Respect) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NSense.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading (TruthCore.Models.ActPotencyRemaining.NSense.model.Being) (TruthCore.Models.ActPotencyRemaining.NSense.model.Respect) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NSense.model.InAct) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotencyRemaining.NSense.model.Being) (TruthCore.Models.ActPotencyRemaining.NSense.model.Respect) (TruthCore.Models.ActPotencyRemaining.NSense.model.InAct) (TruthCore.Models.ActPotencyRemaining.NSense.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotencyRemaining.NSense.model.Being) (TruthCore.Models.ActPotencyRemaining.NSense.model.Respect) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotencyRemaining.NSense.model.Being) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverCannotBeLackingReading (TruthCore.Models.ActPotencyRemaining.NSense.model.Being) (TruthCore.Models.ActPotencyRemaining.NSense.model.Respect) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovesIn)) := by
  intro hC
  apply hC;intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotencyRemaining.NSense.model.Being) (TruthCore.Models.ActPotencyRemaining.NSense.model.Respect) (TruthCore.Models.ActPotencyRemaining.NSense.model.MovedIn)) := by
  intro hMissing
  apply evaluation5
  exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct.primaViaFromBeingInAct model.MovedIn model.MovesIn model.InPotency model.InAct model.MovesAsMoved hMissing evaluation0 evaluation1 evaluation2 evaluation3 evaluation4

end NSense
namespace NPotency
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.NPotency.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.b := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.k := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotencyRemaining.NPotency.model.Being) (TruthCore.Models.ActPotencyRemaining.NPotency.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovedIn) := by exact Exists.intro B2.a (Exists.intro R2.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading (TruthCore.Models.ActPotencyRemaining.NPotency.model.Being) (TruthCore.Models.ActPotencyRemaining.NPotency.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NPotency.model.InAct) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotencyRemaining.NPotency.model.Being) (TruthCore.Models.ActPotencyRemaining.NPotency.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPotency.model.InAct) (TruthCore.Models.ActPotencyRemaining.NPotency.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotencyRemaining.NPotency.model.Being) (TruthCore.Models.ActPotencyRemaining.NPotency.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotencyRemaining.NPotency.model.Being) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverCannotBeLackingReading (TruthCore.Models.ActPotencyRemaining.NPotency.model.Being) (TruthCore.Models.ActPotencyRemaining.NPotency.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovesIn)) := by
  intro hC
  apply hC;intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotencyRemaining.NPotency.model.Being) (TruthCore.Models.ActPotencyRemaining.NPotency.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPotency.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NPotency.model.InPotency)) := by
  intro hMissing
  apply evaluation5
  exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct.primaViaFromBeingInAct model.MovedIn model.MovesIn model.InPotency model.InAct model.MovesAsMoved evaluation0 hMissing evaluation1 evaluation2 evaluation3 evaluation4

end NPotency
namespace NReduction
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.NReduction.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.b := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.k := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotencyRemaining.NReduction.model.Being) (TruthCore.Models.ActPotencyRemaining.NReduction.model.Respect) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovedIn) := by exact Exists.intro B2.a (Exists.intro R2.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotencyRemaining.NReduction.model.Being) (TruthCore.Models.ActPotencyRemaining.NReduction.model.Respect) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NReduction.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotencyRemaining.NReduction.model.Being) (TruthCore.Models.ActPotencyRemaining.NReduction.model.Respect) (TruthCore.Models.ActPotencyRemaining.NReduction.model.InAct) (TruthCore.Models.ActPotencyRemaining.NReduction.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotencyRemaining.NReduction.model.Being) (TruthCore.Models.ActPotencyRemaining.NReduction.model.Respect) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotencyRemaining.NReduction.model.Being) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverCannotBeLackingReading (TruthCore.Models.ActPotencyRemaining.NReduction.model.Being) (TruthCore.Models.ActPotencyRemaining.NReduction.model.Respect) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovesIn)) := by
  intro hC
  apply hC;intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading (TruthCore.Models.ActPotencyRemaining.NReduction.model.Being) (TruthCore.Models.ActPotencyRemaining.NReduction.model.Respect) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NReduction.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NReduction.model.InAct)) := by
  intro hMissing
  apply evaluation5
  exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct.primaViaFromBeingInAct model.MovedIn model.MovesIn model.InPotency model.InAct model.MovesAsMoved evaluation0 evaluation1 hMissing evaluation2 evaluation3 evaluation4

end NReduction
namespace NNotBoth
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.NNotBoth.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.b := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.k := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Being) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Respect) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovedIn) := by exact Exists.intro B2.a (Exists.intro R2.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Being) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Respect) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Being) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Respect) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.InAct) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Being) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Respect) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Being) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverCannotBeLackingReading (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Being) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Respect) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.MovesIn)) := by
  intro hC
  apply hC;intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Being) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.Respect) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.InAct) (TruthCore.Models.ActPotencyRemaining.NNotBoth.model.InPotency)) := by
  intro hMissing
  apply evaluation5
  exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct.primaViaFromBeingInAct model.MovedIn model.MovesIn model.InPotency model.InAct model.MovesAsMoved evaluation0 evaluation1 evaluation2 hMissing evaluation3 evaluation4

end NNotBoth
namespace NPerSe
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.NPerSe.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.b := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.k := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Being) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovedIn) := by exact Exists.intro B2.a (Exists.intro R2.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Being) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Being) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.InAct) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Being) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.InAct) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Being) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovesAsMoved) := by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverCannotBeLackingReading (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Being) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovesIn)) := by
  intro hC
  apply hC;intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Being) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.Respect) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NPerSe.model.MovesAsMoved)) := by
  intro hMissing
  apply evaluation5
  exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct.primaViaFromBeingInAct model.MovedIn model.MovesIn model.InPotency model.InAct model.MovesAsMoved evaluation0 evaluation1 evaluation2 evaluation3 hMissing evaluation4

end NPerSe
namespace NRegress
def model := TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.NRegress.model
theorem enumerateBeing : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.B2.b := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateRespect : ∀ x : TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2, x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.h ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels.R2.k := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Models.ActPotencyRemaining.NRegress.model.Being) (TruthCore.Models.ActPotencyRemaining.NRegress.model.Respect) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovedIn) := by exact Exists.intro B2.a (Exists.intro R2.h trivial)

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Models.ActPotencyRemaining.NRegress.model.Being) (TruthCore.Models.ActPotencyRemaining.NRegress.model.Respect) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NRegress.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading (TruthCore.Models.ActPotencyRemaining.NRegress.model.Being) (TruthCore.Models.ActPotencyRemaining.NRegress.model.Respect) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NRegress.model.InAct) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Models.ActPotencyRemaining.NRegress.model.Being) (TruthCore.Models.ActPotencyRemaining.NRegress.model.Respect) (TruthCore.Models.ActPotencyRemaining.NRegress.model.InAct) (TruthCore.Models.ActPotencyRemaining.NRegress.model.InPotency) := by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Models.ActPotencyRemaining.NRegress.model.Being) (TruthCore.Models.ActPotencyRemaining.NRegress.model.Respect) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovesIn) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovesAsMoved) := by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverCannotBeLackingReading (TruthCore.Models.ActPotencyRemaining.NRegress.model.Being) (TruthCore.Models.ActPotencyRemaining.NRegress.model.Respect) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovedIn) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovesIn)) := by
  intro hC
  apply hC;intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial

theorem evaluation6 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Models.ActPotencyRemaining.NRegress.model.Being) (TruthCore.Models.ActPotencyRemaining.NRegress.model.MovesAsMoved)) := by
  intro hMissing
  apply evaluation5
  exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct.primaViaFromBeingInAct model.MovedIn model.MovesIn model.InPotency model.InAct model.MovesAsMoved evaluation0 evaluation1 evaluation2 evaluation3 evaluation4 hMissing

end NRegress
end TruthCore.Models.ActPotencyRemaining
