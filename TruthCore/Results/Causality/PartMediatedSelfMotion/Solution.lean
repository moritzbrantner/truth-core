module
public import TruthCore.Causality.PartMediatedSelfMotion
@[expose] public section
namespace TruthCore.Results.Causality.PartMediatedSelfMotion
open TruthCore.Causality.PartMediatedSelfMotion
open TruthCore.Causality.MotionMoverFork
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem localLift (moves : Carrier → Carrier → Respect → Prop)
    (h : LocalLift moves) : InternalHasDistinctMover moves := by
  intro w r hi
  cases hi with
  | intro a b ha hb he =>
    apply AnotherMover.intro a
    · rcases ha with ⟨hw, hm | hl⟩ <;> subst w <;> subst a <;> decide
    · exact h a b w r ha hb he

theorem controls : TruthCore.Causality.PartMediatedSelfMotion.Controls := by
  have hi : InternalMotion .whole .displacement :=
    .intro .motor .load ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inr rfl⟩ ⟨rfl, rfl, rfl⟩
  have hc : NothingMovesItselfInSameRespectReading ComponentMoved ComponentMoves := by
    intro x r hm hs
    rcases hs with ⟨ha, hb, hr⟩
    cases ha.symm.trans hb
  have hp : AnotherMover PatientLift .whole .displacement :=
    .intro .motor (by decide) ⟨.load, ⟨rfl, Or.inr rfl⟩, rfl, rfl, rfl⟩
  have hn : ¬ SomeMover ComponentMoves .whole .displacement := by
    intro h
    cases h with
    | intro a he => cases he.2.1
  have hag : ∀ a, AggregateLift a .whole .displacement → a = .whole := by
    intro a ⟨p, q, hpa, _, _⟩
    exact hpa.1
  refine ⟨hi, hc, .intro .motor (by decide) ⟨rfl, rfl, rfl⟩, hp, ?_, hn, ?_, ?_, ?_, ?_⟩
  · intro ⟨a, he, b, hb, hab⟩
    apply he
    exact ⟨rfl, Or.inl hab.1⟩
  · intro h
    exact h .whole .displacement ⟨rfl, rfl⟩
      ⟨.motor, .load, ⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, rfl, rfl, rfl⟩
  · intro h
    cases h .whole .displacement hi with
    | intro a _ he => exact hn (.intro a he)
  · intro h
    cases h .whole .displacement hi with
    | intro a ne he => exact ne (hag a he)
  · intro h
    cases h with
    | intro a b _ _ he => cases he.2.2
end TruthCore.Results.Causality.PartMediatedSelfMotion
