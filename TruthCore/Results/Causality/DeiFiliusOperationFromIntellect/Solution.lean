module

public import TruthCore.Causality.DeiFiliusOperationFromIntellect

/-! The nine's immanent operation derived from intellect as a capacity to
understand, the exercise-or-potency of that capacity, understanding as immanent
operation, and pure act. Analyst formulations, attribution deferred. No premise
is established. -/

@[expose] public section

namespace TruthCore.Results.Causality.DeiFiliusOperationFromIntellect

open TruthCore.Causality.DeiFiliusOperationFromIntellect
open TruthCore.Causality.DeiFiliusLivingNineScope
open TruthCore.Causality.SelfOperationLife
open TruthCore.Causality.TermSenseForks (CapacityPotency)
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)
open TruthCore.Case.Catholicism

/-- Every pure act with intellect has an immanent operation: its intellect is a
capacity to understand; that capacity is exercised or a potency to understanding;
a pure act is in potency in no respect, so it is actually understanding; and an
exercised capacity to understand is an immanent operation. -/
theorem intellectualPureActOperatesFromCapacity {Being Respect : Type}
    (InAct InPotency CanBe : Being → Respect → Prop) (understanding : Respect)
    (HasIntellect Operates : Being → Prop)
    (hCapacity : IntellectIsCapacityToUnderstand HasIntellect CanBe understanding)
    (hExercise : UnderstandingCapacityExercisedOrInPotency InAct InPotency CanBe understanding)
    (hImmanent : ExercisedUnderstandingIsImmanentOperation InAct CanBe understanding Operates) :
    IntellectualPureActOperates InPotency HasIntellect Operates := by
  intro x hPure hIntellect
  have hCap := hCapacity x hIntellect
  rcases hExercise x hCap with hAct | hPot
  · exact hImmanent x hCap hAct
  · exact absurd hPot (hPure understanding)

/-- Strength order: every pure act with intellect operates, so whatever has the
nine operates (the nine include altogether immutability, which is pure act, and
intellect). -/
theorem nineOperateOfIntellectualPureActOperates {Being Respect : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (Operates : Being → Prop)
    (hMiddle : IntellectualPureActOperates InPotency HasIntellect Operates) :
    NineOperate InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
      HasIntellect HasWill Operates :=
  fun g h => hMiddle g h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1

/-- Strength order: every pure act operates, so every pure act with intellect
operates. -/
theorem intellectualPureActOperatesOfPureActOperates {Being Respect : Type}
    (InPotency : Being → Respect → Prop) (HasIntellect Operates : Being → Prop)
    (hStrong : PureActOperates InPotency Operates) :
    IntellectualPureActOperates InPotency HasIntellect Operates :=
  fun x hPure _ => hStrong x hPure

/-- Not registered: under the adopted sense of potency (capable and not actually),
the exercise-or-potency premise follows from excluded middle for actually
understanding at capable beings, constructively. -/
theorem exercisedOrInPotencyOfDecidable {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop) (understanding : Respect)
    (hEM : ∀ x, CanBe x understanding → InAct x understanding ∨ ¬ InAct x understanding) :
    UnderstandingCapacityExercisedOrInPotency InAct
      (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)
      CanBe understanding := by
  intro x hCap
  rcases hEM x hCap with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hCap, h⟩

open TruthCore.Causality.DeiFiliusLivingNineScope.Control

/-- The controls of `DeiFiliusOperationFromIntellect`, checked. -/
theorem controls : TruthCore.Causality.DeiFiliusOperationFromIntellect.Control.Controls := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  -- part 1
  · intro _ h; exact absurd h id
  · intro _ h; exact absurd h id
  · intro h; exact h true rfl
  · exact ⟨id, fun _ _ h => h, ⟨trivial, fun _ _ _ _ => trivial⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩
  · intro h; exact h true ⟨id, fun _ _ h => h, ⟨trivial, fun _ _ _ _ => trivial⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩
  -- part 2
  · intro _ _; trivial
  · intro _ _ h; exact h
  · intro h; rcases h true trivial with h | h <;> exact h
  · exact ⟨id, fun _ _ h => absurd h id, ⟨trivial, fun _ _ _ h => absurd h id⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩
  · intro h; exact h true ⟨id, fun _ _ h => absurd h id, ⟨trivial, fun _ _ _ h => absurd h id⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩
  -- part 3
  · intro _ _; trivial
  · intro _ _; exact Or.inl trivial
  · intro h; exact h true trivial trivial
  · exact ⟨id, fun _ _ h => h, ⟨trivial, fun _ _ _ _ => trivial⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩
  · intro h; exact h true ⟨id, fun _ _ h => h, ⟨trivial, fun _ _ _ _ => trivial⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩
  -- part 4
  · intro _ h; exact h
  · intro _ _; exact Or.inl trivial
  · intro _ h _; exact h
  · exact ⟨id, fun _ _ h => h, ⟨trivial, fun _ _ _ _ => trivial⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩
  -- part 5
  · exact ⟨id, fun _ _ h => h, ⟨trivial, fun _ _ _ _ => trivial⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩
  · rfl
  · intro ⟨_, h⟩; exact h
  · intro h; exact h
  -- part 6
  · intro _ _ h; exact h
  · intro h; exact Bool.false_ne_true (h false (fun _ h => h))
  -- part 7
  · intro g h; exact (h.2.2.2.1 true rfl).symm
  · intro h; exact Bool.false_ne_true (h false (fun _ h => h) trivial)

end TruthCore.Results.Causality.DeiFiliusOperationFromIntellect
