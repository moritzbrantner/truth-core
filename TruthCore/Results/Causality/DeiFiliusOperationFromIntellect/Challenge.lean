import TruthCore.Causality.DeiFiliusOperationFromIntellect

/-! The nine's immanent operation derived from intellect as a capacity to
understand, the exercise-or-potency of that capacity, understanding as immanent
operation, and pure act. Analyst formulations, attribution deferred. No premise
is established. -/

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
  sorry

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
      HasIntellect HasWill Operates := by
  sorry

/-- Strength order: every pure act operates, so every pure act with intellect
operates. -/
theorem intellectualPureActOperatesOfPureActOperates {Being Respect : Type}
    (InPotency : Being → Respect → Prop) (HasIntellect Operates : Being → Prop)
    (hStrong : PureActOperates InPotency Operates) :
    IntellectualPureActOperates InPotency HasIntellect Operates := by
  sorry

open TruthCore.Causality.DeiFiliusLivingNineScope.Control

/-- The controls of `DeiFiliusOperationFromIntellect`, checked. -/
theorem controls : TruthCore.Causality.DeiFiliusOperationFromIntellect.Control.Controls := by
  sorry

end TruthCore.Results.Causality.DeiFiliusOperationFromIntellect
