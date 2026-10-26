import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question75.OrganOperation

namespace TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect

/-- Additional operation-attribution vocabulary for q.75 a.2 co. (31460).
The previous Model has only cognitive capacity; it cannot supply an operation
attributed to the principle itself. Operation indexes a kind of exercise, not
an assertion of a present thinking episode. BodyShares concerns participation
in that exercise, not object-side phantasms (ad 3, 31463). Inheres is specifically
inherence as accident or material form (ad 1–2, 31461–31462), not every dependence,
being a part, or the soul's being the form of the body in q.76 a.1. Complete
records completeness in a species, independently of this weak non-inherence. -/
structure OperationAttribution (Principle Operation : Type) where
  IntellectualExercise : Principle → Operation → Prop
  BodyShares : Operation → Prop
  InheresAsAccidentOrMaterialForm : Principle → Prop
  CompleteInSpecies : Principle → Prop

/-- Q.75 a.2 co.: an intellectual exercise attributed to the principle in
which body does not participate. Capacity and attribution remain distinct;
this existential is not inferred by the meanings of the previous predicates. -/
def PerSeIntellectualOperation {Principle Operation : Type}
    (a : OperationAttribution Principle Operation) (intellect : Principle) : Prop :=
  ∃ op, a.IntellectualExercise intellect op ∧ ¬ a.BodyShares op

/-- Subsistence in the first, incomplete-part-compatible sense of q.75 a.2
ad 1–2: exclusion of inherence as accident or material form. This does not
exclude being a part, assert completeness, or assert survival after death. -/
def SubsistsInWeakSense {Principle Operation : Type}
    (a : OperationAttribution Principle Operation) (intellect : Principle) : Prop :=
  ¬ a.InheresAsAccidentOrMaterialForm intellect

/-- The second sense of hoc aliquid in ad 1 additionally requires completeness
in a species. The result below never concludes this stronger proposition. -/
def SubsistsAsComplete {Principle Operation : Type}
    (a : OperationAttribution Principle Operation) (intellect : Principle) : Prop :=
  SubsistsInWeakSense a intellect ∧ a.CompleteInSpecies intellect

/-- Explicit attribution step at Ipsum igitur (31460): the non-body and
non-organ subconclusions yield an operation attributed to the principle itself,
without bodily participation. This source reading is an open conditional,
not a definition of intellectual operation or a proved consequence of absence
of an organ. Q.75 a.2 ad 2 qualifies attribution: more properly the human being
understands through the soul. -/
def NonorganicOperationAttribution {Principle Nature Operation : Type}
    (m : Model Principle Nature) (through : Principle → Principle → Prop)
    (a : OperationAttribution Principle Operation) (intellect : Principle) : Prop :=
  IntellectIsNotBody m intellect → IntellectUsesNoBodilyOrgan m through intellect →
    PerSeIntellectualOperation a intellect

/-- Q.75 a.2 co., Nihil autem potest per se operari, nisi quod per se subsistit,
restricted to intellectual exercise and the weak sense clarified in ad 1–2.
The operation/existence correspondence remains an open philosophical premise;
no causal or metaphysical explanation is hidden in the predicates. -/
def PerSeOperationRequiresSubsistence {Principle Operation : Type}
    (a : OperationAttribution Principle Operation) : Prop :=
  ∀ p, PerSeIntellectualOperation a p → SubsistsInWeakSense a p

end TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect
