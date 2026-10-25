import TruthCore.Comparison.Resurrection

/-! A formal-schema independence test, not a source interpretation or a
possible-world counterexample to Christian history. The skeleton's fields are
uninterpreted predicates. Even the pilot's independently stipulated
`authorityVindicated` imposes no institutional mandate or agency constraint.
No claim is made that a genuine divine attestation would have this meaning. -/
namespace TruthCore.Case.Catholicism.FoundingIndependence
open TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection

/-- Reuse the existing pilot model and its evidence/history assignments.
Only the two existing society predicates are populated so the antecedent is
nonvacuous. The model has no claim to satisfy unencoded theology. -/
def witness : State :=
  let s := model .risenEncounter true true true false false
  { s with core := { s.core with
      Founded := fun _ _ => True
      VisibleWithAuthority := fun _ => True } }

/-- Every existing report and reading bridge, the Catholic pilot bundle,
and the skeleton's local antecedents coexist with failure of its universal
founding bridge. This establishes only independence in the declared schema;
it neither denies historical founding nor refutes the full root theory. -/
def LocalInputsDoNotForceFounding : Prop :=
  ∃ s : State,
    (∀ r, Reported s r) ∧
    CrucifixionBridge s ∧ EarlyProclamationBridge s ∧ SincerityBridge s ∧
    PaulConversionBridge s ∧ JamesIdentityBeliefBridge s ∧ Catholic s ∧
    GodHasClassicalAttributes s.core ∧
    RevelationPossibleAndRecognizable s.core ∧
    ChristFoundedVisibleChurch s.core ∧
    ¬ BridgeChristsChurchFoundedByGod s.core
end TruthCore.Case.Catholicism.FoundingIndependence
