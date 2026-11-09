module

/-! Analyst formulation, attribution deferred. Shared necessary conditions for
completed cognitive replacement. This is deliberately not the binding of
CORRECTION_2: same-matter and cross-matter replacement remain distinct options.
The supplied history describes actual endorsement, not possible belief; Before
is actual strict temporal precedence, and Correct is a supplied judgment norm.
Neither correctness nor temporal precedence is certified by a report/criterion.
-/

@[expose] public section
namespace TruthCore.Logic.CognitiveReplacement

/-- An actual later endorsement replaces an earlier erroneous endorsement by
this subject only if the old endorsement is withdrawn. `Replaces` supplies the
interpretive link between the two judgments (e.g. revision on the same matter);
it cannot alone make a transition qualify. Correctness is relative to the
supplied norm at each endpoint. No truth, warrant, authority, causation,
permanence, exclusivity of other beliefs, or need-to-accomplishment is inferred.
This is a common core pending the original sense's replacement-scope decision. -/
def ReplacementConditions {Subject Judgment Time : Type}
    (Before : Time → Time → Prop)
    (Endorses : Subject → Judgment → Time → Prop)
    (Correct : Judgment → Time → Prop)
    (Replaces : Subject → Judgment → Judgment → Prop)
    (subject : Subject) (old new : Judgment) (earlier later : Time) : Prop :=
  Before earlier later ∧ Replaces subject old new ∧
  Endorses subject old earlier ∧ ¬ Correct old earlier ∧
  ¬ Endorses subject old later ∧ Endorses subject new later ∧ Correct new later

/-- A finite witness for the common core: a subject withdraws false and endorses
true at the later of two occasions. This is a model of supplied predicates,
not an instance attributed to any historical subject. -/
example : ReplacementConditions
    (fun t u : Bool => t = false ∧ u = true)
    (fun (_ : Unit) (j t : Bool) => j = t)
    (fun (j : Bool) (_ : Bool) => j = true)
    (fun (_ : Unit) (j k : Bool) => j ≠ k)
    () false true false true := by
  simp [ReplacementConditions]

/-- Merely adding a correct judgment while retaining the erroneous one fails. -/
example (Before : Bool → Bool → Prop) (Replaces : Unit → Bool → Bool → Prop) :
    ¬ ReplacementConditions Before (fun _ _ _ => True)
      (fun j _ => j = true) Replaces () false true false true := by
  intro h
  exact h.2.2.2.2.1 trivial

/-- An unrelated later correct belief cannot qualify when the replacement
interpretation supplies no link, even if the other endpoint data fit. -/
example (Before : Bool → Bool → Prop) :
    ¬ ReplacementConditions Before (fun (_ : Unit) (j t : Bool) => j = t)
      (fun j _ => j = true) (fun _ _ _ => False) () false true false true := by
  intro h
  exact h.2.1

/-- A replacement link alone supplies neither a temporal transition nor beliefs. -/
example (Endorses : Unit → Bool → Bool → Prop) (Correct : Bool → Bool → Prop) :
    ¬ ReplacementConditions (fun _ _ => False) Endorses Correct
      (fun _ _ _ => True) () false true false true := by
  intro h
  exact h.1

/-- Changed endorsement with no erroneous starting judgment is not correction. -/
example (Before : Bool → Bool → Prop) (Replaces : Unit → Bool → Bool → Prop) :
    ¬ ReplacementConditions Before (fun (_ : Unit) (j t : Bool) => j = t)
      (fun _ _ => True) Replaces () false true false true := by
  intro h
  exact h.2.2.2.1 trivial

/-- Changed endorsement without correctness afterward also fails. -/
example (Before : Bool → Bool → Prop) (Replaces : Unit → Bool → Bool → Prop) :
    ¬ ReplacementConditions Before (fun (_ : Unit) (j t : Bool) => j = t)
      (fun _ _ => False) Replaces () false true false true := by
  intro h
  exact h.2.2.2.2.2.2

end TruthCore.Logic.CognitiveReplacement
