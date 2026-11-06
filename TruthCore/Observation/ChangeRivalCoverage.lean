module

public import TruthCore.Results.Alternatives.McTaggartDefeatedByChange.Solution
public import TruthCore.Logic.ExcludedMiddle

/-! Exact general-change complement versus the stronger sourced McTaggart
bundle. The latter grants appearings; generic absence of change need not.
Preserve the original observation floor and all source meanings. -/
@[expose] public section
namespace TruthCore.Observation.ChangeRivalCoverage
open TruthCore.Observation.Change
open TruthCore.Comparison.McTaggart

/-- General change, exactly as in F3; not merely A-series change or MovedIn. -/
def NoChange {B : Type} (Changes : B → Prop) : Prop := ∀ x, ¬ Changes x

def ChangeFork {B : Type} (Changes : B → Prop) : Prop :=
  SomethingChangesReading Changes ∨ NoChange Changes

def ChangeFails {B : Type} (Changes : B → Prop) : Prop :=
  ¬ SomethingChangesReading Changes

/-- The carrier is inhabited; no actual opinion is assumed just to deny change.
This is a structural strictness model, not a thinker endorsing a changeless view. -/
def Controls : Prop :=
  Nonempty Unit ∧ NoChange (fun _ : Unit => False) ∧
  ¬ UnrealityOfTime (fun _ : Unit => False) (fun _ _ => False) (fun _ => False)
end TruthCore.Observation.ChangeRivalCoverage
