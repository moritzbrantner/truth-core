module

public import Mathlib.Basic.Logic.Basic

/-!
Independent A3 controls; attribution deferred. Occurrences and their essential
state contents remain distinct. These definitions do not complete the original
A3 sense: equality of state contents is necessary, not stipulated sufficient,
for sameness of an event across histories. No bearer or temporal ontology is
inferred from the supplied explanatory-condition relation.
-/

@[expose] public section

namespace TruthCore.Causality.EventStatePreservation

variable {World Occurrence State Condition : Type}

/-- Structured contents of a transition. State can itself be a structured
state-of-affairs type; neither the world nor occurrence is its identity. -/
structure Content (State : Type) where
  before : State
  after : State
  deriving DecidableEq

/-- Necessary preservation test, deliberately weaker than occurrence identity. -/
def Preserves (content : Occurrence → Content State) (e f : Occurrence) : Prop :=
  (content e).before = (content f).before ∧
  (content e).after = (content f).after

/-- Possible causal realization of this occurrence under a supplied modal
frame. The condition relation remains primitive; it implies no concrete being,
existence at a time, or complete explanatory sufficiency. -/
def PossiblyConditioned (access : World → World → Prop)
    (occurs : World → Occurrence → Prop)
    (condition : World → Condition → Occurrence → Prop)
    (w : World) (e : Occurrence) : Prop :=
  ∃ v, access w v ∧ occurs v e ∧ ∃ c, condition v c e

/-- Identity preserves the essential states; the converse is not asserted. -/
theorem same_preserves (content : Occurrence → Content State)
    (e f : Occurrence) (h : e = f) : Preserves content e f := by
  subst f
  exact ⟨rfl, rfl⟩

/-- Distinct occurrences can share every supplied essential state content. -/
theorem preservation_not_sufficient :
    ∃ (content : Bool → Content Bool) (e f : Bool),
      Preserves content e f ∧ e ≠ f := by
  exact ⟨fun _ => ⟨false, true⟩, false, true, ⟨rfl, rfl⟩, Bool.false_ne_true⟩

/-- A merely analogous transition can have different essential after content. -/
theorem changed_after_not_preserved :
    ¬ Preserves (fun b : Bool => (⟨false, b⟩ : Content Bool)) false true := by
  intro h
  exact Bool.false_ne_true h.2

/-- A conditioned analogous occurrence does not supply a possible condition
for the selected occurrence, and fails its essential-state test. -/
theorem analogous_not_same :
    (∃ f : Bool, PossiblyConditioned (fun _ _ : Unit => True)
      (fun (_ : Unit) (_ : Bool) => True)
      (fun (_ : Unit) (_ : Unit) (f : Bool) => f = true) () f) ∧
    ¬ PossiblyConditioned (fun _ _ : Unit => True)
      (fun (_ : Unit) (_ : Bool) => True)
      (fun (_ : Unit) (_ : Unit) (f : Bool) => f = true) () false ∧
    ¬ Preserves (fun b : Bool => (⟨false, b⟩ : Content Bool)) false true := by
  refine ⟨⟨true, (), True.intro, True.intro, (), rfl⟩, ?_,
    changed_after_not_preserved⟩
  rintro ⟨_, _, _, _, h⟩
  exact Bool.false_ne_true h

/-- The SAME occurrence may be unconditioned here and conditioned elsewhere.
Only two accessible histories are used as a counterexample to actualization;
the definitions above place no finite restriction on their carriers. -/
theorem possible_not_actual :
    PossiblyConditioned (fun _ _ : Bool => True)
      (fun (_ : Bool) (_ : Unit) => True)
      (fun (v : Bool) (_ : Unit) (_ : Unit) => v = true) false () ∧
    ¬ (∃ c : Unit, (fun (v : Bool) (_ : Unit) (_ : Unit) => v = true) false c ()) := by
  constructor
  · exact ⟨true, True.intro, True.intro, (), rfl⟩
  · rintro ⟨_, h⟩
    exact Bool.false_ne_true h

end TruthCore.Causality.EventStatePreservation
