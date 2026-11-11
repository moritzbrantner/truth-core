import Lean
namespace Power1392Exercise
-- Exploratory analyst semantics, NOT a registered/certified corpus result.
-- Agent identity is fixed by the Bool argument of assertFalse/revealTrue.
inductive Task where
  | assertFalse (agent : Bool)
  | revealTrue (agent : Bool)
  deriving DecidableEq
structure Exercise where
  actor : Bool
  falseAssertion : Bool
  signs : Bool
  deriving DecidableEq
-- A successful assertion is performed by the task's very agent.
def Success (t : Task) (e : Exercise) : Prop := match t with
  | .assertFalse a => e.actor = a ∧ e.falseAssertion = true
  | .revealTrue a => e.actor = a ∧ e.falseAssertion = false ∧ e.signs = true
-- Intrinsic profile allows both truth values; signs remain a separate field.
def Intrinsic (a : Bool) (e : Exercise) : Prop := e.actor = a
-- Essential restriction, stipulated; its applicability is OPEN.
def Accessible (a : Bool) (e : Exercise) : Prop :=
  Intrinsic a e ∧ (a = true → e.falseAssertion = false)
def Generic (t : Task) : Prop := ∃ e, Success t e
def Joint (a : Bool) (t : Task) : Prop := ∃ e, Accessible a e ∧ Success t e
def Actual : Exercise := ⟨true, false, false⟩
-- Actual nonlying coexists with intrinsic false-assertion capacity of SAME agent.
theorem actualIntrinsic : Actual.falseAssertion = false ∧
    (∃ e, Intrinsic true e ∧ Success (.assertFalse true) e) := by
  exact ⟨rfl, ⟨⟨true, true, false⟩, rfl, rfl, rfl⟩⟩
-- Same task in both comparisons; nonempty accessibility and feasible-task control.
theorem separatingControl : Generic (.assertFalse true) ∧
    ¬ Joint true (.assertFalse true) ∧ Joint true (.revealTrue true) := by
  refine ⟨⟨⟨true, true, false⟩, rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨e, ha, hs⟩
    have ht := ha.2 rfl
    have hf := hs.2
    rw [ht] at hf
    cases hf
  · exact ⟨⟨true, false, true⟩, ⟨rfl, fun _ => rfl⟩, rfl, rfl, rfl⟩
-- Actual nonlying alone also admits the unrestricted exercise relation.
theorem actualDoesNotForceRestriction : Actual.falseAssertion = false ∧
    (∃ e, Intrinsic true e ∧ Success (.assertFalse true) e) := actualIntrinsic
-- A task-specific realization premise suffices; no universal omnipotence used.
theorem taskSpecific (canDo : Bool → Task → Prop)
    (realize : Joint true (.revealTrue true) → canDo true (.revealTrue true)) :
    canDo true (.revealTrue true) := realize separatingControl.2.2
end Power1392Exercise
