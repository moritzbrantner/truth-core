module

public import TruthCore.Modal.CounterpossibleConservativity
public import TruthCore.Results.Explanation.MechanismInterventionParity.Solution
public import TruthCore.Results.Explanation.ExplanatorySymmetry.Solution

@[expose] public section

namespace TruthCore.Results.Modal.CounterpossibleConservativity
open TruthCore.Modal
open TruthCore.Modal.CounterpossibleConservativity
open TruthCore.Explanation.MechanismInterventionParity

/-- Normal agreement is the actual imported mechanism result at every context. -/
theorem normal_agreement (u : Bool) :
    observation .active (.normal u) = observation .idle (.normal u) :=
  (TruthCore.Results.Explanation.MechanismInterventionParity.natural_agreement ⟨true, u⟩).2.1

theorem normal_source (mode : Mode) (u : Bool) : truth mode (.normal u) .source := by
  cases mode <;> rfl

theorem repair_absence (mode : Mode) (u : Bool) : sourceAbsent mode (.repair u) := by
  cases mode <;> intro impossible <;> cases impossible

theorem no_normal_absence (mode : Mode) : ¬ NormalWitness (sourceAbsent mode) := by
  rintro ⟨u, absent⟩
  exact absent (normal_source mode u)

/-- Success is built into this precise selector; no seriality is inferred. -/
theorem success (origin : Bool) (A : State → Prop) (s : State)
    (selected : Selected origin A s) : A s := by
  cases s with
  | normal _ => exact selected
  | repair _ => exact selected.2.2

/-- A normal witness excludes every repair, leaving exactly normal evaluation. -/
theorem conservative (origin : Bool) (A Q : State → Prop) (normal : NormalWitness A) :
    SelectedConditional origin A Q ↔ NormalConditional A Q := by
  constructor
  · intro h u hu
    exact h (.normal u) hu
  · intro h s selected
    cases s with
    | normal u => exact h u selected
    | repair _ => exact (selected.1 normal).elim

theorem conservativity : Conservativity := by
  refine ⟨conservative, ?_⟩
  intro origin A B Q R normal sameAntecedent sameConsequent
  have normalB : NormalWitness B := by
    rcases normal with ⟨u, hu⟩
    exact ⟨u, (sameAntecedent u).mp hu⟩
  rw [conservative origin A Q normal, conservative origin B R normalB]
  constructor
  · intro h u hu
    exact (sameConsequent u).mp (h u ((sameAntecedent u).mpr hu))
  · intro h u hu
    exact (sameConsequent u).mpr (h u ((sameAntecedent u).mp hu))

/-- A PUBLIC-contributor-off antecedent selects exactly the originating context's
repair in BOTH interpretations; the consequent is not used in selection. -/
theorem source_off_selection (mode : Mode) (origin : Bool) (s : State) :
    Selected origin (sourceAbsent mode) s ↔ s = .repair origin := by
  cases s with
  | normal u =>
    constructor
    · intro absent
      exact (absent (normal_source mode u)).elim
    · intro impossible
      cases impossible
  | repair u =>
    constructor
    · intro selected
      exact congrArg State.repair selected.2.1
    · intro same
      have contexts : u = origin := by cases same; rfl
      exact ⟨no_normal_absence mode, contexts, repair_absence mode u⟩

theorem repaired_iff (mode : Mode) (origin : Bool) (Q : State → Prop) :
    SelectedConditional origin (sourceAbsent mode) Q ↔ Q (.repair origin) := by
  constructor
  · intro h
    exact h _ ((source_off_selection mode origin _).mpr rfl)
  · intro h s selected
    rw [(source_off_selection mode origin s).mp selected]
    exact h

/-- The opposite values come from the unchanged AND/idle equations, not an
arbitrary counterpossible-consequent flag or differing selection prescription. -/
theorem repair_discrimination :
    SelectedConditional true (sourceAbsent .active) (fun s => ¬ effectPresent .active s) ∧
    ¬ SelectedConditional true (sourceAbsent .active) (effectPresent .active) ∧
    SelectedConditional true (sourceAbsent .idle) (effectPresent .idle) ∧
    ¬ SelectedConditional true (sourceAbsent .idle) (fun s => ¬ effectPresent .idle s) := by
  refine ⟨(repaired_iff .active true _).mpr (by intro impossible; cases impossible), ?_,
    (repaired_iff .idle true _).mpr rfl, ?_⟩
  · intro h
    have impossible := (repaired_iff .active true _).mp h
    cases impossible
  · intro h
    exact ((repaired_iff .idle true _).mp h) rfl

theorem strict_absence_baseline : StrictAbsenceBaseline := by
  rcases TruthCore.Results.Explanation.ExplanatorySymmetry.comparison with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, necessaryEnables, _⟩
  exact necessaryEnables

theorem certificate : TruthCore.Modal.CounterpossibleConservativity.Certificate := by
  refine ⟨⟨TruthCore.Results.Explanation.MechanismInterventionParity.natural_agreement,
    TruthCore.Results.Explanation.MechanismInterventionParity.plural_sensitive,
    TruthCore.Results.Explanation.MechanismInterventionParity.idle_not_sensitive⟩,
    strict_absence_baseline, normal_agreement, ?_, ?_, ?_, success, conservativity,
    ?_, source_off_selection, repair_discrimination, ?_⟩
  · intro u _
    exact normal_source .active u
  · exact ⟨rfl, false, trivial, (by intro impossible; cases impossible)⟩
  · intro valid
    exact valid (fun _ _ => False) true true trivial
  · intro mode
    refine ⟨no_normal_absence mode, ?_, ?_⟩
    · intro u absent
      exact (absent (normal_source mode u)).elim
    · intro u absent
      exact (absent (normal_source mode u)).elim
  · intro mode necessary
    have impossible := necessary (.repair true) trivial
    exact repair_absence mode true impossible

end TruthCore.Results.Modal.CounterpossibleConservativity
