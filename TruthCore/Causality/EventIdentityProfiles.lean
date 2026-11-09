module

public import TruthCore.Causality.EventStatePreservation

/-!
Analyst interpretations of A3; attribution deferred. Neither interpretation is
advertised as the original source sense. Carriers are unrestricted. Bearer and
time fields individuate occurrences within this profile; identifying them with
concrete agents, real time, or source events requires separate dictionaries.
Conditioning uses the existing primitive explanatory-condition relation, without
inferring prior presence, concrete causation or actuality.
-/

@[expose] public section

namespace TruthCore.Causality.EventIdentityProfiles

open EventStatePreservation

/-- State-pair sufficiency: a change is individuated by its ordered essential
contents. The inequality excludes an unchanged state, not recurring transitions. -/
structure StatePairEvent (State : Type) where
  content : Content State
  changes : content.before ≠ content.after

/-- Occurrence interpretation: a bearer undergoes a change over an interval.
The ordering is supplied explicitly, not inferred from the name `Time`.
A different bearer or interval can realize the same state-pair event. -/
structure OccurrenceEvent (Bearer Time State : Type) (prior : Time → Time → Prop) where
  bearer : Bearer
  start : Time
  finish : Time
  ordered : prior start finish
  transition : StatePairEvent State

variable {Bearer Time State World Condition : Type} {prior : Time → Time → Prop}

/-- The state-pair interpretation identifies exactly matching contents. -/
theorem pair_ext (e f : StatePairEvent State) (h : e.content = f.content) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- Occurrence-to-state uniqueness is an additional premise, not an identity
flag in the occurrence definition. It rules out repeated realizations. -/
def UniqueRealization (admitted : OccurrenceEvent Bearer Time State prior → Prop) : Prop :=
  ∀ e f, admitted e → admitted f → e.transition = f.transition → e = f

/-- Realizability is separate from uniqueness: every selected state transition
has an admitted bearer/interval occurrence. -/
def Realizable (admitted : OccurrenceEvent Bearer Time State prior → Prop) : Prop :=
  ∀ p : StatePairEvent State, ∃ e, admitted e ∧ e.transition = p

/-- Only the selected pair needs uniqueness to transport a condition from an
analogous occurrence. Global UniqueRealization is stronger than needed. -/
theorem same_event_condition
    (access : World → World → Prop)
    (occurs : World → OccurrenceEvent Bearer Time State prior → Prop)
    (condition : World → Condition → OccurrenceEvent Bearer Time State prior → Prop)
    (w : World) (e : OccurrenceEvent Bearer Time State prior)
    (unique : ∀ f, f.transition = e.transition → f = e)
    (h : ∃ f, f.transition = e.transition ∧
      PossiblyConditioned access occurs condition w f) :
    PossiblyConditioned access occurs condition w e := by
  obtain ⟨f, hp, hc⟩ := h
  rw [unique f hp] at hc
  exact hc

/-- Under an explicit worldwise realization dictionary, pair conditioning and
existence of a conditioned occurrence with those contents coincide. No identity
of occurrences is inferred by this existential equivalence. -/
theorem pair_condition_iff
    (access : World → World → Prop)
    (occurs : World → OccurrenceEvent Bearer Time State prior → Prop)
    (condition : World → Condition → OccurrenceEvent Bearer Time State prior → Prop)
    (w : World) (p : StatePairEvent State) :
    PossiblyConditioned access
      (fun v q => ∃ e, occurs v e ∧ e.transition = q)
      (fun v c q => ∃ e, occurs v e ∧ e.transition = q ∧ condition v c e) w p ↔
    ∃ e, e.transition = p ∧ PossiblyConditioned access occurs condition w e := by
  constructor
  · rintro ⟨v, ha, _, c, e, ho, hp, hc⟩
    exact ⟨e, hp, v, ha, ho, c, hc⟩
  · rintro ⟨e, hp, v, ha, ho, c, hc⟩
    exact ⟨v, ha, ⟨e, ho, hp⟩, c, e, ho, hp, hc⟩

/-- A concrete interval model; finite only as a separating witness. -/
def repeatEvent (b : Bool) : OccurrenceEvent Bool Bool Bool (fun x y => x = false ∧ y = true) :=
  ⟨b, false, true, ⟨rfl, rfl⟩, ⟨⟨false, true⟩, Bool.false_ne_true⟩⟩

/-- Matching contents do not supply occurrence identity or same-event possible
conditioning. Both occurrences are genuine changes over ordered intervals. -/
theorem repeated_transition_control :
    (repeatEvent false).transition = (repeatEvent true).transition ∧
    repeatEvent false ≠ repeatEvent true ∧
    PossiblyConditioned (fun _ _ : Unit => True) (fun _ _ => True)
      (fun (_ : Unit) (_ : Unit) e => e.bearer = true) () (repeatEvent true) ∧
    ¬ PossiblyConditioned (fun _ _ : Unit => True) (fun _ _ => True)
      (fun (_ : Unit) (_ : Unit) e => e.bearer = true) () (repeatEvent false) := by
  refine ⟨rfl, ?_, ⟨(), True.intro, True.intro, (), rfl⟩, ?_⟩
  · intro h
    exact Bool.false_ne_true (congrArg OccurrenceEvent.bearer h)
  · rintro ⟨_, _, _, _, h⟩
    exact Bool.false_ne_true h

/-- Uniqueness without realizability can be vacuous. -/
theorem uniqueness_not_realizability :
    UniqueRealization (fun _ : OccurrenceEvent Bool Bool Bool
      (fun x y => x = false ∧ y = true) => False) ∧
    ¬ Realizable (fun _ : OccurrenceEvent Bool Bool Bool
      (fun x y => x = false ∧ y = true) => False) := by
  constructor
  · intro _ _ h
    exact False.elim h
  · intro h
    obtain ⟨_, hf, _⟩ := h (repeatEvent false).transition
    exact hf

/-- Joint nonvacuity: a singleton admitted occurrence has unique realization
and a possible condition. Global realizability is not claimed. -/
theorem joint_witness :
    UniqueRealization (fun e => e = repeatEvent false) ∧
    (∃ e, e = repeatEvent false) ∧
    PossiblyConditioned (fun _ _ : Unit => True) (fun _ e => e = repeatEvent false)
      (fun (_ : Unit) (_ : Unit) e => e = repeatEvent false) () (repeatEvent false) := by
  refine ⟨?_, ⟨repeatEvent false, rfl⟩, ⟨(), True.intro, rfl, (), rfl⟩⟩
  intro e f he hf _
  exact he.trans hf.symm

/-- A quantified conditional transport law. Its uniqueness premise concerns only
occurrences sharing the selected transition, not all events or all states. -/
def SameEventTransport : Prop :=
  ∀ (B T S W C : Type) (r : T → T → Prop)
    (access : W → W → Prop)
    (occurs : W → OccurrenceEvent B T S r → Prop)
    (condition : W → C → OccurrenceEvent B T S r → Prop)
    (w : W) (e : OccurrenceEvent B T S r),
    (∀ f, f.transition = e.transition → f = e) →
    (∃ f, f.transition = e.transition ∧ PossiblyConditioned access occurs condition w f) →
    PossiblyConditioned access occurs condition w e

end TruthCore.Causality.EventIdentityProfiles
