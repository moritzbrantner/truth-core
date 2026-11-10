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

/-- Transport under TYPE-GLOBAL selected uniqueness. The hypothesis `unique`
ranges over every term of `OccurrenceEvent Bearer Time State prior`, including
occurrences that occur at no world; it is not implied by `UniqueRealization`
of any admission predicate. It holds only when the carriers admit exactly one
bearer and one ordered start/finish pair (`global_unique_collapses`), so it
collapses the occurrence reading into the state-pair reading. The corrected
law `accessible_same_event_condition` relativizes uniqueness to occurrences
occurring at a world accessible from `w`. -/
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

/-- A quantified conditional transport law under TYPE-GLOBAL selected
uniqueness: every term of `OccurrenceEvent B T S r` sharing the selected
transition, whether or not it ever occurs, equals the selected occurrence.
That antecedent forces a single bearer and ordered interval
(`global_unique_collapses`); `AccessibleSameEventTransport` is the corrected
law with uniqueness relativized to accessibly occurring occurrences. -/
def SameEventTransport : Prop :=
  ∀ (B T S W C : Type) (r : T → T → Prop)
    (access : W → W → Prop)
    (occurs : W → OccurrenceEvent B T S r → Prop)
    (condition : W → C → OccurrenceEvent B T S r → Prop)
    (w : W) (e : OccurrenceEvent B T S r),
    (∀ f, f.transition = e.transition → f = e) →
    (∃ f, f.transition = e.transition ∧ PossiblyConditioned access occurs condition w f) →
    PossiblyConditioned access occurs condition w e

/-- The type-global uniqueness hypothesis of `same_event_condition` forces every
bearer and every ordered interval to coincide with the selected occurrence's:
the occurrence reading then has no repeated realizations at all. -/
theorem global_unique_collapses (e : OccurrenceEvent Bearer Time State prior)
    (unique : ∀ f : OccurrenceEvent Bearer Time State prior,
      f.transition = e.transition → f = e) :
    (∀ b : Bearer, b = e.bearer) ∧
    (∀ s t : Time, prior s t → s = e.start ∧ t = e.finish) := by
  refine ⟨fun b => ?_, fun s t h => ?_⟩
  · exact congrArg OccurrenceEvent.bearer
      (unique ⟨b, e.start, e.finish, e.ordered, e.transition⟩ rfl)
  · have hf := unique ⟨e.bearer, s, t, h, e.transition⟩ rfl
    exact ⟨congrArg OccurrenceEvent.start hf, congrArg OccurrenceEvent.finish hf⟩

/-- An occurrence occurs at some world accessible from `w`. -/
def OccursAccessibly (access : World → World → Prop)
    (occurs : World → OccurrenceEvent Bearer Time State prior → Prop) (w : World)
    (f : OccurrenceEvent Bearer Time State prior) : Prop :=
  ∃ v, access w v ∧ occurs v f

/-- Selected uniqueness relativized to accessible occurrence: among the
occurrences that occur at a world accessible from `w`, only `e` carries the
selected transition. Non-occurring occurrences with that transition are allowed. -/
def AccessibleSelectedUnique (access : World → World → Prop)
    (occurs : World → OccurrenceEvent Bearer Time State prior → Prop) (w : World)
    (e : OccurrenceEvent Bearer Time State prior) : Prop :=
  ∀ f, OccursAccessibly access occurs w f → f.transition = e.transition → f = e

/-- Corrected transport: uniqueness is needed only among accessibly occurring
occurrences. The occurrence of the conditioned matching occurrence, supplied by
`PossiblyConditioned`, is what licenses applying uniqueness to it. -/
theorem accessible_same_event_condition
    (access : World → World → Prop)
    (occurs : World → OccurrenceEvent Bearer Time State prior → Prop)
    (condition : World → Condition → OccurrenceEvent Bearer Time State prior → Prop)
    (w : World) (e : OccurrenceEvent Bearer Time State prior)
    (unique : AccessibleSelectedUnique access occurs w e)
    (h : ∃ f, f.transition = e.transition ∧
      PossiblyConditioned access occurs condition w f) :
    PossiblyConditioned access occurs condition w e := by
  obtain ⟨f, hp, v, ha, ho, hc⟩ := h
  obtain rfl := unique f ⟨v, ha, ho⟩ hp
  exact ⟨v, ha, ho, hc⟩

/-- Type-global selected uniqueness implies the relativized hypothesis. -/
theorem global_unique_accessible
    (access : World → World → Prop)
    (occurs : World → OccurrenceEvent Bearer Time State prior → Prop)
    (w : World) (e : OccurrenceEvent Bearer Time State prior)
    (unique : ∀ f, f.transition = e.transition → f = e) :
    AccessibleSelectedUnique access occurs w e :=
  fun f _ hp => unique f hp

/-- `UniqueRealization`, with admission read as accessible occurrence, yields the
relativized hypothesis for any accessibly occurring selected occurrence. -/
theorem unique_realization_accessible
    (access : World → World → Prop)
    (occurs : World → OccurrenceEvent Bearer Time State prior → Prop)
    (w : World) (e : OccurrenceEvent Bearer Time State prior)
    (hu : UniqueRealization (OccursAccessibly access occurs w))
    (he : OccursAccessibly access occurs w e) :
    AccessibleSelectedUnique access occurs w e :=
  fun f hf hp => hu f e hf he hp

/-- Corrected quantified transport law: uniqueness of the selected transition is
required only among occurrences occurring at a world accessible from `w`. -/
def AccessibleSameEventTransport : Prop :=
  ∀ (B T S W C : Type) (r : T → T → Prop)
    (access : W → W → Prop)
    (occurs : W → OccurrenceEvent B T S r → Prop)
    (condition : W → C → OccurrenceEvent B T S r → Prop)
    (w : W) (e : OccurrenceEvent B T S r),
    (∀ f, (∃ v, access w v ∧ occurs v f) → f.transition = e.transition → f = e) →
    (∃ f, f.transition = e.transition ∧ PossiblyConditioned access occurs condition w f) →
    PossiblyConditioned access occurs condition w e

/-- Controls for the corrected law, all over unrestricted carriers except the
finite `repeatEvent` model:
1. the corrected law implies the type-global one;
2. `UniqueRealization` of accessible occurrence plus accessible occurrence of the
   selected event yields the relativized hypothesis;
3. type-global uniqueness collapses bearers and ordered intervals;
4. separating nonvacuity witness: two distinct occurrences share a transition,
   only `repeatEvent true` occurs; the relativized hypothesis and possible
   conditioning hold, the type-global hypothesis fails, the conclusion holds;
5. omitting uniqueness falsifies the law;
6. omitting the possible conditioning of a matching occurrence falsifies it. -/
def AccessibleTransportControls : Prop :=
  (AccessibleSameEventTransport → SameEventTransport) ∧
  (∀ (B T S W : Type) (r : T → T → Prop) (access : W → W → Prop)
    (occurs : W → OccurrenceEvent B T S r → Prop) (w : W) (e : OccurrenceEvent B T S r),
    UniqueRealization (OccursAccessibly access occurs w) →
    OccursAccessibly access occurs w e → AccessibleSelectedUnique access occurs w e) ∧
  (∀ (B T S : Type) (r : T → T → Prop) (e : OccurrenceEvent B T S r),
    (∀ f, f.transition = e.transition → f = e) →
    (∀ b : B, b = e.bearer) ∧ (∀ s t : T, r s t → s = e.start ∧ t = e.finish)) ∧
  ((repeatEvent false).transition = (repeatEvent true).transition ∧
    repeatEvent false ≠ repeatEvent true ∧
    AccessibleSelectedUnique (fun _ _ : Unit => True) (fun _ e => e = repeatEvent true) ()
      (repeatEvent true) ∧
    ¬ (∀ f, f.transition = (repeatEvent true).transition → f = repeatEvent true) ∧
    (∃ f, f.transition = (repeatEvent true).transition ∧
      PossiblyConditioned (fun _ _ : Unit => True) (fun _ e => e = repeatEvent true)
        (fun (_ : Unit) (_ : Unit) e => e = repeatEvent true) () f) ∧
    PossiblyConditioned (fun _ _ : Unit => True) (fun _ e => e = repeatEvent true)
      (fun (_ : Unit) (_ : Unit) e => e = repeatEvent true) () (repeatEvent true)) ∧
  ¬ (∀ (B T S W C : Type) (r : T → T → Prop) (access : W → W → Prop)
    (occurs : W → OccurrenceEvent B T S r → Prop)
    (condition : W → C → OccurrenceEvent B T S r → Prop)
    (w : W) (e : OccurrenceEvent B T S r),
    (∃ f, f.transition = e.transition ∧ PossiblyConditioned access occurs condition w f) →
    PossiblyConditioned access occurs condition w e) ∧
  ¬ (∀ (B T S W C : Type) (r : T → T → Prop) (access : W → W → Prop)
    (occurs : W → OccurrenceEvent B T S r → Prop)
    (condition : W → C → OccurrenceEvent B T S r → Prop)
    (w : W) (e : OccurrenceEvent B T S r),
    (∀ f, (∃ v, access w v ∧ occurs v f) → f.transition = e.transition → f = e) →
    PossiblyConditioned access occurs condition w e)

end TruthCore.Causality.EventIdentityProfiles
