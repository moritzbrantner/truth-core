module

public import TruthCore.Modal.ExistenceDegrees
public import TruthCore.Causality.SurveyCapabilityControls

/-! Analyst profiles for A2 concrete-domain comparisons; attribution deferred.
Rigid candidate identity is shared across worlds. Neither profile supplies the
source-coverage → actualGraph bridge or identifies a source with an outgoing cause.
A disposition here is a productive stimulus-response process description, not
its actual manifestation. Trial descriptions need not be realizable worlds.
Masking blocks response and a fink removes the process before response. No
causal structural laws, reflexivity of accessibility or metaphysical warrant
are assumed. A fragile glass under impact is an intended example; a painted
label with no productive response is excluded. Applicability to real glass,
probabilistic processes and intrinsic powers remains OPEN.
-/

@[expose] public section
namespace TruthCore.Causality.SurveyCapabilityProfiles
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.ExistenceDegrees

/-- Endpoints exist at the witness world; only the subject must exist at the
standpoint. The same x, y are used, without counterpart substitution. -/
def Exercise {W B : Type} (m : Ontic W B) (w : W) (x y : B) : Prop :=
  m.ExistsAt w x ∧ ∃ v, m.frame.access w v ∧ m.ExistsAt v x ∧
    m.ExistsAt v y ∧ m.Causes v x y

/-- Trial and process data are explicit semantic inputs. `response` describes
process production in a trial, not an actual Ontic causal edge. -/
structure Process (T B : Type) where
  stimulus : T → Prop
  masked : T → Prop
  finked : T → Prop
  response : T → B → B → Prop

/-- A deterministic productive response profile, with at least one normal
trial description. Masked and finked trials impose no response requirement. -/
def Disposition {T B : Type} (p : Process T B) (x y : B) : Prop :=
  (∃ t, p.stimulus t ∧ ¬ p.masked t ∧ ¬ p.finked t) ∧
  ∀ t, p.stimulus t → ¬ p.masked t → ¬ p.finked t → p.response t x y

def Outgoing {B : Type} (r : B → B → Prop) (x : B) : Prop := ∃ y, r x y
def Incident {B : Type} (r : B → B → Prop) (x : B) : Prop :=
  Outgoing r x ∨ ∃ y, r y x

theorem outgoingIncident {B : Type} (r : B → B → Prop) (x : B) :
    Outgoing r x → Incident r x :=
  SurveyCapabilityControls.outgoingIncluded r x

theorem guardedPossible {W B : Type} (m : Ontic W B) (w : W) (x y : B)
    (h : Exercise m w x y) : PossibleCauseAt m w x y := by
  obtain ⟨_, v, hv, _, _, hc⟩ := h
  exact ⟨v, hv, hc⟩

/-- Explicit realization bridge: every normal response of this process has
an accessible-world causal realization with the selected endpoint guards. -/
def Realization {W B T : Type} (m : Ontic W B) (w : W) (p : Process T B) : Prop :=
  ∀ t x y, p.stimulus t → ¬ p.masked t → ¬ p.finked t →
    p.response t x y → Exercise m w x y

theorem dispositionExercise {W B T : Type} (m : Ontic W B) (w : W)
    (p : Process T B) (bridge : Realization m w p) (x y : B)
    (h : Disposition p x y) : Exercise m w x y := by
  obtain ⟨⟨t, hs, hm, hf⟩, law⟩ := h
  exact bridge t x y hs hm hf (law t hs hm hf)

/-- Reverse direction requires a process attribution, not mere causal exercise. -/
def Attribution {W B T : Type} (m : Ontic W B) (w : W) (p : Process T B) : Prop :=
  ∀ x y, Exercise m w x y → Disposition p x y

theorem exerciseDisposition {W B T : Type} (m : Ontic W B) (w : W)
    (p : Process T B) (bridge : Attribution m w p) (x y : B)
    (h : Exercise m w x y) : Disposition p x y := bridge x y h

/-- Broad coverage denial transfers only with coverage of the incoming-only
remainder. This theorem is relation-generic and applies to BOTH profiles. -/
theorem denialTransfer {B : Type} (r : B → B → Prop) (covered : B → Prop)
    (remainder : ∀ x, (∃ y, r y x) → ¬ Outgoing r x → covered x)
    (denial : ¬ ∀ x, Incident r x → covered x) :
    ¬ ∀ x, Outgoing r x → covered x := by
  classical
  intro narrow
  apply denial
  intro x hx
  by_cases h : Outgoing r x
  · exact narrow x h
  · rcases hx with ho | hi
    · exact False.elim (h ho)
    · exact remainder x hi h

/-- Nonempty productive process. Incoming-only effect separates the domains. -/
def productive : Process Unit Bool where
  stimulus := fun _ => True
  masked := fun _ => False
  finked := fun _ => False
  response := fun _ x y => x = true ∧ y = false

def inert : Process Unit Bool where
  stimulus := fun _ => True
  masked := fun _ => False
  finked := fun _ => False
  response := fun _ _ _ => False

theorem productiveIff (x y : Bool) :
    Disposition productive x y ↔ (x = true ∧ y = false) := by
  constructor
  · intro h
    exact h.2 () trivial (fun h => h) (fun h => h)
  · intro h
    exact ⟨⟨(), trivial, (fun h => h), (fun h => h)⟩, fun _ _ _ _ => h⟩

theorem dispositionSeparator :
    Outgoing (Disposition productive) true ∧
    Incident (Disposition productive) false ∧ ¬ Outgoing (Disposition productive) false := by
  refine ⟨⟨false, (productiveIff _ _).2 ⟨rfl, rfl⟩⟩,
    Or.inr ⟨true, (productiveIff _ _).2 ⟨rfl, rfl⟩⟩, ?_⟩
  rintro ⟨y, h⟩
  have bad := ((productiveIff _ _).1 h).1
  cases bad

theorem noInertDisposition (x y : Bool) : ¬ Disposition inert x y := by
  intro h
  exact h.2 () trivial (fun h => h) (fun h => h)

/-- Actual world false has no edge; accessible true realizes the response. -/
def later : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun v x y => v = true ∧ x = true ∧ y = false

def empty : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

theorem laterExercise : Exercise later false true false :=
  ⟨trivial, true, trivial, trivial, trivial, rfl, rfl, rfl⟩

theorem unexercisedDisposition :
    Disposition productive true false ∧ ¬ (∃ y, later.Causes false true y) := by
  refine ⟨(productiveIff _ _).2 ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨y, h, _⟩
  cases h

theorem omitRealization :
    Disposition productive true false ∧ ¬ Exercise empty false true false := by
  refine ⟨(productiveIff _ _).2 ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨_, v, _, _, _, h⟩
  exact h

theorem omitAttribution :
    Exercise later false true false ∧ ¬ Disposition inert true false :=
  ⟨laterExercise, noInertDisposition _ _⟩

theorem exerciseIff (x y : Bool) :
    Exercise later false x y ↔ (x = true ∧ y = false) := by
  constructor
  · rintro ⟨_, v, _, _, _, _, hx, hy⟩
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨trivial, true, trivial, trivial, trivial, rfl, hx, hy⟩

theorem exerciseSeparator :
    Outgoing (Exercise later false) true ∧ Incident (Exercise later false) false ∧
      ¬ Outgoing (Exercise later false) false := by
  refine ⟨⟨false, laterExercise⟩, Or.inr ⟨true, laterExercise⟩, ?_⟩
  rintro ⟨y, h⟩
  have bad := ((exerciseIff _ _).1 h).1
  cases bad

theorem bothBridges : Realization later false productive ∧ Attribution later false productive := by
  constructor
  · intro t x y _ _ _ h
    exact (exerciseIff _ _).2 h
  · intro x y h
    exact (productiveIff _ _).2 ((exerciseIff _ _).1 h)

/-- Apply the same strict domain counterexample to each interpreted profile. -/
theorem denialSeparators :
    (∀ x, Outgoing (Exercise later false) x → x = true) ∧
    ¬ (∀ x, Incident (Exercise later false) x → x = true) ∧
    (∀ x, Outgoing (Disposition productive) x → x = true) ∧
    ¬ (∀ x, Incident (Disposition productive) x → x = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, h⟩
    exact ((exerciseIff _ _).1 h).1
  · intro h
    have bad := h false exerciseSeparator.2.1
    cases bad
  · rintro x ⟨y, h⟩
    exact ((productiveIff _ _).1 h).1
  · intro h
    have bad := h false dispositionSeparator.2.1
    cases bad

/-- Package precisely the general comparisons and finite controls. No premise
truth, source interpretation or root conclusion occurs in this certificate. -/
def Certificate : Prop :=
  (∀ (B : Type) (r : B → B → Prop) x, Outgoing r x → Incident r x) ∧
  (∀ (W B T : Type) (m : Ontic W B) w (p : Process T B),
    Realization m w p → ∀ x y, Disposition p x y → Exercise m w x y) ∧
  (∀ (W B T : Type) (m : Ontic W B) w (p : Process T B),
    Attribution m w p → ∀ x y, Exercise m w x y → Disposition p x y) ∧
  (∀ (B : Type) (r : B → B → Prop) (covered : B → Prop),
    (∀ x, (∃ y, r y x) → ¬ Outgoing r x → covered x) →
    (¬ ∀ x, Incident r x → covered x) → ¬ ∀ x, Outgoing r x → covered x) ∧
  (Outgoing (Exercise later false) true ∧ Incident (Exercise later false) false ∧
    ¬ Outgoing (Exercise later false) false) ∧
  (Outgoing (Disposition productive) true ∧ Incident (Disposition productive) false ∧
    ¬ Outgoing (Disposition productive) false) ∧
  (Disposition productive true false ∧ ¬ (∃ y, later.Causes false true y)) ∧
  (Disposition productive true false ∧ ¬ Exercise empty false true false) ∧
  (Exercise later false true false ∧ ¬ Disposition inert true false) ∧
  (Realization later false productive ∧ Attribution later false productive) ∧
  ((∀ x, Outgoing (Exercise later false) x → x = true) ∧
    ¬ (∀ x, Incident (Exercise later false) x → x = true) ∧
    (∀ x, Outgoing (Disposition productive) x → x = true) ∧
    ¬ (∀ x, Incident (Disposition productive) x → x = true))

end TruthCore.Causality.SurveyCapabilityProfiles
