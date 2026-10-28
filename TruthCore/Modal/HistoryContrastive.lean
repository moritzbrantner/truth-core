import TruthCore.Modal.TemporalHistory
import TruthCore.Causality.BruteFoundationExplanations

/-! Analyst controls for #467. Worlds index complete supplied presence histories;
no aggregate being, PSR, externality or metaphysical admissibility is inferred.
Discrimination is an explicit *entailing* standard, not a definition of every
adequate explanation. Internal reason truth can discriminate without explaining
why that contingent reason itself obtains. -/
namespace TruthCore.Modal.HistoryContrastive
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.BruteFoundationExplanations

/-- Extensional equality of the supplied complete presence histories. This does
not identify worlds with histories or include every qualitative property. -/
def SameHistory (h : History W B T) (v w : W) : Prop :=
  ∀ x t, h.IsAt v x t ↔ h.IsAt w x t

/-- A true candidate reason rules out every accessible different presence
history. This adds a cross-world test to world-local explanation labels. -/
def Discriminates (h : History W B T) (truth : W → R → Prop)
    (actual : W) (r : R) : Prop :=
  truth actual r ∧ ∀ v, h.ontic.frame.access actual v →
    truth v r → SameHistory h v actual

/-- Necessary truth plus discrimination excludes a genuinely accessible rival.
Necessity alone supplies no discrimination premise. -/
theorem necessary_discriminating_excludes_rival
    (h : History W B T) (truth : W → R → Prop) (a v : W) (r : R)
    (hn : ∀ w, h.ontic.frame.access a w → truth w r)
    (hd : Discriminates h truth a r)
    (hv : h.ontic.frame.access a v) (hr : ¬ SameHistory h v a) : False :=
  hr (hd.2 v hv (hn v hv))

/-- Two infinite chains, with every member caused by the next member of its
own chain. Universally accessible Bool worlds have disjoint Bool-tagged members.
Time is separate: both chains are present at every supplied Nat time. -/
def chains : History Bool (Bool × Nat) Nat where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => x.1 = w
    Causes := fun w y x => y.1 = w ∧ x.1 = w ∧ y.2 = x.2 + 1
  }
  IsAt := fun w x _ => x.1 = w
  now := 0

/-- Switch only candidate-reason truth. Both assignments retain exactly the
same ontology, causes and local explanatory links. With internal=true reason r
is true exactly when its bearer (r,0) exists; otherwise it is always true. -/
def reasons (internal : Bool) : ExplanationProfile Bool (Bool × Nat) Bool where
  reality := {
    ontic := chains.ontic
    concrete := fun _ => True
    grounds := fun _ _ _ => False
  }
  reasonPresent := fun w r => if internal then r = w else True
  explains := fun w r x => r = w ∧ x.1 = w

theorem distinct_histories : ¬ SameHistory chains true false := by
  intro h
  have hf := (h (false, 0) 0).mpr rfl
  cases hf

theorem causal_coverage :
    ∀ w x, chains.ontic.ExistsAt w x →
      ∃ y, chains.ontic.ExistsAt w y ∧ chains.ontic.Causes w y x := by
  intro w x hx
  exact ⟨(w, x.2 + 1), rfl, rfl, hx, rfl⟩

theorem coverage (b : Bool) : LocallyExplained (reasons b) := by
  intro w x _ hx
  refine ⟨w, ?_, rfl, hx⟩
  cases b <;> trivial

theorem sound (b : Bool) : ExplanationSound (reasons b) := by
  intro w r x hx
  refine ⟨?_, trivial, hx.2⟩
  cases b with
  | false => trivial
  | true => exact hx.1

/-- This internal reason passes the explicitly entailing contrastive test.
That its bearer occurs only in the selected chain is a stipulated contingent
premise, not derived from memberwise coverage or from its explanation label. -/
theorem internal_discriminates :
    Discriminates chains (reasons true).reasonPresent false false := by
  refine ⟨rfl, ?_⟩
  intro v _ hv
  change false = v at hv
  subst v
  intro x t
  rfl

theorem constant_not_discriminating :
    ¬ Discriminates chains (reasons false).reasonPresent false false := by
  intro h
  exact distinct_histories (h.2 true trivial trivial)

/-- The internal candidate has a bearer in the designated history; the same
bearer is absent from the rival, so this does not ground its own obtaining. -/
theorem internal_bearer :
    (∀ w r, (reasons true).reasonPresent w r ↔ chains.ontic.ExistsAt w (r,0)) ∧
    ¬ (reasons true).reasonPresent true false := by
  exact ⟨fun _ _ => Iff.rfl, Bool.noConfusion⟩

/-- An empty discovery assignment leaves a discriminating reason undiscovered.
This is an epistemic omission control, not a theory of actual knowledge. -/
def discovered (_ : Bool) : Prop := False

/-- Closed omission witnesses plus a general necessitation incompatibility.
No philosophical premise or root node is discharged by these assignments. -/
def Controls : Prop :=
  (∀ w x, chains.ontic.ExistsAt w x →
    ∃ y, chains.ontic.ExistsAt w y ∧ chains.ontic.Causes w y x) ∧
  LocallyExplained (reasons false) ∧ ExplanationSound (reasons false) ∧
  LocallyExplained (reasons true) ∧ ExplanationSound (reasons true) ∧
  ¬ SameHistory chains true false ∧
  Discriminates chains (reasons true).reasonPresent false false ∧
  ¬ Discriminates chains (reasons false).reasonPresent false false ∧
  (∀ w, NecessaryReasonAt (reasons false) w false) ∧
  (∀ w r, (reasons true).reasonPresent w r ↔ chains.ontic.ExistsAt w (r,0)) ∧
  ¬ (reasons true).reasonPresent true false ∧
  ¬ (∃ r, discovered r ∧ Discriminates chains (reasons true).reasonPresent false r) ∧
  (∃ r, Discriminates chains (reasons true).reasonPresent false r)

end TruthCore.Modal.HistoryContrastive
