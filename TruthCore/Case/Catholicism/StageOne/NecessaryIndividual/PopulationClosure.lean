import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers

/-! Stipulated accessible-population closure policies for #533/#534.
These impose no frame condition or metaphysical possibility interpretation.
With no accessible pair both policies hold vacuously; neither asserts a successor.
-/
namespace TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Modal
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)
universe u v
variable {W : Type u} {I : Type v}

/-- Each ordered pair of successors has a successor whose population is contained
in both populations. No reverse inclusion or inhabited population is required. -/
def AbsenceAmalgamation (F : Frame W) (present : ExistsAt W I) (w : W) : Prop :=
  ∀ u v, F.access w u → F.access w v →
    ∃ z, F.access w z ∧ ∀ x, present x z → present x u ∧ present x v

/-- Each ordered pair of successors has a successor with exactly the intersection
population. This is extensional equality, stated pointwise without set axioms. -/
def ExactMeetClosure (F : Frame W) (present : ExistsAt W I) (w : W) : Prop :=
  ∀ u v, F.access w u → F.access w v →
    ∃ z, F.access w z ∧ ∀ x, present x z ↔ present x u ∧ present x v

end TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
