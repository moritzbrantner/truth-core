import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.PopulationClosure
import TruthCore.Logic.ExcludedMiddle

/-! Conditional finite-population bridge (#533). Stipulated semantics only.
The ambient rigid roster can be infinite. Cover and amalgamation remain open
metaphysical commitments; these consequences do not establish either policy. -/
namespace TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Modal
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)
universe u v
variable {W : Type u} {I : Type v}

/-- There is at least one successor, independently of population. -/
def AccessibleSuccessor (F : Frame W) (w : W) : Prop := ∃ v, F.access w v

/-- Every individual present anywhere accessible lies in one finite list.
This is a population cover, not a finite hitting set. -/
def FinitePopulationCover (F : Frame W) (present : ExistsAt W I) (w : W) : Prop :=
  ∃ xs : List I, ∀ v, F.access w v → ∀ x, present x v → x ∈ xs

/-- Infinite tails under universal accessibility. This local control uses the
issue's explicit order semantics, not a new modal engine. -/
def finiteCoverTailFrame : Frame Nat := ⟨fun _ _ => True⟩
def finiteCoverTailPresent : ExistsAt Nat Nat := fun x n => n ≤ x

/-- Universal conditional laws; the policies inside the arrows remain open. -/
def FiniteCoverLaws : Prop :=
  (∀ (W I : Type) (F : Frame W) (p : ExistsAt W I) w,
    AccessibleSuccessor F w → AbsenceAmalgamation F p w →
    IndividualContingency F p w → ∀ xs : List I,
    ∃ v, F.access w v ∧ ∀ x, x ∈ xs → ¬ p x v) ∧
  (∀ (W I : Type) (F : Frame W) (p : ExistsAt W I) w,
    AccessibleSuccessor F w → AbsenceAmalgamation F p w →
    IndividualContingency F p w → FinitePopulationCover F p w → JointAbsence F p w) ∧
  (∀ (W I : Type) (F : Frame W) (p : ExistsAt W I) w,
    AccessibleSuccessor F w → AbsenceAmalgamation F p w →
    FinitePopulationCover F p w → DeDicto F p w → ¬ IndividualContingency F p w) ∧
  (∀ (W I : Type) (F : Frame W) (p : ExistsAt W I) w,
    TruthCore.Logic.ExcludedMiddle → AccessibleSuccessor F w → AbsenceAmalgamation F p w →
    FinitePopulationCover F p w → DeDicto F p w → DeRe F p w) ∧
  (∀ (W I : Type) (F : Frame W) (p : ExistsAt W I) w (xs : List I),
    (∀ x, x ∈ xs) → FinitePopulationCover F p w)

/-- Independent controls: alternating failure, infinite tails, and no successors. -/
def FiniteCoverControls : Prop :=
  (¬ AbsenceAmalgamation alternatingFrame alternatingExists false) ∧
  (DeDicto finiteCoverTailFrame finiteCoverTailPresent 0 ∧
    IndividualContingency finiteCoverTailFrame finiteCoverTailPresent 0 ∧
    AbsenceAmalgamation finiteCoverTailFrame finiteCoverTailPresent 0 ∧
    ¬ DeRe finiteCoverTailFrame finiteCoverTailPresent 0 ∧
    ¬ FinitePopulationCover finiteCoverTailFrame finiteCoverTailPresent 0) ∧
  (let F : Frame Unit := ⟨fun _ _ => False⟩
   let p : ExistsAt Unit Empty := fun _ _ => False
   FinitePopulationCover F p () ∧ AbsenceAmalgamation F p () ∧
   IndividualContingency F p () ∧ ¬ JointAbsence F p ())
end TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
