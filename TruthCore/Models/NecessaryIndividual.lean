import TruthCore.Models.FiniteSupport
import TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.Alternating.Solution

/-! Finite interpretations of the existing quantifier vocabulary. These are
mathematical assignments with a universal Boolean frame and literal identity;
no metaphysical possibility, actual ontology or philosophical premise follows. -/
namespace TruthCore.Models.NecessaryIndividual
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- A nonempty rigid roster present at every world. -/
def allPresent : Bool → Bool → Prop := fun _ _ => True
/-- An empty extension at each world, despite a nonempty rigid roster and world type. -/
def allAbsent : Bool → Bool → Prop := fun _ _ => False

namespace Alternating

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation0 : ¬ (DeRe alternatingFrame alternatingExists false) := by
  exact TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.Alternating.checks.2.2.2.2.2.2.1

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation1 : DeDicto alternatingFrame alternatingExists false := by
  unfold DeDicto alternatingFrame alternatingExists
    TruthCore.Isabelle.AFP.GoedelGod.Box
  decide

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation2 : IndividualContingency alternatingFrame alternatingExists false := by
  exact TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.Alternating.checks.2.2.2.2.1

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation3 : ¬ (JointAbsence alternatingFrame alternatingExists false) := by
  unfold JointAbsence alternatingFrame alternatingExists
    TruthCore.Isabelle.AFP.GoedelGod.Dia
  decide
end Alternating

namespace AllPresent

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation0 : DeRe alternatingFrame allPresent false := by
  unfold DeRe alternatingFrame allPresent
    TruthCore.Isabelle.AFP.GoedelGod.Box
  decide

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation1 : DeDicto alternatingFrame allPresent false := by
  unfold DeDicto alternatingFrame allPresent
    TruthCore.Isabelle.AFP.GoedelGod.Box
  decide

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation2 : ¬ (IndividualContingency alternatingFrame allPresent false) := by
  unfold IndividualContingency alternatingFrame allPresent
    TruthCore.Isabelle.AFP.GoedelGod.Dia
  decide

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation3 : ¬ (JointAbsence alternatingFrame allPresent false) := by
  unfold JointAbsence alternatingFrame allPresent
    TruthCore.Isabelle.AFP.GoedelGod.Dia
  decide
end AllPresent

namespace AllAbsent

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation0 : ¬ (DeRe alternatingFrame allAbsent false) := by
  unfold DeRe alternatingFrame allAbsent
    TruthCore.Isabelle.AFP.GoedelGod.Box
  decide

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation1 : ¬ (DeDicto alternatingFrame allAbsent false) := by
  unfold DeDicto alternatingFrame allAbsent
    TruthCore.Isabelle.AFP.GoedelGod.Box
  decide

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation2 : IndividualContingency alternatingFrame allAbsent false := by
  unfold IndividualContingency alternatingFrame allAbsent
    TruthCore.Isabelle.AFP.GoedelGod.Dia
  decide

/-- Closed component evaluation in this explicit finite interpretation. -/
theorem evaluation3 : JointAbsence alternatingFrame allAbsent false := by
  unfold JointAbsence alternatingFrame allAbsent
    TruthCore.Isabelle.AFP.GoedelGod.Dia
  decide
end AllAbsent
end TruthCore.Models.NecessaryIndividual
